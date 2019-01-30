"""Secure client implementation

This is a skeleton file for you to build your secure file store client.

Fill in the methods for the class Client per the project specification.

You may add additional functions and classes as desired, as long as your
Client class conforms to the specification. Be sure to test against the
included functionality tests. 

Authors: Anastasia Scott and Max Lin-He
"""

from base_client import BaseClient, IntegrityError
from crypto import CryptoError
import math


class Client(BaseClient):

    chunk_size = 800 #length in hex-encoded strings

    def __init__(self, storage_server, public_key_server, crypto_object,
                 username):
        super().__init__(storage_server, public_key_server, crypto_object,
                         username)
        self.skey = {} #keeps track of key pairs
        self.sloc = {}  #final data node file id
        self.shash = {} #hash tree

    def upload(self, name, value):
        """
        store HMAC of filename as the identifier
        symmetrically encrypt value and apply a MAC for integrity
        """

        # check if keys are stored. Try in case decryption fail from revocation
        if name in self.sloc and name in self.skey:
            k_e, k_m = self.skey[name]
            id = self.sloc[name]
            hash = self.shash[name]
            try:
                self.upload_by_chunks(k_e, k_m, value, id, name)
                return
            except IntegrityError:
                pass

        #standard upload
        d = self.download_helper(name, 'check')
        if d == None or d[1] == None:
            self.upload_helper(name, value, 'd')
        else:
            info = d[1]
            self.upload_by_chunks(info[0], info[1], value, info[2][:64], name)


    def download(self, name):
        downloaded = self.download_helper(name)
        if downloaded == None:
            return None

        return downloaded[0][0]


    def share(self, user, name):
        ###create a share node that contains the location of user's share/file, as well as encryption key for the node####
        # must be encrypted
        ### share node = (file_id || keypair)

        #get k_n
        download_kn = self.storage_server.get(self.username+"/name")
        if (download_kn == None):
            return None #under attack or k_n does not exist
        else:
            kn_sign = download_kn[:512]
            kn_encrypt = download_kn[512:]
            verify_kn = self.crypto.asymmetric_verify(kn_encrypt + self.username+"/name", kn_sign, self.rsa_priv_key)
            if not verify_kn:
                return None
            k_n = self.crypto.asymmetric_decrypt(kn_encrypt, self.elg_priv_key)

        #get file_id
        file_id = self.crypto.message_authentication_code(name, k_n, hash_name="SHA256")

        #get file keypair
        download_keypair = self.storage_server.get(self.username+'/key/'+file_id)
        if (download_keypair == None):
            return None
        else:
            keypair_sign = download_keypair[:512]
            keypair_encrypt = download_keypair[512:]
            verify_keypair = self.crypto.asymmetric_verify(keypair_encrypt+self.username+'/key/'+file_id, keypair_sign, self.rsa_priv_key)
            if not verify_keypair:
                return None
            keypair = self.crypto.asymmetric_decrypt(keypair_encrypt, self.elg_priv_key)

        user_node = keypair + file_id

        ###encrypt the user_node and create its id###
        k_e = self.crypto.get_random_bytes(32)
        k_m = self.crypto.get_random_bytes(32)
        node_keypair = k_e + k_m

        username_hash = self.crypto.cryptographic_hash(user, hash_name='SHA256')
        user_node_id = self.crypto.cryptographic_hash(user_node + user, hash_name='SHA256')


        user_node_encrypted = self.encrypt_and_mac(k_e, k_m, user_node, user_node_id, "s")
        self.storage_server.put(user_node_id, user_node_encrypted)

        ###check if current user is owner of file (check for data node). if so, add to lst of shared nodes
        file = self.storage_server.get(file_id)
        file = self.decrypt_and_mac(keypair[:64], keypair[64:], file, file_id)
        if file[1] == 'd':
            #check if lst exists
            list_id = self.crypto.cryptographic_hash(file_id+'lst', hash_name='SHA256')
            download_list = self.storage_server.get(list_id)
            if download_list == None:
                lst = node_keypair + user_node_id + username_hash
                lke = self.crypto.get_random_bytes(32)
                lkm = self.crypto.get_random_bytes(32)
                list_keypair_encrypt = self.asymmetric_encrypt_and_sign(self.elg_priv_key, self.rsa_priv_key, lke+lkm, self.username+"/key/"+list_id)
                self.storage_server.put(self.username+"/key/"+list_id, list_keypair_encrypt)
                encrypted_list = self.encrypt_and_mac(lke, lkm, lst, list_id, 'l')
                self.storage_server.put(list_id, encrypted_list)
            else:
                list_keypair_encrypt = self.storage_server.get(self.username+"/key/"+list_id)
                list_keypair = self.asymmetric_decrypt_and_verify(self.elg_priv_key, self.rsa_priv_key, list_keypair_encrypt, self.username+"/key/"+list_id)
                lke = list_keypair[:64]
                lkm = list_keypair[64:]
                lst = self.decrypt_and_mac(lke, lkm, download_list, list_id)[0]
                lst = lst + node_keypair + user_node_id + username_hash
                encrypted_list = self.encrypt_and_mac(lke, lkm, lst, list_id, 'l')
                self.storage_server.put(list_id, encrypted_list)


        ###share returns msg containing encryption key of this share node and its location###
        #encrypted and signed with reciepient's public key#
        rke = self.pks.get_encryption_key(user)
        rks = self.rsa_priv_key

        msg = self.asymmetric_encrypt_and_sign(rke, rks, node_keypair + user_node_id, '')
        return msg

    def receive_share(self, from_username, newname, message):
        ###set newname to point to location given in message###
        k_e = self.elg_priv_key
        k_s = self.pks.get_signature_key(from_username)

        msg = self.asymmetric_decrypt_and_verify(k_e, k_s, message, '')
        if msg == None:
            return None

        self.upload_helper(newname, msg, 's')


    def revoke(self, user, name):
        #get k_n
        download_kn = self.storage_server.get(self.username+"/name")
        if (download_kn == None):
            return None #under attack or k_n does not exist
        else:
            kn_sign = download_kn[:512]
            kn_encrypt = download_kn[512:]
            verify_kn = self.crypto.asymmetric_verify(kn_encrypt + self.username+"/name", kn_sign, self.rsa_priv_key)
            if not verify_kn:
                return None
            k_n = self.crypto.asymmetric_decrypt(kn_encrypt, self.elg_priv_key)

        #get file_id
        file_id = self.crypto.message_authentication_code(name, k_n, hash_name="SHA256")

        #get file keypair
        download_keypair = self.storage_server.get(self.username+'/key/'+file_id)
        if (download_keypair == None):
            return None
        else:
            keypair_sign = download_keypair[:512]
            keypair_encrypt = download_keypair[512:]
            verify_keypair = self.crypto.asymmetric_verify(keypair_encrypt + self.username+'/key/'+file_id, keypair_sign, self.rsa_priv_key)
            if not verify_keypair:
                return None
            keypair = self.crypto.asymmetric_decrypt(keypair_encrypt, self.elg_priv_key)

        #####first check if user is owner of file#####
        file = self.storage_server.get(file_id)
        file = self.decrypt_and_mac(keypair[:64], keypair[64:], file, file_id)
        if file[1] != 'd':
            return None #callee is not owner

        ##### generate new keys and update key node and re-encrypt file#####
        k_e = self.crypto.get_random_bytes(32)
        k_m = self.crypto.get_random_bytes(32)
        keypair_encrypt =  self.crypto.asymmetric_encrypt(k_e + k_m, self.elg_priv_key)
        keypair_sign = self.crypto.asymmetric_sign(keypair_encrypt+self.username+"/key/"+file_id, self.rsa_priv_key)
        self.storage_server.put(self.username+"/key/"+file_id, keypair_sign + keypair_encrypt)

        # encrypted_file = self.encrypt_and_mac(k_e, k_m, file[0], file_id, 'd')
        # self.storage_server.put(file_id, encrypted_file)
        self.upload_by_chunks(k_e, k_m, file[0], file_id, name, naive=True)


        ##### update share nodes not belonging to 'user' #####
        valid_nodes = []
        list_id = self.crypto.cryptographic_hash(file_id+'lst', hash_name='SHA256')
        download_list = self.storage_server.get(list_id)
        list_keypair_encrypt = self.storage_server.get(self.username+"/key/"+list_id)
        if download_list == None or list_keypair_encrypt == None:
            return None

        list_keypair = self.asymmetric_decrypt_and_verify(self.elg_priv_key, self.rsa_priv_key, list_keypair_encrypt, self.username+"/key/"+list_id)
        lke = list_keypair[:64]
        lkm = list_keypair[64:]
        lst = self.decrypt_and_mac(lke, lkm, download_list, list_id)[0]

        revoked_username_hash = self.crypto.cryptographic_hash(user, hash_name='SHA256')
        #iterate through lst and update nodes
        while lst != '':
            node = lst[:256]
            lst = lst[256:]
            kp = node[:128]
            id = node[128:192]
            uh = node[192:]

            if uh != revoked_username_hash:
                new_node = k_e + k_m + file_id
                new_node_encrypted = self.encrypt_and_mac(kp[:64], kp[64:], new_node, id, 's')
                valid_nodes.append(node)
                self.storage_server.put(id, new_node_encrypted)

        #upload updated list
        new_lst = ''.join(valid_nodes)
        encrypted_new_list = self.encrypt_and_mac(lke, lkm, new_lst, list_id, 'l')
        self.storage_server.put(list_id, encrypted_new_list)

    def mac_hash(self, k_m, val, name):
        mac = self.crypto.message_authentication_code(val + name, k_m, hash_name='SHA256')
        return mac + val

    def verify_hash(self, k_m, val, name):
        received_mac = val[:64]
        verify_mac = self.crypto.message_authentication_code(val[64:] + name, k_m, hash_name='SHA256')
        if received_mac != verify_mac:
            raise IntegrityError
        return val[64:]

    def encrypt_and_mac(self, k_e, k_m, val, name, node_type):
        init_vec = self.crypto.get_random_bytes(16)
        encrypted_message = self.crypto.symmetric_encrypt(val, k_e,
            cipher_name='AES', mode_name='CBC', IV=init_vec)

        ciphertext = name + init_vec + encrypted_message + node_type
        #MAC is 256 bits (512 bytes printable string)
        mac = self.crypto.message_authentication_code(ciphertext, k_m,
            hash_name='SHA256')

        # send (MAC, IV, encrypted message) with (64, 32, rest) bytes binary.  Half for binary size
        load = mac + ciphertext
        return load


    def decrypt_and_mac(self, k_e, k_m, val, file_id):
        received_mac = val[:64]
        received_id = val[64:128]
        init_vec = val[128:128+32]
        node_type = val[-1]

        verify_mac = self.crypto.message_authentication_code(val[64:],
            k_m, hash_name='SHA256')

        if received_mac != verify_mac or file_id != received_id:
            raise IntegrityError

        encrypted_message = val[160:-1]
        message = self.crypto.symmetric_decrypt(encrypted_message, k_e,
            cipher_name='AES', mode_name='CBC', IV=init_vec)

        return (message, node_type)


    def asymmetric_encrypt_and_sign(self, k_e, k_s, value, n):
        encrypted_value = self.crypto.asymmetric_encrypt(value, k_e)
        sign = self.crypto.asymmetric_sign(encrypted_value + n, k_s)
        return sign + encrypted_value

    def asymmetric_decrypt_and_verify(self, k_e, k_s, value, n):
        sign = value[:512]
        encrypt = value[512:]
        verify = self.crypto.asymmetric_verify(encrypt + n, sign, k_s)
        if not verify:
            return None
        return self.crypto.asymmetric_decrypt(encrypt, k_e)

    def download_helper(self, name, mode='default'):
        #download k_n to get file_id
        download_kn = self.storage_server.get(self.username+"/name")
        if (download_kn == None):
            return None #under attack or k_n does not exist
        else:
            kn_sign = download_kn[:512]
            kn_encrypt = download_kn[512:]
            verify_kn = self.crypto.asymmetric_verify(kn_encrypt+self.username+"/name", kn_sign, self.rsa_priv_key)
            if not verify_kn:
                return None
            k_n = self.crypto.asymmetric_decrypt(kn_encrypt, self.elg_priv_key)

        file_id = self.crypto.message_authentication_code(name, k_n, hash_name="SHA256")

        ####get keys from server####
        download_keypair = self.storage_server.get(self.username+"/key/"+file_id)
        if (download_keypair == None):
            return None
        else:
            keypair_sign = download_keypair[:512]
            keypair_encrypt = download_keypair[512:]
            verify_keypair = self.crypto.asymmetric_verify(keypair_encrypt + self.username+"/key/"+file_id, keypair_sign, self.rsa_priv_key)
            if not verify_keypair:
                return None
            keypair = self.crypto.asymmetric_decrypt(keypair_encrypt, self.elg_priv_key)
            k_e = keypair[:64]
            k_m = keypair[64:]

        ###download file###
        downloaded_text = self.storage_server.get(file_id)

        #if user,file pair does not exist on server, return None
        if downloaded_text == None:
            return None

        message = self.decrypt_and_mac(k_e, k_m, downloaded_text, file_id)

        info = None
        nloc = file_id
        nke = k_e
        nkm = k_m
        ####check that message is not share node####
        while True:
            if message[1] != 's':
                break

            nke = message[0][:64]
            nkm = message[0][64:128]
            nloc = message[0][128:]

            info = (nke, nkm, nloc)

            dm = self.storage_server.get(nloc)
            message = self.decrypt_and_mac(nke, nkm, dm, nloc[:64])

        #if data note, reconstruct message from chunks
        if message[1] == 'd' and mode != 'check':
            message = (self.reconstruct_data(nke, nkm, nloc, int(message[0])), message[1])
        return message, info


    def reconstruct_data(self, k_e, k_m, id, length):
        """Given HMAC location of file and length, reconstruct the chunks and verify with hash tree"""
        num_chunks = math.ceil(length/self.chunk_size)
        hash_indices = self.get_tree_indices(length)

        #get all chunks from servers
        chunks = []
        for i in range(num_chunks):
            encrypted_chunk = self.storage_server.get(id+str(i))
            chunk = self.decrypt_and_mac(k_e, k_m, encrypted_chunk, id)[0]
            chunks.append(chunk)

        message = ''.join(chunks)

        #construct hash tree and verify match to downloaded tree
        tree = self.create_hash_tree(message)

        #download root hash
        root_id = self.crypto.message_authentication_code("hash/"+id+"/0", k_m, hash_name='SHA256')
        downloaded_root = self.storage_server.get(root_id)
        root_hash = self.verify_hash(k_m, downloaded_root, root_id)
        if tree[0] != root_hash:
            raise IntegrityError

        return message

    def upload_by_chunks(self, k_e, k_m, value, file_id, name, naive=False):
        """
        takes encryptions keys and uploads a data node as chunks
        considers efficiency through hash tree
        """

        def naive_upload():
            #let file id contain length of the file
            encrypted_len = self.encrypt_and_mac(k_e, k_m, str(file_len), file_id, 'd')
            self.storage_server.put(file_id, encrypted_len)

            i = 0
            for chunk in split_file:
                chunk_id = file_id + str(i)
                encrypted_chunk = self.encrypt_and_mac(k_e, k_m, chunk, file_id, 'd') #use file_id, will verify chunk order with hash tree
                self.storage_server.put(chunk_id, encrypted_chunk)
                i += 1

            tree = self.create_hash_tree(value)
            self.shash[name] = tree

            for chunk_num in tree:
                hash = tree[chunk_num]
                hash_id = self.crypto.message_authentication_code("hash/"+file_id+"/"+str(chunk_num), k_m, hash_name='SHA256')
                encrypted_hash = self.mac_hash(k_m, hash, hash_id)
                self.storage_server.put(hash_id, encrypted_hash)

        def delete_hash_tree():
            to_delete = self.get_tree_indices(length)
            for i in to_delete:
                hash_id = self.crypto.message_authentication_code("hash/"+file_id+"/"+str(i), k_m, hash_name='SHA256')
                self.storage_server.delete(hash_id)

        #split file into chunks
        split_file = []
        file_len = len(value)
        for i in range(math.ceil(file_len/self.chunk_size)):
            chunk = value[i*self.chunk_size:(i+1)*self.chunk_size]
            split_file.append(chunk)

        if naive: #for reuploading during revocation
            naive_upload()
            return

        ###download root hash of current file and length###
        download_len = self.storage_server.get(file_id)
        if download_len == None:
            naive_upload()
            return
        length = int(self.decrypt_and_mac(k_e, k_m, download_len, file_id)[0])
        if length != len(value): #different size upload, no need for efficiency
            delete_hash_tree()
            naive_upload()
            return
        root_id = self.crypto.message_authentication_code("hash/"+file_id+"/0", k_m, hash_name='SHA256')
        download_root = self.storage_server.get(root_id)
        prev_root = self.verify_hash(k_m, download_root, root_id)

        #create hash tree
        tree = self.create_hash_tree(value)

        if prev_root == tree[0]:
            return #file is identical to server copy
        self.storage_server.put(root_id, self.mac_hash(k_m, tree[0], root_id)) #update root

        #determine differing chunks
        tree_indices = self.get_tree_indices(len(value))
        tree_depth = self.get_tree_depth(math.ceil(len(value)/self.chunk_size))
        lvl = 1
        diff = [0]
        while lvl < tree_depth:
            temp = [2*x+1 for x in diff] + [2*x+2 for x in diff]
            diff = []
            for i in temp:
                if i in tree:
                    hash_id = self.crypto.message_authentication_code("hash/"+file_id+"/"+str(i), k_m, hash_name='SHA256')
                    dh = self.storage_server.get(hash_id)
                    if dh == None: return None #integrity attack
                    hash = self.verify_hash(k_m, dh, hash_id)
                    if hash != tree[i]:
                        diff.append(i)
                        new_hash = self.mac_hash(k_m, tree[i], hash_id)
                        self.storage_server.put(hash_id, new_hash)
            lvl += 1

        diff_chunks = [x - 2**(tree_depth - 1) + 1 for x in diff]
        for i in diff_chunks:
            chunk_id = file_id + str(i)
            encrypted_chunk = self.encrypt_and_mac(k_e, k_m, split_file[i], file_id, 'd')
            self.storage_server.put(chunk_id, encrypted_chunk)

        self.shash[name] = tree

    def upload_helper(self, name, value, node_type):
        ####check for existence of k_n for HMAC confidentiality of file name_to_hash####
        download_kn = self.storage_server.get(self.username+"/name")
        if (download_kn == None):
            k_n = self.crypto.get_random_bytes(32)
            kn_store = self.asymmetric_encrypt_and_sign(self.elg_priv_key, self.rsa_priv_key, k_n, self.username+"/name")
            self.storage_server.put(self.username+"/name", kn_store)
        else:
            k_n = self.asymmetric_decrypt_and_verify(self.elg_priv_key, self.rsa_priv_key, download_kn, self.username+"/name")
            if k_n == None:
                return False

        #generate file ID
        file_id = self.crypto.message_authentication_code(name, k_n, hash_name='SHA256')

        ####check for corresponding key pair for file_id#####
        download_keypair = self.storage_server.get(self.username+"/key/"+file_id)
        if (download_keypair == None):
            k_e = self.crypto.get_random_bytes(32)
            k_m = self.crypto.get_random_bytes(32)
            keypair_encrypt =  self.crypto.asymmetric_encrypt(k_e + k_m, self.elg_priv_key)
            keypair_sign = self.crypto.asymmetric_sign(keypair_encrypt + self.username+"/key/"+file_id, self.rsa_priv_key)
            self.storage_server.put(self.username+"/key/"+file_id, keypair_sign + keypair_encrypt)
        else:
            keypair = self.asymmetric_decrypt_and_verify(self.elg_priv_key, self.rsa_priv_key, download_keypair, self.username+"/key/"+file_id)
            if keypair == None:
                return False
            k_e = keypair[:64]
            k_m = keypair[64:]

        #####encrypt file####
        if node_type != 'd':
            load = self.encrypt_and_mac(k_e, k_m, value, file_id, node_type)
            self.storage_server.put(file_id, load)
            return

        self.sloc[name] = file_id
        self.skey[name] = (k_e, k_m)
        self.upload_by_chunks(k_e, k_m, value, file_id, name)


    def get_tree_depth(self, num_chunks):
        depth = 1
        num = 1
        while num < num_chunks:
            depth += 1
            num *= 2
        return depth

    def get_num_tree_nodes(self, num_chunks):
        #includes root hash
        if num_chunks <= 1:
            return 1
        num_nodes = 0
        curr = num_chunks
        while curr > 1:
            num_nodes += curr
            curr = math.ceil(curr/2)
        return num_nodes + 1

    def get_tree_indices(self, message_length):

        num_chunks = math.ceil(message_length/self.chunk_size)
        depth = self.get_tree_depth(num_chunks)
        child_start_index = 2**(depth-1) - 1
        indices = [x for x in range(child_start_index, child_start_index+num_chunks)]
        level_indices = indices
        while len(level_indices) > 1:
            level_indices = self.next_level_indices(level_indices)
            indices += level_indices

        return indices


    def next_level_indices(self, index_list):
        if len(index_list) == 1:
            return []

        next_list = []
        while len(index_list) >= 2:
            left = index_list.pop(0)
            right = index_list.pop(0)
            parent = (left-1)//2
            next_list.append(parent)
        #if there is odd branch leaf left over
        if len(index_list) == 1:
            next_list.append((index_list.pop()-1)//2)
        return next_list


    def next_level_hash(self, hash_list):
        """precondition: the hash_list is nonempty"""
        next_list = []
        while len(hash_list) >= 2:
            left = hash_list.pop(0)
            right = hash_list.pop(0)
            new_hash = self.crypto.cryptographic_hash(left+right, hash_name='SHA256')
            next_list.append(new_hash)
        next_list.append(hash_list.pop())
        return next_list


    def create_hash_tree(self, message):
        """
        return a list representation of a binary tree containing hashes of
        each chunk of the intended message

        the hash in index 'r' has
        parent: (r-1)//2
        children: 2r+1 and 2r+2
        """
        chunks = []
        file_len = len(message)
        for i in range(math.ceil(file_len/self.chunk_size)):
            chunk = message[i*self.chunk_size:(i+1)*self.chunk_size]
            chunks.append(chunk)

        #initialize starting parameters
        tree = {}
        num_chunks = len(chunks)
        depth = self.get_tree_depth(num_chunks)
        child_start_index = 2**(depth-1) - 1
        initial_hash = [self.crypto.cryptographic_hash(chunk, hash_name='SHA256') for chunk in chunks]
        initial_indices = [x for x in range(child_start_index, child_start_index+num_chunks)]

        #fill dictionary with leaf hashes
        for i in range(num_chunks):
            tree[initial_indices[i]] = initial_hash[i]

        #build up tree
        level_indices = initial_indices
        while len(level_indices) > 1:
            level_indices = self.next_level_indices(level_indices)
            for i in level_indices:
                if 2*i+1 in tree and 2*i+2 in tree:
                    tree[i] = self.crypto.cryptographic_hash(tree[2*i+1]+tree[2*i+2], hash_name='SHA256')
                else:
                    tree[i] = tree[2*i+1]

        return tree
