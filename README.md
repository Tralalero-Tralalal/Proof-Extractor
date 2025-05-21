## Proof Extractor
A simple script that automatically deletes proofs from a coq file. I made this because Coq'Art , without being handfed already made proofs. All it does is it deletes everything between `Proof` and `Qed`, then 
replaces `Qed` with  `Admitted`. 

Run `python extract_proof.py <input>.v <output>.v` to get started. I added a b_tree.v file that you can test this command on. Enjoy!
