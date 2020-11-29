## Data used for the construction of the tables in [1]

Here we have three folders containing text files, each of which contains a Lisp list. This list represents the edges of the Hasse diagram associated to a finite topological space: for example, in [weakcore1_10_0.4.txt](https://github.com/jcuevas-rozo/finite-topological-spaces-kenzo/blob/master/data/weakcores/weakcore_10/weakcore_10_0.4/weakcore1_10_0.4.txt) file the list `(NIL NIL (2) (3) (4) (5) (6 1) (6) (6 1) (8 7))` represents a finite space with 10 points, density 0.4 and edges `{(2,3), (3,4), (4,5), (5,6), (6,7), (1,7), (6,8), (6,9), (1,9), (8,10), (7,10)}`.

In order to represent such a list as a finite space in Kenzo, we execute: 
```
(setf edges (make-array 10 :initial-contents '(NIL NIL (2) (3) (4) (5) (6 1) (6) (6 1) (8 7))))
(setf finite-space (build-finite-space :stong (edges-to-stong-mtrx edges)))
```
Files in [cores](https://github.com/jcuevas-rozo/finite-topological-spaces-kenzo/tree/master/data/cores) (resp. [weakcores](https://github.com/jcuevas-rozo/finite-topological-spaces-kenzo/tree/master/data/weakcores)) folder were used for making Table 1 (resp. Table 2) and those in [subdivisions](https://github.com/jcuevas-rozo/finite-topological-spaces-kenzo/tree/master/data/subdivisions) folder were used for making Table 3 and Table 4. 

  [1] Cuevas-Rozo J., Lambán L., Romero A. & Sarria H., *Effective homological computations on finite topological spaces*, AAECC, (), 1-24, DOI: [10.1007/s00200-020-00462-8](https://link.springer.com/article/10.1007/s00200-020-00462-8)
