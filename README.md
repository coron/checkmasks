# CheckMasks: formal verification of side-channel countermeasures for cryptographic implementations

This is an implementation in Common Lisp of the techniques described in the paper:

[Cor17b] Jean-Sebastien Coron. Formal Verification of Side-Channel Countermeasures via Elementary Circuit Transformations. IACR eprint archive. https://eprint.iacr.org/2017/879.pdf

#### Generic verification of security properties:
* Generic verification of the t-SNI of multiplication-based refreshing
* Generic verification of the t-SNI of multiplication
* Generic verification of some properties of RefreshMasks: lemmas 5, 6, 7, 8 of [Cor17a]

#### Polynomial-time verification fo security properties:
* Poly-time verification of the t-SNI of multiplication-based refreshing [Cor17b, Lemma 3]
* Poly-time verification of some properties of RefreshMasks: [Cor17b, Lemma 4] corresponding to [Cor17a, Lemma6], and [Cor17b, Lemma 5] corresponding to [Cor17a, Lemma 5]
* Poly-time verification of the t-SNI of multiplication [Cor17b, Lemma 6]

#### Automatic generation of security proof:
* Automatic poly-time verification of t-SNI of multiplication-based refreshing, and of the two previous properties of RefreshMasks.

#### Reference:
[Cor17a] Jean-Sebastien Coron. High-order conversion from boolean to arithmetic masking. Proceedings of CHES 2017.
