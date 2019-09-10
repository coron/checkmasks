# CheckMasks: formal verification of side-channel countermeasures for cryptographic implementations

This is an implementation in Common Lisp of the techniques described in the paper:

[Cor17b] Jean-Sébastien Coron. Formal Verification of Side-Channel Countermeasures via Elementary Circuit Transformations. ACNS 2018: 65-82. https://eprint.iacr.org/2017/879.pdf

#### Generic verification of security properties:
* Generic verification of the t-SNI of multiplication-based refreshing
* Generic verification of the t-SNI of multiplication
* Generic verification of some properties of RefreshMasks: lemmas 5, 6, 7, 8 of [Cor17a], and Lemma 3 from [CRZ18].
* Generic verification of the t-SNI property of the Boolean to arithmetic conversion algorithm from [Cor17a] and [BCZ18].

#### Polynomial-time verification fo security properties:
* Poly-time verification of the t-SNI of multiplication-based refreshing [Cor17b, Lemma 3]
* Poly-time verification of some properties of RefreshMasks: [Cor17b, Lemma 4] corresponding to [Cor17a, Lemma6], and [Cor17b, Lemma 5] corresponding to [Cor17a, Lemma 5]
* Poly-time verification of the t-SNI of multiplication [Cor17b, Lemma 6]

#### Automatic generation of security proof:
* Automatic poly-time verification of t-SNI of multiplication-based refreshing, and of the two previous properties of RefreshMasks.

#### References:
[Cor17a] Jean-Sebastien Coron. High-order conversion from boolean to arithmetic masking. Proceedings of CHES 2017.

[CRZ18] Jean-Sébastien Coron, Franck Rondepierre, Rina Zeitoun. High Order Masking of Look-up Tables 
        with Common Shares. To appear at TCHES 2018. IACR Cryptology ePrint Archive 2017: 271 (2017)

[BCZ18] Luk Bettale, Jean-Sebastien Coron and Rina Zeitoun. Improved High-Order Conversion From Boolean
        to Arithmetic Masking. IACR TCHES 2018(2): 22-45 (2018). IACR Cryptology ePrint Archive 2018: 328 (2018)