/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.CupProduct
public import TauCeti.NumberTheory.HilbertSymbol.Basic

/-!
# The cup-norm theorem

Let `K` be a field in which `2` is invertible. For units `a b : Kˣ`, the cup product
`(a) ∪ (b) ∈ H²(G_K, 𝔽₂)` of their Kummer classes vanishes exactly when the norm equation
`b = x² - a y²` has a solution in `K` (`TauCeti.cup_kummerClass_eq_zero_iff`). The cup product is
the one supplied by continuous cohomology at the multiplication pairing of `𝔽₂`, so the statement
genuinely concerns that pairing. No further hypothesis on `K` is needed: in particular nothing is
assumed about a residue characteristic, and dyadic fields are included.

The proof reads the vanishing of `(a) ∪ (b)` in the Brauer group. The comparison
`Br(K) ≃ H²_cont(G_K, (Kˢ)ˣ)` sends the quaternion symbol `[(a, b)]` to the image of `(a) ∪ (b)`
under the injective map `H²(G_K, 𝔽₂) → H²_cont(G_K, (Kˢ)ˣ)`
(`TauCeti.brauerCohomologyEquiv_quaternionClass`), so `(a) ∪ (b) = 0` exactly when
`[(a, b)] = 1`, that is when `ℍ[K, a, b]` is split. The four-fold splitting criterion for
quaternion algebras then turns splitting into the norm equation, into a norm from the quadratic
algebra `K[√a]`, and into the isotropy of `⟨1, -a, -b⟩`; the norm-equation Hilbert symbol records
the same condition as the sign `+1`.

## Main results

* `TauCeti.cup_kummerClass_eq_zero_iff`: **the cup-norm theorem**, `(a) ∪ (b) = 0` if and only if
  `b = x² - a y²` for some `x y : K`.
* `TauCeti.cup_kummerClass_eq_zero_iff_quaternionClass_eq_one`,
  `TauCeti.cup_kummerClass_eq_zero_iff_nonempty_algEquiv_matrix`,
  `TauCeti.cup_kummerClass_eq_zero_iff_exists_norm_eq`,
  `TauCeti.cup_kummerClass_eq_zero_iff_not_anisotropic_weightedSumSquares`,
  `TauCeti.cup_kummerClass_eq_zero_iff_hilbertSymbol_eq_one`: the vanishing of `(a) ∪ (b)` is
  equivalent to the triviality of the quaternion symbol, to the splitting of `ℍ[K, a, b]`, to `b`
  being a norm from `K[√a]`, to the isotropy of `⟨1, -a, -b⟩`, and to `(a, b) = +1`.
* `TauCeti.cup_kummerClass_eq_cup_kummerClass_iff_quaternionClass_eq`: two cup products of
  Kummer classes agree exactly when the corresponding quaternion symbols agree.
* `TauCeti.cup_kummerClass_congr`: the binary cup identity `(a) ∪ (b) = (c) ∪ (d)` for isometric
  binary forms `⟨a, b⟩ ≅ ⟨c, d⟩`.
* `TauCeti.cup_kummerClass_neg_self` and `TauCeti.cup_kummerClass_eq_zero_of_add_eq_one`: the
  relations `(a) ∪ (-a) = 0` and, for `a + b = 1`, `(a) ∪ (b) = 0`.

## References

* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chapter XIV,
  §2, Propositions 4 and 5.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006),
  Proposition 4.7.1.
-/

public section

noncomputable section

namespace TauCeti

open _root_.ContinuousCohomology

open scoped Quaternion

variable {K : Type} [Field K] [Invertible (2 : K)]

/-- **The cup product of two Kummer classes vanishes exactly when the quaternion symbol is
trivial**: `(a) ∪ (b) = 0` in `H²(G_K, 𝔽₂)` if and only if `[(a, b)] = 1` in `Br(K)`. -/
theorem cup_kummerClass_eq_zero_iff_quaternionClass_eq_one (a b : Kˣ) :
    (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass b) = 0 ↔
      BrauerGroup.quaternionClass a b = 1 := by
  rw [← map_eq_zero_iff _ (h2MuToUnits_injective K), ← brauerCohomologyEquiv_quaternionClass,
    AddEquiv.map_eq_zero_iff, ofMul_eq_zero]

/-- **Two cup products of Kummer classes agree exactly when the quaternion symbols do**:
`(a) ∪ (b) = (c) ∪ (d)` in `H²(G_K, 𝔽₂)` if and only if `[(a, b)] = [(c, d)]` in `Br(K)`. -/
theorem cup_kummerClass_eq_cup_kummerClass_iff_quaternionClass_eq (a b c d : Kˣ) :
    (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass b) =
        (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass c) (kummerClass d) ↔
      BrauerGroup.quaternionClass a b = BrauerGroup.quaternionClass c d := by
  rw [← (h2MuToUnits_injective K).eq_iff, ← brauerCohomologyEquiv_quaternionClass,
    ← brauerCohomologyEquiv_quaternionClass, (brauerCohomologyEquiv K).injective.eq_iff,
    EmbeddingLike.apply_eq_iff_eq]

/-- **The binary cup identity**: `(a) ∪ (b) = (c) ∪ (d)` whenever the binary forms `⟨a, b⟩` and
`⟨c, d⟩` are isometric. This is what makes the second Stiefel–Whitney class of a diagonal form an
invariant of its isometry class. -/
theorem cup_kummerClass_congr {a b c d : Kˣ}
    (h : (QuadraticMap.weightedSumSquares K ![(a : K), b]).Equivalent
      (QuadraticMap.weightedSumSquares K ![(c : K), d])) :
    (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass b) =
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass c) (kummerClass d) :=
  (cup_kummerClass_eq_cup_kummerClass_iff_quaternionClass_eq a b c d).2
    (BrauerGroup.quaternionClass_congr h)

/-- **The cup-norm theorem.** For units `a` and `b` of a field in which `2` is invertible, the cup
product `(a) ∪ (b) ∈ H²(G_K, 𝔽₂)` of their Kummer classes vanishes if and only if the norm
equation `b = x² - a y²` has a solution in `K`. -/
theorem cup_kummerClass_eq_zero_iff (a b : Kˣ) :
    (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass b) = 0 ↔
      ∃ x y : K, (b : K) = x ^ 2 - a * y ^ 2 :=
  (cup_kummerClass_eq_zero_iff_quaternionClass_eq_one a b).trans
    (BrauerGroup.quaternionClass_eq_one_iff_exists_eq_sq_sub_mul_sq a b)

/-- `(a) ∪ (b) = 0` if and only if the quaternion algebra `ℍ[K, a, b]` is split. -/
theorem cup_kummerClass_eq_zero_iff_nonempty_algEquiv_matrix (a b : Kˣ) :
    (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass b) = 0 ↔
      Nonempty (ℍ[K,(a : K),(b : K)] ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) :=
  (cup_kummerClass_eq_zero_iff_quaternionClass_eq_one a b).trans
    (BrauerGroup.quaternionClass_eq_one_iff a b)

/-- `(a) ∪ (b) = 0` if and only if `b` is a norm from the quadratic algebra `K[√a]`. -/
theorem cup_kummerClass_eq_zero_iff_exists_norm_eq (a b : Kˣ) :
    (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass b) = 0 ↔
      ∃ z : QuadraticAlgebra K (a : K) 0, z.norm = b :=
  (cup_kummerClass_eq_zero_iff_nonempty_algEquiv_matrix a b).trans
    (QuaternionAlgebra.nonempty_algEquiv_matrix_iff_exists_norm_eq a b)

/-- `(a) ∪ (b) = 0` if and only if the ternary form `⟨1, -a, -b⟩` is isotropic. -/
theorem cup_kummerClass_eq_zero_iff_not_anisotropic_weightedSumSquares (a b : Kˣ) :
    (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass b) = 0 ↔
      ¬(QuadraticMap.weightedSumSquares K ![1, -(a : K), -(b : K)]).Anisotropic :=
  (cup_kummerClass_eq_zero_iff_quaternionClass_eq_one a b).trans
    (BrauerGroup.quaternionClass_eq_one_iff_not_anisotropic_weightedSumSquares a b)

/-- `(a) ∪ (b) = 0` if and only if the norm-equation Hilbert symbol `(a, b)` is `+1`. Over a
nonarchimedean local field this is the classical `{±1}`-valued Hilbert symbol. -/
theorem cup_kummerClass_eq_zero_iff_hilbertSymbol_eq_one (a b : Kˣ) :
    (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass b) = 0 ↔
      hilbertSymbol a b = 1 :=
  (cup_kummerClass_eq_zero_iff a b).trans (hilbertSymbol_eq_one_iff a b).symm

/-- The relation `(a) ∪ (-a) = 0`. -/
@[simp]
theorem cup_kummerClass_neg_self (a : Kˣ) :
    (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass (-a)) =
      0 :=
  (cup_kummerClass_eq_zero_iff_quaternionClass_eq_one a (-a)).2
    (BrauerGroup.quaternionClass_neg_self a)

/-- **The Steinberg relation**: `(a) ∪ (b) = 0` for units `a` and `b` with `a + b = 1`. -/
theorem cup_kummerClass_eq_zero_of_add_eq_one {a b : Kˣ} (hab : (a : K) + b = 1) :
    (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass b) = 0 :=
  (cup_kummerClass_eq_zero_iff a b).2 ⟨1, 1, by linear_combination hab⟩

end TauCeti
