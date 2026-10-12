/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Hasse
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Clifford

/-!
# The second Stiefel–Whitney class and the Clifford invariant

For a regular quadratic form `q` of rank `n` over a field `K` in which `2` is invertible, the
canonical comparison `ι = TauCeti.brauer2EquivH2 K : Additive Br(K)[2] ≃+ H²(G_K, 𝔽₂)` sends the
Clifford (Witt) invariant `c(q)` to

`ι(c(q)) = w₂(q) + C(n-1, 2) · ((-1) ∪ w₁(q)) + C(n+1, 4) · ((-1) ∪ (-1))`,

where `w₁(q) = (d(q))` is the Kummer class of the plain discriminant
(`TauCeti.sw1Class_eq_kummerSquareClassEquiv_discr`). This is Lam's comparison of the Clifford and
Hasse invariants (`TauCeti.RegularFormClass.cliffordInvariant_eq_hasseInvariant_mul`, Lam V.3.20)
read in Galois cohomology through `ι(s(q)) = w₂(q)` (`TauCeti.brauer2EquivH2_hasseInvariant`) and
`ι([(a, b)]) = (a) ∪ (b)`. Only the parities of the binomial coefficients matter, since
`H²(G_K, 𝔽₂)` has exponent `2`. On a class of rank `2m` with trivial signed discriminant, which is
a class whose Witt class lies in the square of the fundamental ideal, the discriminant term
cancels and the identity becomes `ι(c(q)) = w₂(q) + C(m, 2) · ((-1) ∪ (-1))`.

## Conventions in the literature

The second Stiefel–Whitney class `w₂` here is `∑_{i<j} (aᵢ) ∪ (aⱼ)` on a diagonalization
`⟨a₁, …, aₙ⟩`, Milnor's `w₂`. It is the image of Lam's Hasse invariant `s(q) = ∏_{i<j} [(aᵢ, aⱼ)]`,
which is Serre's `ε`, and not of the Clifford invariant. Serre's formula for the trace form
`Tr(x²)`, Fröhlich's comparison for orthogonal Galois representations and Kahn's formulas are
stated for this `w₂`, that is, for the Hasse invariant, with their own correction terms of the
shape `(2) ∪ (d)`. To read one of them for the Clifford invariant `c(q)`, add the two correction
terms of `TauCeti.brauer2EquivH2_cliffordInvariant`. The two invariants agree in ranks at most
two, but not in general: in rank `3` the constant term has coefficient `C(4, 4) = 1`, so for
`⟨1, 1, 1⟩` over `ℝ`, where `w₁ = w₂ = 0`, the Clifford invariant is the class `(-1) ∪ (-1)` of
Hamilton's quaternions.

## Main results

* `TauCeti.brauerCohomologyEquiv_cliffordInvariant`: the comparison with multiplicative
  coefficients sends `c(q)` to the image under the Kummer injection of the displayed class.
* `TauCeti.brauer2EquivH2_cliffordInvariant`: the exact comparison of `ι(c(q))` with `w₂(q)`.
* `TauCeti.brauer2EquivH2_cliffordInvariant_of_signedDiscr_eq_zero`: its form on a class of rank
  `2m` with trivial signed discriminant.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter V, Definition 3.12 and Theorem 3.20.
* J. Milnor, *Algebraic K-theory and quadratic forms*, Invent. Math. 9 (1970), §3.
* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. 59 (1984),
  651–676.
* A. Fröhlich, *Orthogonal representations of Galois groups, Stiefel–Whitney classes and
  Hasse–Witt invariants*, J. Reine Angew. Math. 360 (1985), 84–123.
* B. Kahn, *Classes de Stiefel–Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. 78 (1984), 223–256.
-/

public section

namespace TauCeti

open _root_.ContinuousCohomology RegularFormClass BrauerGroup

variable {K : Type} [Field K] [Invertible (2 : K)]

/-- The comparison with multiplicative coefficients sends the Clifford invariant of a regular form
class `q` of rank `n` to the image under the Kummer injection of
`w₂(q) + C(n-1, 2) · ((-1) ∪ w₁(q)) + C(n+1, 4) · ((-1) ∪ (-1))`. -/
theorem brauerCohomologyEquiv_cliffordInvariant (q : RegularFormClass K) :
    brauerCohomologyEquiv K (Additive.ofMul q.cliffordInvariant) =
      (h2MuToUnits K).hom (sw2Class q +
        (q.rank - 1).choose 2 • (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
          (kummerClass (-1)) (sw1Class q) +
        (q.rank + 1).choose 4 • (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
          (kummerClass (-1)) (kummerClass (-1))) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : Kˣ, discr q = squareClass δ := ⟨_, (squareClass_toMul_out _).symm⟩
  rw [cliffordInvariant_eq_hasseInvariant_mul, hδ, quaternionClassOnSquareClasses_squareClass,
    sw1Class_eq_kummerSquareClassEquiv_discr, hδ, kummerSquareClassEquiv_squareClass]
  simp only [ofMul_mul, ofMul_pow, map_add, map_nsmul, brauerCohomologyEquiv_hasseInvariant,
    brauerCohomologyEquiv_quaternionClass]

/-- **The exact comparison of the Clifford invariant with `w₂`** (Lam V.3.20 in Galois
cohomology). For a regular form class `q` of rank `n`, the canonical comparison
`ι : Br(K)[2] ≃ H²(G_K, 𝔽₂)` sends the Clifford invariant to
`ι(c(q)) = w₂(q) + C(n-1, 2) · ((-1) ∪ w₁(q)) + C(n+1, 4) · ((-1) ∪ (-1))`, where
`w₁(q) = (d(q))` is the Kummer class of the plain discriminant. The source is `Br(K)[2]`, with
membership supplied by `TauCeti.RegularFormClass.cliffordInvariant_sq`. -/
@[simp]
theorem brauer2EquivH2_cliffordInvariant (q : RegularFormClass K) :
    brauer2EquivH2 K (Additive.ofMul
      ⟨q.cliffordInvariant, mem_twoTorsion.mpr q.cliffordInvariant_sq⟩) =
      sw2Class q +
        (q.rank - 1).choose 2 • (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
          (kummerClass (-1)) (sw1Class q) +
        (q.rank + 1).choose 4 • (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
          (kummerClass (-1)) (kummerClass (-1)) := by
  apply h2MuToUnits_injective K
  rw [brauer2EquivH2_h2MuToUnits, brauerCohomologyEquiv_cliffordInvariant]

/-- **The comparison of the Clifford invariant with `w₂` on the square of the fundamental ideal.**
For a class `q` of rank `2m` with trivial signed discriminant,
`ι(c(q)) = w₂(q) + C(m, 2) · ((-1) ∪ (-1))`. These are the classes whose Witt class lies in the
square of the fundamental ideal (`TauCeti.wittClass_mem_fundamentalIdeal_sq_iff`). -/
theorem brauer2EquivH2_cliffordInvariant_of_signedDiscr_eq_zero {q : RegularFormClass K} {m : ℕ}
    (hq : q.rank = 2 * m) (hd : signedDiscr q = 0) :
    brauer2EquivH2 K (Additive.ofMul
      ⟨q.cliffordInvariant, mem_twoTorsion.mpr q.cliffordInvariant_sq⟩) =
      sw2Class q + m.choose 2 • (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
        (kummerClass (-1)) (kummerClass (-1)) := by
  apply h2MuToUnits_injective K
  rw [brauer2EquivH2_h2MuToUnits]
  simp only [cliffordInvariant_eq_hasseInvariant_mul_of_signedDiscr_eq_zero hq hd, ofMul_mul,
    ofMul_pow, map_add, map_nsmul, brauerCohomologyEquiv_hasseInvariant,
    brauerCohomologyEquiv_quaternionClass]

end TauCeti
