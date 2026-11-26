/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Finsupp
public import TauCeti.Algebra.Module.GradedModule.Homology
public import TauCeti.LowDimTopology.Heegaard.Knot.EulerCharacteristic
public import TauCeti.LowDimTopology.Heegaard.StableInvariant

import TauCeti.Algebra.Module.GradedModule.EulerCharacteristic

/-!
# The bigrading of hat knot Floer homology and its graded Euler characteristic

Let `(Σ, α, β, w, z)` be a doubly pointed Heegaard diagram, recorded by region incidence data
`H : TauCeti.HeegaardRegionSystem` whose basepoints are `w` and `z`. Its hat differential counts
the nonnegative domains of Maslov index one avoiding both basepoints, and when it squares to zero
its homology `H.hatHomology χ hd` is the hat knot Floer homology `HFK̂`, with domains counted in
place of holomorphic disks.

A knot grading `(M, A)` (`TauCeti.HeegaardRegionSystem.IsKnotGrading`) places each generator `x` in
the bidegree `(M x, A x)`. The hat differential lowers the Maslov grading by one and preserves the
Alexander grading, so it is homogeneous of bidegree `(-1, 0)` for this bigrading of the chain
group (`TauCeti.HeegaardRegionSystem.IsKnotGrading.isHomogeneous_hatDifferential`), and the
homology inherits the bigrading `HFK̂ = ⊕_{m, a} HFK̂_m(a)`
(`TauCeti.HeegaardRegionSystem.IsKnotGrading.hatHomologyGrading`): the classes of bidegree
`(m, a)` are the classes of cycles of bidegree `(m, a)`.

**The graded Euler characteristic of `HFK̂`.** The Euler–Poincaré principle for a homogeneous
square-zero endomorphism (`TauCeti.InternalGrading.finsum_finrank_homology_piece_smul`), with the
weight `(m, a) ↦ (-1)^m T^a`, which changes sign under the shift by `(-1, 0)`, identifies

`∑_{m, a} (-1)^m dim HFK̂_m(a) T^a = ∑ₓ (-1)^{M(x)} T^{A(x)}`,

the graded Euler characteristic of the chain group
(`TauCeti.HeegaardRegionSystem.IsKnotGrading.finsum_finrank_hatHomologyGrading_piece_smul`). So
the graded Euler characteristic `TauCeti.HeegaardRegionSystem.gradedEulerChar` computed from the
generators is that of hat knot Floer homology. For a knot in `S³` with the Seifert-normalized
Alexander grading it is the symmetrized Alexander polynomial (Ozsváth–Szabó); that identification
is geometric and is not formalized here.

## Main definitions

* `TauCeti.HeegaardRegionSystem.IsKnotGrading.hatHomologyGrading`: the bigrading of hat knot Floer
  homology by the Maslov and Alexander gradings.

## Main results

* `TauCeti.HeegaardRegionSystem.IsKnotGrading.isHomogeneous_hatDifferential`: the hat differential
  has bidegree `(-1, 0)`.
* `TauCeti.HeegaardRegionSystem.IsKnotGrading.mem_hatHomologyGrading_piece_iff`: a class of `HFK̂`
  has bidegree `(m, a)` exactly when it is the class of a cycle of bidegree `(m, a)`.
* `TauCeti.HeegaardRegionSystem.IsKnotGrading.finsum_finrank_hatHomologyGrading_piece_smul`: the
  graded Euler characteristic of `HFK̂` is that of the chain group.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and knot invariants*, Adv. Math. **186** (2004),
  [arXiv:math/0209056](https://arxiv.org/abs/math/0209056), §3 (the bigraded groups
  `HFK̂_m(K, a)` and their graded Euler characteristic, the Alexander polynomial).
-/

public section

open LaurentPolynomial Module

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  {H : HeegaardRegionSystem n Point Region Basepoint}
  [Fintype Point] [DecidableEq Region] [Fintype Region]
  {χ : Region → ℤ} {w z : Basepoint} {M A : H.Generator → ℤ}

namespace IsKnotGrading

/-- **The hat knot Floer differential has bidegree `(-1, 0)`** for the bigrading of the chain
group placing each generator `x` in bidegree `(M x, A x)`. -/
theorem isHomogeneous_hatDifferential (h : H.IsKnotGrading χ w z M A) :
    (H.hatDifferential χ).IsHomogeneous
      (InternalGrading.finsupp (ZMod 2) fun x ↦ (M x, A x)).piece
      (InternalGrading.finsupp (ZMod 2) fun x ↦ (M x, A x)).piece (-1, 0) := by
  refine LinearMap.isHomogeneous_def.2 fun p c hc ↦ ?_
  rw [InternalGrading.mem_finsupp_piece_iff] at hc ⊢
  intro y hy
  rw [hatDifferential_apply] at hy
  -- Some generator `x` of `c` has a nonzero coefficient to `y`.
  obtain ⟨x, hx, hxy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  have hcoef : H.hatCoefficient χ x y ≠ 0 := right_ne_zero_of_mul hxy
  rw [← hc x (Finsupp.mem_support_iff.mp hx), h.maslov_eq_add_one_of_hatCoefficient_ne_zero hcoef,
    h.alexander_eq_of_hatCoefficient_ne_zero hcoef]
  simp

/-- The **bigrading of hat knot Floer homology** `HFK̂ = ⊕_{m, a} HFK̂_m(a)` by the Maslov grading
`M` and the Alexander grading `A` of a knot grading: the piece of bidegree `(m, a)` consists of the
classes of cycles of bidegree `(m, a)`. -/
noncomputable def hatHomologyGrading (h : H.IsKnotGrading χ w z M A)
    (hd : H.hatDifferential χ ∘ₗ H.hatDifferential χ = 0) :
    InternalGrading (ZMod 2) (H.hatHomology χ hd) (ℤ × ℤ) :=
  (InternalGrading.finsupp (ZMod 2) fun x ↦ (M x, A x)).homology h.isHomogeneous_hatDifferential hd

/-- A class of hat knot Floer homology has bidegree `(m, a)` exactly when it is the class of a cycle
whose generators all have Maslov grading `m` and Alexander grading `a`. -/
theorem mem_hatHomologyGrading_piece_iff (h : H.IsKnotGrading χ w z M A)
    (hd : H.hatDifferential χ ∘ₗ H.hatDifferential χ = 0) {p : ℤ × ℤ} {y : H.hatHomology χ hd} :
    y ∈ (h.hatHomologyGrading hd).piece p ↔
      ∃ c : LinearMap.ker (H.hatDifferential χ),
        (∀ x, (c : H.Generator →₀ ZMod 2) x ≠ 0 → (M x, A x) = p) ∧
          (H.hatDifferential χ).homologyπ hd c = y := by
  rw [hatHomologyGrading, InternalGrading.mem_homology_piece_iff]
  simp only [InternalGrading.mem_finsupp_piece_iff]

/-- **The graded Euler characteristic of hat knot Floer homology.** The Laurent polynomial
`∑_{m, a} (-1)^m dim HFK̂_m(a) T^a` of the bigraded hat knot Floer homology is the graded Euler
characteristic `∑ₓ (-1)^{M(x)} T^{A(x)}` of the chain group. -/
theorem finsum_finrank_hatHomologyGrading_piece_smul (h : H.IsKnotGrading χ w z M A)
    (hd : H.hatDifferential χ ∘ₗ H.hatDifferential χ = 0) :
    ∑ᶠ p : ℤ × ℤ, finrank (ZMod 2) ((h.hatHomologyGrading hd).piece p) • (p.1.negOnePow • T p.2) =
      H.gradedEulerChar M A := by
  rw [hatHomologyGrading, InternalGrading.finsum_finrank_homology_piece_smul _ _ _ fun p ↦ ?_,
    InternalGrading.finsum_finrank_finsupp_piece_smul, gradedEulerChar_def]
  -- The weight `(m, a) ↦ (-1)^m T^a` changes sign under the shift by `(-1, 0)`.
  simp [Int.negOnePow_add, Units.neg_smul]

end IsKnotGrading

end HeegaardRegionSystem

end TauCeti
