/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Ring.NegOnePow
public import TauCeti.LowDimTopology.Heegaard.AlexanderGrading
import TauCeti.Algebra.Polynomial.Laurent.Coeff

/-!
# Knot gradings and the graded Euler characteristic of a doubly pointed diagram

Let `(Σ, α, β, w, z)` be a doubly pointed Heegaard diagram of a knot. The generators of its knot
Floer complex carry two integer gradings, the Maslov grading `M` and the Alexander grading `A`.
Their differences are read off from any domain `D` joining two generators `x` and `y`
(Ozsváth–Szabó, *Holomorphic disks and knot invariants*, §2–3):

`M(x) - M(y) = μ(D) - 2 n_w(D)` and `A(x) - A(y) = n_z(D) - n_w(D)`.

The Maslov grading is the grading of the singly pointed diagram `(Σ, α, β, w)` of the ambient
manifold, so only `w` enters it. For the abstract region incidence data
`TauCeti.HeegaardRegionSystem`, a pair of functions `M A : H.Generator → ℤ` satisfying these two
identities for every domain is a *knot grading* (`TauCeti.HeegaardRegionSystem.IsKnotGrading`).
Such a pair exists only when `μ(P) - 2 n_w(P)` and `n_z(P) - n_w(P)` vanish for every domain `P`
from a generator to itself, as for a knot in `S³`: there these domains are the multiples of the
whole surface, which has `μ = 2` and `n_w = n_z = 1`.

Knot gradings are determined by the domains up to an overall shift: adding constants to `M` and
`A` gives a knot grading (`TauCeti.HeegaardRegionSystem.IsKnotGrading.add_const`), and when every
two generators are joined by a domain, any two knot gradings differ by such constants
(`TauCeti.HeegaardRegionSystem.IsKnotGrading.exists_eq_add`). The hat knot Floer differential,
which counts domains of Maslov index one avoiding both basepoints, lowers `M` by one
(`TauCeti.HeegaardRegionSystem.IsKnotGrading.maslov_eq_add_one_of_hatCoefficient_ne_zero`) and
preserves `A`
(`TauCeti.HeegaardRegionSystem.IsKnotGrading.alexander_eq_of_hatCoefficient_ne_zero`).

The **graded Euler characteristic** of the knot Floer chain group is the Laurent polynomial

`χ(M, A) = ∑ₓ (-1)^{M(x)} T^{A(x)}`

(`TauCeti.HeegaardRegionSystem.gradedEulerChar`). A shift of the gradings by `(m, a)` multiplies it
by the unit `(-1)^m T^a` (`TauCeti.HeegaardRegionSystem.gradedEulerChar_add_const`), so for a
diagram whose generators are joined by domains, it is determined by the diagram up to such a unit
(`TauCeti.HeegaardRegionSystem.IsKnotGrading.exists_gradedEulerChar_eq`). If it is nonzero, at most
one Alexander grading makes it symmetric under `T ↦ T⁻¹`
(`TauCeti.HeegaardRegionSystem.IsKnotGrading.alexander_eq_of_invert_gradedEulerChar_eq`): a shift
`T^a` of a symmetric Laurent polynomial is symmetric only for `a = 0`. For a knot in `S³`,
Ozsváth and Szabó normalize the Alexander grading by a Seifert surface and show that the graded
Euler characteristic is then the symmetrized Alexander polynomial; so the symmetric Alexander
grading is the Seifert-normalized one. That identification is geometric and is not formalized
here. The Maslov shift is not fixed by symmetry; on a diagram of `S³` it is fixed by placing
`HF̂(S³)` in degree zero.

Since the hat differential lowers `M` by one and preserves `A`, the graded Euler characteristic
of the chain group is also that of the hat knot Floer homology; the comparison of the two is not
formalized here.

## Main definitions

* `TauCeti.HeegaardRegionSystem.IsKnotGrading`: integer Maslov and Alexander gradings compatible
  with all domains.
* `TauCeti.HeegaardRegionSystem.gradedEulerChar`: the graded Euler characteristic
  `∑ₓ (-1)^{M(x)} T^{A(x)}`.

## Main results

* `TauCeti.HeegaardRegionSystem.IsKnotGrading.exists_eq_add`: knot gradings are unique up to an
  overall shift when the generators are joined by domains.
* `TauCeti.HeegaardRegionSystem.IsKnotGrading.maslov_eq_add_one_of_hatCoefficient_ne_zero` and
  `TauCeti.HeegaardRegionSystem.IsKnotGrading.alexander_eq_of_hatCoefficient_ne_zero`: the hat
  differential has bidegree `(-1, 0)`.
* `TauCeti.HeegaardRegionSystem.gradedEulerChar_add_const`: shifting the gradings multiplies the
  graded Euler characteristic by `(-1)^m T^a`.
* `TauCeti.HeegaardRegionSystem.IsKnotGrading.exists_gradedEulerChar_eq`: the graded Euler
  characteristic is determined up to a unit `± T^a`.
* `TauCeti.HeegaardRegionSystem.IsKnotGrading.alexander_eq_of_invert_gradedEulerChar_eq`: the
  symmetric Alexander normalization is unique.

## References

* P. Ozsváth and Z. Szabó, *Holomorphic disks and knot invariants*, Adv. Math. **186** (2004),
  [arXiv:math/0209056](https://arxiv.org/abs/math/0209056), §2 (doubly pointed diagrams and the
  relative gradings, Lemma 2.5) and §3 (the absolute Alexander grading, its symmetry and the
  Alexander polynomial as graded Euler characteristic).
-/

public section

open LaurentPolynomial

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  {H : HeegaardRegionSystem n Point Region Basepoint}

section KnotGrading

variable [Fintype Point] [DecidableEq Region] [Fintype Region]

variable (H) in
/-- Integer Maslov and Alexander gradings `M` and `A` of the generators of a doubly pointed
diagram with basepoints `w` and `z`, for the region Euler characteristics `χ`: every domain `D`
from `x` to `y` has `M(x) - M(y) = μ(D) - 2 n_w(D)` and `A(x) - A(y) = n_z(D) - n_w(D)`. -/
structure IsKnotGrading (χ : Region → ℤ) (w z : Basepoint) (M A : H.Generator → ℤ) : Prop where
  /-- The Maslov grading drops by `μ(D) - 2 n_w(D)` along every domain `D`. -/
  maslov_sub_maslov {x y : H.Generator} {D : Region → ℤ} (hD : H.IsDomainBetween x y D) :
    ((M x - M y : ℤ) : ℚ) = H.maslovIndex χ x y D - 2 * D (H.basepoint w)
  /-- The Alexander grading drops by `n_z(D) - n_w(D)` along every domain `D`. -/
  alexander_sub_alexander {x y : H.Generator} {D : Region → ℤ} (hD : H.IsDomainBetween x y D) :
    A x - A y = D (H.basepoint z) - D (H.basepoint w)

variable {χ : Region → ℤ} {w z : Basepoint} {M A M' A' : H.Generator → ℤ}

namespace IsKnotGrading

/-- Shifting a knot grading by constants gives a knot grading. -/
theorem add_const (h : H.IsKnotGrading χ w z M A) (m a : ℤ) :
    H.IsKnotGrading χ w z (fun x => M x + m) (fun x => A x + a) where
  maslov_sub_maslov hD := by
    rw [← h.maslov_sub_maslov hD]
    push_cast
    ring
  alexander_sub_alexander hD := by
    rw [← h.alexander_sub_alexander hD]
    ring

/-- **Knot gradings are unique up to an overall shift.** When every two generators are joined by
a domain, two knot gradings differ by constants. -/
theorem exists_eq_add (h : H.IsKnotGrading χ w z M A) (h' : H.IsKnotGrading χ w z M' A')
    (hconn : ∀ x y : H.Generator, ∃ D, H.IsDomainBetween x y D) :
    ∃ m a : ℤ, M' = (fun x => M x + m) ∧ A' = fun x => A x + a := by
  rcases isEmpty_or_nonempty H.Generator with hH | ⟨⟨x₀⟩⟩
  · exact ⟨0, 0, funext isEmptyElim, funext isEmptyElim⟩
  refine ⟨M' x₀ - M x₀, A' x₀ - A x₀, funext fun x => ?_, funext fun x => ?_⟩ <;>
    obtain ⟨D, hD⟩ := hconn x x₀
  · have hM : M' x - M' x₀ = M x - M x₀ := by
      exact_mod_cast (h'.maslov_sub_maslov hD).trans (h.maslov_sub_maslov hD).symm
    omega
  · have hA := (h'.alexander_sub_alexander hD).trans (h.alexander_sub_alexander hD).symm
    omega

/-- **The hat knot Floer differential lowers the Maslov grading by one.** If the hat
differential, counting domains of Maslov index one with multiplicity zero at every basepoint, has
a nonzero coefficient from `x` to `y`, then `M(x) = M(y) + 1`. -/
theorem maslov_eq_add_one_of_hatCoefficient_ne_zero (h : H.IsKnotGrading χ w z M A)
    {x y : H.Generator} (hc : H.hatCoefficient χ x y ≠ 0) : M x = M y + 1 := by
  obtain ⟨D, hD⟩ := nonempty_hatDomains_of_hatCoefficient_ne_zero hc
  obtain ⟨hD, hb, -, hμ⟩ := mem_hatDomains_iff.mp hD
  have hM : ((M x - M y : ℤ) : ℚ) = 1 := by
    rw [h.maslov_sub_maslov hD, hμ, hb w]
    norm_num
  have hM' : M x - M y = 1 := by exact_mod_cast hM
  omega

/-- **The hat knot Floer differential preserves the Alexander grading.** If the hat differential
has a nonzero coefficient from `x` to `y`, then `A(x) = A(y)`. -/
theorem alexander_eq_of_hatCoefficient_ne_zero (h : H.IsKnotGrading χ w z M A)
    {x y : H.Generator} (hc : H.hatCoefficient χ x y ≠ 0) : A x = A y := by
  obtain ⟨D, hD⟩ := nonempty_hatDomains_of_hatCoefficient_ne_zero hc
  obtain ⟨hD, hb, -, -⟩ := mem_hatDomains_iff.mp hD
  have hA := h.alexander_sub_alexander hD
  rw [hb z, hb w] at hA
  omega

end IsKnotGrading

end KnotGrading

section EulerCharacteristic

variable (H) in
/-- The graded Euler characteristic `∑ₓ (-1)^{M(x)} T^{A(x)}` of the chain group generated by the
generators of `H`, graded by the Maslov grading `M` and the Alexander grading `A`. -/
noncomputable def gradedEulerChar (M A : H.Generator → ℤ) : ℤ[T;T⁻¹] :=
  ∑ x, (M x).negOnePow • T (A x)

theorem gradedEulerChar_def (M A : H.Generator → ℤ) :
    H.gradedEulerChar M A = ∑ x, (M x).negOnePow • T (A x) :=
  (rfl)

/-- Shifting the Maslov grading by `m` and the Alexander grading by `a` multiplies the graded
Euler characteristic by `(-1)^m T^a`. -/
theorem gradedEulerChar_add_const (M A : H.Generator → ℤ) (m a : ℤ) :
    H.gradedEulerChar (fun x => M x + m) (fun x => A x + a) =
      m.negOnePow • (T a * H.gradedEulerChar M A) := by
  simp only [gradedEulerChar_def, Finset.mul_sum, Finset.smul_sum, Int.negOnePow_add, T_add,
    mul_smul, mul_smul_comm, T_mul (A _)]
  exact Finset.sum_congr rfl fun x _ => smul_comm _ _ _

variable [Fintype Point] [DecidableEq Region] [Fintype Region]
  {χ : Region → ℤ} {w z : Basepoint} {M A M' A' : H.Generator → ℤ}

/-- **The graded Euler characteristic is determined up to a unit.** When every two generators are
joined by a domain, the graded Euler characteristics of two knot gradings differ by a factor
`(-1)^m T^a`. -/
theorem IsKnotGrading.exists_gradedEulerChar_eq (h : H.IsKnotGrading χ w z M A)
    (h' : H.IsKnotGrading χ w z M' A')
    (hconn : ∀ x y : H.Generator, ∃ D, H.IsDomainBetween x y D) :
    ∃ m a : ℤ, H.gradedEulerChar M' A' = m.negOnePow • (T a * H.gradedEulerChar M A) := by
  obtain ⟨m, a, rfl, rfl⟩ := h.exists_eq_add h' hconn
  exact ⟨m, a, gradedEulerChar_add_const M A m a⟩

/-- **The symmetric Alexander normalization is unique.** When every two generators are joined by a
domain and the graded Euler characteristic of a knot grading is nonzero and symmetric under
`T ↦ T⁻¹`, every knot grading with symmetric graded Euler characteristic has the same Alexander
grading. -/
theorem IsKnotGrading.alexander_eq_of_invert_gradedEulerChar_eq (h : H.IsKnotGrading χ w z M A)
    (h' : H.IsKnotGrading χ w z M' A')
    (hconn : ∀ x y : H.Generator, ∃ D, H.IsDomainBetween x y D)
    (hne : H.gradedEulerChar M A ≠ 0) (hs : invert (H.gradedEulerChar M A) = H.gradedEulerChar M A)
    (hs' : invert (H.gradedEulerChar M' A') = H.gradedEulerChar M' A') : A' = A := by
  obtain ⟨m, a, rfl, rfl⟩ := h.exists_eq_add h' hconn
  -- The sign `(-1)^m` commutes with `invert` and cancels, so `T a * χ` is symmetric along with
  -- the symmetric nonzero `χ`, which forces `a = 0`.
  rw [gradedEulerChar_add_const, Units.smul_def, map_zsmul] at hs'
  obtain ha | h0 := (invert_T_mul_eq_self_iff hs).mp (smul_right_injective _ (Units.ne_zero _) hs')
  · funext x
    omega
  · exact absurd h0 hne

end EulerCharacteristic

end HeegaardRegionSystem

end TauCeti
