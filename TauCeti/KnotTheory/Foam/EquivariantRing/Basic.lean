/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous.PositiveWeight
import TauCeti.Data.Finsupp.Weight

/-!
# The equivariant coefficient ring of `gl(N)` foams

In symmetric `gl(N)` foam evaluation and equivariant Khovanov–Rozansky link homology, the ground
ring is the `GL(N)`-equivariant cohomology of a point, realized algebraically as the polynomial
ring `Λ_N = ℤ[e₁, …, e_N]` in `N` elementary symmetric generators where `e_{i+1} = X i` sits in
quantum degree `2(i + 1)`.

This file defines `TauCeti.EquivariantRing N` and its `ℤ`-grading
`TauCeti.EquivariantRing.grading N`:

* `EquivariantRing.grading N` equips `EquivariantRing N` with a `GradedAlgebra` structure
  concentrated in nonnegative even degrees whose degree-zero piece is `ℤ`.
* Under Mathlib's fundamental theorem of symmetric polynomials (`MvPolynomial.esymmAlgEquiv`), a
  symmetric polynomial in `N` variables homogeneous of polynomial degree `m` corresponds to an
  element of `EquivariantRing.grading N (2 * m)`
  (`EquivariantRing.esymmAlgEquiv_symm_mem_grading_iff`).

## Main definitions

* `TauCeti.EquivariantRing`: the polynomial ring `MvPolynomial (Fin N) ℤ`, with `X i` representing
  the `(i + 1)`st elementary symmetric generator `e_{i + 1}`.
* `TauCeti.EquivariantRing.weight`: the integer weight `i ↦ 2 * (i + 1)` on `Fin N`.
* `TauCeti.EquivariantRing.grading`: the `ℤ`-grading on `EquivariantRing N` placing `X i` in degree
  `2 * (i + 1)`.

## Main results

* `TauCeti.EquivariantRing.grading_eq_bot_of_lt_zero`,
  `TauCeti.EquivariantRing.grading_eq_bot_of_odd`,
  `TauCeti.EquivariantRing.grading_zero_eq_range`: `EquivariantRing N` is concentrated in
  nonnegative even degrees and connected over `ℤ`.
* `TauCeti.EquivariantRing.esymmAlgEquiv_symm_mem_grading_iff`: degree-doubling correspondence with
  homogeneous symmetric polynomials in `N` variables.

## References

* L.-H. Robert and E. Wagner, *Symmetric Khovanov–Rozansky link homologies*, J. Éc. polytech.
  Math. 7 (2020), 573–651, Section 2.1.
* M. Khovanov and L.-H. Robert, *Foam evaluation and Kronheimer–Mrowka theories*, Adv. Math. 376
  (2021), 107433.
-/

public section

namespace TauCeti

/-- The `gl(N)` equivariant coefficient ring `Λ_N = ℤ[e₁, …, e_N]`, realized as
`MvPolynomial (Fin N) ℤ` with `MvPolynomial.X i` representing `e_{i + 1}`. -/
abbrev EquivariantRing (N : ℕ) : Type := MvPolynomial (Fin N) ℤ

namespace EquivariantRing

/-- The quantum degree `2 * (i + 1)` assigned to the generator `X i = e_{i + 1}` of
`EquivariantRing N`. -/
def weight (N : ℕ) (i : Fin N) : ℤ := 2 * ((i : ℕ) + 1 : ℤ)

/-- `weight N i` is `2 * (i + 1)`. -/
@[simp]
theorem weight_apply (N : ℕ) (i : Fin N) : weight N i = 2 * ((i : ℕ) + 1 : ℤ) :=
  (rfl)

/-- Every generator of `EquivariantRing N` has strictly positive quantum degree. -/
theorem weight_pos (N : ℕ) (i : Fin N) : 0 < weight N i := by
  rw [weight_apply]
  omega

/-- Every generator of `EquivariantRing N` has nonnegative quantum degree. -/
theorem weight_nonneg (N : ℕ) (i : Fin N) : 0 ≤ weight N i :=
  (weight_pos N i).le

/-- Every generator of `EquivariantRing N` has even quantum degree. -/
theorem even_weight (N : ℕ) (i : Fin N) : Even (weight N i) :=
  ⟨(i : ℕ) + 1, by rw [weight_apply]; ring⟩

/-- The integral quantum grading on `EquivariantRing N` placing `X i = e_{i + 1}` in degree
`2 * (i + 1)`. -/
def grading (N : ℕ) : ℤ → Submodule ℤ (EquivariantRing N) :=
  MvPolynomial.weightedHomogeneousSubmodule ℤ (weight N)

/-- `grading N` is the weighted homogeneous submodule family for `weight N`. -/
theorem grading_def (N : ℕ) :
    grading N = MvPolynomial.weightedHomogeneousSubmodule ℤ (weight N) :=
  (rfl)

/-- Membership in `grading N d` is weighted homogeneity of weight `d` with respect to `weight N`. -/
@[simp]
theorem mem_grading_iff {N : ℕ} {d : ℤ} {f : EquivariantRing N} :
    f ∈ grading N d ↔ f.IsWeightedHomogeneous (weight N) d := by
  rw [grading_def, MvPolynomial.mem_weightedHomogeneousSubmodule]

/-- The `ℤ`-graded algebra structure on `EquivariantRing N` induced by `grading N`. -/
@[instance_reducible]
noncomputable def gradedAlgebra (N : ℕ) : GradedAlgebra (grading N) :=
  MvPolynomial.weightedGradedAlgebra ℤ (weight N)

attribute [instance] gradedAlgebra

/-- The degree-`d` component of `f : EquivariantRing N` under `grading N` is its weighted
homogeneous component for `weight N`. -/
@[simp]
theorem coe_decompose_grading (N : ℕ) (f : EquivariantRing N) (d : ℤ) :
    (DirectSum.decompose (grading N) f d : EquivariantRing N) =
      MvPolynomial.weightedHomogeneousComponent (weight N) d f :=
  MvPolynomial.weightedDecomposition.decompose'_apply ℤ (weight N) f d

/-- Integer constants lie in degree zero of `EquivariantRing.grading N`. -/
theorem C_mem_grading_zero (N : ℕ) (c : ℤ) : MvPolynomial.C c ∈ grading N 0 := by
  rw [mem_grading_iff]
  exact MvPolynomial.isWeightedHomogeneous_C (weight N) c

/-- The variable `X i = e_{i + 1}` is homogeneous of degree `2 * (i + 1)` in `EquivariantRing N`. -/
theorem X_mem_grading (N : ℕ) (i : Fin N) :
    MvPolynomial.X i ∈ grading N (2 * ((i : ℕ) + 1 : ℤ)) := by
  rw [mem_grading_iff, ← weight_apply]
  exact MvPolynomial.isWeightedHomogeneous_X ℤ (weight N) i

/-- `EquivariantRing N` vanishes in strictly negative degrees. -/
theorem grading_eq_bot_of_lt_zero (N : ℕ) {d : ℤ} (hd : d < 0) : grading N d = ⊥ := by
  rw [grading_def]
  exact weightedHomogeneousSubmodule_eq_bot_of_lt_zero ℤ (weight_nonneg N) hd

private theorem weight_eq_two_mul (N : ℕ) (c : Fin N →₀ ℕ) :
    Finsupp.weight (weight N) c =
      2 * (Finsupp.weight (fun i : Fin N ↦ (i : ℕ) + 1) c : ℤ) := by
  let f : ℕ →+ ℤ :=
    { toFun := fun n ↦ 2 * (n : ℤ)
      map_zero' := by simp
      map_add' := fun a b ↦ by push_cast; ring }
  have hcomp : weight N = f ∘ (fun i : Fin N ↦ (i : ℕ) + 1) := by
    ext i
    simp [f, weight_apply]
  rw [hcomp, Finsupp.weight_comp_eq_apply_linearCombination]
  rfl

/-- Every monomial exponent vector `c : Fin N →₀ ℕ` has even quantum weight in `EquivariantRing N`.
-/
theorem even_finsupp_weight (N : ℕ) (c : Fin N →₀ ℕ) : Even (Finsupp.weight (weight N) c) :=
  ⟨Finsupp.weight (fun i : Fin N ↦ (i : ℕ) + 1) c, by rw [weight_eq_two_mul, two_mul]⟩

/-- Every odd-degree homogeneous piece of `EquivariantRing N` vanishes. -/
theorem grading_eq_bot_of_odd (N : ℕ) {d : ℤ} (hd : Odd d) : grading N d = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun _ hf ↦
    MvPolynomial.IsWeightedHomogeneous.eq_zero_of_no_monomials (mem_grading_iff.mp hf)
      fun c hc ↦ by
        obtain ⟨k, hk⟩ := even_finsupp_weight N c
        obtain ⟨l, hl⟩ := hd
        omega

/-- The degree-zero piece of `EquivariantRing N` is the image of `ℤ`. -/
theorem grading_zero_eq_range (N : ℕ) :
    grading N 0 = LinearMap.range (Algebra.linearMap ℤ (EquivariantRing N)) := by
  rw [grading_def]
  exact weightedHomogeneousSubmodule_zero_eq_range ℤ (weight_pos N)

/-- Membership in `grading N (2 * m)` (`m : ℕ`) is equivalent to `ℕ`-weighted homogeneity of weight
`m` for the standard elementary-symmetric weights `i ↦ i + 1`. -/
theorem mem_grading_two_mul_iff {N : ℕ} {m : ℕ} {f : EquivariantRing N} :
    f ∈ grading N (2 * (m : ℤ)) ↔ f.IsWeightedHomogeneous (fun i : Fin N ↦ (i : ℕ) + 1) m := by
  rw [mem_grading_iff]
  refine forall_congr' fun c ↦ imp_congr_right fun _ ↦ ?_
  rw [weight_eq_two_mul]
  omega

/-- Under the elementary-symmetric algebra equivalence `MvPolynomial.esymmAlgEquiv`, a symmetric
polynomial in `N` variables is homogeneous of polynomial degree `m` if and only if its coordinate
polynomial in `EquivariantRing N` lies in quantum degree `2 * m`. -/
theorem esymmAlgEquiv_symm_mem_grading_iff {σ : Type*} [Fintype σ] {N : ℕ}
    (hn : Fintype.card σ = N) (p : MvPolynomial.symmetricSubalgebra σ ℤ) (m : ℕ) :
    (MvPolynomial.esymmAlgEquiv σ ℤ hn).symm p ∈ grading N (2 * (m : ℤ)) ↔
      (p : MvPolynomial σ ℤ).IsHomogeneous m := by
  rw [mem_grading_two_mul_iff, MvPolynomial.isWeightedHomogeneous_esymmAlgEquiv_symm_iff]

end EquivariantRing

end TauCeti
