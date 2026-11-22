/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Bases of coefficient subalgebras over the parameter ring

Let `M : ℕ → Submodule R B` be a graded family with `1 ∈ M 1`, so that the coefficient
subalgebra `TauCeti.coeffSubalgebra M ⊆ B[X]` is an `R[X]`-algebra. Suppose `v` is an `R`-basis
of `B` adapted to `M` by a degree function `d`: each `M n` is spanned by the basis vectors `v k`
with `d k ≤ n`. Then the monomials `v k X^(d k)` form an `R[X]`-basis of `coeffSubalgebra M`.
The `R[X]`-coordinate of an element `f` at `k` is the polynomial whose coefficient of `Xʲ` is
the `v`-coordinate at `k` of the coefficient of `X^(j + d k)` in `f`.

For an increasing algebra filtration this says that the Rees algebra of a filtered algebra with
a basis adapted to the filtration is free over the parameter ring, with no hypothesis on `R`
beyond commutativity. Applied to the PBW filtration of
an enveloping algebra and the ordered PBW basis, it gives the ordered PBW basis of the PBW Rees
algebra.

## Main definitions

* `TauCeti.coeffSubalgebra.basis`: the `R[X]`-basis `k ↦ v k X^(d k)` of `coeffSubalgebra M`.

## Main results

* `TauCeti.coeffSubalgebra.coe_basis_apply`: the basis vector at `k` is the monomial
  `v k X^(d k)`.
* `TauCeti.coeffSubalgebra.coeff_basis_repr_apply`: the coefficients of the `R[X]`-coordinates.
-/

public section

open Polynomial

namespace TauCeti.coeffSubalgebra

variable {R B κ : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
  (M : ℕ → Submodule R B) [SetLike.GradedMonoid M] (h1 : (1 : B) ∈ M 1)

variable (v : Module.Basis κ R B) (d : κ → ℕ)
  (hv : ∀ n, Submodule.span R (v '' {k | d k ≤ n}) = M n)
include hv

omit [SetLike.GradedMonoid M] in
/-- The basis vector `v k` belongs to `M (d k)`. -/
private theorem basis_mem (k : κ) : v k ∈ M (d k) :=
  hv (d k) ▸ Submodule.subset_span (Set.mem_image_of_mem v (le_refl (d k)))

/-- The `v`-coordinate at `k` of the coefficient of `X^(j + d k)` in an `R[X]`-linear
combination of the monomials `v i X^(d i)` is the coefficient of `Xʲ` in the `k`-th
polynomial coefficient. -/
private theorem repr_coeff_linearCombination (l : κ →₀ R[X]) (k : κ) (j : ℕ) :
    letI := algebra M h1
    v.repr (((Finsupp.linearCombination R[X]
      (fun i ↦ monomial M (d i) (v i) (basis_mem M v d hv i)) l : coeffSubalgebra M) :
        B[X]).coeff (j + d k)) k = (l k).coeff j := by
  let := algebra M h1
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single i p =>
    -- The coefficient of `X^(j + d k)` in `p (v i) X^(d i)` is a multiple of `v i`.
    rw [Finsupp.linearCombination_single, coe_smul M h1, coe_monomial,
      ← C_mul_X_pow_eq_monomial, ← (commute_X_pow _ (d i)).eq, ← mul_assoc, coeff_mul_C,
      coeff_mul_X_pow']
    split_ifs with h
    · rcases eq_or_ne i k with rfl | hik
      · simp [← Algebra.smul_def]
      · simp [← Algebra.smul_def, hik]
    · have hik : i ≠ k := by
        rintro rfl
        omega
      simp [hik]

/-- The monomials `v k X^(d k)` are linearly independent over the parameter ring. -/
private theorem linearIndependent_monomial :
    letI := algebra M h1
    LinearIndependent R[X] (fun k ↦ monomial M (d k) (v k) (basis_mem M v d hv k)) := by
  let := algebra M h1
  intro l l' h
  ext k j
  rw [← repr_coeff_linearCombination M h1 v d hv l, ← repr_coeff_linearCombination M h1 v d hv l',
    h]

/-- The monomials `v k X^(d k)` span the coefficient subalgebra over the parameter ring. -/
private theorem top_le_span_monomial :
    letI := algebra M h1
    ⊤ ≤ Submodule.span R[X]
      (Set.range fun k ↦ monomial M (d k) (v k) (basis_mem M v d hv k)) := by
  let := algebra M h1
  have := isScalarTower M h1
  set S := Submodule.span R[X]
    (Set.range fun k ↦ monomial M (d k) (v k) (basis_mem M v d hv k))
  -- Each graded piece `b Xⁿ`, `b ∈ M n`, lies in `S`, since `M n` is spanned by the `v k`
  -- with `d k ≤ n` and `v k Xⁿ = X^(n - d k) • (v k X^(d k))`.
  have hgrade (n : ℕ) : M n ≤ ((S.restrictScalars R).map
      (coeffSubalgebra M).val.toLinearMap).comap ((Polynomial.monomial n).restrictScalars R) := by
    rw [← hv n, Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨Polynomial.X ^ (n - d k) • monomial M (d k) (v k) (basis_mem M v d hv k),
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k)), ?_⟩
    simp [coe_smul M h1, X_pow_mul_monomial, Nat.add_sub_of_le hk]
  rintro f -
  induction f using DirectSum.Decomposition.inductionOn (grade M) with
  | zero => exact zero_mem _
  | add f g hf hg => exact add_mem hf hg
  | @homogeneous n f =>
    obtain ⟨b, hb, hf⟩ := mem_grade_iff.mp f.property
    have hbf := hgrade n hb
    simp only [Submodule.mem_comap, Submodule.mem_map, Submodule.restrictScalars_mem,
      AlgHom.toLinearMap_apply, Subalgebra.coe_val, LinearMap.coe_restrictScalars] at hbf
    obtain ⟨g, hg, hgf⟩ := hbf
    rwa [Subtype.ext (hgf.trans hf)] at hg

/-- **The `R[X]`-basis of a coefficient subalgebra from an adapted basis.** If `v` is an
`R`-basis of `B` and each `M n` is spanned by the `v k` with `d k ≤ n`, then the monomials
`v k X^(d k)` form a basis of `coeffSubalgebra M` over the parameter ring `R[X]`. -/
noncomputable def basis : letI := algebra M h1; Module.Basis κ R[X] (coeffSubalgebra M) :=
  letI := algebra M h1
  .mk (linearIndependent_monomial M h1 v d hv) (top_le_span_monomial M h1 v d hv)

/-- The basis vector at `k` is the monomial `v k X^(d k)`. -/
@[simp]
theorem coe_basis_apply (k : κ) :
    letI := algebra M h1
    (basis M h1 v d hv k : B[X]) = Polynomial.monomial (d k) (v k) := by
  let := algebra M h1
  rw [basis, Module.Basis.mk_apply, coe_monomial]

/-- The coefficient of `Xʲ` in the `R[X]`-coordinate at `k` of `f` is the `v`-coordinate at `k`
of the coefficient of `X^(j + d k)` in `f`. -/
@[simp]
theorem coeff_basis_repr_apply (f : coeffSubalgebra M) (k : κ) (j : ℕ) :
    letI := algebra M h1
    ((basis M h1 v d hv).repr f k).coeff j = v.repr ((f : B[X]).coeff (j + d k)) k := by
  let := algebra M h1
  have hb : ⇑(basis M h1 v d hv) = fun i ↦ monomial M (d i) (v i) (basis_mem M v d hv i) :=
    funext fun i ↦ Subtype.ext ((coe_basis_apply M h1 v d hv i).trans (coe_monomial _ _ _).symm)
  conv_rhs => rw [← (basis M h1 v d hv).linearCombination_repr f, hb]
  exact (repr_coeff_linearCombination M h1 v d hv _ k j).symm

end TauCeti.coeffSubalgebra
