/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.BoundedProduct
public import TauCeti.Analysis.Normed.Lp.C0Ideal
public import TauCeti.Analysis.CStarAlgebra.Ideal
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# The `c₀` direct sum of C⋆-algebras

For a family of C⋆-algebras `A i`, the `c₀` direct sum `lp.c0Sum A` is the closed star
subalgebra of the bounded product `lp A ∞` of the families whose coordinate norms tend to `0`
along the cofinite filter: the closed `c₀` ideal `lp.c0Ideal A` as a star subalgebra
(`TwoSidedIdeal.toNonUnitalStarSubalgebra`), so it is a C⋆-algebra and an ideal of the bounded
product. For a finite index type it is the whole bounded
product, which is then the finite direct sum.

## Main declarations

* `lp.c0Sum`: the `c₀` direct sum as a closed star subalgebra of `lp A ∞`.
* `lp.c0SumSingle`: the isometric inclusion of the factor `A i`, with `lp.norm_c0SumSingle`;
  distinct factors are orthogonal (`lp.c0SumSingle_mul_c0SumSingle_of_ne`).
* `lp.hasSum_c0SumSingle`: every element of the `c₀` direct sum is the sum of its coordinates,
  so the finitely supported families are dense.
* `lp.c0Sum_ext_of_continuous` and `lp.c0Sum_nonUnitalStarAlgHom_ext`: continuous additive maps,
  in particular star homomorphisms, out of the `c₀` direct sum agree once they agree on every
  factor.
* `lp.liftToC0Sum`: a family of star homomorphisms `B → A i` from a star algebra `B`, vanishing at
  infinity pointwise, gives a star homomorphism `B → lp.c0Sum A`.
* `lp.c0Sum_eq_top`: for finitely many factors the `c₀` direct sum is the bounded product.

## References

* B. Blackadar, *Operator Algebras*, II.8.1.2.
-/

public section

open Filter Topology
open scoped ENNReal CStarAlgebra

noncomputable section

namespace lp

variable {ι : Type*} (A : ι → Type*) [∀ i, NonUnitalCStarAlgebra (A i)]

/-- The `c₀` direct sum of a family of C⋆-algebras: the families in the bounded product
`lp A ∞` whose coordinate norms tend to `0` along the cofinite filter, as a star subalgebra. It is
the closed ideal `lp.c0Ideal A` viewed as a star subalgebra. -/
def c0Sum : NonUnitalStarSubalgebra ℂ (lp A ∞) :=
  (c0Ideal A).toNonUnitalStarSubalgebra

/-- The carrier of the `c₀` direct sum is the `c₀` ideal of the bounded product. -/
@[simp]
theorem coe_c0Sum : (c0Sum A : Set (lp A ∞)) = c0Ideal A :=
  (c0Ideal A).coe_toNonUnitalStarSubalgebra

/-- The `c₀` direct sum is closed in the bounded product, hence a C⋆-algebra. -/
instance isClosed_c0Sum : IsClosed (c0Sum A : Set (lp A ∞)) :=
  (c0Ideal A).isClosed_toNonUnitalStarSubalgebra

/-- For finitely many factors, the `c₀` direct sum is the whole bounded product. -/
@[simp]
theorem c0Sum_eq_top [Finite ι] : c0Sum A = ⊤ :=
  eq_top_iff.2 fun a _ ↦ by
    rw [← SetLike.mem_coe, coe_c0Sum, SetLike.mem_coe, mem_c0Ideal]
    simp [cofinite_eq_bot]

variable {A}

/-- A bounded family lies in the `c₀` direct sum when its coordinate norms tend to `0`. -/
@[simp]
theorem mem_c0Sum {a : lp A ∞} : a ∈ c0Sum A ↔ Tendsto (fun i ↦ ‖a i‖) cofinite (𝓝 0) := by
  rw [← SetLike.mem_coe, coe_c0Sum, SetLike.mem_coe, mem_c0Ideal]

/-- The `c₀` direct sum absorbs multiplication on the left by the bounded product. -/
theorem mul_mem_c0Sum_left (a : lp A ∞) {b : lp A ∞} (hb : b ∈ c0Sum A) : a * b ∈ c0Sum A := by
  rw [← SetLike.mem_coe, coe_c0Sum] at hb ⊢
  exact (c0Ideal A).mul_mem_left a b hb

/-- The `c₀` direct sum absorbs multiplication on the right by the bounded product. -/
theorem mul_mem_c0Sum_right {a : lp A ∞} (ha : a ∈ c0Sum A) (b : lp A ∞) : a * b ∈ c0Sum A := by
  rw [← SetLike.mem_coe, coe_c0Sum] at ha ⊢
  exact (c0Ideal A).mul_mem_right a b ha

section Lift

variable {B : Type*} [NonUnitalNonAssocSemiring B] [DistribMulAction ℂ B] [Star B]

/-- A family of star homomorphisms `φ i : B → A i` with `‖φ i b‖ → 0` along the cofinite filter
for every `b` gives a star homomorphism into the `c₀` direct sum. The family is bounded at each
`b` because it tends to `0`, so `B` needs no norm. -/
def liftToC0Sum (φ : ∀ i, B →⋆ₙₐ[ℂ] A i)
    (hφ : ∀ b, Tendsto (fun i ↦ ‖φ i b‖) cofinite (𝓝 0)) : B →⋆ₙₐ[ℂ] c0Sum A where
  toFun b := ⟨⟨fun i ↦ φ i b, memℓp_infty (hφ b).bddAbove_range_of_cofinite⟩,
    mem_c0Sum.2 (hφ b)⟩
  map_smul' c b := Subtype.ext <| lp.ext <| funext fun i ↦ map_smul (φ i) c b
  map_zero' := Subtype.ext <| lp.ext <| funext fun i ↦ map_zero (φ i)
  map_add' b b' := Subtype.ext <| lp.ext <| funext fun i ↦ map_add (φ i) b b'
  map_mul' b b' := Subtype.ext <| lp.ext <| funext fun i ↦ map_mul (φ i) b b'
  map_star' b := Subtype.ext <| lp.ext <| funext fun i ↦ map_star (φ i) b

/-- The `i`-th coordinate of `lp.liftToC0Sum φ hφ b` is `φ i b`. -/
@[simp]
theorem liftToC0Sum_apply_apply (φ : ∀ i, B →⋆ₙₐ[ℂ] A i)
    (hφ : ∀ b, Tendsto (fun i ↦ ‖φ i b‖) cofinite (𝓝 0)) (b : B) (i : ι) :
    (liftToC0Sum φ hφ b : lp A ∞) i = φ i b :=
  (rfl)

/-- Over a C⋆-algebra, `lp.liftToC0Sum` is `lp.liftNonUnitalStarAlgHom` with its range in the
`c₀` direct sum. -/
theorem coe_liftToC0Sum_apply {B : Type*} [NonUnitalCStarAlgebra B] (φ : ∀ i, B →⋆ₙₐ[ℂ] A i)
    (hφ : ∀ b, Tendsto (fun i ↦ ‖φ i b‖) cofinite (𝓝 0)) (b : B) :
    (liftToC0Sum φ hφ b : lp A ∞) = liftNonUnitalStarAlgHom φ b :=
  lp.ext <| funext fun i ↦ by simp

end Lift

section Single

variable [DecidableEq ι]

/-- A family supported at a single index lies in the `c₀` direct sum. -/
theorem single_mem_c0Sum (i : ι) (a : A i) : lp.single ∞ i a ∈ c0Sum A := by
  refine mem_c0Sum.2 <| tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_cofinite_ne i] with j hj
  simp [Pi.single_eq_of_ne hj]

/-- The family supported at `i` with value `a * b` is the product of those with values `a` and
`b`. -/
theorem single_mul_single (i : ι) (a b : A i) :
    lp.single ∞ i (a * b) = lp.single ∞ i a * lp.single ∞ i b :=
  lp.ext <| by rw [infty_coeFn_mul, lp.coeFn_single, lp.coeFn_single, lp.coeFn_single,
    Pi.single_mul]

/-- The family supported at `i` with value `star a` is the adjoint of the one with value `a`. -/
theorem single_star (i : ι) (a : A i) : lp.single ∞ i (star a) = star (lp.single ∞ i a) :=
  lp.ext <| funext fun j ↦ by
    rw [lp.star_apply, lp.coeFn_single, lp.coeFn_single, Pi.single_star, Pi.star_apply]

variable (A) in
/-- The inclusion of the factor `A i` into the `c₀` direct sum, as a star homomorphism. -/
def c0SumSingle (i : ι) : A i →⋆ₙₐ[ℂ] c0Sum A where
  toFun a := ⟨lp.single ∞ i a, single_mem_c0Sum i a⟩
  map_smul' c a := Subtype.ext <| lp.single_smul ∞ i c a
  map_zero' := Subtype.ext <| lp.single_zero ∞ i
  map_add' a b := Subtype.ext <| lp.single_add ∞ i a b
  map_mul' a b := Subtype.ext <| single_mul_single i a b
  map_star' a := Subtype.ext <| single_star i a

/-- The inclusion of `A i` sends `a` to the family `lp.single ∞ i a`. -/
@[simp]
theorem coe_c0SumSingle_apply (i : ι) (a : A i) :
    (c0SumSingle A i a : lp A ∞) = lp.single ∞ i a :=
  (rfl)

/-- The inclusion of a factor into the `c₀` direct sum is isometric. -/
theorem norm_c0SumSingle (i : ι) (a : A i) : ‖c0SumSingle A i a‖ = ‖a‖ := by
  rw [AddSubgroupClass.coe_norm, coe_c0SumSingle_apply, lp.norm_single ENNReal.zero_lt_top]

variable (A) in
/-- The inclusion of a factor into the `c₀` direct sum is an isometry. -/
theorem isometry_c0SumSingle (i : ι) : Isometry (c0SumSingle A i) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_c0SumSingle i)

variable (A) in
/-- The inclusion of a factor into the `c₀` direct sum is injective. -/
theorem c0SumSingle_injective (i : ι) : Function.Injective (c0SumSingle A i) :=
  (isometry_c0SumSingle A i).injective

/-- Distinct factors of the `c₀` direct sum are orthogonal. -/
@[simp]
theorem c0SumSingle_mul_c0SumSingle_of_ne {i j : ι} (hij : i ≠ j) (a : A i) (b : A j) :
    c0SumSingle A i a * c0SumSingle A j b = 0 := by
  refine Subtype.ext <| lp.ext <| funext fun k ↦ ?_
  simp only [NonUnitalStarSubalgebra.coe_mul, coe_c0SumSingle_apply, infty_coeFn_mul,
    Pi.mul_apply, lp.coeFn_single, ZeroMemClass.coe_zero]
  obtain rfl | hk := eq_or_ne k i
  · simp [Pi.single_eq_of_ne hij]
  · simp [Pi.single_eq_of_ne hk]

/-- An element of the `c₀` direct sum is the sum of its coordinates, placed in their factors.
In particular the finitely supported families are dense. -/
theorem hasSum_c0SumSingle (a : c0Sum A) :
    HasSum (fun i ↦ c0SumSingle A i ((a : lp A ∞) i)) a := by
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  have hfin := (mem_c0Sum.1 a.property).eventually (gt_mem_nhds (half_pos hε))
  refine ⟨(eventually_cofinite.1 hfin).toFinset, fun s hs ↦ ?_⟩
  rw [Subtype.dist_eq, dist_eq_norm, AddSubmonoidClass.coe_finsetSum]
  refine (lp.norm_le_of_forall_le (half_pos hε).le fun j ↦ ?_).trans_lt (half_lt_self hε)
  rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_sum, Finset.sum_apply]
  simp only [coe_c0SumSingle_apply, lp.coeFn_single, Finset.sum_pi_single]
  split_ifs with hj
  · simpa using (half_pos hε).le
  · have hj' : ‖(a : lp A ∞) j‖ < ε / 2 := by
      by_contra h
      exact hj (hs (by simpa using h))
    simpa using hj'.le

/-- Continuous additive maps out of the `c₀` direct sum into a Hausdorff space agree when they
agree on every factor, since the finitely supported families are dense. -/
theorem c0Sum_ext_of_continuous {F B : Type*} [AddCommMonoid B] [TopologicalSpace B] [T2Space B]
    [FunLike F (c0Sum A) B] [AddMonoidHomClass F (c0Sum A) B] {φ ψ : F} (hφ : Continuous φ)
    (hψ : Continuous ψ) (h : ∀ i a, φ (c0SumSingle A i a) = ψ (c0SumSingle A i a)) : φ = ψ := by
  refine DFunLike.ext _ _ fun a ↦ ?_
  have hψa := (hasSum_c0SumSingle a).map ψ hψ
  simp only [Function.comp_def, ← h] at hψa
  exact ((hasSum_c0SumSingle a).map φ hφ).unique hψa

/-- Star homomorphisms out of the `c₀` direct sum into a C⋆-algebra agree when they agree on every
factor. -/
@[ext]
theorem c0Sum_nonUnitalStarAlgHom_ext {B : Type*} [NonUnitalCStarAlgebra B]
    {φ ψ : c0Sum A →⋆ₙₐ[ℂ] B}
    (h : ∀ i, φ.comp (c0SumSingle A i) = ψ.comp (c0SumSingle A i)) : φ = ψ :=
  c0Sum_ext_of_continuous (map_continuous φ) (map_continuous ψ) fun i a ↦ congr($(h i) a)

end Single

end lp
