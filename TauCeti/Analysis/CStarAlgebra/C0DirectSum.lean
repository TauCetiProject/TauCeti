/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.BoundedProduct
public import TauCeti.Analysis.Normed.Lp.C0Ideal

/-!
# The `c₀` direct sum of C⋆-algebras

For a family of C⋆-algebras `A i`, the `c₀` direct sum `lp.c0Sum A` is the closed star
subalgebra of the bounded product `lp A ∞` of the families whose coordinate norms tend to `0`
along the cofinite filter. Its carrier is the closed `c₀` ideal `lp.c0Ideal A`, so it is a
C⋆-algebra and an ideal of the bounded product. For a finite index type it is the whole bounded
product, which is then the finite direct sum.

## Main declarations

* `lp.c0Sum`: the `c₀` direct sum as a closed star subalgebra of `lp A ∞`.
* `lp.c0SumSingle`: the isometric inclusion of the factor `A i`, with `lp.norm_c0SumSingle`.
* `lp.hasSum_c0SumSingle`: every element of the `c₀` direct sum is the sum of its coordinates,
  so the finitely supported families are dense.
* `lp.c0Sum_hom_ext`: star homomorphisms out of the `c₀` direct sum agree once they agree on
  every factor.
* `lp.liftC0Sum`: a family of star homomorphisms `B → A i` vanishing at infinity pointwise
  gives a star homomorphism `B → lp.c0Sum A`.
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
`lp A ∞` whose coordinate norms tend to `0` along the cofinite filter, as a star subalgebra. -/
@[expose] def c0Sum : NonUnitalStarSubalgebra ℂ (lp A ∞) where
  carrier := c0Ideal A
  add_mem' := (c0Ideal A).add_mem
  zero_mem' := (c0Ideal A).zero_mem
  mul_mem' _ hb := (c0Ideal A).mul_mem_left _ _ hb
  smul_mem' c a ha := mem_c0Ideal.2 <| by
    simpa [lp.coeFn_smul, norm_smul] using (mem_c0Ideal.1 ha).const_mul ‖c‖
  star_mem' := star_mem_c0Ideal

variable {A}

/-- The carrier of the `c₀` direct sum is the `c₀` ideal of the bounded product. -/
@[simp]
theorem coe_c0Sum : (c0Sum A : Set (lp A ∞)) = c0Ideal A :=
  rfl

/-- A bounded family lies in the `c₀` direct sum when its coordinate norms tend to `0`. -/
@[simp]
theorem mem_c0Sum {a : lp A ∞} : a ∈ c0Sum A ↔ Tendsto (fun i ↦ ‖a i‖) cofinite (𝓝 0) :=
  mem_c0Ideal

/-- The `c₀` direct sum is closed in the bounded product, hence a C⋆-algebra. -/
instance : IsClosed (c0Sum A : Set (lp A ∞)) :=
  isClosed_c0Ideal A

/-- For finitely many factors, the `c₀` direct sum is the whole bounded product. -/
theorem c0Sum_eq_top [Finite ι] : c0Sum A = ⊤ :=
  eq_top_iff.2 fun a _ ↦ mem_c0Sum.2 <| by simp [cofinite_eq_bot]

section Lift

variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- A family of star homomorphisms `φ i : B → A i` with `‖φ i b‖ → 0` along the cofinite filter
for every `b` gives a star homomorphism into the `c₀` direct sum. -/
@[expose] def liftC0Sum (φ : ∀ i, B →⋆ₙₐ[ℂ] A i)
    (hφ : ∀ b, Tendsto (fun i ↦ ‖φ i b‖) cofinite (𝓝 0)) : B →⋆ₙₐ[ℂ] c0Sum A :=
  (liftNonUnitalStarAlgHom φ).codRestrict (c0Sum A) fun b ↦ mem_c0Sum.2 (hφ b)

/-- `lp.liftC0Sum` is `lp.liftNonUnitalStarAlgHom` with its range in the `c₀` direct sum. -/
@[simp]
theorem coe_liftC0Sum_apply (φ : ∀ i, B →⋆ₙₐ[ℂ] A i)
    (hφ : ∀ b, Tendsto (fun i ↦ ‖φ i b‖) cofinite (𝓝 0)) (b : B) :
    (liftC0Sum φ hφ b : lp A ∞) = liftNonUnitalStarAlgHom φ b :=
  rfl

end Lift

section Single

variable [DecidableEq ι]

/-- A family supported at a single index lies in the `c₀` direct sum. -/
theorem single_mem_c0Sum (i : ι) (a : A i) : lp.single ∞ i a ∈ c0Sum A := by
  refine mem_c0Sum.2 <| tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_cofinite_ne i] with j hj
  simp [Pi.single_eq_of_ne hj]

variable (A) in
/-- The inclusion of the factor `A i` into the `c₀` direct sum, as a star homomorphism. -/
@[expose] def c0SumSingle (i : ι) : A i →⋆ₙₐ[ℂ] c0Sum A where
  toFun a := ⟨lp.single ∞ i a, single_mem_c0Sum i a⟩
  map_smul' c a := Subtype.ext <| lp.single_smul ∞ i c a
  map_zero' := Subtype.ext <| lp.single_zero ∞ i
  map_add' a b := Subtype.ext <| lp.single_add ∞ i a b
  map_mul' a b := Subtype.ext <| by
    ext j
    obtain rfl | hj := eq_or_ne j i
    · simp [infty_coeFn_mul]
    · simp [infty_coeFn_mul, Pi.single_eq_of_ne hj]
  map_star' a := Subtype.ext <| by
    ext j
    obtain rfl | hj := eq_or_ne j i
    · simp [lp.star_apply]
    · simp [lp.star_apply, Pi.single_eq_of_ne hj]

/-- The inclusion of `A i` sends `a` to the family `lp.single ∞ i a`. -/
@[simp]
theorem coe_c0SumSingle_apply (i : ι) (a : A i) :
    (c0SumSingle A i a : lp A ∞) = lp.single ∞ i a :=
  rfl

/-- The inclusion of a factor into the `c₀` direct sum is isometric. -/
theorem norm_c0SumSingle (i : ι) (a : A i) : ‖c0SumSingle A i a‖ = ‖a‖ :=
  lp.norm_single ENNReal.zero_lt_top i a

/-- An element of the `c₀` direct sum is the sum of its coordinates, placed in their factors.
In particular the finitely supported families are dense. -/
theorem hasSum_c0SumSingle (a : c0Sum A) :
    HasSum (fun i ↦ c0SumSingle A i ((a : lp A ∞) i)) a := by
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  have hfin := (mem_c0Sum.1 a.2).eventually (gt_mem_nhds (half_pos hε))
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

/-- Star homomorphisms out of the `c₀` direct sum into a C⋆-algebra agree when they agree on every
factor: the finitely supported families are dense and star homomorphisms are continuous. -/
@[ext]
theorem c0Sum_hom_ext {B : Type*} [NonUnitalCStarAlgebra B] {φ ψ : c0Sum A →⋆ₙₐ[ℂ] B}
    (h : ∀ i, φ.comp (c0SumSingle A i) = ψ.comp (c0SumSingle A i)) : φ = ψ := by
  ext a
  have h' : ⇑φ ∘ (fun i ↦ c0SumSingle A i ((a : lp A ∞) i)) =
      ⇑ψ ∘ (fun i ↦ c0SumSingle A i ((a : lp A ∞) i)) :=
    funext fun i ↦ congr($(h i) ((a : lp A ∞) i))
  have hψ := (hasSum_c0SumSingle a).map ψ (map_continuous ψ)
  rw [← h'] at hψ
  exact ((hasSum_c0SumSingle a).map φ (map_continuous φ)).unique hψ

end Single

end lp
