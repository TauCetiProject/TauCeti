/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Product.Map
public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Unital
public import TauCeti.Analysis.CStarAlgebra.Quotient

/-!
# The maximal tensor product is exact

Let `A` and `B` be unital C*-algebras and `J` a closed two-sided ideal of `B`. The maximal tensor
product preserves the exactness of `0 → J → B → B/J → 0`
(`TauCeti.MaxTensorProduct.exact_map_starAlgHom_map_mkStarAlgHom`): the kernel of
`A ⊗max B → A ⊗max (B/J)` is the image of `A ⊗max J` (Blackadar II.9.6.6). This is the part of
the kernel formulation of exactness that holds for every `A`; the minimal tensor product has it
only for exact `A`.

The image `I` of `A ⊗max J` in `A ⊗max B` is closed, being the range of a star homomorphism of
C*-algebras, and it is a two-sided ideal (`TauCeti.MaxTensorProduct.rangeIdeal`): the image of
`A ⊗[ℂ] J` is an ideal of `A ⊗[ℂ] B`, and both factors of a product can be approximated from the
algebraic tensor products. The quotient `(A ⊗max B)/I` is a unital C*-algebra, and
`a ↦ a ⊗ 1` and `b ↦ 1 ⊗ b` descend to commuting unital star homomorphisms from `A` and from
`B/J` into it. The universal property of `A ⊗max (B/J)` then gives a star homomorphism
`A ⊗max (B/J) → (A ⊗max B)/I` through which the quotient map by `I` factors
(`TauCeti.MaxTensorProduct.liftQuotient_map_mkStarAlgHom`), so everything killed by
`A ⊗max B → A ⊗max (B/J)` lies in `I`.

## Main declarations

* `TauCeti.MaxTensorProduct.rangeIdeal`: the image of `A ⊗max J` as a closed two-sided ideal of
  `A ⊗max B`.
* `TauCeti.MaxTensorProduct.liftQuotient`: the star homomorphism
  `A ⊗max (B/J) → (A ⊗max B)/(A ⊗max J)`.

## Main statements

* `TauCeti.MaxTensorProduct.exact_map_starAlgHom_map_mkStarAlgHom`: exactness of
  `A ⊗max J → A ⊗max B → A ⊗max (B/J)`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.6.6.
-/

public section

noncomputable section

open TensorProduct TwoSidedIdeal.Quotient
open scoped CStarAlgebra

universe u v

namespace TauCeti

namespace MaxTensorProduct

open Algebra.TensorProduct (mapNonUnitalStarAlgHom mapNonUnitalStarAlgHom_tmul)

section Ideal

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  (J : TwoSidedIdeal B) [IsClosed (J : Set B)]

/-- The image of `A ⊗[ℂ] J` in `A ⊗[ℂ] B` absorbs multiplication on the left. -/
private theorem exists_mapNonUnitalStarAlgHom_eq_mul (y : A ⊗[ℂ] B) (w : A ⊗[ℂ] J) :
    ∃ w' : A ⊗[ℂ] J, mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom w' =
      y * mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom w := by
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' =>
    obtain ⟨w₁, h₁⟩ := hy
    obtain ⟨w₂, h₂⟩ := hy'
    exact ⟨w₁ + w₂, by rw [map_add, h₁, h₂, add_mul]⟩
  | tmul a b =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' =>
      obtain ⟨w₁, h₁⟩ := hw
      obtain ⟨w₂, h₂⟩ := hw'
      exact ⟨w₁ + w₂, by rw [map_add, h₁, h₂, map_add, mul_add]⟩
    | tmul a' j =>
      refine ⟨(a * a') ⊗ₜ ⟨b * j, J.mul_mem_left b _ j.property⟩, ?_⟩
      simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- The image of `A ⊗max J` in `A ⊗max B` absorbs multiplication on the left. -/
theorem mul_mem_range_map_starAlgHom (x : MaxTensorProduct A B) (z : MaxTensorProduct A J) :
    x * map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom z ∈
      Set.range (map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom) := by
  set f := map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom
  have hR := f.isClosed_setRange
  have hf : Continuous f := map_continuous f
  refine induction_on x (hR.preimage (continuous_id.mul continuous_const)) fun y ↦ ?_
  refine induction_on z (hR.preimage (continuous_const.mul hf)) fun w ↦ ?_
  obtain ⟨w', hw'⟩ := exists_mapNonUnitalStarAlgHom_eq_mul J y w
  exact ⟨of A J w', by simp only [f, map_of, hw', map_mul]⟩

variable (A) in
/-- The image of `A ⊗max J` in `A ⊗max B`, as a two-sided ideal. It is closed
(`TauCeti.MaxTensorProduct.isClosed_rangeIdeal`). -/
def rangeIdeal : TwoSidedIdeal (MaxTensorProduct A B) :=
  .mk' (Set.range (map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom)) ⟨0, map_zero _⟩
    (fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x + y, by rw [map_add, hx, hy]⟩)
    (fun ⟨x, hx⟩ ↦ ⟨-x, by rw [map_neg, hx]⟩)
    (fun ⟨z, hz⟩ ↦ hz ▸ mul_mem_range_map_starAlgHom J _ z)
    (fun {x y} ⟨z, hz⟩ ↦ by
      obtain ⟨w, hw⟩ := mul_mem_range_map_starAlgHom J (star y) (star z)
      refine ⟨star w, ?_⟩
      rw [map_star, hw, star_mul, map_star, star_star, star_star, hz])

/-- Membership in `rangeIdeal A J` is membership in the image of `A ⊗max J`. -/
@[simp]
theorem mem_rangeIdeal {x : MaxTensorProduct A B} :
    x ∈ rangeIdeal A J ↔ x ∈ Set.range (map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom) :=
  TwoSidedIdeal.mem_mk' ..

/-- The carrier of `rangeIdeal A J` is the image of `A ⊗max J`. -/
@[simp]
theorem coe_rangeIdeal :
    (rangeIdeal A J : Set (MaxTensorProduct A B)) =
      Set.range (map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom) :=
  TwoSidedIdeal.coe_mk' ..

/-- The image of `A ⊗max J` is closed. -/
instance isClosed_rangeIdeal : IsClosed (rangeIdeal A J : Set (MaxTensorProduct A B)) := by
  rw [coe_rangeIdeal]
  exact NonUnitalStarAlgHom.isClosed_setRange _

/-- The composite `A ⊗max J → A ⊗max B → A ⊗max (B/J)` is zero. -/
@[simp]
theorem map_mkStarAlgHom_map_starAlgHom (z : MaxTensorProduct A J) :
    map (NonUnitalStarAlgHom.id ℂ A) (mkStarAlgHom J)
      (map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom z) = 0 := by
  have h : map (NonUnitalStarAlgHom.id ℂ A) ((mkStarAlgHom J).comp J.starAlgHom) = 0 :=
    starAlgHom_ext fun a j ↦ by
      have hj : mk J (j : B) = 0 := TwoSidedIdeal.Quotient.eq_zero_iff_mem.2 j.property
      simp [hj]
  rw [map_map, NonUnitalStarAlgHom.id_comp, h, NonUnitalStarAlgHom.zero_apply]

end Ideal

section Unital

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
  (J : TwoSidedIdeal B) [IsClosed (J : Set B)]

/-- The unital star homomorphism `B/J → (A ⊗max B)/(A ⊗max J)`, `b ↦ 1 ⊗ b`. -/
def quotientIncludeRight : B ⧸ J →⋆ₐ[ℂ] MaxTensorProduct A B ⧸ rangeIdeal A J :=
  liftUnitalStarAlgHom J ((mkUnitalStarAlgHom (rangeIdeal A J)).comp (includeRight A B))
    fun j hj ↦ by
      rw [StarAlgHom.comp_apply, mkUnitalStarAlgHom_apply, eq_zero_iff_mem, mem_rangeIdeal,
        includeRight_apply]
      exact ⟨of A J (1 ⊗ₜ ⟨j, hj⟩), by simp⟩

/-- `quotientIncludeRight J` sends the class of `b` to the class of `1 ⊗ b`. -/
@[simp]
theorem quotientIncludeRight_mk (b : B) :
    quotientIncludeRight (A := A) J (mk J b) = mk (rangeIdeal A J) (of A B (1 ⊗ₜ b)) := by
  simp [quotientIncludeRight]

/-- The star homomorphism `A ⊗max (B/J) → (A ⊗max B)/(A ⊗max J)` sending `a ⊗ b` to the class
of `a ⊗ b`. -/
def liftQuotient :
    MaxTensorProduct A (B ⧸ J) →⋆ₙₐ[ℂ] MaxTensorProduct A B ⧸ rangeIdeal A J :=
  lift ((mkUnitalStarAlgHom (rangeIdeal A J)).comp (includeLeft A B)).toNonUnitalStarAlgHom
    (quotientIncludeRight J).toNonUnitalStarAlgHom fun a b ↦ by
      obtain ⟨b, rfl⟩ := mk_surjective J b
      -- `lift` sees the quotients through their non-unital C*-algebra instances, which agree
      -- with the unital ones only up to unfolding, so `StarAlgHom.coe_toNonUnitalStarAlgHom`
      -- does not rewrite here
      change Commute (mkUnitalStarAlgHom (rangeIdeal A J) (includeLeft A B a))
        (quotientIncludeRight J (mk J b))
      rw [quotientIncludeRight_mk, ← includeRight_apply, ← mkUnitalStarAlgHom_apply]
      exact (commute_includeLeft_includeRight a b).map (mkUnitalStarAlgHom (rangeIdeal A J))

/-- `liftQuotient J` sends `a ⊗ [b]` to the class of `a ⊗ b`. -/
@[simp]
theorem liftQuotient_of_tmul (a : A) (b : B) :
    liftQuotient J (of A (B ⧸ J) (a ⊗ₜ mk J b)) = mk (rangeIdeal A J) (of A B (a ⊗ₜ b)) := by
  refine (lift_of_tmul _ _ _ _ _).trans ?_
  -- as in `liftQuotient`, the coercions of the unital homomorphisms only unfold by `change`
  change mkUnitalStarAlgHom _ (includeLeft A B a) * quotientIncludeRight J (mk J b) = _
  rw [quotientIncludeRight_mk, ← includeRight_apply, ← mkUnitalStarAlgHom_apply, ← map_mul,
    includeLeft_mul_includeRight, mkUnitalStarAlgHom_apply]

/-- The quotient map by the image of `A ⊗max J` factors through `A ⊗max (B/J)`. -/
@[simp]
theorem liftQuotient_map_mkStarAlgHom (x : MaxTensorProduct A B) :
    liftQuotient J (map (NonUnitalStarAlgHom.id ℂ A) (mkStarAlgHom J) x) =
      mk (rangeIdeal A J) x := by
  have h : (liftQuotient J).comp
      (map (NonUnitalStarAlgHom.id ℂ A) (mkStarAlgHom J)) = mkStarAlgHom (rangeIdeal A J) :=
    starAlgHom_ext fun a b ↦ by simp
  simpa using congr($h x)

/-- **The maximal tensor product is exact** on closed-ideal sequences: for unital `A` and `B`
and a closed two-sided ideal `J` of `B`, the kernel of `A ⊗max B → A ⊗max (B/J)` is the image
of `A ⊗max J`. -/
theorem exact_map_starAlgHom_map_mkStarAlgHom :
    Function.Exact (map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom)
      (map (NonUnitalStarAlgHom.id ℂ A) (mkStarAlgHom J)) := fun x ↦ by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · rw [← mem_rangeIdeal, ← eq_zero_iff_mem, ← liftQuotient_map_mkStarAlgHom, hx, map_zero]
  · rintro ⟨z, rfl⟩
    exact map_mkStarAlgHom_map_starAlgHom J z

end Unital

end MaxTensorProduct

end TauCeti
