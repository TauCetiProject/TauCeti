/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MinTensor.Exact

/-!
# The quotient-norm formulation of exactness

For a closed ideal `J` of a C*-algebra `B`, write `q : B → B/J` for the quotient map. A C*-algebra
`A` is exact (`TauCeti.CStarAlgebra.IsExact`) exactly when, for every such `B` and `J`, the norm of
the image of `u ∈ A ⊗min B` in `A ⊗min (B/J)` is the distance from `u` to the image of
`A ⊗min J`: the canonical map from the quotient of `A ⊗min B` by `A ⊗min J` to `A ⊗min (B/J)` is
isometric (Blackadar IV.3.4.1–IV.3.4.2). One inequality holds for every `A`
(`TauCeti.MinTensorProduct.norm_map_mkStarAlgHom_le_infDist`), since the image of `A ⊗min J` lies
in the kernel of `A ⊗min B → A ⊗min (B/J)`.

The proof uses that a star homomorphism `φ` between C*-algebras satisfies
`‖φ a‖ = infDist a (ker φ)` (`NonUnitalStarAlgHom.norm_apply_eq_infDist_ker`), because the induced
map `A ⧸ ker φ → B` is isometric and the quotient norm is the distance to the kernel.

## Main statements

* `NonUnitalStarAlgHom.norm_apply_eq_infDist_ker`: `‖φ a‖` is the distance from `a` to `ker φ`.
* `TauCeti.MinTensorProduct.norm_map_mkStarAlgHom_le_infDist`: the norm of the image in
  `A ⊗min (B/J)` is at most the distance to the image of `A ⊗min J`, for every `A`.
* `TauCeti.CStarAlgebra.isExact_iff_norm_map_mkStarAlgHom_eq_infDist`: `A` is exact iff equality
  holds for every `B` and `J`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  IV.3.4.1–IV.3.4.2.
-/

public section

open TensorProduct
open scoped CStarAlgebra

universe u w

namespace NonUnitalStarAlgHom

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The norm of `φ a` for a star homomorphism `φ` of C*-algebras is the distance from `a` to the
kernel of `φ`: the induced map `A ⧸ ker φ → B` is isometric. -/
theorem norm_apply_eq_infDist_ker (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    ‖φ a‖ = Metric.infDist a (TwoSidedIdeal.ker φ : Set A) := by
  set K := TwoSidedIdeal.ker φ
  have himage : (‖a + ·‖) '' (K : Set A) = (dist a ·) '' (K : Set A) := by
    ext r
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨-y, neg_mem hy, by simp [dist_eq_norm]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨-y, neg_mem hy, by simp [dist_eq_norm, sub_eq_add_neg]⟩
  rw [← φ.quotientKerHom_mk a, φ.isometry_quotientKerHom.norm_map_of_map_zero (map_zero _),
    TwoSidedIdeal.Quotient.norm_mk_eq, himage, Metric.infDist_eq_iInf, sInf_image']

end NonUnitalStarAlgHom

namespace TauCeti

namespace MinTensorProduct

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  (J : TwoSidedIdeal B) [IsClosed (J : Set B)]

open TwoSidedIdeal.Quotient (mkStarAlgHom)

/-- For every `A`, the norm of the image of `u ∈ A ⊗min B` in `A ⊗min (B/J)` is at most the
distance from `u` to the image of `A ⊗min J`. Equality for all `B` and `J` is exactness of `A`
(`TauCeti.CStarAlgebra.isExact_iff_norm_map_mkStarAlgHom_eq_infDist`). -/
theorem norm_map_mkStarAlgHom_le_infDist (u : MinTensorProduct A B) :
    ‖map (NonUnitalStarAlgHom.id ℂ A) (mkStarAlgHom J) u‖ ≤
      Metric.infDist u (Set.range (map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom)) := by
  rw [NonUnitalStarAlgHom.norm_apply_eq_infDist_ker]
  refine Metric.infDist_le_infDist_of_subset ?_ ⟨0, 0, map_zero _⟩
  rintro _ ⟨v, rfl⟩
  simp [TwoSidedIdeal.mem_ker]

end MinTensorProduct

namespace CStarAlgebra

open MinTensorProduct TwoSidedIdeal.Quotient

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- **The quotient-norm formulation of exactness**: `A` is exact iff for every `B` and every closed
ideal `J` of `B`, the norm of the image of `u ∈ A ⊗min B` in `A ⊗min (B/J)` is the distance from
`u` to the image of `A ⊗min J`. -/
theorem isExact_iff_norm_map_mkStarAlgHom_eq_infDist : IsExact.{w} A ↔
    ∀ (B : Type w) [NonUnitalCStarAlgebra B] (J : TwoSidedIdeal B) [IsClosed (J : Set B)]
      (u : MinTensorProduct A B), ‖map (NonUnitalStarAlgHom.id ℂ A) (mkStarAlgHom J) u‖ =
        Metric.infDist u (Set.range (map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom)) := by
  refine ⟨fun h B _ J _ u ↦ ?_, fun h ↦ isExact_iff.2 fun B _ J _ u hu ↦ ?_⟩
  · rw [NonUnitalStarAlgHom.norm_apply_eq_infDist_ker]
    congr 1
    ext v
    exact (TwoSidedIdeal.mem_ker _).trans (h.exact_map B J v)
  · have hdist := h B J u
    rw [hu, norm_zero] at hdist
    rw [← (map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom).isClosed_setRange.closure_eq]
    exact (Metric.mem_closure_iff_infDist_zero (Set.range_nonempty _)).2 hdist.symm

/-- For exact `A`, the norm of the image of `u ∈ A ⊗min B` in `A ⊗min (B/J)` is the distance from
`u` to the image of `A ⊗min J`. -/
theorem IsExact.norm_map_mkStarAlgHom_eq_infDist [IsExact.{w} A] {B : Type w}
    [NonUnitalCStarAlgebra B] (J : TwoSidedIdeal B) [IsClosed (J : Set B)]
    (u : MinTensorProduct A B) :
    ‖map (NonUnitalStarAlgHom.id ℂ A) (mkStarAlgHom J) u‖ =
      Metric.infDist u (Set.range (map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom)) :=
  isExact_iff_norm_map_mkStarAlgHom_eq_infDist.1 ‹_› B J u

end CStarAlgebra

end TauCeti
