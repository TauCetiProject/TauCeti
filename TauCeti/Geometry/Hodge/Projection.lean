/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Orthogonal

/-!
# Hodge projectors defined over `ℚ`

A rational Hodge substructure of a polarizable pure Hodge structure is a direct summand of it as an
*object*, not merely as a subspace: it is the image of an **idempotent rational endomorphism whose
complexification is a morphism of pure Hodge structures**. That projector is the projection onto
the rational subspace along its orthogonal complement for a polarizing form, and its
complexification is the projection onto the complexified substructure along the complexified
complement, because extension of scalars along `ℚ → ℂ` preserves idempotents, ranges and kernels.
Being a morphism is then automatic: an idempotent endomorphism of the ambient complex space whose
range and kernel are sub-Hodge structures commutes with the conjugation and preserves the Hodge
filtration.

Conversely, the image and the kernel of *any* rational linear map whose complexification is a
morphism of pure Hodge structures are rational Hodge substructures, with no polarization needed.
So over a polarizable structure the rational Hodge substructures are exactly the images of the
idempotent rational Hodge endomorphisms.

This sharpens the splitting of `TauCeti.Hodge.exists_isCompl_of_isPolarizable`, which produces a
complementary rational subspace, into a splitting by endomorphisms of the Hodge structure itself:
the semisimplicity of polarizable rational Hodge structures in the form that speaks about
morphisms rather than about subspaces.

Following Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.1.2, and Peters–Steenbrink,
*Mixed Hodge Structures*, §2.

## Main declarations

* `TauCeti.Hodge.RationalHodgeSubstructure.projection`: the projector onto a rational Hodge
  substructure along its orthogonal complement for a chosen polarization, with
  `…isMorphism_rationalMapToComplex_projection` exhibiting its complexification as a morphism of
  pure Hodge structures.
* `TauCeti.Hodge.exists_isIdempotentElem_isMorphism_range_eq_of_isPolarizable`: **every rational
  Hodge substructure of a polarizable pure Hodge structure is the image of an idempotent rational
  Hodge endomorphism**, and `TauCeti.Hodge.exists_isIdempotentElem_isMorphism_range_eq_iff` is the
  characterization of the rational Hodge substructures it yields.
-/

public section

namespace TauCeti.Hodge

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ]
variable [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {n : ℤ} {hs : HodgeStructure hℂ n}

/-! ### The projector onto a rational Hodge substructure -/

namespace RationalHodgeSubstructure

variable [Module.Finite ℚ Vℚ] (P : Polarization hℂ hs) (W : RationalHodgeSubstructure hℚ hs)

/-- The **Hodge projector** onto a rational Hodge substructure for a chosen polarization: the
projection onto its rational subspace along the orthogonal complement of that subspace. -/
noncomputable def projection : Vℚ →ₗ[ℚ] Vℚ :=
  W.WQ.projection (orthogonal P W).WQ (isCompl_WQ_orthogonal_WQ P W)

@[simp]
theorem range_projection : LinearMap.range (projection P W) = W.WQ :=
  Submodule.range_projection _

@[simp]
theorem ker_projection : LinearMap.ker (projection P W) = (orthogonal P W).WQ :=
  Submodule.ker_projection _

@[simp]
theorem isIdempotentElem_projection : IsIdempotentElem (projection P W) :=
  Submodule.isIdempotentElem_projection _

/-- The Hodge projector is the submodule projection along the orthogonal complement. -/
theorem projection_eq_submodule_projection :
    projection P W =
      W.WQ.projection (orthogonal P W).WQ (isCompl_WQ_orthogonal_WQ P W) :=
  by
    have h := LinearMap.IsIdempotentElem.eq_projection (isIdempotentElem_projection P W)
    simpa only [range_projection, ker_projection] using h

/-- The Hodge projector fixes the rational Hodge substructure it projects onto. -/
@[simp]
theorem projection_apply_of_mem {x : Vℚ} (hx : x ∈ W.WQ) : projection P W x = x :=
  Submodule.projection_apply_of_mem_left _ hx

/-- The Hodge projector annihilates the orthogonal complement it projects along. -/
@[simp]
theorem projection_apply_of_mem_orthogonal {x : Vℚ}
    (hx : ∀ y ∈ W.WQ, integralFormBaseChange hℚ P.Qint y x = 0) :
    projection P W x = 0 :=
  -- The expanded premise is the simp-normal form of membership in `(orthogonal P W).WQ`.
  Submodule.projection_apply_of_mem_right _ <| by
    rw [orthogonal_WQ, LinearMap.BilinForm.mem_orthogonal_iff]
    exact hx

omit [Module.Finite ℚ Vℚ] in
/-- Projection along complementary rational Hodge substructures is a morphism of the ambient pure
Hodge structure. -/
theorem isMorphism_rationalMapToComplex_projection_of_isCompl
    (W' : RationalHodgeSubstructure hℚ hs) (h : IsCompl W W') :
    HodgeStructureOn.IsMorphism hs hs
      (rationalMapToComplex hℚ hℂ hℚ hℂ
        (W.WQ.projection W'.WQ (isCompl_iff_WQ.1 h))) := by
  -- Apply the idempotent criterion using the projector's range and kernel.
  refine HodgeStructureOn.isMorphism_of_isIdempotentElem
    (isIdempotentElem_rationalMapToComplex hℚ hℂ
      (Submodule.isIdempotentElem_projection (isCompl_iff_WQ.1 h))) ?_ ?_
  · rw [range_rationalMapToComplex, Submodule.range_projection, ← WC_def]
    exact W.isSubstructure
  · rw [ker_rationalMapToComplex, Submodule.ker_projection, ← W'.WC_def]
    exact W'.isSubstructure

/-- The complexification of the Hodge projector is a morphism of pure Hodge structures. -/
theorem isMorphism_rationalMapToComplex_projection :
    HodgeStructureOn.IsMorphism hs hs (rationalMapToComplex hℚ hℂ hℚ hℂ (projection P W)) :=
  W.isMorphism_rationalMapToComplex_projection_of_isCompl (orthogonal P W)
    (isCompl_orthogonal P W)

end RationalHodgeSubstructure

/-- **Semisimplicity of polarizable pure Hodge structures, in projector form.** Every rational
Hodge substructure of a polarizable pure Hodge structure is the image of an idempotent rational
endomorphism whose complexification is a morphism of pure Hodge structures: the substructure is a
direct summand as an object, split off by an endomorphism of the Hodge structure. -/
theorem exists_isIdempotentElem_isMorphism_range_eq_of_isPolarizable [Module.Finite ℚ Vℚ]
    (h : IsPolarizable hℂ hs) (W : RationalHodgeSubstructure hℚ hs) :
    ∃ e : Vℚ →ₗ[ℚ] Vℚ, IsIdempotentElem e ∧
      HodgeStructureOn.IsMorphism hs hs (rationalMapToComplex hℚ hℂ hℚ hℂ e) ∧
      LinearMap.range e = W.WQ := by
  obtain ⟨P⟩ := isPolarizable_iff_nonempty.1 h
  exact ⟨RationalHodgeSubstructure.projection P W,
    RationalHodgeSubstructure.isIdempotentElem_projection P W,
    RationalHodgeSubstructure.isMorphism_rationalMapToComplex_projection P W,
    RationalHodgeSubstructure.range_projection P W⟩

/-- **The rational Hodge substructures of a polarizable pure Hodge structure are exactly the images
of the idempotent rational Hodge endomorphisms.** The forward implication needs neither
idempotency nor a polarization: the image of any rational Hodge morphism is a rational Hodge
substructure. -/
theorem exists_isIdempotentElem_isMorphism_range_eq_iff [Module.Finite ℚ Vℚ]
    (h : IsPolarizable hℂ hs)
    (A : Submodule ℚ Vℚ) :
    (∃ e : Vℚ →ₗ[ℚ] Vℚ, IsIdempotentElem e ∧
        HodgeStructureOn.IsMorphism hs hs (rationalMapToComplex hℚ hℂ hℚ hℂ e) ∧
        LinearMap.range e = A) ↔
      ∃ W : RationalHodgeSubstructure hℚ hs, W.WQ = A := by
  constructor
  · rintro ⟨e, -, he, rfl⟩
    exact ⟨RationalHodgeSubstructure.ofRationalMorphismRange he,
      RationalHodgeSubstructure.ofRationalMorphismRange_WQ he⟩
  · rintro ⟨W, rfl⟩
    exact exists_isIdempotentElem_isMorphism_range_eq_of_isPolarizable h W

end TauCeti.Hodge
