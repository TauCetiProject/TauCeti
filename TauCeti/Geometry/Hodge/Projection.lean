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

* `TauCeti.Hodge.RationalHodgeSubstructure.ofRationalMorphismRange` and
  `…ofRationalMorphismKer`: the image and the kernel of a rational linear map whose
  complexification is a morphism of pure Hodge structures are rational Hodge substructures.
* `TauCeti.Hodge.RationalHodgeSubstructure.projection`: the projector onto a rational Hodge
  substructure along its orthogonal complement for a chosen polarization, with
  `…isMorphism_rationalMapToComplex_projection` exhibiting its complexification as a morphism of
  pure Hodge structures.
* `TauCeti.Hodge.exists_isIdempotentElem_isMorphism_of_isPolarizable`: **every rational Hodge
  substructure of a polarizable pure Hodge structure is the image of an idempotent rational Hodge
  endomorphism**, and `TauCeti.Hodge.exists_isIdempotentElem_isMorphism_iff` is the
  characterization of the rational Hodge substructures it yields.
-/

public section

namespace TauCeti.Hodge

universe u v w u' v' w'

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ]
variable [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
variable {hℚ : IsBaseChange ℚ ιℚ} {hℂ : IsBaseChange ℂ ιℂ}
variable {n : ℤ} {hs : HodgeStructure hℂ n}

/-! ### Subobjects cut out by rational morphisms -/

section Morphism

variable {V'ℤ : Type u'} {V'ℚ : Type v'} {V'ℂ : Type w'}
variable [AddCommGroup V'ℤ]
variable [AddCommGroup V'ℚ] [Module ℚ V'ℚ]
variable [AddCommGroup V'ℂ] [Module ℂ V'ℂ]
variable {ι'ℚ : V'ℤ →ₗ[ℤ] V'ℚ} {ι'ℂ : V'ℤ →ₗ[ℤ] V'ℂ}
variable {h'ℚ : IsBaseChange ℚ ι'ℚ} {h'ℂ : IsBaseChange ℂ ι'ℂ}
variable {hs' : HodgeStructure h'ℂ n} {f : Vℚ →ₗ[ℚ] V'ℚ}
variable (hf : HodgeStructureOn.IsMorphism hs hs' (rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f))

namespace RationalHodgeSubstructure

/-- **The image of a rational Hodge morphism**, as a rational Hodge substructure of the target: its
complexification is the image of the complexified map, which is a sub-Hodge structure. -/
def ofRationalMorphismRange : RationalHodgeSubstructure h'ℚ hs' :=
  ofIsSubstructure (LinearMap.range f) <| by
    rw [← range_rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f]
    exact hf.isSubstructure_range

@[simp]
theorem ofRationalMorphismRange_WQ : (ofRationalMorphismRange hf).WQ = LinearMap.range f :=
  ofIsSubstructure_WQ _ _

/-- The complexification of the image of a rational Hodge morphism is the image of the
complexified map. -/
@[simp]
theorem ofRationalMorphismRange_WC :
    (ofRationalMorphismRange hf).WC = LinearMap.range (rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f) := by
  rw [WC_def, ofRationalMorphismRange_WQ, range_rationalMapToComplex]

/-- **The kernel of a rational Hodge morphism**, as a rational Hodge substructure of the source:
its complexification is the kernel of the complexified map, which is a sub-Hodge structure. -/
def ofRationalMorphismKer : RationalHodgeSubstructure hℚ hs :=
  ofIsSubstructure (LinearMap.ker f) <| by
    rw [← ker_rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f]
    exact hf.isSubstructure_ker

@[simp]
theorem ofRationalMorphismKer_WQ : (ofRationalMorphismKer hf).WQ = LinearMap.ker f :=
  ofIsSubstructure_WQ _ _

/-- The complexification of the kernel of a rational Hodge morphism is the kernel of the
complexified map. -/
@[simp]
theorem ofRationalMorphismKer_WC :
    (ofRationalMorphismKer hf).WC = LinearMap.ker (rationalMapToComplex hℚ hℂ h'ℚ h'ℂ f) := by
  rw [WC_def, ofRationalMorphismKer_WQ, ker_rationalMapToComplex]

end RationalHodgeSubstructure

end Morphism

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

/-- The Hodge projector fixes the rational Hodge substructure it projects onto. -/
theorem projection_apply_of_mem {x : Vℚ} (hx : x ∈ W.WQ) : projection P W x = x :=
  Submodule.projection_apply_of_mem_left _ hx

/-- The Hodge projector annihilates the orthogonal complement it projects along. -/
theorem projection_apply_of_mem_orthogonal {x : Vℚ} (hx : x ∈ (orthogonal P W).WQ) :
    projection P W x = 0 :=
  Submodule.projection_apply_of_mem_right _ hx

/-- **The Hodge projector is a morphism of pure Hodge structures.** Its complexification is an
idempotent whose range is the complexified substructure and whose kernel is the complexified
orthogonal complement, and both are sub-Hodge structures. -/
theorem isMorphism_rationalMapToComplex_projection :
    HodgeStructureOn.IsMorphism hs hs (rationalMapToComplex hℚ hℂ hℚ hℂ (projection P W)) := by
  refine HodgeStructureOn.isMorphism_of_isIdempotentElem
    (isIdempotentElem_rationalMapToComplex hℚ hℂ (isIdempotentElem_projection P W)) ?_ ?_
  · rw [range_rationalMapToComplex, range_projection, ← WC_def]
    exact W.isSubstructure
  · rw [ker_rationalMapToComplex, ker_projection, ← WC_def]
    exact (orthogonal P W).isSubstructure

end RationalHodgeSubstructure

/-- **Semisimplicity of polarizable pure Hodge structures, in projector form.** Every rational
Hodge substructure of a polarizable pure Hodge structure is the image of an idempotent rational
endomorphism whose complexification is a morphism of pure Hodge structures: the substructure is a
direct summand as an object, split off by an endomorphism of the Hodge structure. -/
theorem exists_isIdempotentElem_isMorphism_of_isPolarizable [Module.Finite ℚ Vℚ]
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
theorem exists_isIdempotentElem_isMorphism_iff [Module.Finite ℚ Vℚ] (h : IsPolarizable hℂ hs)
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
    exact exists_isIdempotentElem_isMorphism_of_isPolarizable h W

end TauCeti.Hodge
