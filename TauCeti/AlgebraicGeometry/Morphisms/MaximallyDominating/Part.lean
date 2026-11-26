/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.MaximallyDominating.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import TauCeti.AlgebraicGeometry.Morphisms.FiniteType.Over
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal

/-!
# The maximally dominating part of a scheme over a base

For a morphism `f : X ⟶ S`, give the closure in `X` of the inverse image of the generic
points of `S` its reduced induced scheme structure. Over a locally Noetherian base this
construction is right adjoint, on finite-type schemes, to the inclusion of the reduced
maximally dominating schemes. In particular, maps from such schemes into a fibre product
factor uniquely through its maximally dominating part.

The categorical construction follows the dense-replacement adjunction for compactifications
in `TauCeti.AlgebraicGeometry.Compactification.DenseReplacement.Basic`.

## References

* L. Illusie, Y. Laszlo and F. Orgogozo (eds.), *Travaux de Gabber sur l'uniformisation
  locale et la cohomologie étale des schémas quasi-excellents*, Exposé II, §1.2.5.
-/

public section

noncomputable section

universe u

open CategoryTheory TopologicalSpace Set

namespace AlgebraicGeometry.Scheme.Hom

open IdealSheafData

variable {X S U : Scheme.{u}} (f : X ⟶ S)

/-- The reduced closed subscheme supported on the closure of the generic fibre of `f`. -/
def maximallyDominatingPart : Scheme.{u} :=
  (vanishingIdeal ⟨closure (f ⁻¹' genericPoints S), isClosed_closure⟩).subscheme

/-- The inclusion of the maximally dominating part in the original scheme. -/
def maximallyDominatingPartι : f.maximallyDominatingPart ⟶ X :=
  (vanishingIdeal ⟨closure (f ⁻¹' genericPoints S), isClosed_closure⟩).subschemeι

instance : IsReduced f.maximallyDominatingPart := by
  unfold maximallyDominatingPart
  infer_instance

instance : IsClosedImmersion f.maximallyDominatingPartι := by
  unfold maximallyDominatingPartι maximallyDominatingPart
  infer_instance

/-- The maximally dominating part is supported on the closure of the points over generic
points of the base. -/
@[simp]
theorem range_maximallyDominatingPartι :
    range f.maximallyDominatingPartι = closure (f ⁻¹' genericPoints S) := by
  unfold maximallyDominatingPartι maximallyDominatingPart
  rw [range_subschemeι, coe_support_vanishingIdeal, Closeds.coe_mk]

/-- For a locally Noetherian source the maximally dominating part is maximally dominating
over the base. -/
theorem isMaximallyDominating_maximallyDominatingPartι_comp [IsLocallyNoetherian X] :
    (f.maximallyDominatingPartι ≫ f).IsMaximallyDominating := by
  have := LocallyOfFiniteType.isLocallyNoetherian f.maximallyDominatingPartι
  rw [
    isMaximallyDominating_iff_isDominant_pullback_fst_fromGenericPointScheme_of_isLocallyNoetherian,
    isDominant_iff, DenseRange, range_pullback_fst_fromGenericPointScheme,
    comp_base, TopCat.coe_comp, preimage_comp,
    f.maximallyDominatingPartι.isClosedEmbedding.isInducing.dense_iff,
    image_preimage_eq_of_subset]
  · intro x
    exact f.range_maximallyDominatingPartι ▸ mem_range_self x
  · rw [range_maximallyDominatingPartι]
    exact subset_closure

/-- A map from a reduced scheme maximally dominating the base factors through the maximally
dominating part of its target. -/
def liftMaximallyDominatingPart (g : U ⟶ X) [IsReduced U]
    (hg : (g ≫ f).IsMaximallyDominating) : U ⟶ f.maximallyDominatingPart :=
  IsClosedImmersion.lift f.maximallyDominatingPartι g (by
    unfold maximallyDominatingPartι maximallyDominatingPart
    rw [ker_subschemeι]
    apply vanishingIdeal_le_ker_of_range_subset
    have h : MapsTo g (genericPoints U) (f ⁻¹' genericPoints S) :=
      (g ≫ f).isMaximallyDominating_iff.mp hg
    rintro _ ⟨u, rfl⟩
    exact h.closure g.continuous (genericPoints.closure (α := U) ▸ mem_univ u))

/-- Composing the factorization with the closed immersion recovers the given map. -/
@[reassoc (attr := simp)]
theorem liftMaximallyDominatingPart_ι (g : U ⟶ X) [IsReduced U]
    (hg : (g ≫ f).IsMaximallyDominating) :
    f.liftMaximallyDominatingPart g hg ≫ f.maximallyDominatingPartι = g :=
  IsClosedImmersion.lift_fac _ _ _

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.FiniteType

variable (S : Scheme.{u})

/-- The full subcategory of finite-type schemes over `S` that are reduced and maximally
dominating. Its morphisms are all scheme morphisms over `S`. -/
abbrev reducedMaximallyDominating : ObjectProperty S.FiniteType :=
  fun T ↦ IsReduced T.left ∧ T.hom.IsMaximallyDominating

variable {S} [IsLocallyNoetherian S]

/-- The maximally dominating part as a reduced maximally dominating finite-type scheme. -/
abbrev maximallyDominatingPart (T : S.FiniteType) :
    (reducedMaximallyDominating S).FullSubcategory :=
  have : IsLocallyNoetherian T.left :=
    LocallyOfFiniteType.isLocallyNoetherian (X := T.left) (Y := S) T.hom
  ⟨FiniteType.mk (T.hom.maximallyDominatingPartι ≫ T.hom),
    (inferInstance : IsReduced T.hom.maximallyDominatingPart),
    Hom.isMaximallyDominating_maximallyDominatingPartι_comp (X := T.left) T.hom⟩

/-- The inclusion of the maximally dominating part as a morphism of finite-type schemes. -/
def maximallyDominatingPartι (T : S.FiniteType) : T.maximallyDominatingPart.obj ⟶ T :=
  MorphismProperty.Over.homMk T.hom.maximallyDominatingPartι rfl

@[simp]
theorem maximallyDominatingPartι_left (T : S.FiniteType) :
    T.maximallyDominatingPartι.left = T.hom.maximallyDominatingPartι := (rfl)

instance (T : S.FiniteType) : Mono T.maximallyDominatingPartι where
  right_cancellation {Z} f g h := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono T.hom.maximallyDominatingPartι).mp
    exact congrArg (·.left) h

/-- The factorization through the maximally dominating part as a morphism over the base. -/
def liftMaximallyDominatingPart {U : (reducedMaximallyDominating S).FullSubcategory}
    {T : S.FiniteType} (g : U.obj ⟶ T) : U ⟶ T.maximallyDominatingPart := by
  have : IsReduced U.obj.left := U.property.1
  have hg : (g.left ≫ T.hom).IsMaximallyDominating :=
    (MorphismProperty.Over.w g) ▸ U.property.2
  refine ObjectProperty.homMk (MorphismProperty.Over.homMk
    (Hom.liftMaximallyDominatingPart (U := U.obj.left) T.hom g.left hg) ?_)
  exact (Hom.liftMaximallyDominatingPart_ι_assoc (U := U.obj.left) T.hom g.left hg T.hom).trans
    (MorphismProperty.Over.w g)

@[reassoc (attr := simp)]
theorem liftMaximallyDominatingPart_hom_ι {U : (reducedMaximallyDominating S).FullSubcategory}
    {T : S.FiniteType} (g : U.obj ⟶ T) :
    (liftMaximallyDominatingPart g).hom ≫ T.maximallyDominatingPartι = g := by
  have : IsReduced U.obj.left := U.property.1
  exact MorphismProperty.Over.Hom.ext (Hom.liftMaximallyDominatingPart_ι (U := U.obj.left)
    T.hom g.left ((MorphismProperty.Over.w g) ▸ U.property.2))

/-- The inclusion in the target detects equality of maps to its maximally dominating part. -/
theorem maximallyDominatingPart_hom_ext {U : (reducedMaximallyDominating S).FullSubcategory}
    {T : S.FiniteType} {f g : U ⟶ T.maximallyDominatingPart}
    (h : f.hom ≫ T.maximallyDominatingPartι = g.hom ≫ T.maximallyDominatingPartι) : f = g :=
  ObjectProperty.hom_ext _ ((cancel_mono T.maximallyDominatingPartι).mp h)

variable (S)

/-- Taking the reduced closure of the generic fibre is functorial on finite-type schemes. -/
-- Morphism formulas use the identification of the functor value with the concrete closed subscheme.
@[expose, implicit_reducible]
def maximallyDominatingPartFunctor :
    S.FiniteType ⥤ (reducedMaximallyDominating S).FullSubcategory where
  obj := maximallyDominatingPart
  map g := liftMaximallyDominatingPart (maximallyDominatingPartι _ ≫ g)
  map_id _ := maximallyDominatingPart_hom_ext (by simp)
  map_comp _ _ := maximallyDominatingPart_hom_ext (by simp)

@[simp]
theorem maximallyDominatingPartFunctor_obj (T : S.FiniteType) :
    (maximallyDominatingPartFunctor S).obj T = T.maximallyDominatingPart := (rfl)

@[reassoc (attr := simp)]
theorem maximallyDominatingPartFunctor_map_hom_ι {T T' : S.FiniteType} (g : T ⟶ T') :
    ((maximallyDominatingPartFunctor S).map g).hom ≫ T'.maximallyDominatingPartι =
      T.maximallyDominatingPartι ≫ g :=
  liftMaximallyDominatingPart_hom_ι _

/-- The inclusion of reduced maximally dominating finite-type schemes is left adjoint to
taking the maximally dominating part. -/
def maximallyDominatingPartAdjunction :
    (reducedMaximallyDominating S).ι ⊣ maximallyDominatingPartFunctor S :=
  Adjunction.mkOfHomEquiv
    { homEquiv U T :=
        { toFun := liftMaximallyDominatingPart
          invFun h := h.hom ≫ T.maximallyDominatingPartι
          left_inv := liftMaximallyDominatingPart_hom_ι
          right_inv _ := maximallyDominatingPart_hom_ext (liftMaximallyDominatingPart_hom_ι _) }
      homEquiv_naturality_left_symm _ _ := by simp
      homEquiv_naturality_right _ _ := maximallyDominatingPart_hom_ext (by simp [Equiv.coe_fn_mk]) }

/-- The unit of the adjunction factors the identity of a reduced maximally dominating scheme. -/
@[simp]
theorem maximallyDominatingPartAdjunction_unit_app
    (U : (reducedMaximallyDominating S).FullSubcategory) :
    (maximallyDominatingPartAdjunction S).unit.app U =
      liftMaximallyDominatingPart (𝟙 U.obj) := by
  simp [maximallyDominatingPartAdjunction]

/-- The counit at `T` is the inclusion of the reduced closure of its generic fibre. -/
@[simp]
theorem maximallyDominatingPartAdjunction_counit_app (T : S.FiniteType) :
    (maximallyDominatingPartAdjunction S).counit.app T = T.maximallyDominatingPartι := by
  simp [maximallyDominatingPartAdjunction]

/-- Reduced maximally dominating finite-type schemes form a coreflective subcategory. -/
instance : Coreflective (reducedMaximallyDominating S).ι :=
  ⟨_, maximallyDominatingPartAdjunction S⟩

end AlgebraicGeometry.Scheme.FiniteType
