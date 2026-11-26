/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Geometrically.Integral
public import TauCeti.Geometry.Toric.Algebraic.BaseChange.Fan
public import TauCeti.Geometry.Toric.Algebraic.Normal
import TauCeti.AlgebraicGeometry.Morphisms.FiniteType.Basic
import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Finiteness

/-!
# Field fibres of toric schemes

The zero-cone chart is dense in the toric scheme over any coefficient ring. Over a domain it
is irreducible and all affine charts are reduced, so a nonempty fan gives an integral scheme.
Since coefficient change is cartesian, the structure morphism of a nonempty fan has
geometrically integral fibres over any base. Normality over integrally closed domains follows
from normality of the saturated dual-semigroup algebras.

The chart cover is finite and each dual semigroup is finitely generated. Thus these schemes
are Noetherian over Noetherian coefficient rings. In particular, over fields a nonempty fan
has the normality, integrality and finiteness needed for Weil divisors, even for singular cones.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.1.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Toric.Fan

universe u

variable (R : Type u) [CommRing R] {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (Φ : Fan i)

/-- The zero-cone chart, the split torus over `R`, has dense image in the toric scheme. -/
theorem denseRange_affineChartι_bot (h₀ : (⊥ : PointedCone ℝ V) ∈ Φ.cones) :
    DenseRange (Φ.affineChartι R ⟨⊥, h₀⟩) := by
  intro x
  obtain ⟨σ, y, rfl⟩ := Φ.exists_affineChartι_apply_eq R x
  let hface := (Φ.isToricCone σ.property).salient.bot_isFaceOf
  have hdense := denseRange_faceAffineChartMap R Φ.lattice hface y
  have hy := mem_closure_image (Φ.affineChartι R σ).continuous.continuousAt hdense
  have hcomp : ⇑(Φ.affineChartι R σ) ∘ ⇑(faceAffineChartMap R Φ.lattice hface) =
      ⇑(Φ.affineChartι R ⟨⊥, h₀⟩) := by
    funext z
    simpa only [Scheme.Hom.comp_apply, Function.comp_apply] using
      congrArg (fun f : affineChart R Φ.lattice ⊥ ⟶ Φ.finiteFanScheme R ↦ f z)
        (Φ.faceAffineChartMap_comp_affineChartι R (τ := ⟨⊥, h₀⟩) (σ := σ) hface)
  rwa [← Set.range_comp, hcomp] at hy

/-- A nonempty finite fan over a domain defines an integral scheme. -/
instance isIntegral_finiteFanScheme [IsDomain R] [hΦ : Nonempty Φ.cones] :
    IsIntegral (Φ.finiteFanScheme R) := by
  have h₀ := Φ.bot_mem hΦ.some.property
  have hirr := (IrreducibleSpace.isIrreducible_univ (affineChart R Φ.lattice ⊥)).image
    (Φ.affineChartι R ⟨⊥, h₀⟩) (Φ.affineChartι R ⟨⊥, h₀⟩).continuous.continuousOn
  rw [Set.image_univ, ← isIrreducible_iff_closure,
    (Φ.denseRange_affineChartι_bot R h₀).closure_range] at hirr
  refine (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨
    (irreducibleSpace_def _).mpr hirr, ?_⟩
  refine (IsReduced.iff_of_openCover _ (Φ.affineChartOpenCover R)).mpr fun (σ : Φ.cones) ↦ ?_
  rw [affineChartOpenCover_X]
  infer_instance

/-- The toric scheme of a finite fan over an integrally closed domain is normal. -/
instance isNormalScheme_finiteFanScheme [IsDomain R] [IsIntegrallyClosed R] :
    TauCeti.AlgebraicGeometry.IsNormalScheme (Φ.finiteFanScheme R) := by
  refine (TauCeti.AlgebraicGeometry.isNormalScheme_iff_openCover
    (Φ.affineChartOpenCover R)).mpr fun (σ : Φ.cones) ↦ ?_
  rw [affineChartOpenCover_X]
  exact TauCeti.AlgebraicGeometry.isNormalScheme_Spec (.of (affineChartRing R Φ.lattice σ.val))

/-- The structure morphism of a nonempty finite fan has geometrically integral fibres. -/
instance geometricallyIntegral_finiteFanSchemeToSpec [Nonempty Φ.cones] :
    GeometricallyIntegral (Φ.finiteFanSchemeToSpec R) where
  geometrically_isIntegral := by
    rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro K _ _
    exact IsIntegral.of_isIso (Φ.isPullback_finiteFanSchemeMap R K).isoPullback.hom

/-- The structure morphism of a finite fan scheme is locally of finite type. -/
instance locallyOfFiniteType_finiteFanSchemeToSpec :
    LocallyOfFiniteType (Φ.finiteFanSchemeToSpec R) := by
  have : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType)
    (Φ.affineChartOpenCover R)).mpr fun (σ : Φ.cones) ↦ ?_
  have := (Φ.isToricCone σ.property).fg_dualSemigroup Φ.lattice
  have hchart : LocallyOfFiniteType (Spec.algebraMap R (affineChartRing R Φ.lattice σ.val)) :=
    LocallyOfFiniteType.Spec_algebraMap_iff.mpr inferInstance
  exact (Φ.affineChartι_finiteFanSchemeToSpec R σ).symm ▸ hchart

/-- A finite fan scheme over a Noetherian coefficient ring is Noetherian. -/
instance isNoetherian_finiteFanScheme [IsNoetherianRing R] :
    IsNoetherian (Φ.finiteFanScheme R) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (Φ.finiteFanSchemeToSpec R)
  toCompactSpace := by
    let 𝒰 := Φ.affineChartOpenCover R
    have : Finite 𝒰.I₀ := inferInstanceAs (Finite Φ.cones)
    have : ∀ σ : 𝒰.I₀, CompactSpace (𝒰.X σ) := fun (σ : Φ.cones) ↦ by
      rw [affineChartOpenCover_X]
      infer_instance
    exact 𝒰.compactSpace

end TauCeti.Toric.Fan
