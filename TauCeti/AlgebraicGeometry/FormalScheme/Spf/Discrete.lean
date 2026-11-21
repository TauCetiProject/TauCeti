/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Quotient

/-!
# The formal spectrum of a discrete ring

For a discrete adic ring, the canonical inclusion of the zero-ideal thickening is an
isomorphism. Composing it with `Spec (A / 0) ≅ Spec A` identifies the formal spectrum with the
ordinary spectrum as a locally ringed space, not just on points. This comparison allows
ordinary affine schemes to be regarded as affine formal schemes.

More generally, an ideal-of-definition thickening `Spec (A / J) → Spf A` is an isomorphism
exactly when `J = 0`. In particular, a nonzero nilpotent ideal cannot be discarded merely
because its quotient has the same prime spectrum.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, 10.1.2.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

universe u

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

namespace TauCeti.FormalScheme.Spf

variable (A : Type u) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]

/-- The canonical identification of the formal spectrum of a discrete ring with its ordinary
spectrum. Its inverse is the zero-ideal quotient inclusion, after identifying `A / 0` with
`A`. -/
noncomputable def discreteIsoSpec :
    Spf A ≅ Spec.locallyRingedSpaceObj (CommRingCat.of A) :=
  (asIso (fromSpecQuotient (is_bot_adic_iff.mpr inferInstance))).symm ≪≫
    Spec.toLocallyRingedSpace.mapIso
      (RingEquiv.quotientBot A).toCommRingCatIso.symm.op

/-- The inverse discrete comparison is the canonical zero-ideal thickening, after the
canonical quotient identification. -/
theorem discreteIsoSpec_inv :
    (discreteIsoSpec A).inv =
      Spec.locallyRingedSpaceMap
        (CommRingCat.ofHom (RingEquiv.quotientBot A).toRingHom) ≫
      fromSpecQuotient (is_bot_adic_iff.mpr inferInstance) :=
  (rfl)

/-- On points, the inverse comparison is the identity on the underlying prime ideals. -/
@[simp]
theorem discreteIsoSpec_inv_base_apply (q : PrimeSpectrum A) :
    Subtype.val ((discreteIsoSpec A).inv.base q : carrier A) = q := by
  calc
    _ = Subtype.val ((fromSpecQuotient (is_bot_adic_iff.mpr inferInstance)).base
        (PrimeSpectrum.comap (RingEquiv.quotientBot A).toRingHom q) : carrier A) := by
      rw [discreteIsoSpec_inv]
      rfl
    _ = PrimeSpectrum.comap (Ideal.Quotient.mk (⊥ : Ideal A))
        (PrimeSpectrum.comap (RingEquiv.quotientBot A).toRingHom q) :=
      (congrArg Subtype.val (fromSpecQuotient_points _ _)).trans
        (coe_homeomorphSpecQuotient_symm_apply _ _)
    _ = q := by
      ext a
      simp [Ideal.mem_comap]

/-- On points, the discrete comparison forgets only the proof that the prime is open. -/
@[simp]
theorem discreteIsoSpec_hom_base_apply (p : carrier A) :
    (discreteIsoSpec A).hom.base p = (p : PrimeSpectrum A) := by
  have h := discreteIsoSpec_inv_base_apply A ((discreteIsoSpec A).hom.base p)
  have hinv := LocallyRingedSpace.iso_hom_base_inv_base_apply (discreteIsoSpec A) p
  exact h.symm.trans (congrArg Subtype.val hinv)

/-- The discrete comparison preserves global coefficients: the inverse induces the usual
map `A → Γ(Spec A)` on global sections. -/
@[reassoc (attr := simp)]
theorem discreteIsoSpec_inv_globalSections :
    have := (IsAdicRing.ideal_spec A).2.2
    (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv ≫
        (discreteIsoSpec A).inv.c.app (op ⊤) = toSpecΓ (CommRingCat.of A) := by
  intro
  rw [← LocallyRingedSpace.Γ_map_op]
  let h0 : IsAdic (⊥ : Ideal A) := is_bot_adic_iff.mpr inferInstance
  let e := CommRingCat.ofHom (RingEquiv.quotientBot A).toRingHom
  let t := LocallyRingedSpace.Γ.map (Spec.toLocallyRingedSpace.map e.op).op
  calc
    _ = ((globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv ≫
        LocallyRingedSpace.Γ.map (fromSpecQuotient h0).op) ≫ t := by
      rw [discreteIsoSpec_inv, op_comp, Functor.map_comp]
      exact (Category.assoc _ _ _).symm
    _ = (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal A)) ≫
        toSpecΓ (CommRingCat.of (A ⧸ (⊥ : Ideal A)))) ≫ t := by
      rw [globalSectionsIso_inv_comp_fromSpecQuotient]
      rfl
    _ = CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal A)) ≫
        (e ≫ toSpecΓ (CommRingCat.of A)) := by
      rw [Category.assoc, ← Spec_Γ_naturality e]
    _ = _ := by
      rw [← Category.assoc]
      have he : CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal A)) ≫ e = 𝟙 _ := by
        ext a
        exact RingEquiv.quotientBot_mk a
      rw [he, Category.id_comp]

end TauCeti.FormalScheme.Spf
