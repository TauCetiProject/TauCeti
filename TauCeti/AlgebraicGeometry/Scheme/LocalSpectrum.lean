/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Local rings on the spectrum of a stalk

The canonical map `Spec 𝒪_{X,x} ⟶ X` identifies local rings at corresponding points.
Consequently the height of a prime of `𝒪_{X,x}` is the local dimension at its image in `X`.
Together with `Scheme.range_fromSpecStalk`, this identifies height-one primes of a stalk
with codimension-one generizations of its point, as needed to pass between local algebra
and pointwise ramification conditions.

The local-ring comparison uses Mathlib's
`isIso_specMap_stalkMap_localization` on an affine neighbourhood.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The spectrum of a stalk has the same local rings as the ambient scheme at corresponding
points. No Noetherianity hypothesis is needed. -/
instance isIso_stalkMap_fromSpecStalk (X : Scheme.{u}) (x : X)
    (q : Spec (X.presheaf.stalk x)) : IsIso ((X.fromSpecStalk x).stalkMap q) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  replace hU : IsAffineOpen U := hU
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  let p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let e := IsLocalization.algEquiv p.primeCompl (Localization p.primeCompl)
    (X.presheaf.stalk x)
  have hg : X.presheaf.germ U x hxU =
      CommRingCat.ofHom (algebraMap Γ(X, U) (Localization p.primeCompl)) ≫
        e.toRingEquiv.toCommRingCatIso.hom := by
    ext r
    exact (e.commutes r).symm
  have heq : X.fromSpecStalk x = Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec :=
    (hU.fromSpecStalk_eq_fromSpecStalk hxU).symm
  rw [heq, hg, Spec.map_comp, Scheme.Hom.stalkMap_comp]
  have hloc : IsIso ((Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, U) (Localization p.primeCompl)))).stalkMap
        (Spec.map e.toRingEquiv.toCommRingCatIso.hom q)) :=
    isIso_specMap_stalkMap_localization _ _ _
  rw [Scheme.Hom.stalkMap_comp]
  apply IsIso.comp_isIso'
  · -- The composition step unfolds stalk-map wrappers; instance search needs the
    -- scheme-level form to recognize the open immersion `hU.fromSpec`.
    exact inferInstanceAs (IsIso (hU.fromSpec.stalkMap _))
  · exact IsIso.comp_isIso' hloc inferInstance

/-- The height of a prime in a stalk equals the local dimension of its image in the scheme. -/
theorem height_eq_ringKrullDim_fromSpecStalk (X : Scheme.{u}) (x : X)
    (q : Spec (X.presheaf.stalk x)) :
    (q.asIdeal.height : WithBot ℕ∞) =
      ringKrullDim (X.presheaf.stalk (X.fromSpecStalk x q)) := by
  rw [idealHeight_eq_coheight, ← ringKrullDim_stalk_eq_coheight]
  exact (ringKrullDim_eq_of_ringEquiv
    (asIso ((X.fromSpecStalk x).stalkMap q)).commRingCatIsoToRingEquiv).symm

end AlgebraicGeometry.Scheme
