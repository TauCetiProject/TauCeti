/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Localization.Ideal

/-!
# Reduced closed subschemes and radical ideal sheaves

A closed subscheme is reduced exactly when its defining ideal sheaf is radical. Equivalently,
its ideal on every affine open is radical. This permits reducedness of a divisor to be checked
on its local equations, rather than on the local rings of the closed subscheme.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, §3, reduced induced subscheme structures.
-/

public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme} (I : X.IdealSheafData)

/-- A closed subscheme is reduced exactly when its ideal sheaf equals its radical. -/
theorem isReduced_subscheme_iff_radical_eq : IsReduced I.subscheme ↔ I.radical = I := by
  constructor
  · intro h
    have := vanishingIdeal_le_ker_of_range_subset I.subschemeι
      (Z := I.support) (by rw [range_subschemeι])
    rw [ker_subschemeι, vanishingIdeal_support] at this
    exact le_antisymm this I.le_radical
  · intro h
    have heq : I = vanishingIdeal I.support := by rw [vanishingIdeal_support, h]
    rw [heq]
    infer_instance

/-- A closed subscheme is reduced exactly when its ideal on each affine open is radical. -/
theorem isReduced_subscheme_iff_isRadical_ideal :
    IsReduced I.subscheme ↔ ∀ U : X.affineOpens, (I.ideal U).IsRadical := by
  rw [isReduced_subscheme_iff_radical_eq]
  constructor
  · intro h U
    exact Ideal.radical_eq_iff.mp (congrArg (fun J : X.IdealSheafData ↦ J.ideal U) h)
  · intro h
    exact IdealSheafData.ext (funext fun U ↦ Ideal.radical_eq_iff.mpr (h U))

open CategoryTheory in
/-- Mapping the radical of an ideal sheaf's ideal on an affine open to a stalk commutes with
 taking the radical. -/
theorem map_radical_ideal_germ (U : X.affineOpens) (x : X) (hx : x ∈ U.1) :
    (I.ideal U).radical.map (X.presheaf.germ U.1 x hx).hom =
      ((I.ideal U).map (X.presheaf.germ U.1 x hx).hom).radical := by
  let := (X.presheaf.germ U.1 x hx).hom.toAlgebra
  have := U.2.isLocalization_stalk ⟨x, hx⟩
  simpa only [RingHom.algebraMap_toAlgebra] using
    IsLocalization.map_radical (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) (I.ideal U)

open CategoryTheory in
/-- The zero scheme of a global function is reduced exactly when all of its germs are radical
elements, that is, generate radical principal ideals. -/
theorem isReduced_subscheme_ofIdealTop_span_singleton_iff (f : Γ(X, ⊤)) :
    IsReduced (ofIdealTop (Ideal.span {f})).subscheme ↔
      ∀ x : X, IsRadical (X.presheaf.germ ⊤ x trivial f) := by
  let I := ofIdealTop (Ideal.span {f})
  have hmap (U : X.affineOpens) (x : X) (hx : x ∈ U.1) :
      (I.ideal U).map (X.presheaf.germ U.1 x hx).hom =
        Ideal.span {X.presheaf.germ ⊤ x trivial f} := by
    rw [ofIdealTop_ideal, Ideal.map_map, Ideal.map_span, Set.image_singleton,
      ← CommRingCat.hom_comp, TopCat.Presheaf.germ_res]
  rw [isReduced_subscheme_iff_isRadical_ideal]
  constructor
  · intro h x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hrad : (Ideal.span {X.presheaf.germ ⊤ x trivial f}).IsRadical := by
      apply Ideal.radical_eq_iff.mp
      rw [← hmap ⟨U, hU⟩ x hxU, ← I.map_radical_ideal_germ ⟨U, hU⟩ x hxU,
        Ideal.radical_eq_iff.mpr (h ⟨U, hU⟩)]
    exact isRadical_iff_span_singleton.mpr hrad
  · intro h U
    apply Ideal.radical_eq_iff.mp
    apply U.2.ideal_ext_iff.mpr
    intro x hxU
    rw [I.map_radical_ideal_germ U x hxU, hmap U x hxU]
    exact Ideal.radical_eq_iff.mpr (isRadical_iff_span_singleton.mp (h x))

end AlgebraicGeometry.Scheme.IdealSheafData
