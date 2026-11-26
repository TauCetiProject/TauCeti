/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Support.BasicOpen

/-!
# Example: `H¹_Z(𝔸¹, 𝒪) = R[t, t⁻¹] / R[t]` for `Z` the origin

On the affine line `𝔸¹_R = Spec R[t]` over a commutative ring `R`, let `Z = V(t)` be the origin,
the complement of the basic open `D(t)`. Since `𝔸¹_R` is affine, `H¹(𝔸¹_R, 𝒪) = 0`, so the long
exact sequence of supports identifies `H¹_Z(𝔸¹_R, 𝒪)` with the cokernel of the restriction
`Γ(𝔸¹_R, 𝒪) → Γ(D(t), 𝒪)`, that is, of `R[t] → R[t, t⁻¹]`
(`TauCeti.AlgebraicGeometry.SupportDegreeOneExample.cohomologyWithSupportOneAddEquiv`).
-/

public section

open AlgebraicGeometry Polynomial

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.SupportDegreeOneExample

variable (R : Type u) [CommRing R]

/-- The affine line `𝔸¹_R = Spec R[t]`. -/
abbrev affineLine : Scheme.{u} := Spec (.of R[X])

/-- The coordinate `t` of `𝔸¹_R`, as a global function. -/
abbrev coordinate : Γ(affineLine R, ⊤) := (Scheme.ΓSpecIso (.of R[X])).inv X

/-- The ring isomorphism `Γ(𝔸¹_R, 𝒪) ≅ R[t]` sends the localization at the coordinate to the
Laurent polynomials. -/
def localizationRingEquiv : Localization.Away (coordinate R) ≃+* Localization.Away (X : R[X]) :=
  IsLocalization.ringEquivOfRingEquiv _ _
    (Scheme.ΓSpecIso (.of R[X])).commRingCatIsoToRingEquiv
    (show (Submonoid.powers (coordinate R)).map _ = Submonoid.powers (X : R[X]) by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers ((Scheme.ΓSpecIso (.of R[X])).inv_hom_id_apply X))

/-- `localizationRingEquiv` carries the image of `Γ(𝔸¹_R, 𝒪)` onto the image of `R[t]`. -/
lemma map_range_algebraMap :
    (LinearMap.range (Algebra.linearMap Γ(affineLine R, ⊤)
        (Localization.Away (coordinate R)))).toAddSubgroup.map
        (localizationRingEquiv R).toAddEquiv.toAddMonoidHom =
      (algebraMap R[X] (Localization.Away (X : R[X]))).toAddMonoidHom.range := by
  have key (a : Γ(affineLine R, ⊤)) : localizationRingEquiv R (algebraMap _ _ a) =
      algebraMap R[X] (Localization.Away (X : R[X])) ((Scheme.ΓSpecIso (.of R[X])).hom a) := by
    unfold localizationRingEquiv
    exact IsLocalization.ringEquivOfRingEquiv_eq _ a
  ext y
  simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.mem_range,
    Algebra.linearMap_apply, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨(Scheme.ΓSpecIso (.of R[X])).hom a, (key a).symm⟩
  · rintro ⟨r, rfl⟩
    refine ⟨_, ⟨(Scheme.ΓSpecIso (.of R[X])).inv r, rfl⟩, ?_⟩
    refine (key _).trans ?_
    exact congrArg _ ((Scheme.ΓSpecIso (.of R[X])).inv_hom_id_apply r)

/-- **`H¹_Z(𝔸¹_R, 𝒪) = R[t, t⁻¹] / R[t]` for `Z` the origin.** On the affine line over a
commutative ring `R`, the first cohomology of the structure sheaf with supports in the origin
`V(t)` is the quotient of the Laurent polynomials `R[t, t⁻¹]` by the polynomials `R[t]`. -/
def cohomologyWithSupportOneAddEquiv :
    (Scheme.Modules.unit (affineLine R)).cohomologyWithSupport
        ((affineLine R).basicOpen (coordinate R)).compl ⊤ 1 ≃+
      Localization.Away (X : R[X]) ⧸
        (algebraMap R[X] (Localization.Away (X : R[X]))).toAddMonoidHom.range :=
  (Scheme.Modules.cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv _
    (coordinate R)).toAddEquiv.trans
    (QuotientAddGroup.congr _ _ (localizationRingEquiv R).toAddEquiv (map_range_algebraMap R))

/-- The identification of `H¹_Z(𝔸¹_R, 𝒪)` with `R[t, t⁻¹] / R[t]` sends the class of a Laurent
polynomial back through `localizationRingEquiv` to `H¹_{V(f)}(X, 𝒪) ≅ Γ(X, 𝒪)_f / Γ(X, 𝒪)` for
the coordinate `f = t`. -/
lemma cohomologyWithSupportOneAddEquiv_symm_mk (y : Localization.Away (X : R[X])) :
    (cohomologyWithSupportOneAddEquiv R).symm (QuotientAddGroup.mk y) =
      (Scheme.Modules.cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv _ (coordinate R)).symm
        (Submodule.Quotient.mk ((localizationRingEquiv R).symm y)) :=
  (rfl)

end TauCeti.AlgebraicGeometry.SupportDegreeOneExample

end
