/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Support.BasicOpen
public import TauCeti.AlgebraicGeometry.Cohomology.Support.Integral
public import TauCeti.RingTheory.DiscreteValuationRing.FractionRing

/-!
# Example: local cohomology of a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K`, uniformizer `ϖ` and maximal ideal
`𝔪 = (ϖ)`. On `Spec R` the closed point `V(𝔪)` is the complement `V(ϖ)` of the basic open `D(ϖ)`,
which is the generic point. Then `H⁰_𝔪(Spec R, 𝒪) = 0`, since `Spec R` is integral and the closed
point is not everything, and `H¹_𝔪(Spec R, 𝒪) ≅ K / R`: `Spec R` is affine, so the long exact
sequence of supports identifies `H¹_{V(ϖ)}` with the cokernel of `R → R_ϖ`, and `R_ϖ = K`.

## Main declarations

* `TauCeti.AlgebraicGeometry.SupportDVRExample.mem_compl_basicOpen_uniformizer_iff`: `V(ϖ)` is
  the closed point.
* `TauCeti.AlgebraicGeometry.SupportDVRExample.subsingleton_cohomologyWithSupport_zero`:
  `H⁰_𝔪(Spec R, 𝒪) = 0`.
* `TauCeti.AlgebraicGeometry.SupportDVRExample.cohomologyWithSupportOneAddEquiv`:
  `H¹_𝔪(Spec R, 𝒪) ≅ K / R`.
-/

public section

open AlgebraicGeometry IsLocalRing

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.SupportDVRExample

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}

variable (ϖ) in
/-- The uniformizer `ϖ`, as a global function on `Spec R`. -/
abbrev uniformizer : Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).inv ϖ

/-- The complement `V(ϖ)` of the basic open `D(ϖ)` of `Spec R` is the closed point `V(𝔪)`. -/
theorem mem_compl_basicOpen_uniformizer_iff (hϖ : Irreducible ϖ) (x : PrimeSpectrum R) :
    x ∈ ((Spec (.of R)).basicOpen (uniformizer ϖ)).compl ↔ x = closedPoint R := by
  change x ∉ (Spec (.of R)).basicOpen (uniformizer ϖ) ↔ _
  rw [basicOpen_eq_of_affine]
  -- Membership in `PrimeSpectrum.basicOpen ϖ` is `ϖ ∉ x.asIdeal` by definition.
  change ¬ϖ ∉ x.asIdeal ↔ _
  rw [not_not, PrimeSpectrum.ext_iff, closedPoint, ← Ideal.span_singleton_le_iff_mem,
    ← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
  exact ⟨fun h ↦ ((maximalIdeal.isMaximal R).eq_of_le x.isPrime.ne_top h).symm,
    fun h ↦ h.symm.le⟩

/-- **`H⁰_𝔪(Spec R, 𝒪) = 0`** for a discrete valuation ring `R`: the generic point is not the
closed point `V(ϖ)`, and `Spec R` is integral. -/
theorem subsingleton_cohomologyWithSupport_zero (hϖ : Irreducible ϖ) :
    Subsingleton ((Scheme.Modules.unit (Spec (.of R))).cohomologyWithSupport
      ((Spec (.of R)).basicOpen (uniformizer ϖ)).compl ⊤ 0) := by
  refine Scheme.Modules.subsingleton_cohomologyWithSupport_zero_unit _ fun h ↦ ?_
  -- The generic point `(0)` is not the closed point, since `ϖ ≠ 0` lies in `𝔪`.
  have := (mem_compl_basicOpen_uniformizer_iff hϖ ⟨⊥, Ideal.isPrime_bot⟩).1
    ((Set.eq_univ_iff_forall.1 h) _)
  rw [PrimeSpectrum.ext_iff] at this
  have h𝔪 : ϖ ∈ (closedPoint R).asIdeal := (mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  rw [← this] at h𝔪
  exact hϖ.ne_zero (Ideal.mem_bot.1 h𝔪)

variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The ring isomorphism `Γ(Spec R, 𝒪) ≅ R` sends the localization at the uniformizer to the
fraction field `K`. -/
def localizationRingEquiv (hϖ : Irreducible ϖ) : Localization.Away (uniformizer ϖ) ≃+* K :=
  have : IsLocalization.Away ϖ K := hϖ.isLocalizationAway_fractionRing
  IsLocalization.ringEquivOfRingEquiv _ _
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
    (show (Submonoid.powers (uniformizer ϖ)).map _ = Submonoid.powers ϖ by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers ((Scheme.ΓSpecIso (.of R)).inv_hom_id_apply ϖ))

/-- `localizationRingEquiv` is compatible with the identification `Γ(Spec R, 𝒪) ≅ R`. -/
lemma localizationRingEquiv_algebraMap (hϖ : Irreducible ϖ) (a : Γ(Spec (.of R), ⊤)) :
    localizationRingEquiv K hϖ (algebraMap _ _ a) =
      algebraMap R K ((Scheme.ΓSpecIso (.of R)).hom a) :=
  have : IsLocalization.Away ϖ K := hϖ.isLocalizationAway_fractionRing
  by unfold localizationRingEquiv; exact IsLocalization.ringEquivOfRingEquiv_eq _ a

/-- `localizationRingEquiv` carries the image of `Γ(Spec R, 𝒪)` onto the image of `R`. -/
lemma map_range_algebraMap (hϖ : Irreducible ϖ) :
    (LinearMap.range (Algebra.linearMap Γ(Spec (.of R), ⊤)
        (Localization.Away (uniformizer ϖ)))).toAddSubgroup.map
        (localizationRingEquiv K hϖ).toAddEquiv.toAddMonoidHom =
      (algebraMap R K).toAddMonoidHom.range := by
  ext y
  simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.mem_range,
    Algebra.linearMap_apply, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨(Scheme.ΓSpecIso (.of R)).hom a, (localizationRingEquiv_algebraMap K hϖ a).symm⟩
  · rintro ⟨r, rfl⟩
    refine ⟨_, ⟨(Scheme.ΓSpecIso (.of R)).inv r, rfl⟩, ?_⟩
    refine (localizationRingEquiv_algebraMap K hϖ _).trans ?_
    exact congrArg _ ((Scheme.ΓSpecIso (.of R)).inv_hom_id_apply r)

/-- **`H¹_𝔪(Spec R, 𝒪) ≅ K / R`** for a discrete valuation ring `R` with fraction field `K`: the
first cohomology of the structure sheaf with supports in the closed point `V(ϖ)` is the quotient of
`K` by the image of `R`. -/
def cohomologyWithSupportOneAddEquiv (hϖ : Irreducible ϖ) :
    (Scheme.Modules.unit (Spec (.of R))).cohomologyWithSupport
        ((Spec (.of R)).basicOpen (uniformizer ϖ)).compl ⊤ 1 ≃+
      K ⧸ (algebraMap R K).toAddMonoidHom.range :=
  (Scheme.Modules.cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv _
    (uniformizer ϖ)).toAddEquiv.trans
    (QuotientAddGroup.congr _ _ (localizationRingEquiv K hϖ).toAddEquiv
      (map_range_algebraMap K hϖ))

/-- The identification of `H¹_𝔪(Spec R, 𝒪)` with `K / R` sends the class of an element of `K`
back through `localizationRingEquiv` to `H¹_{V(f)}(X, 𝒪) ≅ Γ(X, 𝒪)_f / Γ(X, 𝒪)` for `f = ϖ`. -/
lemma cohomologyWithSupportOneAddEquiv_symm_mk (hϖ : Irreducible ϖ) (y : K) :
    (cohomologyWithSupportOneAddEquiv K hϖ).symm (QuotientAddGroup.mk y) =
      (Scheme.Modules.cohomologyWithSupportOneComplBasicOpenUnitLinearEquiv _
        (uniformizer ϖ)).symm (Submodule.Quotient.mk ((localizationRingEquiv K hϖ).symm y)) :=
  -- As in `SupportDegreeOneExample.cohomologyWithSupportOneAddEquiv_symm_mk`: the `Submodule`
  -- and `AddSubgroup` quotients agree only definitionally, so this is `rfl` rather than `rw`.
  (rfl)

end TauCeti.AlgebraicGeometry.SupportDVRExample

end
