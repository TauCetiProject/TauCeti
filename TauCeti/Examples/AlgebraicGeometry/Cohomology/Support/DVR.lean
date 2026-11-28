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
  -- Mathlib has no membership lemma for `Opens.compl`: `U.compl` is the closed set `⟨Uᶜ, _⟩`, so
  -- membership in it is `x ∉ U` by definition.
  change x ∉ (Spec (.of R)).basicOpen (uniformizer ϖ) ↔ _
  rw [basicOpen_eq_of_affine]
  refine (PrimeSpectrum.mem_basicOpen ϖ x).not.trans ?_
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

variable (K : Type*) [CommRing K] [Algebra R K] [IsFractionRing R K]

/-- **`H¹_𝔪(Spec R, 𝒪) ≅ K / R`** for a discrete valuation ring `R` with fraction field `K`: the
first cohomology of the structure sheaf with supports in the closed point `V(ϖ)` is the quotient of
`K` by the image of `R`, since `K` is the localization of `R` away from `ϖ`. -/
abbrev cohomologyWithSupportOneAddEquiv (hϖ : Irreducible ϖ) :
    (Scheme.Modules.unit (Spec (.of R))).cohomologyWithSupport
        ((Spec (.of R)).basicOpen (uniformizer ϖ)).compl ⊤ 1 ≃+
      K ⧸ (algebraMap R K).toAddMonoidHom.range :=
  have : IsLocalization.Away ϖ K := hϖ.isLocalizationAway_fractionRing
  Scheme.Modules.cohomologyWithSupportOneComplBasicOpenSpecUnitAddEquiv ϖ K

end TauCeti.AlgebraicGeometry.SupportDVRExample

end
