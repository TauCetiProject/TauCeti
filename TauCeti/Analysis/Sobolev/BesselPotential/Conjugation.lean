/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.Conjugation
public import TauCeti.Analysis.Sobolev.BesselPotential.Postcomp
import Mathlib.Analysis.RCLike.Extend
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Conjugation on the Bessel-potential spaces

A continuous conjugate-linear map `L : F →L⋆[ℂ] G`, for instance complex conjugation on `ℂ` or
componentwise conjugation on `ℂʳ`, acts on `F`-valued tempered distributions by
`(L u) φ = L (u (conj φ))` (`TemperedDistribution.conjPostcompCLM`). Its symbol `⟨ξ⟩ ^ s` being real
and even, the Bessel potential `J^s` commutes with this action, and on `Lᵖ` functions the action is
`f ↦ L ∘ f`. Hence `L` induces a bounded conjugate-linear operator

`H^{s,p}(E, F) → H^{s,p}(E, G)`, `u ↦ L u`, with `J^s (L u) = L ∘ J^s u`,

on Mathlib's Bessel-potential spaces, for every real order `s`, including negative orders, and
every `1 ≤ p ≤ ∞` (`BesselPotentialSpace.conjPostcomp`). On Schwartz functions it is `u ↦ L ∘ u`.
If `L` preserves norms, so does the induced operator, since the `H^{s,p}` norm of `u` is the `Lᵖ`
norm of `J^s u`. A conjugate-linear isometric equivalence `L : F ≃ₗᵢ⋆[ℂ] G` therefore induces a
conjugate-linear isometric equivalence of the Bessel-potential spaces
(`BesselPotentialSpace.conjPostcompₗᵢ`). In particular complex conjugation is a
conjugate-linear isometric involution of `H^{s,p}(E)` for every real `s`.

It is the input for describing the Sobolev spaces of real-valued functions, and of sections of real
vector bundles, as the fixed points of conjugation on the complex ones.

## Main declarations

* `BesselPotentialSpace.conjPostcomp`: the bounded conjugate-linear operator
  `H^{s,p}(E, F) → H^{s,p}(E, G)` induced by `L : F →L⋆[ℂ] G`.
* `BesselPotentialSpace.norm_conjPostcomp_apply`: it preserves norms when `L` does.
* `BesselPotentialSpace.conjPostcomp_conjPostcomp`: two conjugations compose to the complex-linear
  operator `BesselPotentialSpace.postcomp` of the composite.
* `BesselPotentialSpace.conjPostcompₗᵢ`: the conjugate-linear isometric equivalence induced by
  `L : F ≃ₗᵢ⋆[ℂ] G`.
* `SchwartzMap.toBesselPotentialSpaceCLM_conjPostcompCLM`: on Schwartz functions the operator is
  `u ↦ L ∘ u`.
* `TemperedDistribution.MemSobolev.compLp_conj`: applying `L` to the values of an `Lᵖ` function
  in `H^{s,p}` gives an `Lᵖ` function in `H^{s,p}`.
* `TemperedDistribution.MemSobolev.ofReal_compLp`: so does a real-linear functional `ℓ`, read as a
  complex-valued function: `ℓ` is the real part of the complex-linear functional
  `StrongDual.extendRCLike ℓ`, and the real part of `z` is `(z + conj z) / 2`.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace ComplexConjugate

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

namespace BesselPotentialSpace

variable {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (E s p) in
/-- The bounded conjugate-linear operator `H^{s,p}(E, F) → H^{s,p}(E, G)` induced by a continuous
conjugate-linear map `L : F →L⋆[ℂ] G`. It sends the tempered distribution `u` to
`φ ↦ L (u (conj φ))` and its `Lᵖ` part `J^s u` to `L ∘ J^s u`. -/
def conjPostcomp (L : F →L⋆[ℂ] G) : H^{s, p}(E, F) →L⋆[ℂ] H^{s, p}(E, G) :=
  LinearMap.mkContinuous
    { toFun f :=
        { toDistr := conjPostcompCLM L f.toDistr
          toLp := L.compLp f.toLp
          bessel_toDistr_eq_toLp := by
            rw [besselPotential_conjPostcompCLM, f.bessel_toDistr_eq_toLp,
              conjPostcompCLM_toTemperedDistribution_eq] }
      map_add' f g := ext (map_add (conjPostcompCLM L) f.toDistr g.toDistr)
      map_smul' c f := ext (map_smulₛₗ (conjPostcompCLM L) c f.toDistr) }
    ‖L‖ fun f ↦ by
      rw [← norm_toLp_eq, ← norm_toLp_eq]
      exact L.norm_compLp_le f.toLp

@[simp]
theorem toDistr_conjPostcomp (L : F →L⋆[ℂ] G) (f : H^{s, p}(E, F)) :
    (conjPostcomp E s p L f).toDistr = conjPostcompCLM L f.toDistr :=
  (rfl)

theorem toDistr_conjPostcomp_apply (L : F →L⋆[ℂ] G) (f : H^{s, p}(E, F)) (φ : 𝓢(E, ℂ)) :
    (conjPostcomp E s p L f).toDistr φ = L (f.toDistr (SchwartzMap.conjCLM φ)) :=
  conjPostcompCLM_apply_apply L f.toDistr φ

@[simp]
theorem toLp_conjPostcomp (L : F →L⋆[ℂ] G) (f : H^{s, p}(E, F)) :
    (conjPostcomp E s p L f).toLp = L.compLp f.toLp :=
  (rfl)

/-- The operator induced by `L` has norm at most `‖L‖`. -/
theorem norm_conjPostcomp_apply_le (L : F →L⋆[ℂ] G) (f : H^{s, p}(E, F)) :
    ‖conjPostcomp E s p L f‖ ≤ ‖L‖ * ‖f‖ := by
  rw [← norm_toLp_eq, ← norm_toLp_eq, toLp_conjPostcomp]
  exact L.norm_compLp_le f.toLp

/-- **Conjugation is isometric on `H^{s,p}`.** If `L` preserves norms, so does the operator it
induces on `H^{s,p}`, for every real `s`. -/
theorem norm_conjPostcomp_apply (L : F →L⋆[ℂ] G) (hL : ∀ x, ‖L x‖ = ‖x‖)
    (f : H^{s, p}(E, F)) : ‖conjPostcomp E s p L f‖ = ‖f‖ := by
  rw [← norm_toLp_eq, ← norm_toLp_eq, toLp_conjPostcomp, Lp.norm_def, Lp.norm_def]
  congr 1
  exact eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    ((L.coeFn_compLp f.toLp).mono fun x hx ↦ by rw [hx, hL])

/-- Two conjugations compose to the complex-linear operator induced by the composite. -/
@[simp]
theorem conjPostcomp_conjPostcomp {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (L' : G →L⋆[ℂ] H) (L : F →L⋆[ℂ] G) (f : H^{s, p}(E, F)) :
    conjPostcomp E s p L' (conjPostcomp E s p L f) = postcomp E s p (L'.comp L) f := by
  ext φ
  rw [toDistr_conjPostcomp_apply, toDistr_conjPostcomp_apply, toDistr_postcomp_apply]
  simp

variable (E s p) in
/-- The conjugate-linear isometric equivalence `H^{s,p}(E, F) ≃ H^{s,p}(E, G)` induced by a
conjugate-linear isometric equivalence `L : F ≃ₗᵢ⋆[ℂ] G`. For complex conjugation on `ℂ` this is
complex conjugation of `H^{s,p}(E)`, an isometric involution. -/
def conjPostcompₗᵢ (L : F ≃ₗᵢ⋆[ℂ] G) : H^{s, p}(E, F) ≃ₗᵢ⋆[ℂ] H^{s, p}(E, G) where
  toFun := conjPostcomp E s p (L : F →L⋆[ℂ] G)
  invFun := conjPostcomp E s p (L.symm : G →L⋆[ℂ] F)
  map_add' := map_add _
  map_smul' := map_smulₛₗ _
  left_inv f := by
    ext φ
    rw [conjPostcomp_conjPostcomp, toDistr_postcomp_apply]
    simp
  right_inv f := by
    ext φ
    rw [conjPostcomp_conjPostcomp, toDistr_postcomp_apply]
    simp
  norm_map' := norm_conjPostcomp_apply _ L.norm_map

@[simp]
theorem conjPostcompₗᵢ_apply (L : F ≃ₗᵢ⋆[ℂ] G) (f : H^{s, p}(E, F)) :
    conjPostcompₗᵢ E s p L f = conjPostcomp E s p (L : F →L⋆[ℂ] G) f :=
  (rfl)

@[simp]
theorem conjPostcompₗᵢ_symm (L : F ≃ₗᵢ⋆[ℂ] G) :
    (conjPostcompₗᵢ E s p L).symm = conjPostcompₗᵢ E s p L.symm :=
  (rfl)

end BesselPotentialSpace

/-- On Schwartz functions, the operator induced by a conjugate-linear map `L` on `H^{s,p}` is
`u ↦ L ∘ u`. -/
theorem SchwartzMap.toBesselPotentialSpaceCLM_conjPostcompCLM {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (L : F →L⋆[ℂ] G) (u : 𝓢(E, F)) :
    toBesselPotentialSpaceCLM s p (conjPostcompCLM L u) =
      BesselPotentialSpace.conjPostcomp E s p L (toBesselPotentialSpaceCLM s p u) := by
  ext1
  rw [toDistr_toBesselPotentialSpaceCLM, BesselPotentialSpace.toDistr_conjPostcomp,
    toDistr_toBesselPotentialSpaceCLM, conjPostcompCLM_toTemperedDistributionCLM_eq]

namespace TemperedDistribution

variable {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : Lp F p (volume : Measure E)}

/-- Applying a conjugate-linear map to the values of an `Lᵖ` function preserves `H^{s,p}`. -/
theorem MemSobolev.compLp_conj (hu : MemSobolev s p (u : 𝓢'(E, F))) (L : F →L⋆[ℂ] G) :
    MemSobolev s p ((L.compLp u : Lp G p volume) : 𝓢'(E, G)) := by
  have h :=
    (BesselPotentialSpace.conjPostcomp E s p L hu.toBesselPotentialSpace).memSobolev_toDistr
  rwa [BesselPotentialSpace.toDistr_conjPostcomp, MemSobolev.toBesselPotentialSpace_toDistr,
    conjPostcompCLM_toTemperedDistribution_eq] at h

/-- Applying a real-linear functional to the values of an `Lᵖ` function preserves `H^{s,p}`: the
complexification of `x ↦ ℓ (u x)` lies in `H^{s,p}(E, ℂ)`. -/
theorem MemSobolev.ofReal_compLp (hu : MemSobolev s p (u : 𝓢'(E, F))) (ℓ : F →L[ℝ] ℝ) :
    MemSobolev s p
      ((Complex.ofRealCLM.compLp (ℓ.compLp u) : Lp ℂ p volume) : 𝓢'(E, ℂ)) := by
  set L : F →L[ℂ] ℂ := StrongDual.extendRCLike ℓ
  have hL := hu.compLp L
  have hc := hL.compLp_conj (starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap
  have heq : (Complex.ofRealCLM.compLp (ℓ.compLp u) : Lp ℂ p volume) =
      (2⁻¹ : ℂ) • (L.compLp u + (starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap.compLp
        (L.compLp u)) := by
    refine Lp.ext ?_
    filter_upwards [Complex.ofRealCLM.coeFn_compLp (ℓ.compLp u), ℓ.coeFn_compLp u,
      Lp.coeFn_smul (2⁻¹ : ℂ) (L.compLp u + (starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap.compLp
        (L.compLp u)),
      Lp.coeFn_add (L.compLp u) ((starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap.compLp
        (L.compLp u)),
      (starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap.coeFn_compLp (L.compLp u),
      L.coeFn_compLp u] with x h₁ h₂ h₃ h₄ h₅ h₆
    rw [h₁, h₂, h₃, Pi.smul_apply, h₄, Pi.add_apply, h₅, h₆]
    simp only [Complex.ofRealCLM_apply, ContinuousLinearEquiv.coe_coe, starL_apply,
      RCLike.star_def, Complex.add_conj, smul_eq_mul]
    have hre : (L (u x)).re = ℓ (u x) := StrongDual.re_extendRCLike_apply (𝕜 := ℂ) ℓ (u x)
    rw [hre]
    push_cast
    ring
  rw [heq, Lp.toTemperedDistribution_smul, Lp.toTemperedDistribution_add]
  exact (hL.add hc).smul _

end TemperedDistribution
