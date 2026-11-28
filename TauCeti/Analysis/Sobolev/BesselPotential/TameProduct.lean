/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Product
import TauCeti.Analysis.Sobolev.BesselPotential.Besov

/-!
# The tame product estimate on `H^s(ℝⁿ)`

Let `E` be a finite-dimensional real inner product space, `H` a complex Hilbert space and
`s > 0`. If `u ∈ H^s(E)` and `v ∈ H^s(E, H)` are bounded functions, their pointwise product lies
in `H^s(E, H)` (`TemperedDistribution.MemSobolev.smul_of_ae_eq`), and there is a constant `C`,
depending only on `E`, `H` and `s`, with

`‖u v‖_{H^s} ≤ C (‖u‖_∞ ‖v‖_{H^s} + ‖u‖_{H^s} ‖v‖_∞)`

(`TemperedDistribution.exists_norm_toBesselPotentialSpace_smul_le`). Here `H^s(E, H)` is
Mathlib's Bessel-potential space `H^{s,2}`, with norm `‖J^s u‖₂`.

Unlike the algebra estimate `‖u v‖_{H^s} ≤ C ‖u‖_{H^s} ‖v‖_{H^s}` of
`TauCeti.Analysis.Sobolev.BesselPotential.Algebra`, which needs `s > n / 2`, the tame estimate
holds for every `s > 0`, and it is linear in the highest norm `‖·‖_{H^s}`. This is the form in
which nonlinear terms are bounded in energy estimates on the scale `H^s`: a quadratic expression
in a field costs one factor `‖·‖_{H^s}` against one factor `‖·‖_∞`, the latter controlled by a
lower norm.

The estimate is the case `p₁ = p₂ = r = q = 2`, `p₃ = p₄ = ∞` of the tame product estimate on
Besov spaces, `TauCeti.BesovSpace.exists_toDistr_eq_smul_and_norm_le`, since
`H^{s,2} = B^s_{2,2}` with equivalent norms (`TauCeti.BesovSpace.besselPotentialSpaceEquiv`).

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Corollary 2.86.
* T. Kato and G. Ponce, *Commutator estimates and the Euler and Navier–Stokes equations*, Comm.
  Pure Appl. Math. **41** (1988), 891–907.
-/

public section

noncomputable section

open MeasureTheory TauCeti.BesovSpace
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {s : ℝ}

namespace TemperedDistribution

/-- The tame product estimate, with the product realized as an element of `H^s(E, H)`. -/
private theorem exists_besselPotentialSpace_toDistr_eq_smul_and_norm_le (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : Lp ℂ 2 (volume : Measure E)} {v : Lp H 2 (volume : Measure E)}
      (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ))) (hv : MemSobolev s 2 (v : 𝓢'(E, H)))
      {f : Lp ℂ ∞ (volume : Measure E)} {g : Lp H ∞ (volume : Measure E)},
      u =ᵐ[volume] f → v =ᵐ[volume] g →
      ∃ w : H^{s, 2}(E, H), w.toDistr = ((u • g : Lp H 2 (volume : Measure E)) : 𝓢'(E, H)) ∧
        ‖w‖ ≤ C * (‖f‖ * ‖hv.toBesselPotentialSpace‖ + ‖hu.toBesselPotentialSpace‖ * ‖g‖) := by
  let φ : ContDiffBump (0 : E) := default
  obtain ⟨C, hC, hCw⟩ := TauCeti.BesovSpace.exists_toDistr_eq_smul_and_norm_le H φ hs
  -- Transport through `B^s_{2,2} ≃ H^{s,2}`, for scalar and for `H`-valued functions.
  let e := besselPotentialSpaceEquiv H φ s
  let e' := besselPotentialSpaceEquiv ℂ φ s
  set K := ‖(e.symm : H^{s, 2}(E, H) →L[ℂ] TauCeti.BesovSpace H φ s 2 2)‖ +
    ‖(e'.symm : H^{s, 2}(E, ℂ) →L[ℂ] TauCeti.BesovSpace ℂ φ s 2 2)‖
  refine ⟨‖(e : TauCeti.BesovSpace H φ s 2 2 →L[ℂ] H^{s, 2}(E, H))‖ * C * K, by positivity,
    fun {u v} hu hv f g hf hg ↦ ?_⟩
  set U := e'.symm hu.toBesselPotentialSpace
  set V := e.symm hv.toBesselPotentialSpace
  have hU : U.toDistr = u := by simp [U, e']
  have hV : V.toDistr = v := by simp [V, e]
  obtain ⟨w, hw, hwn⟩ := hCw (r := 2) U V
    (hU.trans (Lp.toTemperedDistribution_eq_toTemperedDistribution_iff.2 hf))
    (hV.trans (Lp.toTemperedDistribution_eq_toTemperedDistribution_iff.2 hg))
  have hUu : toLpCLM ℂ φ 2 2 hs U = u :=
    Lp.toTemperedDistribution_injective (by simp only [coe_toLpCLM, hU])
  refine ⟨e w, by rw [toDistr_besselPotentialSpaceEquiv, hw, hUu], ?_⟩
  have hUn : ‖U‖ ≤ K * ‖hu.toBesselPotentialSpace‖ :=
    ((e'.symm : H^{s, 2}(E, ℂ) →L[ℂ] TauCeti.BesovSpace ℂ φ s 2 2).le_opNorm _).trans <| by
      gcongr
      exact le_add_of_nonneg_left (norm_nonneg _)
  have hVn : ‖V‖ ≤ K * ‖hv.toBesselPotentialSpace‖ :=
    ((e.symm : H^{s, 2}(E, H) →L[ℂ] TauCeti.BesovSpace H φ s 2 2).le_opNorm _).trans <| by
      gcongr
      exact le_add_of_nonneg_right (norm_nonneg _)
  calc ‖e w‖ ≤ ‖(e : TauCeti.BesovSpace H φ s 2 2 →L[ℂ] H^{s, 2}(E, H))‖ * ‖w‖ :=
        (e : TauCeti.BesovSpace H φ s 2 2 →L[ℂ] H^{s, 2}(E, H)).le_opNorm w
    _ ≤ ‖(e : TauCeti.BesovSpace H φ s 2 2 →L[ℂ] H^{s, 2}(E, H))‖ *
          (C * (‖f‖ * (K * ‖hv.toBesselPotentialSpace‖) +
            K * ‖hu.toBesselPotentialSpace‖ * ‖g‖)) := by
        gcongr
        exact hwn.trans (by gcongr)
    _ = _ := by ring

/-- **Products of bounded `H^s` functions, `s > 0`, are in `H^s`.** If `u ∈ H^s(E)` and
`v ∈ H^s(E, H)` are `L²` functions that are almost everywhere equal to `L^∞` functions `f` and
`g`, then their pointwise product, the `L²` function `u • g`, lies in `H^s(E, H)`. -/
theorem MemSobolev.smul_of_ae_eq (hs : 0 < s) {u : Lp ℂ 2 (volume : Measure E)}
    {v : Lp H 2 (volume : Measure E)} (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ)))
    (hv : MemSobolev s 2 (v : 𝓢'(E, H))) {f : Lp ℂ ∞ (volume : Measure E)}
    {g : Lp H ∞ (volume : Measure E)} (hf : u =ᵐ[volume] f) (hg : v =ᵐ[volume] g) :
    MemSobolev s 2 ((u • g : Lp H 2 (volume : Measure E)) : 𝓢'(E, H)) := by
  obtain ⟨w, hw, -⟩ :=
    (exists_besselPotentialSpace_toDistr_eq_smul_and_norm_le (E := E) (H := H) hs).choose_spec.2
      hu hv hf hg
  exact hw ▸ w.memSobolev_toDistr

/-- **The tame product estimate on `H^s`, `s > 0`** (Bahouri–Chemin–Danchin, Corollary 2.86;
Kato–Ponce). There is a constant `C`, depending only on `E`, `H` and `s`, such that for `L²`
functions `u ∈ H^s(E)` and `v ∈ H^s(E, H)` that are almost everywhere equal to `L^∞` functions
`f` and `g`,

`‖u v‖_{H^s} ≤ C (‖f‖_∞ ‖v‖_{H^s} + ‖u‖_{H^s} ‖g‖_∞)`. -/
theorem exists_norm_toBesselPotentialSpace_smul_le (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : Lp ℂ 2 (volume : Measure E)} {v : Lp H 2 (volume : Measure E)}
      (hu : MemSobolev s 2 (u : 𝓢'(E, ℂ))) (hv : MemSobolev s 2 (v : 𝓢'(E, H)))
      {f : Lp ℂ ∞ (volume : Measure E)} {g : Lp H ∞ (volume : Measure E)}
      (hf : u =ᵐ[volume] f) (hg : v =ᵐ[volume] g),
      ‖(hu.smul_of_ae_eq hs hv hf hg).toBesselPotentialSpace‖ ≤
        C * (‖f‖ * ‖hv.toBesselPotentialSpace‖ + ‖hu.toBesselPotentialSpace‖ * ‖g‖) := by
  obtain ⟨C, hC, h⟩ :=
    exists_besselPotentialSpace_toDistr_eq_smul_and_norm_le (E := E) (H := H) hs
  refine ⟨C, hC, fun {u v} hu hv f g hf hg ↦ ?_⟩
  obtain ⟨w, hw, hwn⟩ := h hu hv hf hg
  have hw' : (hu.smul_of_ae_eq hs hv hf hg).toBesselPotentialSpace = w :=
    BesselPotentialSpace.ext (by rw [MemSobolev.toBesselPotentialSpace_toDistr, hw])
  rwa [hw']

end TemperedDistribution
