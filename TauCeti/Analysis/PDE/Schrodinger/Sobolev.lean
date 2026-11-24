/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.PDE.Schrodinger.MixedNorm
public import TauCeti.Analysis.PDE.Schrodinger.TemperedDistribution
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion

/-!
# The Schrödinger equation with data in `H^s`

On a finite-dimensional real inner product space `E` of dimension `n`, let `S(t) = exp(itΔ)` be
the Schrödinger propagator and let `H^s = H^{s,2}(E, F)` be the Bessel-potential space of order
`s ∈ ℝ`: the tempered distributions `u` with `J^s u ∈ L²`, normed by `‖J^s u‖₂`, where `J^s` is
the Fourier multiplier with symbol `(1 + ‖ξ‖²)^(s/2)`. Since `S(t)` commutes with `J^s`
(`TemperedDistribution.besselPotential_schrodingerPropagator`), it maps `H^s` isometrically onto
itself, and under the isometry `J^s : H^s ≃ L²` it is the propagator on `L²`:

`J^s (S(t) u) = S(t) (J^s u)`.

This file bundles `S(t)` on `H^s` (`BesselPotentialSpace.schrodingerPropagator`) and Duhamel's
formula for the inhomogeneous equation `i ∂ₜu + Δu = G`, `u(0) = f`, with data `f ∈ H^s` and a
forcing term `G` with values in `H^s` (`BesselPotentialSpace.schrodingerDuhamel`). The isometry
carries this solution to the solution on `L²` with data `J^s f` and forcing `J^s G`
(`BesselPotentialSpace.toLp_schrodingerDuhamel`), so every estimate on `L²` holds at every
regularity `s`, with the same constant. In particular the Strichartz estimates hold for the
regularity-shifted solution `J^s u`: for a non-endpoint admissible pair `(q, r)`, that is
`2 < q < ∞` and `2 / q + n / r = n / 2` (in dimension one this includes `(4, ∞)`), and `p`, `r'`
the Hölder conjugates of `q`, `r`,

`‖J^s S(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖_{H^s}` and
`‖J^s u‖_{L^q([0, T]; L^r)} ≤ C (‖f‖_{H^s} + ‖J^s G‖_{L^p((0, T]; L^{r'})})`,

with `C` depending neither on `s` nor on `T`. The `Lʳ` norm of `J^s v` is the norm of `v` in the
Bessel-potential space `H^{s,r}`, so these estimates bound the solution in `L^q_t H^{s,r}_x`. For
`s = k` a natural number and `1 < r < ∞`, `H^{k,r}` is the Sobolev space `W^{k,r}` of functions
with `k` weak derivatives in `Lʳ` (`MeasureTheory.Lp.memSobolev_natCast_iff_exists_wkp_value_eq`).

## Main declarations

* `BesselPotentialSpace.schrodingerPropagator`: the propagator `S(t)` on `H^s`, with
  `BesselPotentialSpace.toLp_schrodingerPropagator` and
  `BesselPotentialSpace.toDistr_schrodingerPropagator` describing it through `J^s` and on
  tempered distributions.
* `BesselPotentialSpace.schrodingerDuhamel`: Duhamel's formula in `H^s`, with
  `BesselPotentialSpace.toLp_schrodingerDuhamel` identifying `J^s` of it with Duhamel's formula
  on `L²`.
* `BesselPotentialSpace.continuousOn_schrodingerDuhamel_Icc`,
  `BesselPotentialSpace.norm_schrodingerDuhamel_le`: the solution lies in `C([0, T]; H^s)`, with
  the energy estimate.
* `BesselPotentialSpace.exists_eLpNorm_eLpNorm_toLp_schrodingerPropagator_le`,
  `BesselPotentialSpace.exists_eLpNorm_eLpNorm_toLp_schrodingerDuhamel_le`: the homogeneous and
  inhomogeneous Strichartz estimates in `H^s`.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3.
-/

public section

noncomputable section

open MeasureTheory Set TemperedDistribution
open scoped ENNReal NNReal BesselPotentialSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {s : ℝ}

namespace BesselPotentialSpace

/-! ### The propagator on `H^s` -/

variable (F s) in
/-- **The Schrödinger propagator on `H^s`**: `S(t) = exp(itΔ)` restricted to the
Bessel-potential space `H^{s,2}(E, F)`, which it preserves
(`TemperedDistribution.MemSobolev.schrodingerPropagator`). On the underlying tempered
distributions it is `TemperedDistribution.schrodingerPropagator`
(`BesselPotentialSpace.toDistr_schrodingerPropagator`), and under the isometry `J^s : H^s ≃ L²`
it is the propagator on `L²` (`BesselPotentialSpace.toLp_schrodingerPropagator`). -/
def schrodingerPropagator (t : ℝ) : H^{s}(E, F) →L[ℂ] H^{s}(E, F) :=
  mapCLM (TemperedDistribution.schrodingerPropagator E F t) fun u ↦
    u.memSobolev_toDistr.schrodingerPropagator t

/-- On the underlying tempered distributions, the propagator on `H^s` is
`TemperedDistribution.schrodingerPropagator`. -/
@[simp]
theorem toDistr_schrodingerPropagator (t : ℝ) (u : H^{s}(E, F)) :
    (schrodingerPropagator F s t u).toDistr =
      TemperedDistribution.schrodingerPropagator E F t u.toDistr :=
  toDistr_mapCLM _ _ u

/-- **`J^s` intertwines the propagators** on `H^s` and on `L²`: `J^s (S(t) u) = S(t) (J^s u)`. -/
@[simp]
theorem toLp_schrodingerPropagator (t : ℝ) (u : H^{s}(E, F)) :
    (schrodingerPropagator F s t u).toLp = TauCeti.schrodingerPropagator F t u.toLp := by
  rw [← toLpₗᵢ_apply, ← (toLpₗᵢ E F s 2).eq_symm_apply]
  refine ext ?_
  rw [toDistr_schrodingerPropagator, toLpₗᵢ_symm_apply,
    ← schrodingerPropagator_toTemperedDistribution, besselPotential_schrodingerPropagator,
    besselPotential_neg_toLp_eq]

/-- The propagator on `H^s` is an isometry. -/
@[simp]
theorem norm_schrodingerPropagator_apply (t : ℝ) (u : H^{s}(E, F)) :
    ‖schrodingerPropagator F s t u‖ = ‖u‖ := by
  rw [← norm_toLp_eq, toLp_schrodingerPropagator,
    TauCeti.norm_phasePropagator_apply TauCeti.laplacianSymbol, norm_toLp_eq]

/-- At time `0` the propagator on `H^s` is the identity. -/
@[simp]
theorem schrodingerPropagator_zero_apply (u : H^{s}(E, F)) : schrodingerPropagator F s 0 u = u :=
  injective_toLp E F s 2 <| by
    simp [TauCeti.phasePropagator_zero]

/-- **The group law** `S(t₁ + t₂) = S(t₁) S(t₂)` on `H^s`. -/
theorem schrodingerPropagator_add_apply (t₁ t₂ : ℝ) (u : H^{s}(E, F)) :
    schrodingerPropagator F s (t₁ + t₂) u =
      schrodingerPropagator F s t₁ (schrodingerPropagator F s t₂ u) :=
  injective_toLp E F s 2 <| by
    simp [TauCeti.schrodingerPropagator_def, TauCeti.phasePropagator_add_apply]

/-- **Strong continuity**: `t ↦ S(t) u` is continuous with values in `H^s`. -/
theorem continuous_schrodingerPropagator_apply (u : H^{s}(E, F)) :
    Continuous fun t ↦ schrodingerPropagator F s t u := by
  refine (toLpₗᵢ E F s 2).comp_continuous_iff.1 ?_
  simpa [Function.comp_def] using
    TauCeti.continuous_phasePropagator_apply TauCeti.laplacianSymbol u.toLp

/-! ### Duhamel's formula in `H^s` -/

/-- **Duhamel's formula in `H^s`** for the inhomogeneous Schrödinger equation
`i ∂ₜu + Δu = G`, `u(0) = f`: `u(t) = S(t) f - i ∫_0^t S(t - τ) G(τ) dτ`, with `S(t)` the
propagator on `H^s` and the integral oriented and taken in `H^s`. -/
def schrodingerDuhamel (f : H^{s}(E, F)) (G : ℝ → H^{s}(E, F)) (t : ℝ) : H^{s}(E, F) :=
  schrodingerPropagator F s t f -
    Complex.I • ∫ τ in (0 : ℝ)..t, schrodingerPropagator F s (t - τ) (G τ)

/-- Unfold Duhamel's formula in `H^s`. -/
theorem schrodingerDuhamel_def (f : H^{s}(E, F)) (G : ℝ → H^{s}(E, F)) (t : ℝ) :
    schrodingerDuhamel f G t = schrodingerPropagator F s t f -
      Complex.I • ∫ τ in (0 : ℝ)..t, schrodingerPropagator F s (t - τ) (G τ) :=
  (rfl)

/-- **`J^s` of the solution in `H^s` is the solution in `L²`** with data `J^s f` and forcing
`J^s G`. -/
@[simp]
theorem toLp_schrodingerDuhamel (f : H^{s}(E, F)) (G : ℝ → H^{s}(E, F)) (t : ℝ) :
    (schrodingerDuhamel f G t).toLp =
      TauCeti.schrodingerDuhamel f.toLp (fun τ ↦ (G τ).toLp) t := by
  simp [schrodingerDuhamel_def, TauCeti.schrodingerDuhamel_def, toLp_intervalIntegral]

/-- Duhamel's formula in `H^s` takes the initial value `f` at time `0`. -/
@[simp]
theorem schrodingerDuhamel_apply_zero (f : H^{s}(E, F)) (G : ℝ → H^{s}(E, F)) :
    schrodingerDuhamel f G 0 = f :=
  injective_toLp E F s 2 <| by simp

/-- Without forcing, Duhamel's formula in `H^s` is the free evolution `S(t) f`. -/
@[simp]
theorem schrodingerDuhamel_zero_right (f : H^{s}(E, F)) (t : ℝ) :
    schrodingerDuhamel f 0 t = schrodingerPropagator F s t f := by
  simp [schrodingerDuhamel_def]

/-- Duhamel's formula is continuous on `[0, T]`, with values in `H^s`, for a forcing term
integrable on `(0, T]` with values in `H^s`. -/
theorem continuousOn_schrodingerDuhamel_Icc (f : H^{s}(E, F)) {G : ℝ → H^{s}(E, F)} {T : ℝ}
    (hG : IntegrableOn G (Ioc 0 T)) : ContinuousOn (schrodingerDuhamel f G) (Icc 0 T) := by
  have hG' : IntegrableOn (fun τ ↦ (G τ).toLp) (Ioc 0 T) := integrable_toLp_iff.2 hG
  refine (toLpₗᵢ E F s 2).comp_continuousOn_iff.1 ?_
  simpa [Function.comp_def] using TauCeti.continuousOn_schrodingerDuhamel_Icc f.toLp hG'

/-- **The energy estimate in `H^s`**: `‖u(t)‖_{H^s} ≤ ‖f‖_{H^s} + ∫_{Ι(0,t)} ‖G(τ)‖_{H^s} dτ` at
every time `t`, where `Ι(0,t)` is `(0, t]` for `t ≥ 0` and `(t, 0]` for `t ≤ 0`. -/
theorem norm_schrodingerDuhamel_le (f : H^{s}(E, F)) (G : ℝ → H^{s}(E, F)) (t : ℝ) :
    ‖schrodingerDuhamel f G t‖ ≤ ‖f‖ + ∫ τ in uIoc 0 t, ‖G τ‖ := by
  simpa only [← norm_toLp_eq, toLp_schrodingerDuhamel] using
    TauCeti.norm_schrodingerDuhamel_le f.toLp (fun τ ↦ (G τ).toLp) t

/-! ### Strichartz estimates in `H^s` -/

variable {p q : ℝ≥0} {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- **The Strichartz estimate in `H^s`**, at a non-endpoint admissible pair:
`2 < q < ∞` and `2 / q + n / r = n / 2`, with `p` the Hölder conjugate of `q`. There
is `C` such that for every order `s` and every `f ∈ H^s(E)`,

`‖J^s S(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖_{H^s}`.

The constant does not depend on `s`. -/
theorem exists_eLpNorm_eLpNorm_toLp_schrodingerPropagator_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ (s : ℝ) (f : H^{s}(E)),
      eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator ℂ s t f).toLp r volume) q volume ≤
        C * ‖f‖ₑ := by
  obtain ⟨C, hC⟩ := TauCeti.exists_eLpNorm_eLpNorm_schrodingerPropagator_le hq hpq hqr
  refine ⟨C, fun s f ↦ ?_⟩
  simpa only [toLp_schrodingerPropagator, enorm_toLp_eq] using hC f.toLp

/-- **The Strichartz estimate for the inhomogeneous Schrödinger equation in `H^s`**, at a
non-endpoint admissible pair: `2 < q < ∞` and `2 / q + n / r = n / 2`,
with `p` and `r'` the Hölder conjugates of `q` and `r`. There is `C` such that for every order `s`,
every `T`, every initial value `f ∈ H^s(E)` and every forcing term `G : ℝ → H^s(E)` integrable on
`(0, T]`, the solution `u = BesselPotentialSpace.schrodingerDuhamel f G` satisfies

`‖J^s u‖_{L^q([0, T]; L^r)} ≤ C (‖f‖_{H^s} + ‖J^s G‖_{L^p((0, T]; L^{r'})})`.

The constant depends neither on `s` nor on `T`. -/
theorem exists_eLpNorm_eLpNorm_toLp_schrodingerDuhamel_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ (s : ℝ) (f : H^{s}(E)) (G : ℝ → H^{s}(E)) (T : ℝ), IntegrableOn G (Ioc 0 T) →
      eLpNorm (fun t ↦ eLpNorm (schrodingerDuhamel f G t).toLp r volume) q
          (volume.restrict (Icc 0 T)) ≤
        C * (‖f‖ₑ + eLpNorm (fun τ ↦ eLpNorm (G τ).toLp r' volume) p
          (volume.restrict (Ioc 0 T))) := by
  obtain ⟨C, hC⟩ :=
    TauCeti.exists_eLpNorm_eLpNorm_schrodingerDuhamel_le (r₁' := r') hq hpq hqr hq hpq hqr
  refine ⟨C, fun s f G T hG ↦ ?_⟩
  have hG' : IntegrableOn (fun τ ↦ (G τ).toLp) (Ioc 0 T) := integrable_toLp_iff.2 hG
  simpa only [toLp_schrodingerDuhamel, enorm_toLp_eq] using hC f.toLp (fun τ ↦ (G τ).toLp) T hG'

end BesselPotentialSpace
