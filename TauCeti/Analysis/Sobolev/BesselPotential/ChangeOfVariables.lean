/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.BesselPotential.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Extension
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Calculus.IteratedFDeriv.OrthonormalBasis
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Coordinates
import TauCeti.Analysis.Sobolev.BesselPotential.Adjoint
import TauCeti.Analysis.Sobolev.BesselPotential.ComplexInterpolation
import TauCeti.Analysis.Sobolev.BesselPotential.MatrixMultiplier
import TauCeti.Analysis.Sobolev.BesselPotential.OrderInterpolation
import TauCeti.Analysis.Sobolev.BesselPotential.SmoothMultiplier
import TauCeti.MeasureTheory.Function.Jacobian
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.CastMeasure

/-!
# Changes of variables in Bessel-potential spaces

## Integer orders, `1 < p < ∞`

For `1 < p < ∞` and a natural order `k`, the real Bessel-potential functions
`TemperedDistribution.realSobolevFunctions E k p` are preserved by precomposition with a change of
variables of order `k` of the whole space (`TauCeti.Wkp.IsChangeOfVariables`): a `Cᵏ`
injective map with bounded derivatives of orders `1` through `k` and Jacobian determinant bounded
away from zero. In particular they are invariant under translations and under linear
automorphisms of `E`. The proof passes through the weak-derivative Sobolev space `W^{k,p}(E)`,
which has the same real elements by Calderón's theorem
(`MeasureTheory.Lp.memSobolev_natCast_iff_exists_wkp_value_eq`), and on which precomposition is
the bounded operator `TauCeti.Wkp.compL`.

## Pullback of distributions at every real order, `1 < p < ∞`

For tempered distributions with values in a complex Hilbert space and every real order `s`,
positive or negative, the pullback `Φ^*` (`TemperedDistribution.compCLM`) along a bijection `Φ`
such that `Φ` and `Φ⁻¹` have temperate growth and bounded derivatives of orders `1` to
`⌈|s|⌉ + 1` preserves `H^{s,p}`, and restricts to an isomorphism of `H^{s,p}` with inverse the
pullback along `Φ⁻¹`.
These are the coordinate changes that make the Sobolev norms of sections of a vector bundle
independent of the chart. The integer orders `k` come first. Each step of the proof is an
induction on `k`, starting from `H^{0,p} = Lᵖ`, which `Φ^*` preserves because the Jacobian of `Φ`
is bounded below in terms of `DΦ⁻¹`
(`TemperedDistribution.exists_compCLM_toTemperedDistribution_eq_and_norm_le`).

* Going up, a distribution lies in `H^{k+1,p}` exactly when it lies in `Lᵖ` and its directional
  derivatives lie in `H^{k,p}` (`TemperedDistribution.memSobolev_natCast_add_one_iff`). By the
  chain rule `∂_v (Φ^* T) = ∑ᵢ cᵢ Φ^* (∂_{bᵢ} T)` (`TemperedDistribution.lineDerivOp_compCLM`),
  where `DΦ(x) v = ∑ᵢ cᵢ(x) bᵢ`, and the coefficients `cᵢ` multiply `H^{k,p}` into itself
  (`TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le`).
* Going down, a distribution lies in `H^{-k-1,p}` exactly when it is `u + ∑ᵢ ∂ᵢ wᵢ` with `u` and
  `wᵢ` in `H^{-k,p}` (`TemperedDistribution.memSobolev_sub_one_iff`). The chain rule for `Φ⁻¹`
  gives `Φ^* (∂ᵢ wᵢ) = ∑ⱼ cᵢⱼ ∂ⱼ (Φ^* wᵢ)` (`TemperedDistribution.compCLM_lineDerivOp`), where
  `DΦ⁻¹(Φ x) bᵢ = ∑ⱼ cᵢⱼ(x) bⱼ`, and the Leibniz rule
  `cᵢⱼ ∂ⱼ (Φ^* wᵢ) = ∂ⱼ (cᵢⱼ Φ^* wᵢ) - (∂ⱼ cᵢⱼ) Φ^* wᵢ` puts `Φ^* T` in the same form
  (`TemperedDistribution.compCLM_lineDerivOp_eq_sum_sub`).

A real order `s` that is not an integer lies between `⌊s⌋` and `⌊s⌋ + 1`, and `H^{s,p}` is the
complex interpolation space `[H^{⌊s⌋,p}, H^{⌊s⌋+1,p}]_θ` with `θ = s - ⌊s⌋`
(`TauCeti.CompatibleCouple.besselPotentialSpaceComplexMethodContinuousLinearEquiv`). A continuous
linear map of tempered distributions preserving both endpoint spaces therefore preserves
`H^{s,p}` (`TemperedDistribution.MemSobolev.map_of_memSobolev_of_memSobolev`).

## Every real order, `p = 2`

Let `φ` be a bijection of `E` such that `φ` and `φ⁻¹` have temperate growth and bounded
derivatives of every positive order, for instance an affine automorphism. The pullback of tempered
distributions `TemperedDistribution.compCLM` along `φ` preserves the Hilbert-space-valued
Bessel-potential space `H^s = H^{s,2}` for every real `s`, negative orders included
(`TemperedDistribution.MemSobolev.compCLM`, the case `p = 2` of the above), and restricts to a
continuous linear automorphism of `H^s` with inverse the pullback along `φ⁻¹`
(`BesselPotentialSpace.compEquiv`). This is the whole-space coordinate-change estimate behind the
localization of the Sobolev scale to charts.

On the Hilbert scale the bound `‖u ∘ φ‖_{H^s} ≤ C ‖u‖_{H^s}` on Schwartz functions
(`SchwartzMap.hasSobolevExtension_compCLM`) also has a direct proof, in three steps.

* **Nonnegative integer orders**, by induction. At order `0` it is the `L²` bound for precomposition
  with a map whose Jacobian determinant is bounded away from zero
  (`TemperedDistribution.exists_compCLM_toTemperedDistribution_eq_and_norm_le`). Raising the order
  by one adds the first derivatives,
  `‖v‖²_{H^{k+1}} = ‖v‖²_{H^k} + (2π)⁻² ∑ᵢ ‖∂ᵢ v‖²_{H^k}`
  (`SchwartzMap.norm_toBesselPotentialSpaceCLM_add_one_sq`), and by the chain rule
  `∂ᵢ (u ∘ φ) = ∑ⱼ cᵢⱼ (∂ⱼ u) ∘ φ`, where `Dφ bᵢ = ∑ⱼ cᵢⱼ bⱼ`
  (`SchwartzMap.lineDerivOp_compCLM_apply`), whose coefficients are bounded multipliers on `H^k`
  (`SchwartzMap.hasSobolevExtension_smulLeftCLM`).
* **Negative integer orders**, by duality. For the `L²` pairing the transpose of `u ↦ u ∘ φ` is the
  pushforward of densities `φ_* v = |det Dφ⁻¹| (v ∘ φ⁻¹)` (`SchwartzMap.integral_inner_compCLM_eq`),
  which is bounded on `H^k` by the previous step applied to `φ⁻¹` and the multiplier bound for the
  Jacobian factor. A transpose of an operator bounded on `H^k` is bounded on `H^{-k}` with the same
  constant (`SchwartzMap.norm_toBesselPotentialSpaceCLM_le_of_integral_inner_eq`).
* **Real orders**, by complex interpolation of the Hilbert scale between `⌊s⌋` and `⌊s⌋ + 1`
  (`SchwartzMap.HasSobolevExtension.interpolate`).

## Main results

* `TemperedDistribution.comp_mem_realSobolevFunctions_natCast`: precomposition with a change of
  variables of order `k` preserves the real elements of `H^{k,p}`.
* `TemperedDistribution.comp_add_mem_realSobolevFunctions_natCast`: translations.
* `TemperedDistribution.comp_continuousLinearEquiv_mem_realSobolevFunctions_natCast`: linear
  automorphisms.
* `TemperedDistribution.MemSobolev.compCLM_of_norm_fderiv_symm_le`: the pullback preserves
  `H^{0,p} = Lᵖ`, for `1 ≤ p ≤ ∞`.
* `TemperedDistribution.MemSobolev.compCLM_of_norm_iteratedFDeriv_le`,
  `TemperedDistribution.MemSobolev.compCLM_of_norm_iteratedFDeriv_le_neg` and
  `TemperedDistribution.MemSobolev.compCLM_of_norm_iteratedFDeriv_le_intCast`: the pullback
  preserves `H^{k,p}`, `H^{-k,p}` and `H^{k,p}` for `k ∈ ℤ`, for `1 < p < ∞`.
* `TemperedDistribution.MemSobolev.compCLM_of_norm_iteratedFDeriv_le_real`: the pullback preserves
  `H^{s,p}` for every real `s`, for `1 < p < ∞`.
* `BesselPotentialSpace.compCLE`: the pullback as an isomorphism of `H^{s,p}`, `s ∈ ℝ`, with
  inverse the pullback along `Φ⁻¹` (`BesselPotentialSpace.compCLE_symm`); on Schwartz functions it
  is composition with `Φ` (`BesselPotentialSpace.compCLE_toBesselPotentialSpaceCLM`).
* `TemperedDistribution.MemSobolev.compCLM`: the pullback preserves `H^s`.
* `BesselPotentialSpace.compCLM`, `BesselPotentialSpace.compEquiv`: the pullback as a bounded
  operator and as a continuous linear automorphism of `H^s`.
* `SchwartzMap.hasSobolevExtension_compCLM`: composition with `φ` on Schwartz functions extends to
  `H^s → H^s`, in the form `SchwartzMap.HasSobolevExtension` used for composing Sobolev estimates.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1
  (invariance of `H^s` under diffeomorphisms, via integer orders, duality and interpolation).
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Springer, 1976, §§4.1, 6.4.
-/

public section

noncomputable section

namespace TemperedDistribution

open MeasureTheory TauCeti TopologicalSpace
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Changes of variables in `H^{k,p}`.** For `1 < p < ∞` and a natural order `k`, precomposition
with a change of variables of order `k` of the whole space preserves the real Bessel-potential
functions of order `k`. -/
theorem comp_mem_realSobolevFunctions_natCast (hp : 1 < p) (hp_top : p ≠ ∞) {k : ℕ}
    {Φ : E → E} {L c : ℝ} (hΦ : Wkp.IsChangeOfVariables k ⊤ ⊤ Φ L c) {f : E → ℝ}
    (hf : f ∈ realSobolevFunctions E k p) :
    (fun x ↦ f (Φ x)) ∈ realSobolevFunctions E k p := by
  obtain ⟨u, huf, hu⟩ := mem_realSobolevFunctions.1 hf
  have hvolume : (volume : Measure E) = volume.restrict ((⊤ : Opens E) : Set E) := by simp
  -- Pass to `W^{k,p}`, precompose there with `Φ`, and return to `H^{k,p}`.
  obtain ⟨w, hw⟩ := (Lp.memSobolev_natCast_iff_exists_wkp_value_eq hp hp_top k u).1 hu
  set w' := Wkp.compL (mu := volume) hΦ w
  set u' : Lp ℝ p (volume : Measure E) := castLpₗᵢ (𝕜 := ℝ) hvolume.symm (Wkp.value k w')
  have hu' : (u' : E → ℝ) = Wkp.value k w' := funext (coeFn_castLpₗᵢ hvolume.symm _)
  refine mem_realSobolevFunctions.2 ⟨u', ?_,
    (Lp.memSobolev_natCast_iff_exists_wkp_value_eq hp hp_top k u').2
      ⟨w', .of_forall fun x ↦ by rw [hu']⟩⟩
  have hae := Measure.ae_restrict_coe_opens_top (volume : Measure E)
  have hcomp := Wkp.value_compL_ae (mu := volume) hΦ w
  have hpull := hΦ.ae_comp (mu := volume) (P := fun y ↦ Wkp.value k w y = f y) <| by
    rw [hae]
    filter_upwards [hw, huf] with y h₁ h₂
    rw [h₁, h₂]
  rw [Filter.EventuallyEq, hae] at hcomp
  rw [hae] at hpull
  filter_upwards [hcomp, hpull] with x h₁ h₂
  rw [hu', h₁, h₂]

/-- For `1 < p < ∞` and a natural order `k`, the real Bessel-potential functions of order `k` are
invariant under translation. -/
theorem comp_add_mem_realSobolevFunctions_natCast (hp : 1 < p) (hp_top : p ≠ ∞) {k : ℕ}
    (a : E) {f : E → ℝ} (hf : f ∈ realSobolevFunctions E k p) :
    (fun x ↦ f (x + a)) ∈ realSobolevFunctions E k p :=
  comp_mem_realSobolevFunctions_natCast hp hp_top
    (Wkp.IsChangeOfVariables.add_const a (Set.mapsTo_univ _ _)) hf

/-- For `1 < p < ∞` and a natural order `k`, the real Bessel-potential functions of order `k` are
invariant under linear automorphisms of `E`. -/
theorem comp_continuousLinearEquiv_mem_realSobolevFunctions_natCast (hp : 1 < p)
    (hp_top : p ≠ ∞) {k : ℕ} (e : E ≃L[ℝ] E) {f : E → ℝ}
    (hf : f ∈ realSobolevFunctions E k p) :
    (fun x ↦ f (e x)) ∈ realSobolevFunctions E k p :=
  comp_mem_realSobolevFunctions_natCast hp hp_top
    (Wkp.IsChangeOfVariables.continuousLinearEquiv e (Set.mapsTo_univ _ _)) hf

/-! ### Pullback of tempered distributions in `H^{k,p}`, `k ∈ ℤ` -/

section Pullback

open scoped SchwartzMap LineDeriv

variable {F : Type*} [NormedAddCommGroup F]

section NormedSpace

variable [NormedSpace ℂ F] [CompleteSpace F]

/-- **Pullback on `H^{0,p} = Lᵖ`.** If `Φ` is a bijection such that `Φ` and `Φ⁻¹` have temperate
growth and `DΦ⁻¹` is bounded, then `Φ^* T ∈ H^{0,p}` for every `T ∈ H^{0,p}`, for every
`1 ≤ p ≤ ∞`. -/
theorem MemSobolev.compCLM_of_norm_fderiv_symm_le {Φ : E ≃ E}
    (hΦ : (Φ : E → E).HasTemperateGrowth) (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
    (hΨb : ∃ C, ∀ x, ‖fderiv ℝ Φ.symm x‖ ≤ C) {T : 𝓢'(E, F)} (hT : MemSobolev 0 p T) :
    MemSobolev 0 p (compCLM F Φ hΦ hΨ T) := by
  obtain ⟨f, rfl⟩ := memSobolev_zero_iff.1 hT
  obtain ⟨C, hC⟩ := hΨb
  -- The Jacobian of `Φ` is bounded below in terms of the bound for `DΦ⁻¹`.
  have hdet (x : E) : (max 1 C ^ Module.finrank ℝ E)⁻¹ ≤ |(fderiv ℝ Φ x).det| :=
    Φ.inv_pow_le_abs_det_fderiv (hΦ.1.differentiable (by simp) x)
      (hΨ.1.differentiable (by simp) _) ((hC _).trans (le_max_right 1 C))
  obtain ⟨v, hv, -⟩ := exists_compCLM_toTemperedDistribution_eq_and_norm_le volume hΦ hΨ
    (by positivity) hdet f
  exact memSobolev_zero_iff.2 ⟨v, hv⟩

end NormedSpace

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Pullback on `H^{k,p}`.** Let `1 < p < ∞` and let `Φ` be a bijection such that `Φ` and
`Φ⁻¹` have temperate growth, the derivatives of `Φ` of orders `1` to `k` are bounded and `DΦ⁻¹`
is bounded. Then `Φ^* T ∈ H^{k,p}` for every `T ∈ H^{k,p}`. -/
theorem MemSobolev.compCLM_of_norm_iteratedFDeriv_le (hp : 1 < p) (hp_top : p ≠ ∞) {k : ℕ}
    {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth) (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
    (hΦb : ∀ n, 1 ≤ n → n ≤ k → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∃ C, ∀ x, ‖fderiv ℝ Φ.symm x‖ ≤ C) {T : 𝓢'(E, F)} (hT : MemSobolev k p T) :
    MemSobolev k p (compCLM F Φ hΦ hΨ T) := by
  induction k generalizing T with
  | zero =>
    rw [Nat.cast_zero] at hT ⊢
    exact hT.compCLM_of_norm_fderiv_symm_le hΦ hΨ hΨb
  | succ k ih =>
    rw [Nat.cast_succ] at hT ⊢
    have hT' := (memSobolev_natCast_add_one_iff hp hp_top).1 hT
    refine (memSobolev_natCast_add_one_iff hp hp_top).2
      ⟨hT'.1.compCLM_of_norm_fderiv_symm_le hΦ hΨ hΨb, fun v ↦ ?_⟩
    -- By the chain rule `∂_v (Φ^* T) = ∑ᵢ cᵢ Φ^* (∂_{bᵢ} T)`, where `DΦ(x) v = ∑ᵢ cᵢ(x) bᵢ` and
    -- the coefficients `cᵢ` have bounded derivatives up to order `k`.
    set b := stdOrthonormalBasis ℝ E
    rw [lineDerivOp_compCLM b.toBasis hΦ hΨ]
    refine MemSobolev.sum fun i _ ↦ ?_
    have hc : ∀ n ≤ k, ∃ C, ∀ x,
        ‖iteratedFDeriv ℝ n (fun x ↦ ((b.toBasis.repr (fderiv ℝ Φ x v) i : ℝ) : ℂ)) x‖ ≤ C := by
      obtain ⟨L, hL⟩ := exists_forall_norm_iteratedFDeriv_le_of_forall_one_le hΦb
      obtain ⟨A, -, hAy⟩ := b.exists_clm_norm_le_one_and_repr_eq i
      simp only [hAy]
      exact fun n hn ↦ ⟨_, hΦ.1.norm_iteratedFDeriv_clm_fderiv_apply_le (by simp) A hL v n hn⟩
    exact MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le hp hp_top
      (hΦ.basis_repr_fderiv_apply b.toBasis v i) hc
      (ih (fun n h₁ h₂ ↦ hΦb n h₁ (by omega)) (by simpa using hT'.2 (b i)))

/-- **Pullback on `H^{-k,p}`.** Let `1 < p < ∞` and let `Φ` be a bijection such that `Φ` and
`Φ⁻¹` have temperate growth, the derivatives of `Φ` of orders `1` to `k` are bounded and those of
`Φ⁻¹` of orders `1` to `k + 1` are bounded. Then `Φ^* T ∈ H^{-k,p}` for every `T ∈ H^{-k,p}`. -/
theorem MemSobolev.compCLM_of_norm_iteratedFDeriv_le_neg (hp : 1 < p) (hp_top : p ≠ ∞) {k : ℕ}
    {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth) (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
    (hΦb : ∀ n, 1 ≤ n → n ≤ k → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∀ n, 1 ≤ n → n ≤ k + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C)
    {T : 𝓢'(E, F)} (hT : MemSobolev (-k) p T) : MemSobolev (-k) p (compCLM F Φ hΦ hΨ T) := by
  induction k generalizing T with
  | zero =>
    rw [Nat.cast_zero, neg_zero] at hT ⊢
    obtain ⟨C, hC⟩ := hΨb 1 le_rfl le_rfl
    exact hT.compCLM_of_norm_fderiv_symm_le hΦ hΨ ⟨C, fun x ↦ by simpa using hC x⟩
  | succ k ih =>
    have hk : -((k + 1 : ℕ) : ℝ) = -k - 1 := by push_cast; ring
    rw [hk] at hT ⊢
    set b := stdOrthonormalBasis ℝ E
    have ih' {T : 𝓢'(E, F)} (hT : MemSobolev (-k) p T) :
        MemSobolev (-k) p (compCLM F Φ hΦ hΨ T) :=
      ih (fun n h₁ h₂ ↦ hΦb n h₁ (by omega)) (fun n h₁ h₂ ↦ hΨb n h₁ (by omega)) hT
    -- The coefficients `cᵢⱼ` of `DΦ⁻¹(Φ x) bᵢ` in `b` have bounded derivatives to order `k + 1`.
    have hct (v : E) (j : Fin (Module.finrank ℝ E)) :
        (fun x ↦ ((b.toBasis.repr (fderiv ℝ Φ.symm (Φ x) v) j : ℝ) : ℂ)).HasTemperateGrowth :=
      (hΨ.basis_repr_fderiv_apply b.toBasis v j).comp hΦ
    have hcb (v : E) (j : Fin (Module.finrank ℝ E)) : ∀ n ≤ k + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n
        (fun x ↦ ((b.toBasis.repr (fderiv ℝ Φ.symm (Φ x) v) j : ℝ) : ℂ)) x‖ ≤ C := by
      obtain ⟨K, hK⟩ := exists_forall_norm_iteratedFDeriv_le_of_forall_one_le hΦb
      obtain ⟨L, hL⟩ := exists_forall_norm_iteratedFDeriv_le_of_forall_one_le hΨb
      obtain ⟨A, -, hAy⟩ := b.exists_clm_norm_le_one_and_repr_eq j
      simp only [hAy]
      exact fun n hn ↦ ⟨_, hΨ.1.norm_iteratedFDeriv_clm_fderiv_comp_apply_le hΦ.1 (by simp) A hK hL
        v n hn⟩
    -- Write `T = u + ∑ᵢ ∂ᵢ wᵢ` with `u` and `wᵢ` in `H^{-k,p}`. By the chain rule
    -- `Φ^* (∂ᵢ wᵢ) = ∑ⱼ cᵢⱼ ∂ⱼ (Φ^* wᵢ) = ∑ⱼ (∂ⱼ (cᵢⱼ Φ^* wᵢ) - (∂ⱼ cᵢⱼ) Φ^* wᵢ)`, so `Φ^* T` is
    -- again of this form.
    obtain ⟨u, w, hu, hw, rfl⟩ := (memSobolev_sub_one_iff hp hp_top b).1 hT
    refine (memSobolev_sub_one_iff hp hp_top b).2
      ⟨compCLM F Φ hΦ hΨ u - ∑ j, ∑ i, smulLeftCLM F
          (fun x ↦ fderiv ℝ (fun y ↦ ((b.toBasis.repr (fderiv ℝ Φ.symm (Φ y) (b i)) j : ℝ) : ℂ))
            x (b j)) (compCLM F Φ hΦ hΨ (w i)),
        fun j ↦ ∑ i, smulLeftCLM F
          (fun x ↦ ((b.toBasis.repr (fderiv ℝ Φ.symm (Φ x) (b i)) j : ℝ) : ℂ))
          (compCLM F Φ hΦ hΨ (w i)), ?_, fun j ↦ ?_, ?_⟩
    · exact (ih' hu).sub (MemSobolev.sum fun j _ ↦ MemSobolev.sum fun i _ ↦
        MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le_neg hp hp_top ((hct _ _).fderiv_apply _)
          ((hct _ _).1.exists_bound_iteratedFDeriv_fderiv_apply (by simp) (hcb _ _) _)
          (ih' (hw i)))
    · exact MemSobolev.sum fun i _ ↦ MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le_neg hp hp_top
        (hct _ _) (fun n hn ↦ hcb _ _ n (by omega)) (ih' (hw i))
    · simp only [map_add, map_sum, compCLM_lineDerivOp_eq_sum_sub b.toBasis hΦ hΨ,
        OrthonormalBasis.coe_toBasis, LineDeriv.lineDerivOp_sum]
      conv_lhs => rw [Finset.sum_comm]
      simp only [Finset.sum_sub_distrib]
      abel

/-- **Pullback on `H^{k,p}` for every integer `k`.** Let `1 < p < ∞` and let `Φ` be a bijection
such that `Φ` and `Φ⁻¹` have temperate growth, the derivatives of `Φ` of orders `1` to `|k|` are
bounded and those of `Φ⁻¹` of orders `1` to `|k| + 1` are bounded. Then `Φ^* T ∈ H^{k,p}` for
every `T ∈ H^{k,p}`. -/
theorem MemSobolev.compCLM_of_norm_iteratedFDeriv_le_intCast (hp : 1 < p) (hp_top : p ≠ ∞)
    {k : ℤ} {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
    (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
    (hΦb : ∀ n, 1 ≤ n → n ≤ k.natAbs → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∀ n, 1 ≤ n → n ≤ k.natAbs + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C)
    {T : 𝓢'(E, F)} (hT : MemSobolev k p T) : MemSobolev k p (compCLM F Φ hΦ hΨ T) := by
  obtain ⟨k, rfl | rfl⟩ := k.eq_nat_or_neg
  · obtain ⟨C, hC⟩ := hΨb 1 le_rfl (by omega)
    exact_mod_cast hT.compCLM_of_norm_iteratedFDeriv_le hp hp_top hΦ hΨ (by simpa using hΦb)
      ⟨C, fun x ↦ by simpa using hC x⟩
  · push_cast at hT ⊢
    exact hT.compCLM_of_norm_iteratedFDeriv_le_neg hp hp_top hΦ hΨ (by simpa using hΦb)
      (by simpa using hΨb)

/-- For a real number `s` that is not an integer, the integer orders `⌊s⌋` and `⌊s⌋ + 1` between
which `s` lies have absolute values at most `⌈|s|⌉`. -/
private theorem natAbs_floor_le_natCeil_abs {s : ℝ} (hs : Int.fract s ≠ 0) :
    (⌊s⌋).natAbs ≤ ⌈|s|⌉₊ ∧ (⌊s⌋ + 1).natAbs ≤ ⌈|s|⌉₊ := by
  have h₁ := Int.floor_le s
  have h₂ := Int.lt_floor_add_one s
  have h₃ : (⌊s⌋ : ℝ) ≠ s := fun h ↦ hs (by rw [Int.fract, h, sub_self])
  have h₄ := Nat.le_ceil |s|
  have h₅ := Nat.ceil_lt_add_one (abs_nonneg s)
  rcases le_or_gt 0 s with h | h
  · rw [abs_of_nonneg h] at h₄ h₅ ⊢
    have h₆ : ⌊s⌋ < (⌈s⌉₊ : ℤ) := by
      exact_mod_cast lt_of_lt_of_le (lt_of_le_of_ne h₁ h₃) h₄
    have h₇ : 0 ≤ ⌊s⌋ := Int.floor_nonneg.2 h
    omega
  · rw [abs_of_neg h] at h₄ h₅ ⊢
    have h₆ : -⌊s⌋ - 1 < (⌈-s⌉₊ : ℤ) := by
      have : -(⌊s⌋ : ℝ) - 1 < ⌈-s⌉₊ := by linarith
      exact_mod_cast this
    have h₇ : (⌈-s⌉₊ : ℤ) < -⌊s⌋ + 1 := by
      have : (⌈-s⌉₊ : ℝ) < -⌊s⌋ + 1 := by linarith
      exact_mod_cast this
    have h₈ : ⌊s⌋ < 0 := Int.floor_lt.2 (by simpa using h)
    omega

/-- **Pullback on `H^{s,p}` for every real `s`.** Let `1 < p < ∞` and let `Φ` be a bijection such
that `Φ` and `Φ⁻¹` have temperate growth, the derivatives of `Φ` of orders `1` to `⌈|s|⌉` are
bounded and those of `Φ⁻¹` of orders `1` to `⌈|s|⌉ + 1` are bounded. Then `Φ^* T ∈ H^{s,p}` for
every `T ∈ H^{s,p}`. -/
theorem MemSobolev.compCLM_of_norm_iteratedFDeriv_le_real (hp : 1 < p) (hp_top : p ≠ ∞)
    {s : ℝ} {Φ : E ≃ E} (hΦ : (Φ : E → E).HasTemperateGrowth)
    (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
    (hΦb : ∀ n, 1 ≤ n → n ≤ ⌈|s|⌉₊ → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∀ n, 1 ≤ n → n ≤ ⌈|s|⌉₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C)
    {T : 𝓢'(E, F)} (hT : MemSobolev s p T) : MemSobolev s p (compCLM F Φ hΦ hΨ T) := by
  rcases eq_or_ne (Int.fract s) 0 with hs | hs
  · -- An integer order `s = ⌊s⌋`, for which `⌈|s|⌉ = |⌊s⌋|`.
    have hk : (⌊s⌋ : ℝ) = s := (sub_eq_zero.1 ((Int.self_sub_floor s).trans hs)).symm
    have hc : ⌈|((⌊s⌋ : ℤ) : ℝ)|⌉₊ = (⌊s⌋).natAbs := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast, Nat.ceil_natCast]
    rw [hk] at hc
    rw [← hk] at hT ⊢
    exact hT.compCLM_of_norm_iteratedFDeriv_le_intCast hp hp_top hΦ hΨ (hc ▸ hΦb) (hc ▸ hΨb)
  -- Otherwise interpolate between the integer orders `⌊s⌋` and `⌊s⌋ + 1`.
  obtain ⟨h₀, h₁⟩ := natAbs_floor_le_natCeil_abs hs
  have hθ : s = (1 - Int.fract s) * ((⌊s⌋ : ℤ) : ℝ) + Int.fract s * ((⌊s⌋ + 1 : ℤ) : ℝ) := by
    rw [← Int.self_sub_floor]
    push_cast
    ring
  have hθ' : Int.fract s ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨(Int.fract_nonneg s).lt_of_ne' hs, Int.fract_lt_one s⟩
  have hp' :
      p⁻¹ = ENNReal.ofReal (1 - Int.fract s) * p⁻¹ + ENNReal.ofReal (Int.fract s) * p⁻¹ := by
    rw [← add_mul, ← ENNReal.ofReal_add (by linarith [hθ'.2]) hθ'.1.le, sub_add_cancel,
      ENNReal.ofReal_one, one_mul]
  rw [hθ] at hT ⊢
  exact MemSobolev.map_of_memSobolev_of_memSobolev hp hp_top hp hp_top hθ' hp' _
    (fun _ hu ↦ hu.compCLM_of_norm_iteratedFDeriv_le_intCast hp hp_top hΦ hΨ
      (fun n hn₁ hn₂ ↦ hΦb n hn₁ (hn₂.trans h₀)) (fun n hn₁ hn₂ ↦ hΨb n hn₁ (by omega)))
    (fun _ hu ↦ hu.compCLM_of_norm_iteratedFDeriv_le_intCast hp hp_top hΦ hΨ
      (fun n hn₁ hn₂ ↦ hΦb n hn₁ (hn₂.trans h₁)) (fun n hn₁ hn₂ ↦ hΨb n hn₁ (by omega))) hT

end Pullback

end TemperedDistribution

namespace SchwartzMap

open MeasureTheory TemperedDistribution
open scoped BesselPotentialSpace InnerProductSpace LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] {φ : E ≃ E}

/-- The coefficients `x ↦ (b.repr (Dg(x) v))ⱼ` of the chain rule for composition with `g` are
bounded multipliers on `H^k` when the derivatives of `g` of positive order are bounded. -/
private theorem exists_norm_toBesselPotentialSpaceCLM_smulLeftCLM_repr_fderiv_le {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ E) {g : E → E} (hg : g.HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) g x‖ ≤ C) (k : ℕ) (v : E) (j : ι) :
    ∃ c, 0 ≤ c ∧ ∀ w : 𝓢(E, F),
      ‖toBesselPotentialSpaceCLM k 2
        (smulLeftCLM F (fun x ↦ ((b.toBasis.repr (fderiv ℝ g x v) j : ℝ) : ℂ)) w)‖ ≤
        c * ‖toBesselPotentialSpaceCLM k 2 w‖ :=
  hasSobolevExtension_iff_exists_norm_le.1 <| hasSobolevExtension_smulLeftCLM (k : ℝ)
    (hg.basis_repr_fderiv_apply b.toBasis v j) fun n _ ↦ by
      obtain ⟨C, hC⟩ := hb n
      exact ⟨C * ‖v‖, fun x ↦
        (hg.1.norm_iteratedFDeriv_basis_repr_fderiv_apply_le (mod_cast le_top) b v j x).trans
          (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))⟩

/-- The induction step of `SchwartzMap.exists_norm_toBesselPotentialSpaceCLM_compCLM_le_natCast`:
a bound for `u ↦ u ∘ φ` on `H^k` gives one on `H^{k+1}`, through the chain rule and the
multiplier bounds for its coefficients. -/
private theorem exists_sq_bound_compCLM_succ
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C) (k : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u : 𝓢(E, F), ‖toBesselPotentialSpaceCLM k 2
        (compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) u)‖ ^ 2 ≤
      C * ‖toBesselPotentialSpaceCLM k 2 u‖ ^ 2) :
    ∃ C', 0 ≤ C' ∧ ∀ u : 𝓢(E, F), ‖toBesselPotentialSpaceCLM (k + 1 : ℕ) 2
        (compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) u)‖ ^ 2 ≤
      C' * ‖toBesselPotentialSpaceCLM (k + 1 : ℕ) 2 u‖ ^ 2 := by
  set P := compCLM ℂ (F := F) hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv)
  let b := stdOrthonormalBasis ℝ E
  -- The chain rule `∂ᵢ (u ∘ φ) = ∑ⱼ cᵢⱼ (∂ⱼ u) ∘ φ`, where `Dφ(x) bᵢ = ∑ⱼ cᵢⱼ(x) bⱼ`.
  have hchain (i : Fin (Module.finrank ℝ E)) (u : 𝓢(E, F)) : ∂_{b i} (P u) =
      ∑ j, smulLeftCLM F (fun x ↦ ((b.toBasis.repr (fderiv ℝ φ x (b i)) j : ℝ) : ℂ))
        (P (∂_{b j} u)) := by
    ext x
    simp only [P]
    rw [lineDerivOp_compCLM_apply ℂ b.toBasis hφ hψ, sum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [smulLeftCLM_apply_apply (hφ.basis_repr_fderiv_apply b.toBasis (b i) j), compCLM_apply,
      Function.comp_apply, OrthonormalBasis.coe_toBasis, RCLike.ofReal_eq_complex_ofReal]
  choose c _ hc using fun i j ↦
    exists_norm_toBesselPotentialSpaceCLM_smulLeftCLM_repr_fderiv_le (F := F) b hφ hb k (b i) j
  set K := ∑ i, ∑ j, c i j ^ 2
  refine ⟨C * (1 + K), by positivity, fun u ↦ ?_⟩
  have hd (i : Fin (Module.finrank ℝ E)) :
      ‖toBesselPotentialSpaceCLM k 2 (∂_{b i} (P u))‖ ^ 2 ≤
        (∑ j, c i j ^ 2) * (C * ∑ j, ‖toBesselPotentialSpaceCLM k 2 (∂_{b j} u)‖ ^ 2) := by
    rw [hchain, map_sum]
    have h1 : ‖∑ j, toBesselPotentialSpaceCLM k 2
        (smulLeftCLM F (fun x ↦ ((b.toBasis.repr (fderiv ℝ φ x (b i)) j : ℝ) : ℂ))
          (P (∂_{b j} u)))‖ ≤
        ∑ j, c i j * ‖toBesselPotentialSpaceCLM k 2 (P (∂_{b j} u))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ hc i j _)
    calc _ ≤ (∑ j, c i j * ‖toBesselPotentialSpaceCLM k 2 (P (∂_{b j} u))‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ j, c i j ^ 2) * ∑ j, ‖toBesselPotentialSpaceCLM k 2 (P (∂_{b j} u))‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (∑ j, c i j ^ 2) * (C * ∑ j, ‖toBesselPotentialSpaceCLM k 2 (∂_{b j} u)‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun j _ ↦ hC _
  have hsum : ∑ i, ‖toBesselPotentialSpaceCLM k 2 (∂_{b i} (P u))‖ ^ 2 ≤
      K * (C * ∑ j, ‖toBesselPotentialSpaceCLM k 2 (∂_{b j} u)‖ ^ 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ ↦ hd i
  -- Expand both sides with `‖v‖²_{H^{k+1}} = ‖v‖²_{H^k} + (2π)⁻² ∑ᵢ ‖∂ᵢ v‖²_{H^k}`.
  have hrec := norm_toBesselPotentialSpaceCLM_add_one_sq (F := F) b (k : ℝ)
  rw [Nat.cast_succ, hrec, hrec]
  set X := ‖toBesselPotentialSpaceCLM k 2 u‖ ^ 2
  set Y := ∑ j, ‖toBesselPotentialSpaceCLM k 2 (∂_{b j} u)‖ ^ 2
  set π' := (2 * Real.pi)⁻¹ ^ 2
  calc _ ≤ C * X + π' * (K * (C * Y)) := by gcongr; exact hC u
    _ ≤ C * X + π' * (K * (C * Y)) + (C * K * X + π' * (C * Y)) :=
        le_add_of_nonneg_right (by positivity)
    _ = C * (1 + K) * (X + π' * Y) := by ring

/-- **Changes of variables on `H^k`, on Schwartz functions.** Let `φ` be a bijection such that `φ`
and `φ⁻¹` have temperate growth, the derivatives of `φ` of positive order are bounded and
`c ≤ |det Dφ|` for some `c > 0`. Then `‖u ∘ φ‖_{H^k} ≤ C ‖u‖_{H^k}` for every natural `k` and
every Schwartz function `u`, with `C` independent of `u`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_compCLM_le_natCast
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C) {c : ℝ} (hc : 0 < c)
    (hdet : ∀ x, c ≤ |(fderiv ℝ φ x).det|) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(E, F),
      ‖toBesselPotentialSpaceCLM k 2 (compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) u)‖
        ≤ C * ‖toBesselPotentialSpaceCLM k 2 u‖ := by
  set P := compCLM ℂ (F := F) hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv)
  -- It suffices to bound the squares of the norms.
  suffices h : ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(E, F),
      ‖toBesselPotentialSpaceCLM k 2 (P u)‖ ^ 2 ≤ C * ‖toBesselPotentialSpaceCLM k 2 u‖ ^ 2 by
    obtain ⟨C, hC0, hC⟩ := h
    refine ⟨√C, Real.sqrt_nonneg _, fun u ↦ ?_⟩
    rw [← Real.sqrt_sq (norm_nonneg (toBesselPotentialSpaceCLM k 2 (P u))),
      ← Real.sqrt_sq (norm_nonneg (toBesselPotentialSpaceCLM k 2 u)), ← Real.sqrt_mul hC0]
    exact Real.sqrt_le_sqrt (hC u)
  induction k with
  | zero =>
    refine ⟨c⁻¹, inv_nonneg.2 hc.le, fun u ↦ ?_⟩
    obtain ⟨v, hv, -, hvn⟩ :=
      exists_compCLM_toTemperedDistribution_eq_and_norm_le volume hφ hψ hc hdet (u.toLp 2)
    have hPv : (P u).toLp 2 = v := Lp.toTemperedDistribution_injective <| by
      beta_reduce
      rw [← hv, Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq,
        TemperedDistribution.compCLM_toTemperedDistributionCLM]
    rw [Nat.cast_zero, norm_toBesselPotentialSpaceCLM_zero, norm_toBesselPotentialSpaceCLM_zero,
      ← SchwartzMap.norm_toLp (f := P u), ← SchwartzMap.norm_toLp (f := u), hPv]
    refine (pow_le_pow_left₀ (norm_nonneg _) hvn 2).trans_eq ?_
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  | succ k ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    exact exists_sq_bound_compCLM_succ hφ hψ hb k hC0 hC

/-- **Changes of variables on `H^{-k}`, on Schwartz functions.** If `φ` and `φ⁻¹` have temperate
growth and bounded derivatives of positive order, then `‖w ∘ φ‖_{H^{-k}} ≤ C ‖w‖_{H^{-k}}` for every
natural `k` and every Schwartz function `w`. By duality this is the bound of the pushforward
`φ_* v = |det Dφ⁻¹| (v ∘ φ⁻¹)` on `H^k`. -/
private theorem exists_norm_toBesselPotentialSpaceCLM_compCLM_le_neg_natCast
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C)
    (hb' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm x‖ ≤ C) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ w : 𝓢(E, F),
      ‖toBesselPotentialSpaceCLM (-k) 2
          (compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) w)‖ ≤
        C * ‖toBesselPotentialSpaceCLM (-k) 2 w‖ := by
  have hφ' : (φ.symm.symm : E → E).HasTemperateGrowth := by simpa using hφ
  set J : E → ℂ := fun y ↦ ((|(fderiv ℝ φ.symm y).det| : ℝ) : ℂ)
  have hJ : J.HasTemperateGrowth :=
    (RCLike.hasTemperateGrowth_ofReal ℂ).comp (hφ.abs_det_fderiv_symm hψ)
  -- The pushforward `φ_* v = J (v ∘ φ⁻¹)` is bounded on `H^k`.
  obtain ⟨L, hL⟩ := hb 0
  obtain ⟨Cs, hCs0, hCs⟩ := exists_norm_toBesselPotentialSpaceCLM_compCLM_le_natCast (F := F)
    (φ := φ.symm) hψ hφ' hb' (by positivity) (φ.symm.inv_max_one_pow_le_abs_det_fderiv
      (hψ.1.differentiable (by simp)) (hφ'.1.differentiable (by simp)) (by simpa using hL)) k
  obtain ⟨CJ, hCJ0, hCJ⟩ := hasSobolevExtension_iff_exists_norm_le.1 <|
    hasSobolevExtension_smulLeftCLM (F := F) (k : ℝ) hJ fun n _ ↦
      hφ.exists_norm_iteratedFDeriv_abs_det_fderiv_symm_le hψ n fun m _ ↦ hb' m
  have hQ (v : 𝓢(E, F)) : ‖toBesselPotentialSpaceCLM k 2 (pushforwardCLM ℂ φ hφ hψ v)‖ ≤
      CJ * (Cs * ‖toBesselPotentialSpaceCLM k 2 v‖) := by
    have hv : pushforwardCLM ℂ φ hφ hψ v = smulLeftCLM F J
        (compCLM ℂ hψ (hφ'.exists_norm_le_of_leftInverse φ.symm.left_inv) v) := by
      ext y
      simp only [pushforwardCLM_apply, smulLeftCLM_apply_apply hJ, compCLM_apply,
        Function.comp_apply, J, RCLike.ofReal_eq_complex_ofReal]
    rw [hv]
    exact (hCJ _).trans (mul_le_mul_of_nonneg_left (hCs v) hCJ0)
  -- `u ↦ u ∘ φ` is a formal adjoint of `φ_*`.
  have hadj (v w : 𝓢(E, F)) : ∫ x, ⟪pushforwardCLM ℂ φ hφ hψ v x, w x⟫_ℂ =
      ∫ x, ⟪v x, compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) w x⟫_ℂ := by
    rw [← integral_inner_conj_symm, ← integral_inner_compCLM_eq volume hφ hψ,
      integral_inner_conj_symm]
  -- Duality turns the bound of the transpose `φ_*` on `H^k` into the bound on `H^{-k}`.
  exact ⟨CJ * Cs, mul_nonneg hCJ0 hCs0, norm_toBesselPotentialSpaceCLM_le_of_integral_inner_eq
    (mul_nonneg hCJ0 hCs0) hadj fun v ↦ (hQ v).trans_eq (mul_assoc ..).symm⟩

/-- **Changes of variables on `H^m` for integer `m`, on Schwartz functions.** -/
private theorem hasSobolevExtension_compCLM_intCast
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C)
    (hb' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm x‖ ≤ C) (m : ℤ) :
    HasSobolevExtension
      (compCLM ℂ (F := F) hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv)) m m := by
  refine hasSobolevExtension_iff_exists_norm_le.2 ?_
  obtain ⟨k, rfl | rfl⟩ := m.eq_nat_or_neg
  · obtain ⟨L, hL⟩ := hb' 0
    rw [Int.cast_natCast]
    exact exists_norm_toBesselPotentialSpaceCLM_compCLM_le_natCast (F := F) hφ hψ hb (by positivity)
      (φ.inv_max_one_pow_le_abs_det_fderiv (hφ.1.differentiable (by simp))
        (hψ.1.differentiable (by simp)) (by simpa using hL)) k
  · rw [Int.cast_neg, Int.cast_natCast]
    exact exists_norm_toBesselPotentialSpaceCLM_compCLM_le_neg_natCast (F := F) hφ hψ hb hb' k

/-- **Changes of variables extend to `H^s`.** If `φ` and `φ⁻¹` have temperate growth and bounded
derivatives of every positive order, then composition with `φ` on Schwartz functions extends to a
bounded operator `H^s → H^s`, for every real `s`. Between consecutive integers this is
interpolation of the Hilbert scale. -/
theorem hasSobolevExtension_compCLM (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C)
    (hb' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm x‖ ≤ C) (s : ℝ) :
    HasSobolevExtension
      (compCLM ℂ (F := F) hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv)) s s := by
  have h := (hasSobolevExtension_compCLM_intCast (F := F) hφ hψ hb hb' ⌊s⌋).interpolate
    (hasSobolevExtension_compCLM_intCast hφ hψ hb hb' (⌊s⌋ + 1))
    ⟨Int.fract_nonneg s, (Int.fract_lt_one s).le⟩
  have hs : (1 - Int.fract s) * (⌊s⌋ : ℝ) + Int.fract s * ((⌊s⌋ + 1 : ℤ) : ℝ) = s := by
    rw [Int.fract]
    push_cast
    ring
  rwa [hs] at h

end SchwartzMap

namespace TemperedDistribution

open MeasureTheory
open scoped SchwartzMap BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] {φ : E ≃ E}

/-- **Changes of variables preserve `H^s`.** If `φ` and `φ⁻¹` have temperate growth and bounded
derivatives of every positive order, then the pullback `φ^* u` of a tempered distribution
`u ∈ H^s` lies in `H^s`, for every real `s`. -/
theorem MemSobolev.compCLM (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C)
    (hb' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm x‖ ≤ C) {s : ℝ} {u : 𝓢'(E, F)}
    (hu : MemSobolev s 2 u) : MemSobolev s 2 (TemperedDistribution.compCLM F φ hφ hψ u) :=
  hu.compCLM_of_norm_iteratedFDeriv_le_real ENNReal.one_lt_two ENNReal.ofNat_ne_top hφ hψ
    (fun n hn _ ↦ Nat.sub_add_cancel hn ▸ hb (n - 1))
    (fun n hn _ ↦ Nat.sub_add_cancel hn ▸ hb' (n - 1))

end TemperedDistribution


namespace BesselPotentialSpace

open TemperedDistribution
open scoped SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] {φ : E ≃ E} {s : ℝ}

/-- **Pullback along a change of variables on `H^s`.** For a bijection `φ` such that `φ` and `φ⁻¹`
have temperate growth and bounded derivatives of every positive order, the pullback of tempered
distributions `TemperedDistribution.compCLM` restricts to a bounded operator `H^s → H^s`, for every
real `s` (`BesselPotentialSpace.toDistr_compCLM`). On Schwartz functions it is `u ↦ u ∘ φ`
(`BesselPotentialSpace.compCLM_toBesselPotentialSpaceCLM`). -/
def compCLM (φ : E ≃ E) (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C)
    (hb' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm x‖ ≤ C) (s : ℝ) :
    H^{s}(E, F) →L[ℂ] H^{s}(E, F) :=
  mapCLM (TemperedDistribution.compCLM F φ hφ hψ) fun u ↦
    u.memSobolev_toDistr.compCLM hφ hψ hb hb'

variable (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C)
    (hb' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm x‖ ≤ C)

@[simp]
theorem toDistr_compCLM (u : H^{s}(E, F)) :
    (compCLM φ hφ hψ hb hb' s u).toDistr = TemperedDistribution.compCLM F φ hφ hψ u.toDistr :=
  toDistr_mapCLM _ _ u

/-- On Schwartz functions the pullback is composition with `φ`. -/
@[simp]
theorem compCLM_toBesselPotentialSpaceCLM (u : 𝓢(E, F)) :
    compCLM φ hφ hψ hb hb' s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM s 2
        (SchwartzMap.compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) u) :=
  ext (by simp [compCLM_toTemperedDistributionCLM])

/-- Pulling back along `φ` and then along `φ⁻¹` is the identity of `H^s`. -/
@[simp]
theorem compCLM_symm_compCLM (hφ' : (φ.symm.symm : E → E).HasTemperateGrowth)
    (hb'' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm.symm x‖ ≤ C) (u : H^{s}(E, F)) :
    compCLM φ.symm hψ hφ' hb' hb'' s (compCLM φ hφ hψ hb hb' s u) = u :=
  ext (by simp)

/-- Pulling back along `φ⁻¹` and then along `φ` is the identity of `H^s`. -/
@[simp]
theorem compCLM_compCLM_symm (hφ' : (φ.symm.symm : E → E).HasTemperateGrowth)
    (hb'' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm.symm x‖ ≤ C) (u : H^{s}(E, F)) :
    compCLM φ hφ hψ hb hb' s (compCLM φ.symm hψ hφ' hb' hb'' s u) = u :=
  ext (by simp)

/-- **Changes of variables are isomorphisms of `H^s`.** The pullback along `φ` as a continuous
linear automorphism of `H^s`, with inverse the pullback along `φ⁻¹`. -/
def compEquiv (φ : E ≃ E) (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C)
    (hb' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm x‖ ≤ C) (s : ℝ) :
    H^{s}(E, F) ≃L[ℂ] H^{s}(E, F) :=
  .ofContinuousLinearMap (compCLM φ hφ hψ hb hb' s)
    (compCLM φ.symm hψ (by simpa using hφ) hb' (by simpa using hb) s)
    (ContinuousLinearMap.ext (compCLM_compCLM_symm hφ hψ hb hb' _ _))
    (ContinuousLinearMap.ext (compCLM_symm_compCLM hφ hψ hb hb' _ _))

@[simp]
theorem compEquiv_apply (u : H^{s}(E, F)) :
    compEquiv φ hφ hψ hb hb' s u = compCLM φ hφ hψ hb hb' s u :=
  (rfl)

/-- The inverse of the pullback along `φ` is the pullback along `φ⁻¹`. -/
@[simp]
theorem compEquiv_symm_apply (u : H^{s}(E, F)) :
    (compEquiv φ hφ hψ hb hb' s).symm u =
      compCLM φ.symm hψ (by simpa using hφ) hb' (by simpa using hb) s u :=
  (rfl)

end BesselPotentialSpace

namespace BesselPotentialSpace

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (F) in
/-- **Pullback by a diffeomorphism with bounded derivatives**, as an isomorphism of `H^{s,p}` for
a real order `s` and `1 < p < ∞`. Here `Φ` is a bijection such that `Φ` and `Φ⁻¹` have temperate
growth and bounded derivatives of orders `1` to `⌈|s|⌉ + 1`. It acts on the underlying
tempered distributions by the pullback `TemperedDistribution.compCLM`
(`BesselPotentialSpace.toDistr_compCLE`), and its inverse is the pullback along `Φ⁻¹`
(`BesselPotentialSpace.compCLE_symm`). -/
def compCLE (hp : 1 < p) (hp_top : p ≠ ∞) (s : ℝ) (Φ : E ≃ E)
    (hΦ : (Φ : E → E).HasTemperateGrowth) (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
    (hΦb : ∀ n, 1 ≤ n → n ≤ ⌈|s|⌉₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∀ n, 1 ≤ n → n ≤ ⌈|s|⌉₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C) :
    H^{s, p}(E, F) ≃L[ℂ] H^{s, p}(E, F) :=
  .ofContinuousLinearMap
    (mapCLM (TemperedDistribution.compCLM F Φ hΦ hΨ) fun u ↦
      u.memSobolev_toDistr.compCLM_of_norm_iteratedFDeriv_le_real hp hp_top hΦ hΨ
        (fun n h₁ h₂ ↦ hΦb n h₁ (by omega)) hΨb)
    (mapCLM (TemperedDistribution.compCLM F Φ.symm hΨ hΦ) fun u ↦
      u.memSobolev_toDistr.compCLM_of_norm_iteratedFDeriv_le_real hp hp_top hΨ hΦ
        (fun n h₁ h₂ ↦ hΨb n h₁ (by omega)) hΦb)
    (ContinuousLinearMap.ext fun u ↦ ext (by simp)) (ContinuousLinearMap.ext fun u ↦ ext (by simp))

variable {hp : 1 < p} {hp_top : p ≠ ∞} {s : ℝ} {Φ : E ≃ E} {hΦ : (Φ : E → E).HasTemperateGrowth}
  {hΨ : (Φ.symm : E → E).HasTemperateGrowth}
  {hΦb : ∀ n, 1 ≤ n → n ≤ ⌈|s|⌉₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C}
  {hΨb : ∀ n, 1 ≤ n → n ≤ ⌈|s|⌉₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C}

@[simp]
theorem toDistr_compCLE (u : H^{s, p}(E, F)) :
    (compCLE F hp hp_top s Φ hΦ hΨ hΦb hΨb u).toDistr =
      TemperedDistribution.compCLM F Φ hΦ hΨ u.toDistr :=
  toDistr_mapCLM _ _ u

/-- The inverse of the pullback along `Φ` is the pullback along `Φ⁻¹`. -/
@[simp]
theorem compCLE_symm :
    (compCLE F hp hp_top s Φ hΦ hΨ hΦb hΨb).symm = compCLE F hp hp_top s Φ.symm hΨ hΦ hΨb hΦb :=
  ContinuousLinearEquiv.ext <| funext fun u ↦
    (ContinuousLinearEquiv.symm_apply_eq _).2 (ext (by simp))

/-- On Schwartz functions the pullback is composition with `Φ`. -/
@[simp]
theorem compCLE_toBesselPotentialSpaceCLM (u : 𝓢(E, F)) :
    compCLE F hp hp_top s Φ hΦ hΨ hΦb hΨb (SchwartzMap.toBesselPotentialSpaceCLM s p u) =
      SchwartzMap.toBesselPotentialSpaceCLM s p
        (SchwartzMap.compCLM ℂ hΦ (hΨ.exists_norm_le_of_leftInverse Φ.left_inv) u) :=
  ext (by simp)

end BesselPotentialSpace
