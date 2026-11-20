/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.BesselPotential.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Coordinates
import TauCeti.Analysis.Sobolev.BesselPotential.SmoothMultiplier
import TauCeti.MeasureTheory.Function.Jacobian
import TauCeti.MeasureTheory.Function.Lp.CastMeasure

/-!
# Changes of variables in integer-order Bessel-potential spaces

For `1 < p < ∞` and a natural order `k`, the real Bessel-potential functions
`TemperedDistribution.realSobolevFunctions E k p` are preserved by precomposition with a change of
variables of order `k` of the whole space (`TauCeti.Wkp.IsChangeOfVariables`): a `Cᵏ`
injective map with bounded derivatives of orders `1` through `k` and Jacobian determinant bounded
away from zero. In particular they are invariant under translations and under linear
automorphisms of `E`.

The proof passes through the weak-derivative Sobolev space `W^{k,p}(E)`, which has the same real
elements by Calderón's theorem (`MeasureTheory.Lp.memSobolev_natCast_iff_exists_wkp_value_eq`), and
on which precomposition is the bounded operator `TauCeti.Wkp.compL`.

For tempered distributions with values in a complex Hilbert space and every integer order `k`,
positive or negative, the pullback `Φ^*` (`TemperedDistribution.compCLM`) along a bijection `Φ`
such that `Φ` and `Φ⁻¹` have temperate growth and bounded derivatives of orders `1` to `|k| + 1`
preserves `H^{k,p}`, and restricts to an isomorphism of `H^{k,p}` with inverse the pullback along
`Φ⁻¹`.
These are the coordinate changes that make the integer-order Sobolev norms of sections of a vector
bundle independent of the chart. Each step of the proof is an induction on `k`, starting from
`H^{0,p} = Lᵖ`, which `Φ^*` preserves because the Jacobian of `Φ` is bounded below in terms of
`DΦ⁻¹` (`TemperedDistribution.exists_compCLM_toTemperedDistribution_eq_and_norm_le`).

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

## Main results

* `TemperedDistribution.comp_mem_realSobolevFunctions_natCast`: precomposition with a change of
  variables of order `k`.
* `TemperedDistribution.comp_add_mem_realSobolevFunctions_natCast`: translations.
* `TemperedDistribution.comp_continuousLinearEquiv_mem_realSobolevFunctions_natCast`: linear
  automorphisms.
* `TemperedDistribution.MemSobolev.compCLM_of_norm_fderiv_symm_le`: the pullback preserves
  `H^{0,p} = Lᵖ`, for `1 ≤ p ≤ ∞`.
* `TemperedDistribution.MemSobolev.compCLM_of_norm_iteratedFDeriv_le`,
  `TemperedDistribution.MemSobolev.compCLM_of_norm_iteratedFDeriv_le_neg` and
  `TemperedDistribution.MemSobolev.compCLM_of_norm_iteratedFDeriv_le_intCast`: the pullback
  preserves `H^{k,p}`, `H^{-k,p}` and `H^{k,p}` for `k ∈ ℤ`, for `1 < p < ∞`.
* `BesselPotentialSpace.compCLE`: the pullback as an isomorphism of `H^{k,p}`, `k ∈ ℤ`, with
  inverse the pullback along `Φ⁻¹` (`BesselPotentialSpace.compCLE_symm`); on Schwartz functions it
  is composition with `Φ` (`BesselPotentialSpace.compCLE_toBesselPotentialSpaceCLM`).
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
  have hae : ae (volume.restrict ((⊤ : Opens E) : Set E)) = ae (volume : Measure E) := by
    rw [← hvolume]
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

end Pullback

end TemperedDistribution

namespace BesselPotentialSpace

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (F) in
/-- **Pullback by a diffeomorphism with bounded derivatives**, as an isomorphism of `H^{k,p}` for
an integer order `k` and `1 < p < ∞`. Here `Φ` is a bijection such that `Φ` and `Φ⁻¹` have
temperate growth and bounded derivatives of orders `1` to `|k| + 1`. It acts on the underlying
tempered distributions by the pullback `TemperedDistribution.compCLM`
(`BesselPotentialSpace.toDistr_compCLE`), and its inverse is the pullback along `Φ⁻¹`
(`BesselPotentialSpace.compCLE_symm`). -/
def compCLE (hp : 1 < p) (hp_top : p ≠ ∞) (k : ℤ) (Φ : E ≃ E)
    (hΦ : (Φ : E → E).HasTemperateGrowth) (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
    (hΦb : ∀ n, 1 ≤ n → n ≤ k.natAbs + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∀ n, 1 ≤ n → n ≤ k.natAbs + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C) :
    H^{k, p}(E, F) ≃L[ℂ] H^{k, p}(E, F) :=
  .ofContinuousLinearMap
    (mapCLM (TemperedDistribution.compCLM F Φ hΦ hΨ) fun u ↦
      u.memSobolev_toDistr.compCLM_of_norm_iteratedFDeriv_le_intCast hp hp_top hΦ hΨ
        (fun n h₁ h₂ ↦ hΦb n h₁ (by omega)) hΨb)
    (mapCLM (TemperedDistribution.compCLM F Φ.symm hΨ hΦ) fun u ↦
      u.memSobolev_toDistr.compCLM_of_norm_iteratedFDeriv_le_intCast hp hp_top hΨ hΦ
        (fun n h₁ h₂ ↦ hΨb n h₁ (by omega)) hΦb)
    (ContinuousLinearMap.ext fun u ↦ ext (by simp)) (ContinuousLinearMap.ext fun u ↦ ext (by simp))

variable {hp : 1 < p} {hp_top : p ≠ ∞} {k : ℤ} {Φ : E ≃ E} {hΦ : (Φ : E → E).HasTemperateGrowth}
  {hΨ : (Φ.symm : E → E).HasTemperateGrowth}
  {hΦb : ∀ n, 1 ≤ n → n ≤ k.natAbs + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C}
  {hΨb : ∀ n, 1 ≤ n → n ≤ k.natAbs + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C}

@[simp]
theorem toDistr_compCLE (u : H^{k, p}(E, F)) :
    (compCLE F hp hp_top k Φ hΦ hΨ hΦb hΨb u).toDistr =
      TemperedDistribution.compCLM F Φ hΦ hΨ u.toDistr :=
  toDistr_mapCLM _ _ u

/-- The inverse of the pullback along `Φ` is the pullback along `Φ⁻¹`. -/
@[simp]
theorem compCLE_symm :
    (compCLE F hp hp_top k Φ hΦ hΨ hΦb hΨb).symm = compCLE F hp hp_top k Φ.symm hΨ hΦ hΨb hΦb :=
  ContinuousLinearEquiv.ext <| funext fun u ↦
    (ContinuousLinearEquiv.symm_apply_eq _).2 (ext (by simp))

/-- On Schwartz functions the pullback is composition with `Φ`. -/
@[simp]
theorem compCLE_toBesselPotentialSpaceCLM (u : 𝓢(E, F)) :
    compCLE F hp hp_top k Φ hΦ hΨ hΦb hΨb (SchwartzMap.toBesselPotentialSpaceCLM k p u) =
      SchwartzMap.toBesselPotentialSpaceCLM k p
        (SchwartzMap.compCLM ℂ hΦ (hΨ.exists_norm_le_of_leftInverse Φ.left_inv) u) :=
  ext (by simp)

end BesselPotentialSpace
