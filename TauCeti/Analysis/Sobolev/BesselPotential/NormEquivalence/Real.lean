/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.NormEquivalence.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Real
import TauCeti.Analysis.Sobolev.Wkp.Density
import TauCeti.Analysis.Sobolev.Wkp.Multiplication

/-!
# `W^{k,2}` is the real Hilbert space of real elements of `H^k`

The identification `TauCeti.Wkp.toBesselPotentialSpace` of the weak-derivative Sobolev space
`W^{k,2}(E)` of real functions on the whole space with Mathlib's Bessel-potential space `H^k(E)` of
complex distributions is injective, and its range consists of the elements of `H^k(E)` given by real
`L²` functions. Those are the closed real subspace `BesselPotentialSpace.realSubmodule E h` of
`H^k(E)`. This file packages the identification as a continuous real-linear equivalence

`TauCeti.Wkp.toRealSubmodule k : W^{k,2}(E) ≃L[ℝ] realSubmodule E h`,

characterized by the `L²` function of the image (`TauCeti.Wkp.coeFn_inclusionLp_toRealSubmodule`,
`TauCeti.Wkp.toRealSubmodule_eq_iff`); above the Sobolev threshold the value of `u` is almost
everywhere the continuous representative of the image
(`TauCeti.Wkp.value_ae_eq_continuousRep_toRealSubmodule`). Its inverse is bounded by the open
mapping theorem, and takes `F` to the real part of its `L²` function
(`TauCeti.Wkp.value_toRealSubmodule_symm`,
`TauCeti.Wkp.value_toRealSubmodule_symm_ae_eq_continuousRep`). So
operators constructed on `W^{k,2}` with weak derivatives, such as Schrödinger operators inverted by
the Lax–Milgram method, transfer to the real Bessel-potential scale, where products and power
series act.

Explicit bounds also transfer. Multiplication by a smooth real `ψ` whose derivatives through order
`k` are bounded by `M` has norm at most `2^(k+1) M` on `W^{k,2}(E)`, so on the real elements of
`H^k(E)` it has norm at most `C M`, with `C` depending only on `E` and `k`
(`BesselPotentialSpace.exists_forall_exists_inclusionLp_ae_eq_mul_and_norm_le`). The closed graph
theorem gives no such dependence on `ψ`, and it is what makes elliptic estimates uniform over
families of coefficients.
-/

public section

noncomputable section

open MeasureTheory BesselPotentialSpace
open scoped BesselPotentialSpace

namespace TauCeti.Wkp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem toBesselPotentialSpace_mem_realSubmodule (k : ℕ) (u : Wkp (volume : Measure E) ⊤ 2 k) :
    toBesselPotentialSpace ENNReal.one_lt_two ENNReal.ofNat_ne_top k u ∈
      realSubmodule E (Nat.cast_nonneg k) := by
  rw [mem_realSubmodule_iff]
  filter_upwards [coeFn_inclusionLp_toBesselPotentialSpace ENNReal.one_lt_two
    ENNReal.ofNat_ne_top k u] with z hz
  rw [hz, Complex.ofReal_im]

private theorem exists_toBesselPotentialSpace_eq (k : ℕ)
    (F : realSubmodule E (Nat.cast_nonneg k)) :
    ∃ u : Wkp (volume : Measure E) ⊤ 2 k,
      toBesselPotentialSpace ENNReal.one_lt_two ENNReal.ofNat_ne_top k u = F := by
  refine (exists_toBesselPotentialSpace_eq_iff ENNReal.one_lt_two ENNReal.ofNat_ne_top k _).2
    ⟨Complex.reCLM.compLp (inclusionLp (Nat.cast_nonneg k) (F : H^{(k : ℝ)}(E))), ?_⟩
  rw [← toTemperedDistribution_inclusionLp (Nat.cast_nonneg k)]
  congr 1
  refine Lp.ext ?_
  filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := 2) (μ := volume)
    (Complex.reCLM.compLp (inclusionLp (Nat.cast_nonneg k) (F : H^{(k : ℝ)}(E)))),
    Complex.reCLM.coeFn_compLp (p := 2) (μ := volume)
      (inclusionLp (Nat.cast_nonneg k) (F : H^{(k : ℝ)}(E))),
    (mem_realSubmodule_iff (Nat.cast_nonneg k)).1 F.property] with z h₁ h₂ h₃
  rw [h₁, Complex.ofRealCLM_apply, h₂, Complex.reCLM_apply]
  exact Complex.ext (by simp) (by simp [h₃])

/-- **`W^{k,2}(E)` is the space of real elements of `H^k(E)`**: the identification
`TauCeti.Wkp.toBesselPotentialSpace` as a continuous real-linear equivalence onto
`realSubmodule E h`. The image of `u` is the element of `H^k(E)` whose `L²` function is the value
of `u` (`TauCeti.Wkp.coeFn_inclusionLp_toRealSubmodule`). -/
def toRealSubmodule (k : ℕ) :
    Wkp (volume : Measure E) ⊤ 2 k ≃L[ℝ] realSubmodule E (Nat.cast_nonneg k) :=
  ContinuousLinearEquiv.ofBijective
    ((toBesselPotentialSpace ENNReal.one_lt_two ENNReal.ofNat_ne_top k).codRestrict _
      (toBesselPotentialSpace_mem_realSubmodule k))
    (LinearMap.ker_eq_bot.2 fun _ _ huv ↦
      toBesselPotentialSpace_injective ENNReal.one_lt_two ENNReal.ofNat_ne_top k
        (congrArg Subtype.val huv))
    (LinearMap.range_eq_top.2 fun F ↦ by
      obtain ⟨u, hu⟩ := exists_toBesselPotentialSpace_eq k F
      exact ⟨u, Subtype.ext hu⟩)

@[simp]
theorem coe_toRealSubmodule (k : ℕ) (u : Wkp (volume : Measure E) ⊤ 2 k) :
    (toRealSubmodule k u : H^{(k : ℝ)}(E)) =
      toBesselPotentialSpace ENNReal.one_lt_two ENNReal.ofNat_ne_top k u :=
  (rfl)

/-- The `L²` function of `toRealSubmodule k u` is the value of `u`. -/
theorem coeFn_inclusionLp_toRealSubmodule (k : ℕ) (u : Wkp (volume : Measure E) ⊤ 2 k) :
    ⇑(inclusionLp (Nat.cast_nonneg k) (toRealSubmodule k u : H^{(k : ℝ)}(E))) =ᵐ[volume]
      fun x ↦ (value k u x : ℂ) :=
  coeFn_inclusionLp_toBesselPotentialSpace ENNReal.one_lt_two ENNReal.ofNat_ne_top k u

/-- `toRealSubmodule k u` is the real element of `H^k(E)` whose `L²` function is the value of
`u`. -/
theorem toRealSubmodule_eq_iff {k : ℕ} {u : Wkp (volume : Measure E) ⊤ 2 k}
    {F : realSubmodule E (Nat.cast_nonneg k)} :
    toRealSubmodule k u = F ↔
      ⇑(inclusionLp (Nat.cast_nonneg k) (F : H^{(k : ℝ)}(E))) =ᵐ[volume]
        fun x ↦ (value k u x : ℂ) := by
  rw [← Subtype.coe_inj, coe_toRealSubmodule]
  exact toBesselPotentialSpace_eq_iff ENNReal.one_lt_two ENNReal.ofNat_ne_top

/-- Above the Sobolev threshold `k > dim E / 2`, the value of `u ∈ W^{k,2}(E)` is almost everywhere
the continuous representative of `toRealSubmodule k u`. -/
theorem value_ae_eq_continuousRep_toRealSubmodule {k : ℕ}
    (hk : (Module.finrank ℝ E : ℝ) < 2 * k) (u : Wkp (volume : Measure E) ⊤ 2 k) :
    (value k u : E → ℝ) =ᵐ[volume] continuousRep (toRealSubmodule k u) := by
  filter_upwards [coeFn_inclusionLp_toRealSubmodule k u,
    coeFn_inclusionLp_ae_eq_continuousRep hk (toRealSubmodule k u)] with z h₁ h₂
  exact_mod_cast h₁.symm.trans h₂

/-- The value of `(toRealSubmodule k).symm F` is the real part of the `L²` function of `F`. -/
theorem value_toRealSubmodule_symm (k : ℕ) (F : realSubmodule E (Nat.cast_nonneg k)) :
    (value k ((toRealSubmodule k).symm F) : E → ℝ) =ᵐ[volume]
      fun x ↦ (inclusionLp (Nat.cast_nonneg k) (F : H^{(k : ℝ)}(E)) x).re := by
  have h := coeFn_inclusionLp_toRealSubmodule k ((toRealSubmodule k).symm F)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  filter_upwards [h] with x hx
  rw [hx, Complex.ofReal_re]

/-- Above the Sobolev threshold `k > dim E / 2`, the value of `(toRealSubmodule k).symm F` is
almost everywhere the continuous representative of `F`. -/
theorem value_toRealSubmodule_symm_ae_eq_continuousRep {k : ℕ}
    (hk : (Module.finrank ℝ E : ℝ) < 2 * k) (F : realSubmodule E (Nat.cast_nonneg k)) :
    (value k ((toRealSubmodule k).symm F) : E → ℝ) =ᵐ[volume] continuousRep F := by
  have h := value_ae_eq_continuousRep_toRealSubmodule hk ((toRealSubmodule k).symm F)
  rwa [ContinuousLinearEquiv.apply_symm_apply] at h

end TauCeti.Wkp

/-! ### An explicit multiplier bound at integer orders -/

namespace BesselPotentialSpace

open TauCeti
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Multipliers with bounded derivatives on real elements of `H^k`, with an explicit bound.**
For every integer order `k ≥ 0` there is a constant `C`, depending only on `E` and `k`, with the
following property. Let `ψ` be a smooth real function whose derivatives through order `k` are
bounded by `M`, and let `u ∈ H^k(E)` be represented by a real function `g`. Then `ψ g` is
represented by an element `w ∈ H^k(E)` with `‖w‖ ≤ C M ‖u‖`.

The constant does not depend on `ψ`, only on the bound `M`. The proof passes through the
weak-derivative space `W^{k,2}(E)`, identified with the real elements of `H^k(E)` by
`TauCeti.Wkp.toRealSubmodule`, on which multiplication by `ψ` has norm at most `2^(k+1) M`
(`TauCeti.Wkp0.norm_contDiffSMulL_le`). -/
theorem exists_forall_exists_inclusionLp_ae_eq_mul_and_norm_le (k : ℕ) :
    ∃ C ≥ 0, ∀ (ψ : E → ℝ), ContDiff ℝ ∞ ψ → ∀ M : ℝ,
      (∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j ψ x‖ ≤ M) →
      ∀ (u : H^{(k : ℝ)}(E)) (g : E → ℝ),
        ⇑(inclusionLp (Nat.cast_nonneg k) u) =ᵐ[volume] (fun x ↦ (g x : ℂ)) →
        ∃ w : H^{(k : ℝ)}(E),
          ⇑(inclusionLp (Nat.cast_nonneg k) w) =ᵐ[volume] (fun x ↦ ((ψ x * g x : ℝ) : ℂ)) ∧
          ‖w‖ ≤ C * M * ‖u‖ := by
  set e := Wkp.toRealSubmodule (E := E) k
  refine ⟨‖e.toContinuousLinearMap‖ * 2 ^ (k + 1) *
    ‖e.symm.toContinuousLinearMap‖, by positivity,
    fun ψ hψ M hbound u g hu ↦ ?_⟩
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 0 (Nat.zero_le k) 0)
  have hF : u ∈ realSubmodule E (Nat.cast_nonneg k) :=
    (mem_realSubmodule_iff _).2 (hu.mono fun x hx ↦ by rw [hx, Complex.ofReal_im])
  set F : realSubmodule E (Nat.cast_nonneg k) := ⟨u, hF⟩ with hFu
  have hw₀ : e.symm F ∈ wkp0Submodule (volume : Measure E) ⊤ 2 k := by
    rw [wkp0Submodule_top_eq_top (p := 2) ENNReal.ofNat_ne_top]
    trivial
  set v₀ := Wkp0.contDiffSMulL k hψ ⟨e.symm F, hw₀⟩
  refine ⟨(e v₀ : H^{(k : ℝ)}(E)), ?_, ?_⟩
  · -- The `L²` function of `e v₀` is the value of `v₀`, which is `ψ` times the value of
    -- `e.symm F`, the real part of the `L²` function `g` of `u`.
    have hv := Wkp0.value_contDiffSMulL_ae (mu := (volume : Measure E)) (Omega := ⊤)
      (p := 2) k hψ (fun j hj x _ ↦ hbound j hj x) ⟨e.symm F, hw₀⟩
    have hv' := (ae_restrict_iff' (⊤ : TopologicalSpace.Opens E).isOpen.measurableSet).mp hv
    filter_upwards [Wkp.coeFn_inclusionLp_toRealSubmodule k v₀.val, hv',
      Wkp.value_toRealSubmodule_symm k F, hu] with x h₁ h₂ h₃ h₄
    rw [h₁, h₂ (Set.mem_univ x)]
    rw [h₃, hFu, Submodule.coe_mk u hF, h₄, Complex.ofReal_re]
  · calc ‖(e v₀ : H^{(k : ℝ)}(E))‖
        = ‖e v₀‖ := Submodule.norm_coe _
      _ ≤ ‖e.toContinuousLinearMap‖ * ‖v₀.val‖ :=
          e.toContinuousLinearMap.le_opNorm v₀.val
      _ ≤ ‖e.toContinuousLinearMap‖ *
            (2 ^ (k + 1) * M * ‖e.symm F‖) := by
          gcongr
          exact ((Wkp0.contDiffSMulL k hψ).le_opNorm _).trans (mul_le_mul
            (Wkp0.norm_contDiffSMulL_le k hψ hM fun j hj x _ ↦ hbound j hj x) le_rfl
            (norm_nonneg _) (by positivity))
      _ ≤ ‖e.toContinuousLinearMap‖ *
            (2 ^ (k + 1) * M *
              (‖e.symm.toContinuousLinearMap‖ * ‖F‖)) := by
          gcongr
          exact e.symm.toContinuousLinearMap.le_opNorm F
      _ = _ := by
          rw [← Submodule.norm_coe, hFu, Submodule.coe_mk u hF]
          ring

end BesselPotentialSpace
