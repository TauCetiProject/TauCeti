/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.NormEquivalence.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Real

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
mapping theorem. So
operators constructed on `W^{k,2}` with weak derivatives, such as Schrödinger operators inverted by
the Lax–Milgram method, transfer to the real Bessel-potential scale, where products and power
series act.
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

end TauCeti.Wkp
