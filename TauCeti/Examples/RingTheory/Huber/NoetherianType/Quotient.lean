/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Huber.Adic
import TauCeti.RingTheory.Huber.NoetherianType.Quotient
import TauCeti.RingTheory.Huber.Padic.Basic
import TauCeti.RingTheory.Huber.Padic.TateAlgebra

/-!
# Examples: ideals and quotients of Huber rings of noetherian type

Both alternatives of noetherian type are exercised. In the strongly noetherian Tate ring
`ℚ_p⟨T₁, …, Tₙ⟩` every ideal is closed and every quotient is of noetherian type. The ring `ℤ_[p]`
is not Tate, but it is its own noetherian ring of definition, so every quotient of `ℤ_[p]` is of
noetherian type through the image of that ring of definition.

Finally, the Hausdorff hypothesis of `TauCeti.Huber.IsNoetherianType.isClosed_ideal` cannot be
dropped: with the indiscrete topology every Cauchy filter on `ℤ` converges, but the zero ideal is
not closed.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Lemma 2.3(ii).
-/

open TauCeti.Huber

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- In `ℚ_p⟨T₁, …, Tₙ⟩` every ideal is closed. -/
example (J : Ideal (MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) fun _ : Fin n ↦ (1 : ℝ))) :
    IsClosed (J : Set (MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) fun _ : Fin n ↦ (1 : ℝ))) :=
  IsNoetherianType.isClosed_ideal J

/-- Every quotient of `ℚ_p⟨T₁, …, Tₙ⟩` is Hausdorff and of noetherian type. -/
example (J : Ideal (MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) fun _ : Fin n ↦ (1 : ℝ))) :
    T2Space ((MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) fun _ : Fin n ↦ (1 : ℝ)) ⧸ J) ∧
      IsNoetherianType
        ((MvPowerSeries.IsRestricted.subring (R := ℚ_[p]) fun _ : Fin n ↦ (1 : ℝ)) ⧸ J) :=
  ⟨inferInstance, inferInstance⟩

/-- Every quotient of `ℤ_[p]` is of noetherian type, although `ℤ_[p]` is not a Tate ring: the
pair of definition `(ℤ_[p], (p))` has a noetherian ring of definition. -/
example (J : Ideal ℤ_[p]) : IsNoetherianType (ℤ_[p] ⧸ J) := by
  have hfg : (IsLocalRing.maximalIdeal ℤ_[p]).FG := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Submodule.fg_span_singleton _
  have : IsNoetherianType ℤ_[p] :=
    .of_pairOfDefinition (.adic _ PadicInt.isAdic_maximalIdeal hfg) <| by
      rw [PairOfDefinition.adic_ringOfDefinition]
      exact isNoetherianRing_of_ringEquiv _ Subring.topEquiv.symm
  infer_instance

/-- With the indiscrete topology on `ℤ`, the zero ideal is not closed. -/
example :
    letI : TopologicalSpace ℤ := ⊤
    ¬ IsClosed ((⊥ : Ideal ℤ) : Set ℤ) := by
  let : TopologicalSpace ℤ := ⊤
  intro h
  have h1 := isClosed_iff_nhds.mp h 1 fun U hU ↦ by
    rw [_root_.nhds_top, Filter.mem_top] at hU
    exact ⟨0, by simp [hU]⟩
  simp at h1
