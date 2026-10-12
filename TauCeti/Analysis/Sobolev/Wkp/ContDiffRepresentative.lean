/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.Analysis.Sobolev.WeakDeriv.Classical
import TauCeti.Analysis.Sobolev.Wkp.MeyersSerrin
import TauCeti.MeasureTheory.Function.LocalRepresentative

/-!
# Interior Sobolev embedding into `Cʲ(Ω)`

Let `Ω` be an open subset of a finite-dimensional real inner product space `E` of dimension `n`.
If `2k > n`, every `u ∈ W^{k+j,2}(Ω)` agrees almost everywhere on `Ω` with a function that is
`Cʲ` on `Ω`. In particular, a function lying in `W^{m,2}(Ω)` for every `m` agrees almost
everywhere on `Ω` with a function smooth on `Ω`. No boundedness or boundary regularity of `Ω` is
assumed: the statements are interior ones, and the representative need not be bounded or extend
continuously to the boundary.

## Localization

Continuity is local. Near a point of `Ω`, multiply `u` by a smooth bump `ζ` equal to one near the
point and supported in `Ω`; then `ζ u ∈ W^{k,2}_0(Ω)`
(`TauCeti.Wkp.exists_mem_wkp0Submodule_value_ae_eq_mul`), its extension by zero lies in
`W^{k,2}(E)`, and the whole-space embedding `W^{k,2}(E) → C₀(E)` for `2k > n`
(`TauCeti.Wkp.toZeroAtInfty`) gives a continuous function equal to `u` almost everywhere near the
point. The local continuous representatives glue to one on `Ω`
(`TauCeti.exists_contDiffOn_ae_eq_of_locally`).

## Derivatives

For `u ∈ W^{k+j+1,2}(Ω)`, the weak derivatives `∂ᵢu` along an orthonormal basis lie in
`W^{k+j,2}(Ω)` (`TauCeti.Wkp.exists_hasWeakLineDerivOn_value`), so by induction they have `Cʲ`
representatives. Assembled into a `Cʲ` field of linear maps, they form a weak derivative of the
continuous representative of `u`, which is therefore `Cʲ⁺¹`
(`TauCeti.HasWeakFDerivOn.contDiffOn_succ`).

The statements are for Lebesgue measure `volume`, the measure of the whole-space embedding.

## Main results

* `TauCeti.Wkp.exists_continuousOn_ae_eq`: `W^{k,2}(Ω) ⊆ C(Ω)` for `2k > n`.
* `TauCeti.Wkp.exists_contDiffOn_ae_eq`: `W^{k+j,2}(Ω) ⊆ Cʲ(Ω)` for `2k > n`.
* `TauCeti.exists_contDiffOn_ae_eq_of_forall_wkp`: a function in `W^{m,2}(Ω)` for every `m` has a
  representative smooth on `Ω`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.6.3, Theorem 6, and its use in
  §6.3.1, Theorem 3 (infinite differentiability in the interior).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Corollary 7.11.
-/

public section

open MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Topology

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {Omega : Opens E} {k : ℕ}

namespace Wkp

/-- **Interior Sobolev embedding into `C(Ω)`.** If `2k > dim E`, every `u ∈ W^{k,2}(Ω)` agrees
almost everywhere on `Ω` with a function continuous on `Ω`. -/
theorem exists_continuousOn_ae_eq (hk : finrank ℝ E < 2 * k)
    (u : Wkp (volume : Measure E) Omega 2 k) :
    ∃ g : E → ℝ, ContinuousOn g Omega ∧ (value k u : E → ℝ) =ᵐ[volume.restrict Omega] g := by
  simp_rw [← contDiffOn_zero (𝕜 := ℝ)]
  refine exists_contDiffOn_ae_eq_of_locally Omega.isOpen fun x hx => ?_
  obtain ⟨R, hR, hRΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hx)
  -- A bump equal to one on `ball x (R / 2)` and supported in `closedBall x R ⊆ Ω`.
  let ζ : ContDiffBump x := ⟨R / 2, R, half_pos hR, half_lt_self hR⟩
  have hts : tsupport ζ ⊆ Omega := ζ.tsupport_eq ▸ hRΩ
  obtain ⟨v, hv, hvu⟩ := exists_mem_wkp0Submodule_value_ae_eq_mul (by norm_num) ζ.contDiff
    ζ.hasCompactSupport hts k u
  -- Extend `ζ u` by zero to the whole space, where the Sobolev embedding applies.
  set w : Wkp (volume : Measure E) ⊤ 2 k := ↑(Wkp0.extendByZeroₗᵢ le_top k ⟨v, hv⟩)
  have hwv : (value k w : E → ℝ) =ᵐ[volume.restrict Omega] value k v := by
    rw [Wkp0.value_extendByZeroₗᵢ]
    exact coeFn_extendByZeroLpₗᵢ_restrict ℝ _ _ _
  have hball : ball x (R / 2) ⊆ Omega := ball_subset_closedBall.trans
    ((closedBall_subset_closedBall (half_le_self hR.le)).trans hRΩ)
  refine ⟨ball x (R / 2), ball_mem_nhds x (half_pos hR), toZeroAtInfty hk w,
    contDiffOn_zero.2 (toZeroAtInfty hk w).continuous.continuousOn, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae_restrict_of_subset hball hvu,
    ae_restrict_of_ae_restrict_of_subset hball hwv,
    ae_restrict_of_ae (value_ae_eq_toZeroAtInfty hk w)] with y hy hvy hwy hzy
  rw [← hzy, hwy, hvy, ζ.one_of_mem_closedBall (ball_subset_closedBall hy), one_mul]

/-- **Interior Sobolev embedding into `Cʲ(Ω)`.** If `2k > dim E`, every `u ∈ W^{k+j,2}(Ω)` agrees
almost everywhere on `Ω` with a function that is `Cʲ` on `Ω`. -/
theorem exists_contDiffOn_ae_eq (hk : finrank ℝ E < 2 * k) :
    ∀ (j : ℕ) (u : Wkp (volume : Measure E) Omega 2 (k + j)),
      ∃ g : E → ℝ, ContDiffOn ℝ j g Omega ∧
        (value (k + j) u : E → ℝ) =ᵐ[volume.restrict Omega] g
  | 0, u => by
    simp_rw [Nat.cast_zero, contDiffOn_zero]
    exact exists_continuousOn_ae_eq hk u
  | j + 1, u => by
    obtain ⟨g, hg, hug⟩ := exists_continuousOn_ae_eq (hk.trans_le (by omega)) u
    let b := stdOrthonormalBasis ℝ E
    -- The weak derivatives along `b` lie in `W^{k+j,2}(Ω)`, so they have `Cʲ` representatives.
    have hd : ∀ i, ∃ gi : E → ℝ, ContDiffOn ℝ j gi Omega ∧
        HasWeakLineDerivOn volume Omega g gi (b i) := by
      intro i
      obtain ⟨d, hd⟩ := exists_hasWeakLineDerivOn_value (k + j) u (b i)
      obtain ⟨gi, hgi, hdgi⟩ := exists_contDiffOn_ae_eq hk j d
      exact ⟨gi, hgi, (hd.congr_ae hug).congr_ae_deriv hdgi⟩
    choose G hG hdG using hd
    -- They assemble into a `Cʲ` weak derivative of `g`.
    set D : E → E →L[ℝ] ℝ := fun y => ∑ i, G i y • innerSL ℝ (b i)
    have hD : ContDiffOn ℝ j D Omega :=
      ContDiffOn.sum fun i _ => (hG i).smul contDiffOn_const
    have hDb : ∀ i y, D y (b i) = G i y := fun i y => by
      simp [D, b.inner_eq_ite]
    have hgD : HasWeakFDerivOn volume Omega g D :=
      b.toBasis.hasWeakFDerivOn_of_forall (hg.locallyIntegrableOn Omega.isOpen.measurableSet)
        fun i => by simpa only [OrthonormalBasis.coe_toBasis, hDb] using hdG i
    exact ⟨g, by exact_mod_cast hgD.contDiffOn_succ hg hD, hug⟩

end Wkp

/-- **Smoothness from all Sobolev orders.** A function that agrees almost everywhere on `Ω` with
an element of `W^{m,2}(Ω)` for every `m` agrees almost everywhere on `Ω` with a function smooth on
`Ω`. -/
theorem exists_contDiffOn_ae_eq_of_forall_wkp {u : E → ℝ}
    (h : ∀ m, ∃ w : Wkp (volume : Measure E) Omega 2 m,
      (Wkp.value m w : E → ℝ) =ᵐ[volume.restrict Omega] u) :
    ∃ g : E → ℝ, ContDiffOn ℝ ∞ g Omega ∧ u =ᵐ[volume.restrict Omega] g := by
  have hk : finrank ℝ E < 2 * (finrank ℝ E + 1) := by omega
  obtain ⟨w, hw⟩ := h (finrank ℝ E + 1)
  obtain ⟨g, hg, hwg⟩ := Wkp.exists_continuousOn_ae_eq hk w
  refine ⟨g, contDiffOn_infty.2 fun j => ?_, hw.symm.trans hwg⟩
  -- The `Cʲ` representative coincides with the continuous one on `Ω`.
  obtain ⟨wj, hwj⟩ := h (finrank ℝ E + 1 + j)
  obtain ⟨gj, hgj, hwgj⟩ := Wkp.exists_contDiffOn_ae_eq hk j wj
  exact hgj.congr (Measure.eqOn_open_of_ae_eq ((hwg.symm.trans hw).trans (hwj.symm.trans hwgj))
    Omega.isOpen hg hgj.continuousOn)

end TauCeti
