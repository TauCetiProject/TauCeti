/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Topology.Baire.Lemmas
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Singular directions of analytic functions

A direction `v` is *singular* for a function `f` at a point `x` if `f` vanishes identically on
the line through `x` in the direction `v`, near `x`: `f (x + ξ • v) = 0` for all small `ξ`.
For an analytic function this is a countable family of equations in the pair `(x, v)`: if `f` has
the power series `p` at `x`, then `f (x + ξ • v) = ∑ₙ ξ ^ n • p n (v, …, v)`, so `v` is singular
exactly when every homogeneous term `p n (v, …, v)` vanishes
(`HasFPowerSeriesAt.eventually_apply_add_smul_eq_zero_iff`). Over a field of characteristic zero,
these terms are the directional derivatives `Dⁿ f (x) (v, …, v) / n!`, and `v` is singular exactly
when all the directional derivatives of `f` at `x` in the direction `v` vanish, starting with the
value `f x` itself (`AnalyticAt.eventually_apply_add_smul_eq_zero_iff`).

At a fixed point `x`, the singular directions of any function analytic at `x` form a closed set
(`AnalyticAt.isClosed_setOf_eventually_apply_add_smul_eq_zero`) invariant under multiplication by
nonzero scalars (`TauCeti.eventually_apply_add_smul_smul_eq_zero_iff`). When `f` does not vanish on
a neighbourhood of `x`, its singular directions have empty interior
(`AnalyticAt.interior_setOf_eventually_apply_add_smul_eq_zero_eq_empty`), so the nonsingular
directions form a dense open set (`AnalyticAt.dense_setOf_not_eventually_apply_add_smul_eq_zero`).
Consequently, a finite family of germs not vanishing near `x` shares an open dense set of
nonsingular directions (`TauCeti.dense_setOf_forall_not_eventually_apply_add_smul_eq_zero`), and a
countable family shares a residual set of nonsingular directions
(`TauCeti.eventually_residual_forall_not_eventually_apply_add_smul_eq_zero`), hence a dense one in
any Baire space. Placing a common nonzero nonsingular direction along a coordinate axis puts any
finite family of non-locally-zero analytic germs simultaneously in Weierstrass general position
(`TauCeti.exists_continuousLinearEquiv_forall_analyticOrderAt_ne_top`,
`TauCeti.exists_continuousLinearEquiv_finSucc_forall_analyticOrderAt_ne_top`).

Where `f` is analytic, the directional derivatives `(x, v) ↦ Dⁿ f (x) (v, …, v)` are analytic
functions of the pair `(x, v)` (`AnalyticOnNhd.iteratedFDeriv_apply_diag`), so the incidence set
of points `x` of a set `s` on a neighbourhood of which `f` is analytic and of directions singular
at `x` is the common zero set in `s × E` of a countable family of analytic functions
(`AnalyticOnNhd.setOf_eventually_apply_add_smul_eq_zero`).

Finally, singular directions of a function of real variables can be detected after
complexification. If `F` is complex analytic at the real point `x` of `ι → ℂ` and agrees with
`f` on the real points near `x`, then a real direction `v` is singular for `f` at `x` exactly when
it is singular for `F` along the complex line through `x`
(`AnalyticAt.eventually_real_apply_add_smul_eq_zero_iff`), so exactly when the complex
directional derivatives `Dⁿ F (x) (v, …, v)` all vanish
(`AnalyticAt.eventually_real_apply_add_smul_eq_zero_iff_iteratedFDeriv`).

## Main results

* `HasFPowerSeriesAt.eventually_apply_add_smul_eq_zero_iff`: `v` is singular for `f` at `x` if
  and only if every term of the power series of `f` at `x` vanishes at `(v, …, v)`.
* `AnalyticAt.isClosed_setOf_eventually_apply_add_smul_eq_zero`,
  `AnalyticAt.interior_setOf_eventually_apply_add_smul_eq_zero_eq_empty`: the singular directions
  at `x` form a closed set, with empty interior when `f` is not locally zero at `x`.
* `TauCeti.dense_setOf_forall_not_eventually_apply_add_smul_eq_zero`,
  `TauCeti.exists_ne_zero_forall_not_eventually_apply_add_smul_eq_zero`: open density and existence
  of common nonzero nonsingular directions for finite families of non-locally-zero analytic germs.
* `TauCeti.eventually_residual_forall_not_eventually_apply_add_smul_eq_zero`,
  `TauCeti.dense_setOf_forall_not_eventually_apply_add_smul_eq_zero_of_countable`: residuality
  and Baire-space density of common nonsingular directions for countable families.
* `TauCeti.exists_continuousLinearEquiv_forall_analyticOrderAt_ne_top`,
  `TauCeti.exists_continuousLinearEquiv_finSucc_forall_analyticOrderAt_ne_top`: simultaneous linear
  general position for finite families of non-locally-zero analytic germs.
* `AnalyticAt.eventually_apply_add_smul_eq_zero_iff`: `v` is singular for `f` at `x` if and only
  if every directional derivative `Dⁿ f (x) (v, …, v)` vanishes.
* `AnalyticOnNhd.iteratedFDeriv_apply_diag`: the directional derivatives are analytic in `(x, v)`.
* `AnalyticOnNhd.setOf_eventually_apply_add_smul_eq_zero`: the incidence set of points and
  singular directions is the common zero set of the directional derivatives.
* `AnalyticAt.eventually_real_apply_add_smul_eq_zero_iff_iteratedFDeriv`: a real direction is
  singular for a function of real variables if and only if all the directional derivatives of its
  complexification vanish.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §2, Lemma 3.
-/

public section

open Filter Set Topology
open scoped ENNReal

namespace TauCeti

/-- Whether `f` vanishes near `x` on the line through `x` in the direction `v` does not change
when `v` is rescaled by a nonzero scalar. -/
theorem eventually_apply_add_smul_smul_eq_zero_iff {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Zero F] {f : E → F} {x v : E} {c : 𝕜} (hc : c ≠ 0) :
    (∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • c • v) = 0) ↔ ∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • v) = 0 := by
  have h : map (· * c) (𝓝 (0 : 𝕜)) = 𝓝 0 := by
    simpa using (Homeomorph.mulRight₀ c hc).map_nhds_eq 0
  conv_rhs => rw [← h, eventually_map]
  simp only [smul_smul]

end TauCeti

section NontriviallyNormedField

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {x v : E}

/-- If the homogeneous polynomial `v ↦ m (v, …, v)` associated to a continuous multilinear map
vanishes near a point `v₀`, then it vanishes on the whole space. -/
private theorem continuousMultilinearMap_apply_diag_eq_zero_of_eventuallyEq {n : ℕ}
    {m : E [×n]→L[𝕜] F} {v₀ : E} (h : (fun v ↦ m fun _ ↦ v) =ᶠ[𝓝 v₀] 0) (v : E) :
    (m fun _ ↦ v) = 0 := by
  let q : FormalMultilinearSeries 𝕜 E F := fun k ↦ if hk : k = n then hk ▸ m else 0
  have hq₀ : HasFiniteFPowerSeriesOnBall (fun y ↦ m fun _ ↦ y) q 0 (n + 1) ⊤ := by
    refine .mk' (fun k hk ↦ dite_eq_right (by omega)) ENNReal.zero_lt_top fun y _ ↦ ?_
    rw [Finset.sum_eq_single_of_mem n (Finset.self_mem_range_succ n)
      fun k _ hkn ↦ by simp [q, hkn]]
    simp [q]
  have hq : HasFPowerSeriesOnBall (fun y ↦ m fun _ ↦ y) (q.changeOrigin v₀) v₀ ⊤ := by
    simpa using (hq₀.changeOrigin (y := v₀) ENNReal.coe_lt_top).toHasFPowerSeriesOnBall
  have hzero : HasFPowerSeriesAt 0 (q.changeOrigin v₀) v₀ := hq.hasFPowerSeriesAt.congr h
  have hsum : HasSum (fun k ↦ q.changeOrigin v₀ k fun _ ↦ v - v₀) 0 := by
    convert hasSum_zero (α := F) using 1
    ext k
    exact hzero.apply_eq_zero k (v - v₀)
  exact (hq.hasSum_sub (Metric.mem_eball.2 (edist_lt_top v v₀))).unique hsum

namespace HasFPowerSeriesAt

/-- **Singular directions and power series.** If `f` has the power series `p` at `x`, then `f`
vanishes near `x` on the line through `x` in the direction `v` if and only if every homogeneous
term `p n` of the series vanishes at `(v, …, v)`. -/
theorem eventually_apply_add_smul_eq_zero_iff {p : FormalMultilinearSeries 𝕜 E F}
    (hf : HasFPowerSeriesAt f p x) :
    (∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • v) = 0) ↔ ∀ n, p n (fun _ ↦ v) = 0 := by
  set u : 𝕜 →L[𝕜] E := (ContinuousLinearMap.id 𝕜 𝕜).smulRight v
  -- the restriction of `f` to the line has the power series `p` composed with `ξ ↦ ξ • v`
  have h0 : HasFPowerSeriesAt (fun z ↦ f (x + z)) p (u 0) := by
    rw [map_zero]
    convert hf.comp_sub (-x) using 1
    · ext z
      rw [sub_neg_eq_add, add_comm]
    · rw [add_neg_cancel]
  have hline : HasFPowerSeriesAt (fun ξ : 𝕜 ↦ f (x + ξ • v)) (p.compContinuousLinearMap u) 0 :=
    h0.compContinuousLinearMap
  have hcoeff (n : ℕ) : p.compContinuousLinearMap u n (fun _ ↦ 1) = p n (fun _ ↦ v) := by
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
    congr 1
    ext
    simp [u]
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · rw [← hcoeff, hline.eq_zero_of_eventually h]
    simp
  · have hzero : p.compContinuousLinearMap u = 0 := by
      ext n : 1
      rw [← ContinuousMultilinearMap.mkPiRing_apply_one_eq_self (p.compContinuousLinearMap u n)]
      ext
      simp [hcoeff, h]
    exact (hzero ▸ hline).eventually_eq_zero

end HasFPowerSeriesAt

namespace AnalyticAt

/-- The directions singular for a function analytic at `x` form a closed set. -/
theorem isClosed_setOf_eventually_apply_add_smul_eq_zero (hf : AnalyticAt 𝕜 f x) :
    IsClosed {v | ∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • v) = 0} := by
  obtain ⟨p, r, hp⟩ := hf
  simp_rw [hp.hasFPowerSeriesAt.eventually_apply_add_smul_eq_zero_iff, ofPred_forall]
  exact isClosed_iInter fun n ↦ isClosed_eq
    ((p n).coe_continuous.comp (continuous_pi fun _ ↦ continuous_id)) continuous_const

/-- The directions nonsingular for a function analytic at `x` form an open set. -/
theorem isOpen_setOf_not_eventually_apply_add_smul_eq_zero (hf : AnalyticAt 𝕜 f x) :
    IsOpen {v | ¬ ∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • v) = 0} :=
  hf.isClosed_setOf_eventually_apply_add_smul_eq_zero.isOpen_compl

/-- If `f` is analytic at `x` and does not vanish on a neighbourhood of `x`, then its singular
directions at `x` have empty interior. -/
theorem interior_setOf_eventually_apply_add_smul_eq_zero_eq_empty (hf : AnalyticAt 𝕜 f x)
    (h0 : ¬ f =ᶠ[𝓝 x] 0) :
    interior {v | ∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • v) = 0} = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun v₀ hv₀ ↦ h0 ?_
  obtain ⟨p, r, hp⟩ := hf
  have hmem : ∀ᶠ v in 𝓝 v₀, ∀ n, p n (fun _ ↦ v) = 0 := by
    filter_upwards [mem_interior_iff_mem_nhds.1 hv₀] with v hv
    exact (hp.hasFPowerSeriesAt.eventually_apply_add_smul_eq_zero_iff.1 hv)
  have hdiag (n : ℕ) (y : E) : p n (fun _ ↦ y) = 0 :=
    continuousMultilinearMap_apply_diag_eq_zero_of_eventuallyEq
      (hmem.mono fun v hv ↦ hv n) y
  filter_upwards [Metric.isOpen_eball.mem_nhds (Metric.mem_eball_self hp.r_pos)] with z hz
  have hsum : HasSum (fun n ↦ p n fun _ ↦ z - x) 0 := by
    convert hasSum_zero (α := F) using 1
    ext n
    exact hdiag n (z - x)
  exact (hp.hasSum_sub hz).unique hsum

/-- If `f` is analytic at `x` and does not vanish on a neighbourhood of `x`, then its singular
directions at `x` form a nowhere dense closed set. -/
theorem isNowhereDense_setOf_eventually_apply_add_smul_eq_zero (hf : AnalyticAt 𝕜 f x)
    (h0 : ¬ f =ᶠ[𝓝 x] 0) :
    IsNowhereDense {v | ∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • v) = 0} := by
  rw [IsNowhereDense, hf.isClosed_setOf_eventually_apply_add_smul_eq_zero.closure_eq,
    hf.interior_setOf_eventually_apply_add_smul_eq_zero_eq_empty h0]

/-- If `f` is analytic at `x` and does not vanish on a neighbourhood of `x`, then its nonsingular
directions at `x` form a dense open set. -/
theorem dense_setOf_not_eventually_apply_add_smul_eq_zero (hf : AnalyticAt 𝕜 f x)
    (h0 : ¬ f =ᶠ[𝓝 x] 0) :
    Dense {v | ¬ ∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • v) = 0} := by
  rw [show {v | ¬ ∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • v) = 0} =
      {v | ∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • v) = 0}ᶜ from rfl,
    dense_iff_closure_eq, closure_compl,
    hf.interior_setOf_eventually_apply_add_smul_eq_zero_eq_empty h0, compl_empty]

section CharZero

variable [CharZero 𝕜] [CompleteSpace F]

/-- **Singular directions and directional derivatives.** A function `f` analytic at `x` vanishes
near `x` on the line through `x` in the direction `v` if and only if all its directional
derivatives `Dⁿ f (x) (v, …, v)` vanish, including the value `f x` for `n = 0`. -/
theorem eventually_apply_add_smul_eq_zero_iff (hf : AnalyticAt 𝕜 f x) :
    (∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • v) = 0) ↔ ∀ n, iteratedFDeriv 𝕜 n f x (fun _ ↦ v) = 0 := by
  obtain ⟨p, r, hp⟩ := hf
  rw [hp.hasFPowerSeriesAt.eventually_apply_add_smul_eq_zero_iff]
  refine forall_congr' fun n ↦ ?_
  rw [← hp.factorial_smul v n, ← Nat.cast_smul_eq_nsmul 𝕜, smul_eq_zero,
    or_iff_right (Nat.cast_ne_zero.2 n.factorial_ne_zero)]

end CharZero

end AnalyticAt

namespace TauCeti

section Families

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]
  {g : ∀ i, E → G i}

/-- The common nonsingular directions at `x` of a finite family of functions analytic at `x` form
an open set. -/
theorem isOpen_setOf_forall_not_eventually_apply_add_smul_eq_zero [Finite ι]
    (hg : ∀ i, AnalyticAt 𝕜 (g i) x) :
    IsOpen {v | ∀ i, ¬ ∀ᶠ ξ in 𝓝 (0 : 𝕜), g i (x + ξ • v) = 0} := by
  rw [ofPred_forall]
  exact isOpen_iInter_of_finite fun i ↦ (hg i).isOpen_setOf_not_eventually_apply_add_smul_eq_zero

/-- The common nonsingular directions at `x` of a finite family of functions analytic at `x`, none
of which vanishes on a neighbourhood of `x`, form a dense open set. -/
theorem dense_setOf_forall_not_eventually_apply_add_smul_eq_zero [Finite ι]
    (hg : ∀ i, AnalyticAt 𝕜 (g i) x) (h0 : ∀ i, ¬ g i =ᶠ[𝓝 x] 0) :
    Dense {v | ∀ i, ¬ ∀ᶠ ξ in 𝓝 (0 : 𝕜), g i (x + ξ • v) = 0} := by
  classical
  cases nonempty_fintype ι
  suffices ∀ s : Finset ι,
      IsOpen {v | ∀ i ∈ s, ¬ ∀ᶠ ξ in 𝓝 (0 : 𝕜), g i (x + ξ • v) = 0} ∧
        Dense {v | ∀ i ∈ s, ¬ ∀ᶠ ξ in 𝓝 (0 : 𝕜), g i (x + ξ • v) = 0} by
    simpa using (this Finset.univ).2
  intro s
  induction s using Finset.induction_on with
  | empty => simp [dense_univ]
  | insert i s _ ih =>
    have heq : {v | ∀ j ∈ insert i s, ¬ ∀ᶠ ξ in 𝓝 (0 : 𝕜), g j (x + ξ • v) = 0} =
        {v | ¬ ∀ᶠ ξ in 𝓝 (0 : 𝕜), g i (x + ξ • v) = 0} ∩
          {v | ∀ j ∈ s, ¬ ∀ᶠ ξ in 𝓝 (0 : 𝕜), g j (x + ξ • v) = 0} := by
      ext v
      simp
    rw [heq]
    have ho := (hg i).isOpen_setOf_not_eventually_apply_add_smul_eq_zero
    have hd := (hg i).dense_setOf_not_eventually_apply_add_smul_eq_zero (h0 i)
    exact ⟨ho.inter ih.1, hd.inter_of_isOpen_left ih.2 ho⟩

/-- Every finite family of functions analytic at `x` on a nontrivial normed space, none of which
vanishes on a neighbourhood of `x`, admits a common nonzero nonsingular direction at `x`. -/
theorem exists_ne_zero_forall_not_eventually_apply_add_smul_eq_zero [Nontrivial E] [Finite ι]
    (hg : ∀ i, AnalyticAt 𝕜 (g i) x) (h0 : ∀ i, ¬ g i =ᶠ[𝓝 x] 0) :
    ∃ v ≠ 0, ∀ i, ¬ ∀ᶠ ξ in 𝓝 (0 : 𝕜), g i (x + ξ • v) = 0 := by
  obtain ⟨v, hv, hv0⟩ :=
    (dense_setOf_forall_not_eventually_apply_add_smul_eq_zero hg h0).exists_mem_open
      isOpen_compl_singleton (Set.nonempty_compl_of_nontrivial 0)
  exact ⟨v, hv0, hv⟩

/-- The common nonsingular directions at `x` of a countable family of functions analytic at `x`,
none of which vanishes on a neighbourhood of `x`, form a residual set in `E`. -/
theorem eventually_residual_forall_not_eventually_apply_add_smul_eq_zero [Countable ι]
    (hg : ∀ i, AnalyticAt 𝕜 (g i) x) (h0 : ∀ i, ¬ g i =ᶠ[𝓝 x] 0) :
    ∀ᶠ v in residual E, ∀ i, ¬ ∀ᶠ ξ in 𝓝 (0 : 𝕜), g i (x + ξ • v) = 0 := by
  rw [eventually_countable_forall]
  exact fun i ↦ residual_of_dense_open
    (hg i).isOpen_setOf_not_eventually_apply_add_smul_eq_zero
    ((hg i).dense_setOf_not_eventually_apply_add_smul_eq_zero (h0 i))

/-- In a Baire normed space, the common nonsingular directions at `x` of a countable family of
functions analytic at `x`, none of which vanishes on a neighbourhood of `x`, form a dense set. -/
theorem dense_setOf_forall_not_eventually_apply_add_smul_eq_zero_of_countable [BaireSpace E]
    [Countable ι] (hg : ∀ i, AnalyticAt 𝕜 (g i) x) (h0 : ∀ i, ¬ g i =ᶠ[𝓝 x] 0) :
    Dense {v | ∀ i, ¬ ∀ᶠ ξ in 𝓝 (0 : 𝕜), g i (x + ξ • v) = 0} :=
  dense_of_mem_residual (eventually_residual_forall_not_eventually_apply_add_smul_eq_zero hg h0)

end Families

section GeneralPosition

/-- **Simultaneous Weierstrass general position on `E × 𝕜`.** Let `f i` be a finite family of
functions analytic at `p : E × 𝕜`, none of which vanishes on a neighbourhood of `p`. If continuous
linear forms separate points of `E × 𝕜` (for instance when `RCLike 𝕜`), there is a continuous
linear equivalence `L : (E × 𝕜) ≃L[𝕜] (E × 𝕜)` such that every `f i ∘ L` has finite analytic order
along the vertical coordinate at `L.symm p`. -/
theorem exists_continuousLinearEquiv_forall_analyticOrderAt_ne_top [SeparatingDual 𝕜 (E × 𝕜)]
    {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
    [∀ i, NormedSpace 𝕜 (G i)] {f : ∀ i, E × 𝕜 → G i} {p : E × 𝕜}
    (hf : ∀ i, AnalyticAt 𝕜 (f i) p) (h0 : ∀ i, ¬ f i =ᶠ[𝓝 p] 0) :
    ∃ L : (E × 𝕜) ≃L[𝕜] (E × 𝕜),
      ∀ i, analyticOrderAt (fun t ↦ f i (L ((L.symm p).1, t))) (L.symm p).2 ≠ ⊤ := by
  have : Nontrivial (E × 𝕜) := ⟨(0, 1), 0, by simp⟩
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_forall_not_eventually_apply_add_smul_eq_zero hf h0
  obtain ⟨L, hL⟩ := SeparatingDual.exists_continuousLinearEquiv_apply_eq
    (R := 𝕜) (x := ((0 : E), (1 : 𝕜))) (y := v) (by simp) hv0
  refine ⟨L, fun i htop ↦ hv i ?_⟩
  rw [analyticOrderAt_eq_top] at htop
  have hnhds : map (· + (L.symm p).2) (𝓝 (0 : 𝕜)) = 𝓝 (L.symm p).2 := by simp
  filter_upwards [(eventually_map.1 (hnhds ▸ htop))] with ξ hξ
  have hline : L ((L.symm p).1, ξ + (L.symm p).2) = p + ξ • v := by
    have hpt : ((L.symm p).1, ξ + (L.symm p).2) = L.symm p + ξ • ((0 : E), (1 : 𝕜)) := by
      ext <;> simp [add_comm]
    rw [hpt, map_add, map_smul, L.apply_symm_apply, hL]
  rwa [← hline]

/-- **Simultaneous Weierstrass general position on `Fin (n + 1) → 𝕜`.** For any finite family of
functions `f i` analytic at `p : Fin (n + 1) → 𝕜`, none of which vanishes on a neighbourhood of
`p`, there is a continuous linear equivalence `L : (Fin (n + 1) → 𝕜) ≃L[𝕜] (Fin (n + 1) → 𝕜)` such
that every `f i ∘ L` has finite analytic order in the `0`-th coordinate at `L.symm p`. -/
theorem exists_continuousLinearEquiv_finSucc_forall_analyticOrderAt_ne_top {n : ℕ}
    {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
    [∀ i, NormedSpace 𝕜 (G i)] {f : ∀ i, (Fin (n + 1) → 𝕜) → G i} {p : Fin (n + 1) → 𝕜}
    (hf : ∀ i, AnalyticAt 𝕜 (f i) p) (h0 : ∀ i, ¬ f i =ᶠ[𝓝 p] 0) :
    ∃ L : (Fin (n + 1) → 𝕜) ≃L[𝕜] (Fin (n + 1) → 𝕜),
      ∀ i, analyticOrderAt (fun t ↦ f i (L (Fin.cons t (Fin.tail (L.symm p)))))
        (L.symm p 0) ≠ ⊤ := by
  have : SeparatingDual 𝕜 (Fin (n + 1) → 𝕜) :=
    ⟨fun y hy ↦ let ⟨j, hj⟩ := Function.ne_iff.1 hy; ⟨ContinuousLinearMap.proj j, hj⟩⟩
  have : Nontrivial (Fin (n + 1) → 𝕜) := ⟨Fin.cons 1 0, 0, fun h ↦ one_ne_zero (congrFun h 0)⟩
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_forall_not_eventually_apply_add_smul_eq_zero hf h0
  obtain ⟨L, hL⟩ := SeparatingDual.exists_continuousLinearEquiv_apply_eq
    (R := 𝕜) (x := Fin.cons (1 : 𝕜) (0 : Fin n → 𝕜)) (y := v)
    (fun h ↦ one_ne_zero (congrFun h 0)) hv0
  refine ⟨L, fun i htop ↦ hv i ?_⟩
  rw [analyticOrderAt_eq_top] at htop
  have hnhds : map (· + L.symm p 0) (𝓝 (0 : 𝕜)) = 𝓝 (L.symm p 0) := by simp
  filter_upwards [(eventually_map.1 (hnhds ▸ htop))] with ξ hξ
  have hline : L (Fin.cons (ξ + L.symm p 0) (Fin.tail (L.symm p))) = p + ξ • v := by
    have hpt : Fin.cons (ξ + L.symm p 0) (Fin.tail (L.symm p)) =
        L.symm p + ξ • Fin.cons (1 : 𝕜) (0 : Fin n → 𝕜) := by
      ext j
      refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp [Fin.tail, add_comm]
    rw [hpt, map_add, map_smul, L.apply_symm_apply, hL]
  rwa [← hline]

end GeneralPosition

end TauCeti

namespace AnalyticOnNhd

variable [CompleteSpace F] {s : Set E}

/-- The directional derivatives `(x, v) ↦ Dⁿ f (x) (v, …, v)` of a function analytic on a
neighbourhood of `s` are analytic in the pair `(x, v)` on a neighbourhood of `s ×ˢ univ`. -/
theorem iteratedFDeriv_apply_diag (hf : AnalyticOnNhd 𝕜 f s) (n : ℕ) :
    AnalyticOnNhd 𝕜 (fun q : E × E ↦ iteratedFDeriv 𝕜 n f q.1 fun _ ↦ q.2) (s ×ˢ univ) := by
  intro q hq
  have happly : AnalyticAt 𝕜 (fun r : (E [×n]→L[𝕜] F) × (Fin n → E) ↦ r.1 r.2)
      (iteratedFDeriv 𝕜 n f q.1, fun _ ↦ q.2) := by
    simpa using (ContinuousLinearMap.id 𝕜 (E [×n]→L[𝕜] F)).analyticAt_uncurry_of_multilinear
      (x := (iteratedFDeriv 𝕜 n f q.1, fun _ ↦ q.2))
  have hdiag : AnalyticAt 𝕜 (fun q : E × E ↦ fun _ : Fin n ↦ q.2) q :=
    analyticAt_pi_iff.2 fun _ ↦ analyticAt_snd
  have hpair : AnalyticAt 𝕜 (fun q : E × E ↦ (iteratedFDeriv 𝕜 n f q.1, fun _ : Fin n ↦ q.2)) q :=
    (((hf.iteratedFDeriv n) q.1 hq.1).comp analyticAt_fst).prod hdiag
  exact happly.comp_of_eq hpair rfl

variable [CharZero 𝕜]

/-- **The incidence set of singular directions.** For `f` analytic on a neighbourhood of `s`, the
pairs `(x, v)` with `x ∈ s` such that `f` vanishes near `x` on the line through `x` in the direction
`v` are the common zeros in `s ×ˢ univ` of the directional derivatives
`(x, v) ↦ Dⁿ f (x) (v, …, v)`, which are analytic by `AnalyticOnNhd.iteratedFDeriv_apply_diag`. -/
theorem setOf_eventually_apply_add_smul_eq_zero (hf : AnalyticOnNhd 𝕜 f s) :
    {q : E × E | q.1 ∈ s ∧ ∀ᶠ ξ in 𝓝 (0 : 𝕜), f (q.1 + ξ • q.2) = 0} =
      s ×ˢ univ ∩ ⋂ n, {q | iteratedFDeriv 𝕜 n f q.1 (fun _ ↦ q.2) = 0} := by
  ext q
  simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, and_true, mem_iInter]
  exact and_congr_right fun hq ↦ (hf q.1 hq).eventually_apply_add_smul_eq_zero_iff

end AnalyticOnNhd

end NontriviallyNormedField

section Complexification

variable {ι G : Type*} [Fintype ι] [NormedAddCommGroup G] [NormedSpace ℂ G]
  {F : (ι → ℂ) → G} {f : (ι → ℝ) → G} {x v : ι → ℝ}

namespace AnalyticAt

/-- **Singular directions after complexification.** Let `F` be complex analytic at the real point
`x` of `ι → ℂ` and agree with `f` at the real points near `x`. Then `f` vanishes near `x` on the
real line through `x` in the real direction `v` if and only if `F` vanishes near `x` on the complex
line through `x` in the direction `v`. -/
theorem eventually_real_apply_add_smul_eq_zero_iff (hF : AnalyticAt ℂ F fun i ↦ (x i : ℂ))
    (hFf : ∀ᶠ y in 𝓝 x, F (fun i ↦ (y i : ℂ)) = f y) :
    (∀ᶠ ξ in 𝓝 (0 : ℝ), f (x + ξ • v) = 0) ↔
      ∀ᶠ ζ in 𝓝 (0 : ℂ), F ((fun i ↦ (x i : ℂ)) + ζ • fun i ↦ (v i : ℂ)) = 0 := by
  set g : ℂ → G := fun ζ ↦ F ((fun i ↦ (x i : ℂ)) + ζ • fun i ↦ (v i : ℂ))
  have hg : AnalyticAt ℂ g 0 := by
    refine hF.comp_of_eq (analyticAt_const.add (analyticAt_id.smul analyticAt_const)) ?_
    simp
  -- on the real points of the complex line, `g` is the restriction of `f` to the real line
  have hline : Tendsto (fun ξ : ℝ ↦ x + ξ • v) (𝓝 0) (𝓝 x) := by
    have hcont : Continuous fun ξ : ℝ ↦ x + ξ • v := by fun_prop
    simpa using hcont.tendsto 0
  have hgf : ∀ᶠ ξ : ℝ in 𝓝 0, g ξ = f (x + ξ • v) := by
    filter_upwards [hline.eventually hFf] with ξ hξ
    rw [← hξ]
    simp only [g]
    congr 1
    funext i
    simp
  have hreal : Tendsto (fun ξ : ℝ ↦ (ξ : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) :=
    Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun ξ hξ ↦ by
      simpa using hξ
  refine ⟨fun h ↦ hg.frequently_zero_iff_eventually_zero.1 ?_, fun h ↦ ?_⟩
  · refine hreal.frequently (Eventually.frequently ?_)
    filter_upwards [nhdsWithin_le_nhds (h.and hgf)] with ξ ⟨hξ, hgξ⟩
    rw [hgξ, hξ]
  · filter_upwards [Complex.continuous_ofReal.tendsto' 0 0 Complex.ofReal_zero |>.eventually h,
      hgf] with ξ hξ hgξ
    rw [← hgξ]
    exact hξ

/-- **Singular directions and complex directional derivatives.** Let `F` be complex analytic at
the real point `x` of `ι → ℂ` and agree with `f` at the real points near `x`. Then `f` vanishes
near `x` on the real line through `x` in the real direction `v` if and only if all the complex
directional derivatives `Dⁿ F (x) (v, …, v)` vanish. -/
theorem eventually_real_apply_add_smul_eq_zero_iff_iteratedFDeriv [CompleteSpace G]
    (hF : AnalyticAt ℂ F fun i ↦ (x i : ℂ)) (hFf : ∀ᶠ y in 𝓝 x, F (fun i ↦ (y i : ℂ)) = f y) :
    (∀ᶠ ξ in 𝓝 (0 : ℝ), f (x + ξ • v) = 0) ↔
      ∀ n, iteratedFDeriv ℂ n F (fun i ↦ (x i : ℂ)) (fun _ ↦ fun i ↦ (v i : ℂ)) = 0 := by
  rw [hF.eventually_real_apply_add_smul_eq_zero_iff hFf, hF.eventually_apply_add_smul_eq_zero_iff]

end AnalyticAt

end Complexification
