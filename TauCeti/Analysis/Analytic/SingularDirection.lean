/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Algebra.Module.Equiv.Pi
-- Proof-only: `Set.Finite.dense_sInter` for finite intersections of dense open sets.
import Mathlib.Topology.Baire.Lemmas
import TauCeti.Analysis.Analytic.Constructions
import TauCeti.Analysis.Analytic.Uniqueness

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
directions form an open (`AnalyticAt.isOpen_setOf_not_eventually_apply_add_smul_eq_zero`) and dense
(`AnalyticAt.dense_setOf_not_eventually_apply_add_smul_eq_zero`) set. Consequently, a finite family
of germs not vanishing near `x` shares an open
(`TauCeti.isOpen_setOf_forall_not_eventually_apply_add_smul_eq_zero`) and dense
(`TauCeti.dense_setOf_forall_not_eventually_apply_add_smul_eq_zero`) set of nonsingular directions.
Picking a common nonsingular direction with nonzero vertical component and applying an explicit
linear shear puts any finite family of non-locally-zero analytic germs simultaneously in
Weierstrass general position (`TauCeti.exists_continuousLinearEquiv_forall_analyticOrderAt_ne_top`,
`TauCeti.exists_continuousLinearEquiv_finSucc_forall_analyticOrderAt_ne_top`). This generalizes
the single-germ `RCLike` general-position theorem formerly proved via `SeparatingDual` in
`TauCeti.Analysis.Analytic.Uniqueness`, which is retained here as the `Unit`-indexed corollary
`AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top` over any nontrivially normed
field.

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
* `TauCeti.isOpen_setOf_forall_not_eventually_apply_add_smul_eq_zero`,
  `TauCeti.dense_setOf_forall_not_eventually_apply_add_smul_eq_zero`,
  `TauCeti.exists_ne_zero_forall_not_eventually_apply_add_smul_eq_zero`: openness, density, and
  existence of common nonzero nonsingular directions for finite families of non-locally-zero
  analytic germs.
* `TauCeti.exists_continuousLinearEquiv_forall_analyticOrderAt_ne_top`,
  `AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`,
  `TauCeti.exists_continuousLinearEquiv_finSucc_forall_analyticOrderAt_ne_top`: simultaneous and
  single-germ linear general position for finite families of non-locally-zero analytic germs.
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
* S. Łojasiewicz, *Ensembles semi-analytiques*, IHÉS, 1965, §15 (Weierstrass general position).
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §6.1.
* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B.
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

namespace HasFPowerSeriesAt

/-- **Singular directions and power series.** If `f` has the power series `p` at `x`, then `f`
vanishes near `x` on the line through `x` in the direction `v` if and only if every homogeneous
term `p n` of the series vanishes at `(v, …, v)`. -/
theorem eventually_apply_add_smul_eq_zero_iff {p : FormalMultilinearSeries 𝕜 E F}
    (hf : HasFPowerSeriesAt f p x) :
    (∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • v) = 0) ↔ ∀ n, p n (fun _ ↦ v) = 0 := by
  obtain ⟨r, hr⟩ := hf
  have hline : HasFPowerSeriesAt (fun ξ : 𝕜 ↦ f (x + ξ • v))
      (p.compContinuousLinearMap (ContinuousLinearMap.toSpanSingleton 𝕜 v)) 0 :=
    (hr.comp_add_smul v).hasFPowerSeriesAt
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · rw [← p.compContinuousLinearMap_toSpanSingleton_apply_one v n, hline.eq_zero_of_eventually h]
    simp
  · have hzero : p.compContinuousLinearMap (ContinuousLinearMap.toSpanSingleton 𝕜 v) = 0 := by
      ext n : 1
      rw [← ContinuousMultilinearMap.mkPiRing_apply_one_eq_self
        (p.compContinuousLinearMap (ContinuousLinearMap.toSpanSingleton 𝕜 v) n)]
      ext
      simp [p.compContinuousLinearMap_toSpanSingleton_apply_one, h]
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
    (p n).apply_diag_eq_zero_of_eventuallyEq (hmem.mono fun v hv ↦ hv n) y
  filter_upwards [Metric.isOpen_eball.mem_nhds (Metric.mem_eball_self hp.r_pos)] with z hz
  have hsum : HasSum (fun n ↦ p n fun _ ↦ z - x) 0 := by
    convert hasSum_zero (α := F) using 1
    ext n
    exact hdiag n (z - x)
  exact (hp.hasSum_sub hz).unique hsum

/-- If `f` is analytic at `x` and does not vanish on a neighbourhood of `x`, then its singular
directions at `x` form a nowhere dense set. -/
theorem isNowhereDense_setOf_eventually_apply_add_smul_eq_zero (hf : AnalyticAt 𝕜 f x)
    (h0 : ¬ f =ᶠ[𝓝 x] 0) :
    IsNowhereDense {v | ∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • v) = 0} := by
  rw [IsNowhereDense, hf.isClosed_setOf_eventually_apply_add_smul_eq_zero.closure_eq,
    hf.interior_setOf_eventually_apply_add_smul_eq_zero_eq_empty h0]

/-- If `f` is analytic at `x` and does not vanish on a neighbourhood of `x`, then its nonsingular
directions at `x` form a dense set. -/
theorem dense_setOf_not_eventually_apply_add_smul_eq_zero (hf : AnalyticAt 𝕜 f x)
    (h0 : ¬ f =ᶠ[𝓝 x] 0) :
    Dense {v | ¬ ∀ᶠ ξ in 𝓝 (0 : 𝕜), f (x + ξ • v) = 0} := by
  rw [← compl_ofPred, ← interior_eq_empty_iff_dense_compl]
  exact hf.interior_setOf_eventually_apply_add_smul_eq_zero_eq_empty h0

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
of which vanishes on a neighbourhood of `x`, form a dense set. -/
theorem dense_setOf_forall_not_eventually_apply_add_smul_eq_zero [Finite ι]
    (hg : ∀ i, AnalyticAt 𝕜 (g i) x) (h0 : ∀ i, ¬ g i =ᶠ[𝓝 x] 0) :
    Dense {v | ∀ i, ¬ ∀ᶠ ξ in 𝓝 (0 : 𝕜), g i (x + ξ • v) = 0} := by
  rw [ofPred_forall, ← sInter_range]
  exact (finite_range _).dense_sInter
    (forall_mem_range.2 fun i ↦ (hg i).isOpen_setOf_not_eventually_apply_add_smul_eq_zero)
    (forall_mem_range.2 fun i ↦ (hg i).dense_setOf_not_eventually_apply_add_smul_eq_zero (h0 i))

/-- Every finite family of functions analytic at `x` on a nontrivial normed space, none of which
vanishes on a neighbourhood of `x`, admits a common nonzero nonsingular direction at `x`. -/
theorem exists_ne_zero_forall_not_eventually_apply_add_smul_eq_zero [Nontrivial E] [Finite ι]
    (hg : ∀ i, AnalyticAt 𝕜 (g i) x) (h0 : ∀ i, ¬ g i =ᶠ[𝓝 x] 0) :
    ∃ v ≠ 0, ∀ i, ¬ ∀ᶠ ξ in 𝓝 (0 : 𝕜), g i (x + ξ • v) = 0 := by
  obtain ⟨v, hv, hv0⟩ :=
    (dense_setOf_forall_not_eventually_apply_add_smul_eq_zero hg h0).exists_mem_open
      isOpen_compl_singleton (Set.nonempty_compl_of_nontrivial 0)
  exact ⟨v, hv0, hv⟩

end Families

section GeneralPosition

/-- **Simultaneous Weierstrass general position on `E × 𝕜`.** Let `f i` be a finite family of
functions analytic at `p : E × 𝕜`, none of which vanishes on a neighbourhood of `p`. There is a
continuous linear equivalence `L : (E × 𝕜) ≃L[𝕜] (E × 𝕜)` such that every `f i ∘ L` has finite
analytic order along the vertical coordinate at `L.symm p`. -/
theorem exists_continuousLinearEquiv_forall_analyticOrderAt_ne_top {ι : Type*} [Finite ι]
    {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]
    {f : ∀ i, E × 𝕜 → G i} {p : E × 𝕜}
    (hf : ∀ i, AnalyticAt 𝕜 (f i) p) (h0 : ∀ i, ¬ f i =ᶠ[𝓝 p] 0) :
    ∃ L : (E × 𝕜) ≃L[𝕜] (E × 𝕜),
      ∀ i, analyticOrderAt (fun t ↦ f i (L ((L.symm p).1, t))) (L.symm p).2 ≠ ⊤ := by
  -- Choose a common nonsingular direction with nonzero vertical component and normalize it.
  have hopen : IsOpen {v : E × 𝕜 | v.2 ≠ 0} := isOpen_compl_singleton.preimage continuous_snd
  obtain ⟨v, hv, hv2⟩ :=
    (dense_setOf_forall_not_eventually_apply_add_smul_eq_zero hf h0).exists_mem_open hopen
      ⟨(0, 1), by simp⟩
  set u : E := v.2⁻¹ • v.1
  have hv' (i : ι) : ¬ ∀ᶠ ξ in 𝓝 (0 : 𝕜), f i (p + ξ • (u, (1 : 𝕜))) = 0 := by
    have hvu : v.2⁻¹ • v = (u, (1 : 𝕜)) := by
      ext <;> simp [u, inv_mul_cancel₀ hv2]
    rw [← hvu, eventually_apply_add_smul_smul_eq_zero_iff (inv_ne_zero hv2)]
    exact hv i
  -- Apply the vertical shear `(x, t) ↦ (x + t • u, t)`, sending `(0, 1)` to `(u, 1)`.
  let c : (E × 𝕜) ≃L[𝕜] (𝕜 × E) := ContinuousLinearEquiv.prodComm 𝕜 E 𝕜
  let L : (E × 𝕜) ≃L[𝕜] (E × 𝕜) :=
    c.trans (((ContinuousLinearEquiv.refl 𝕜 𝕜).skewProd (ContinuousLinearEquiv.refl 𝕜 E)
      ((ContinuousLinearMap.id 𝕜 𝕜).smulRight u)).trans c.symm)
  refine ⟨L, fun i htop ↦ hv' i ?_⟩
  rw [analyticOrderAt_eq_top] at htop
  have hnhds : map (· + (L.symm p).2) (𝓝 (0 : 𝕜)) = 𝓝 (L.symm p).2 := by simp
  filter_upwards [(eventually_map.1 (hnhds ▸ htop))] with ξ hξ
  have hline : L ((L.symm p).1, ξ + (L.symm p).2) = p + ξ • (u, (1 : 𝕜)) := by
    have hpt : ((L.symm p).1, ξ + (L.symm p).2) = L.symm p + ξ • ((0 : E), (1 : 𝕜)) := by
      ext <;> simp [add_comm]
    rw [hpt, map_add, map_smul, L.apply_symm_apply]
    simp [L, c]
  rwa [← hline]

/-- **General position in the last variable.** A function analytic at `p` on `E × 𝕜` that does not
vanish near `p` becomes regular in the last variable after a linear change of coordinates: there
are a continuous linear automorphism `L` and a point `q` with `L q = p` such that
`t ↦ f (L (q.1, t))` has finite analytic order at `q.2`. -/
theorem _root_.AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top {f : E × 𝕜 → F}
    {p : E × 𝕜} (hf : AnalyticAt 𝕜 f p) (hf0 : ¬ f =ᶠ[𝓝 p] 0) :
    ∃ (L : (E × 𝕜) ≃L[𝕜] E × 𝕜) (q : E × 𝕜), L q = p ∧
      analyticOrderAt (fun t ↦ f (L (q.1, t))) q.2 ≠ ⊤ := by
  obtain ⟨L, hL⟩ := exists_continuousLinearEquiv_forall_analyticOrderAt_ne_top
    (f := fun _ : Unit ↦ f) (fun _ ↦ hf) (fun _ ↦ hf0)
  exact ⟨L, L.symm p, L.apply_symm_apply p, hL ()⟩

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
  let e : ((Fin n → 𝕜) × 𝕜) ≃L[𝕜] (Fin (n + 1) → 𝕜) :=
    (ContinuousLinearEquiv.prodComm 𝕜 (Fin n → 𝕜) 𝕜).trans (Fin.consEquivL 𝕜 fun _ ↦ 𝕜)
  have hf' (i : ι) : AnalyticAt 𝕜 (f i ∘ e) (e.symm p) :=
    (hf i).comp_of_eq (e.analyticAt _) (e.apply_symm_apply p)
  have h0' (i : ι) : ¬ (f i ∘ e) =ᶠ[𝓝 (e.symm p)] 0 := fun h ↦ h0 i <| by
    have htend : Tendsto e.symm (𝓝 p) (𝓝 (e.symm p)) := e.symm.continuous.continuousAt
    filter_upwards [htend.eventually h] with y hy
    simpa [Function.comp_apply] using hy
  obtain ⟨L₀, hL₀⟩ := exists_continuousLinearEquiv_forall_analyticOrderAt_ne_top hf' h0'
  refine ⟨e.symm.trans (L₀.trans e), fun i ↦ ?_⟩
  have he (q : (Fin n → 𝕜) × 𝕜) : e q = Fin.cons q.2 q.1 := by
    ext j
    simp [e, Fin.consEquivL_apply]
  have hsymm : (e.symm.trans (L₀.trans e)).symm p = e (L₀.symm (e.symm p)) := by
    simp [ContinuousLinearEquiv.symm_trans_apply]
  have h0_eq : (e.symm.trans (L₀.trans e)).symm p 0 = (L₀.symm (e.symm p)).2 := by
    rw [hsymm, he, Fin.cons_zero]
  have htail_eq : Fin.tail ((e.symm.trans (L₀.trans e)).symm p) = (L₀.symm (e.symm p)).1 := by
    rw [hsymm, he, Fin.tail_cons]
  have hfun : (fun t ↦ f i ((e.symm.trans (L₀.trans e))
      (Fin.cons t (Fin.tail ((e.symm.trans (L₀.trans e)).symm p))))) =
      fun t ↦ (f i ∘ e) (L₀ ((L₀.symm (e.symm p)).1, t)) := by
    ext t
    rw [htail_eq, ← he ((L₀.symm (e.symm p)).1, t)]
    simp
  rw [hfun, h0_eq]
  exact hL₀ i

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
