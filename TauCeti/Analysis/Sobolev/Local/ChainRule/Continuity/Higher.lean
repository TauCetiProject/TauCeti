/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.ChainRule.Continuity
import TauCeti.Analysis.Sobolev.Local.ChainRule.Higher
import TauCeti.Analysis.Sobolev.Local.Multiplication.Bound.Higher
import TauCeti.Analysis.Sobolev.WeakDeriv.ChainRule
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Continuity of composition in `W^{k,p}_loc` at every order

Let `p > 2`, let `Ω` be an open planar domain, and let `F` and `G` be finite-dimensional real
normed spaces. Let `g : F → G` be `C^{k+1}` on an open set `W`, and let `u₀ ∈ W^{k+1,p}_loc(Ω)`
map `Ω` into `W`. If maps `uₙ`, eventually continuous on every compact subset of `Ω`, converge to
`u₀` locally uniformly on `Ω` and in `W^{k+1,p}` on every compact subset of `Ω`, then
`g ∘ uₙ → g ∘ u₀` in `W^{k+1,p}` on every compact subset of `Ω`
(`TauCeti.MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub`). This is the continuity of the
composition operator `u ↦ g ∘ u` on local Sobolev maps, at every positive order.

The proof is an induction on the order, starting from the order-one statement
`TauCeti.MemWkpLoc.tendsto_eLpNormWkp_one_comp_sub`. Fix a compact set `K ⊆ Ω` and a relatively
compact open set `V` with `K ⊆ V` and `closure V ⊆ Ω`. On `V` the weak derivative of
`g ∘ uₙ - g ∘ u₀` is `Dg(uₙ) ∘ Duₙ - Dg(u₀) ∘ Du₀`, and

`Dg(uₙ) ∘ Duₙ - Dg(u₀) ∘ Du₀ = (Dg(uₙ) - Dg(u₀)) ∘ Duₙ + Dg(u₀) ∘ D(uₙ - u₀)`.

Since `Dg` is `C^k`, the induction hypothesis gives `Dg ∘ uₙ → Dg ∘ u₀` in `W^{k,p}(closure V)`
(for `k ≥ 1`), while `D(uₙ - u₀) → 0` in `W^{k,p}(V)`. The local product bound
`TauCeti.exists_eLpNormWkp_succ_bilin_le` for the bilinear map `(A, B) ↦ A ∘L B` estimates both
terms in `W^{k,p}(K)` by products of these norms on `V`, so both tend to `0`.

The derivative count matches the order-one statement: convergence in `W^{k+1,p}` needs `g` to be
`C^{k+1}`, given the locally uniform convergence. For `p > 2`, Morrey's embedding turns
`W^{1,p}_loc` convergence of continuous maps into locally uniform convergence; that consequence is
not used here, and the locally uniform convergence remains a hypothesis, as in the order-one
statement.

## Main declarations

* `TauCeti.MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub`: continuity of composition with a
  `C^{k+1}` map in `W^{k+1,p}` on compact subsets.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (composition in local Sobolev spaces).
-/

public noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology

namespace TauCeti

universe uF uG

variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {Ω : Opens ℂ} {p : ℝ≥0}

omit [FiniteDimensional ℝ F] in
/-- The estimate behind the inductive step of `TauCeti.MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub`.
Let `V` be open, `K ⊆ V`, let `c` bound the product `(A, B) ↦ A ∘L B` from `W^{k+1,p}(V)` to
`W^{k+1,p}(K)`, and let `Du` be a weak derivative of `u₀` on `V`. For `v` continuous on `V` with
`‖v - u₀‖_{W^{k+2,p}(V)}` finite, the `W^{k+2,p}(K)` norm of `g ∘ v - g ∘ u₀` is bounded through
its `W^{1,p}(K)` norm, `‖Dg ∘ v - Dg ∘ u₀‖_{W^{k+1,p}(V)}` and `‖v - u₀‖_{W^{k+2,p}(V)}`: the weak
derivative of `g ∘ v - g ∘ u₀` is `(Dg(v) - Dg(u₀)) ∘ Dv + Dg(u₀) ∘ D(v - u₀)`. -/
private theorem eLpNormWkp_succ_succ_comp_sub_le {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] (hp1 : (1 : ℝ≥0∞) ≤ p) {k : ℕ} {V : Opens ℂ}
    {K : Set ℂ} (hKV : K ⊆ V) {c : ℝ≥0∞}
    (hcB : ∀ (a : ℂ → F →L[ℝ] G) (b : ℂ → ℂ →L[ℝ] F),
      eLpNormWkp p K (k + 1) (fun z => ContinuousLinearMap.compL ℝ ℂ F G (a z) (b z)) ≤
        c * eLpNormWkp p V (k + 1) a * eLpNormWkp p V (k + 1) b)
    {v u₀ : ℂ → F} {Du : ℂ → ℂ →L[ℝ] F} {g : F → G} {W : Set F} (hW : IsOpen W)
    (hg : ContDiffOn ℝ 1 g W) (hvc : ContinuousOn v V) (hvW : MapsTo v V W)
    (hu₀c : ContinuousOn u₀ V) (hu₀W : MapsTo u₀ V W) (hDu : HasWeakFDerivOn volume V u₀ Du)
    (hfin : eLpNormWkp p V (k + 2) (v - u₀) ≠ ∞) :
    eLpNormWkp p K (k + 2) (g ∘ v - g ∘ u₀) ≤
      eLpNormWkp p K 1 (g ∘ v - g ∘ u₀) +
        (c * eLpNormWkp p V (k + 1) (fderiv ℝ g ∘ v - fderiv ℝ g ∘ u₀) *
            (eLpNormWkp p V (k + 2) (v - u₀) + eLpNormWkp p V (k + 1) Du) +
          c * eLpNormWkp p V (k + 1) (fun z => fderiv ℝ g (u₀ z)) *
            eLpNormWkp p V (k + 2) (v - u₀)) := by
  -- A weak derivative `D` of `v - u₀` on `V`, of norm at most that of `v - u₀`.
  obtain ⟨D, hD, -, hDeq⟩ := exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top hfin
  have hDV : eLpNormWkp p V (k + 1) D ≤ eLpNormWkp p V (k + 2) (v - u₀) :=
    le_add_self.trans_eq hDeq.symm
  have hv : HasWeakFDerivOn volume V v (D + Du) := by simpa using hD.add hDu
  -- The weak derivative of `g ∘ v - g ∘ u₀` on `V`, split into two products.
  have hE := (hv.contDiffOn_comp hvc hW hg hvW).sub (hDu.contDiffOn_comp hu₀c hW hg hu₀W)
  have hsplit : ((fun z => (fderiv ℝ g (v z)).comp ((D + Du) z)) -
      fun z => (fderiv ℝ g (u₀ z)).comp (Du z)) =
      (fun z => ContinuousLinearMap.compL ℝ ℂ F G
          ((fderiv ℝ g ∘ v - fderiv ℝ g ∘ u₀) z) ((D + Du) z)) +
        fun z => ContinuousLinearMap.compL ℝ ℂ F G (fderiv ℝ g (u₀ z)) (D z) := by
    ext1 z
    simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.sub_comp]
    abel
  have hKV' : Opens.interior K ≤ V := fun z hz => hKV (interior_subset hz)
  refine (eLpNormWkp_succ_le (hE.mono hKV')).trans ?_
  rw [hsplit]
  refine add_le_add eLpNorm_le_eLpNormWkp ((eLpNormWkp_add_le hp1).trans
    (add_le_add ((hcB _ _).trans ?_) ((hcB _ _).trans ?_)))
  · gcongr
    exact (eLpNormWkp_add_le hp1).trans (add_le_add hDV le_rfl)
  · gcongr

/-- `TauCeti.MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub` for values in a universe at least that
of `F`, so that the induction can pass from `g` to its derivative, valued in `F →L[ℝ] G`. -/
private theorem tendsto_eLpNormWkp_succ_comp_sub_aux (hp : 2 < p) (k : ℕ) {G : Type (max uF uG)}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] {ι : Type*} {l : Filter ι}
    {u : ι → ℂ → F} {u₀ : ℂ → F} {g : F → G} {W : Set F} (hu₀ : MemWkpLoc p Ω (k + 1) u₀)
    (hW : IsOpen W) (hg : ContDiffOn ℝ (k + 1) g W) (hu₀W : MapsTo u₀ Ω W)
    (huc : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∀ᶠ n in l, ContinuousOn (u n) K)
    (hunif : TendstoLocallyUniformlyOn u u₀ l Ω)
    (hlim : ∀ K ⊆ (Ω : Set ℂ), IsCompact K →
      Tendsto (fun n => eLpNormWkp p K (k + 1) (u n - u₀)) l (𝓝 0)) :
    ∀ K ⊆ (Ω : Set ℂ), IsCompact K →
      Tendsto (fun n => eLpNormWkp p K (k + 1) (g ∘ u n - g ∘ u₀)) l (𝓝 0) := by
  induction k generalizing G g with
  | zero => exact hu₀.tendsto_eLpNormWkp_one_comp_sub hW (by simpa using hg) hu₀W huc hunif hlim
  | succ k ih =>
    intro K hKΩ hK
    rcases l.eq_or_neBot with rfl | _
    · exact tendsto_bot
    have hp1 : (1 : ℝ≥0) < p := one_lt_two.trans hp
    have hp1' : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp1.le
    -- Convergence at a lower order follows from convergence at a higher one.
    have hlim_le {m : ℕ} (hm : m ≤ k + 2) (K : Set ℂ) (hKΩ : K ⊆ Ω) (hK : IsCompact K) :
        Tendsto (fun n => eLpNormWkp p K m (u n - u₀)) l (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim K hKΩ hK)
        (fun _ => zero_le) fun _ => eLpNormWkp_mono_order hm
    -- `u₀` is continuous on `Ω`, as a locally uniform limit.
    have hu₀c : ContinuousOn u₀ Ω := by
      intro z hz
      obtain ⟨L, hL, hzL, hLΩ⟩ := exists_compact_subset Ω.isOpen hz
      have hcont : ContinuousOn u₀ L :=
        ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hL).1
          (hunif.mono hLΩ)).continuousOn (huc L hLΩ hL).frequently
      exact (hcont.continuousAt (mem_interior_iff_mem_nhds.1 hzL)).continuousWithinAt
    -- A relatively compact open neighbourhood `V` of `K` in `Ω`.
    obtain ⟨V, hVo, hKV, hLΩ, hL⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
    let V' : Opens ℂ := ⟨V, hVo⟩
    have hVL : (V' : Set ℂ) ⊆ closure V := subset_closure
    have hVΩ : V' ≤ Ω := fun z hz => hLΩ (subset_closure hz)
    have hg1 : ContDiffOn ℝ 1 g W := hg.of_le (by exact_mod_cast (by omega : 1 ≤ k + 2))
    have hDg : ContDiffOn ℝ (k + 1) (fderiv ℝ g) W := hg.fderiv_of_isOpen hW (by push_cast; rfl)
    -- The three quantities that tend to `0`.
    have hT₀ : Tendsto (fun n => eLpNormWkp p K 1 (g ∘ u n - g ∘ u₀)) l (𝓝 0) :=
      (hu₀.of_le (by omega)).tendsto_eLpNormWkp_one_comp_sub hW hg1 hu₀W huc hunif
        (hlim_le (by omega)) K hKΩ hK
    have hT₁ : Tendsto (fun n => eLpNormWkp p (closure V) (k + 1)
        (fderiv ℝ g ∘ u n - fderiv ℝ g ∘ u₀)) l (𝓝 0) :=
      ih (hu₀.of_le (by omega)) hDg (hlim_le (by omega)) (closure V) hLΩ hL
    have hT₂ := hlim (closure V) hLΩ hL
    -- A weak derivative of `u₀` and the finite norms of `Du₀` and `Dg ∘ u₀` on `V`.
    obtain ⟨Du, hDu, hDuk⟩ := hu₀.exists_weakFDeriv_of_isOpen
    have hcb : eLpNormWkp p V' (k + 1) Du ≠ ∞ := hDuk.eLpNormWkp_ne_top_of_closure_subset hL hLΩ
    have hca : eLpNormWkp p V' (k + 1) (fun z => fderiv ℝ g (u₀ z)) ≠ ∞ :=
      ((hu₀.of_le (by omega)).contDiffOn_comp_succ hp hu₀c hW hDg
        hu₀W).eLpNormWkp_ne_top_of_closure_subset hL hLΩ
    -- The product bound for `(A, B) ↦ A ∘L B` from `V` to `K`.
    obtain ⟨C, hC⟩ := exists_eLpNormWkp_succ_bilin_le (F := F →L[ℝ] G) (G := ℂ →L[ℝ] F)
      (H := ℂ →L[ℝ] G) (Ω := V') hp hp1 le_rfl k (U := K) (by rwa [hK.isClosed.closure_eq])
      (by rw [hK.isClosed.closure_eq]; exact hKV)
    obtain ⟨c, hc, hcB⟩ : ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ (a : ℂ → F →L[ℝ] G) (b : ℂ → ℂ →L[ℝ] F),
        eLpNormWkp p K (k + 1) (fun z => ContinuousLinearMap.compL ℝ ℂ F G (a z) (b z)) ≤
          c * eLpNormWkp p V' (k + 1) a * eLpNormWkp p V' (k + 1) b := by
      refine ⟨_, ENNReal.mul_ne_top ENNReal.coe_ne_top ?_, hC (ContinuousLinearMap.compL ℝ ℂ F G)⟩
      rw [← ofReal_norm]
      exact ENNReal.ofReal_ne_top
    -- Eventually `u n` is continuous on `closure V`, maps it into `W`, and is close to `u₀`.
    have hunifL : TendstoUniformlyOn u u₀ l (closure V) :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hL).1
      (hunif.mono hLΩ)
    have hcpt : IsCompact (u₀ '' closure V) := hL.image_of_continuousOn (hu₀c.mono hLΩ)
    have hmaps := hunifL.eventually_mapsTo (mapsTo_image u₀ _) hcpt
      (hW.mem_nhdsSet.2 (image_subset_iff.2 (hu₀W.mono_left hLΩ)))
    have hfin : ∀ᶠ n in l, eLpNormWkp p (closure V) (k + 2) (u n - u₀) ≠ ∞ :=
      (hT₂.eventually (gt_mem_nhds zero_lt_one)).mono fun _ hn => (hn.trans ENNReal.one_lt_top).ne
    have key : ∀ᶠ n in l, eLpNormWkp p K (k + 2) (g ∘ u n - g ∘ u₀) ≤
        eLpNormWkp p K 1 (g ∘ u n - g ∘ u₀) +
          (c * eLpNormWkp p (closure V) (k + 1) (fderiv ℝ g ∘ u n - fderiv ℝ g ∘ u₀) *
              (eLpNormWkp p (closure V) (k + 2) (u n - u₀) + eLpNormWkp p V' (k + 1) Du) +
            c * eLpNormWkp p V' (k + 1) (fun z => fderiv ℝ g (u₀ z)) *
              eLpNormWkp p (closure V) (k + 2) (u n - u₀)) := by
      filter_upwards [huc (closure V) hLΩ hL, hmaps, hfin] with n hnc hnW hnfin
      refine (eLpNormWkp_succ_succ_comp_sub_le hp1' hKV hcB hW hg1 (hnc.mono hVL)
        (hnW.mono_left hVL) (hu₀c.mono hVΩ) (hu₀W.mono_left hVΩ) (hDu.mono hVΩ)
        (ne_top_of_le_ne_top hnfin (eLpNormWkp_mono_set hVL))).trans ?_
      gcongr <;> exact eLpNormWkp_mono_set hVL
    -- The bound tends to `0`.
    have hlim₁ : Tendsto (fun n =>
        c * eLpNormWkp p (closure V) (k + 1) (fderiv ℝ g ∘ u n - fderiv ℝ g ∘ u₀) *
          (eLpNormWkp p (closure V) (k + 2) (u n - u₀) + eLpNormWkp p V' (k + 1) Du)) l (𝓝 0) := by
      have h := ENNReal.Tendsto.mul (ENNReal.Tendsto.const_mul hT₁ (Or.inr hc))
        (Or.inr (by simpa using hcb)) (hT₂.add tendsto_const_nhds) (Or.inr (by simp))
      simpa using h
    have hlim₂ : Tendsto (fun n => c * eLpNormWkp p V' (k + 1) (fun z => fderiv ℝ g (u₀ z)) *
        eLpNormWkp p (closure V) (k + 2) (u n - u₀)) l (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hT₂ (Or.inr (ENNReal.mul_ne_top hc hca))
    have hsum := hT₀.add (hlim₁.add hlim₂)
    simp only [add_zero] at hsum
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (.of_forall fun _ => zero_le) key

/-- **Continuity of composition in `W^{k+1,p}_loc`.** Let `p > 2`, let `F` and `G` be
finite-dimensional, let `g : F → G` be `C^{k+1}` on an open set `W`, and let
`u₀ ∈ W^{k+1,p}_loc(Ω)` map `Ω` into `W`. Let maps `uₙ` converge to `u₀` locally uniformly on
`Ω`, and for every compact `K ⊆ Ω` let `uₙ` be eventually continuous on `K` with
`‖uₙ - u₀‖_{W^{k+1,p}(K)} → 0`. Then `‖g ∘ uₙ - g ∘ u₀‖_{W^{k+1,p}(K)} → 0` for every compact
`K ⊆ Ω`. At order one this is `TauCeti.MemWkpLoc.tendsto_eLpNormWkp_one_comp_sub`. -/
theorem MemWkpLoc.tendsto_eLpNormWkp_succ_comp_sub {G : Type uG} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] (hp : 2 < p) {k : ℕ} {ι : Type*} {l : Filter ι}
    {u : ι → ℂ → F} {u₀ : ℂ → F} {g : F → G} {W : Set F} (hu₀ : MemWkpLoc p Ω (k + 1) u₀)
    (hW : IsOpen W) (hg : ContDiffOn ℝ (k + 1) g W) (hu₀W : MapsTo u₀ Ω W)
    (huc : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∀ᶠ n in l, ContinuousOn (u n) K)
    (hunif : TendstoLocallyUniformlyOn u u₀ l Ω)
    (hlim : ∀ K ⊆ (Ω : Set ℂ), IsCompact K →
      Tendsto (fun n => eLpNormWkp p K (k + 1) (u n - u₀)) l (𝓝 0)) :
    ∀ K ⊆ (Ω : Set ℂ), IsCompact K →
      Tendsto (fun n => eLpNormWkp p K (k + 1) (g ∘ u n - g ∘ u₀)) l (𝓝 0) := by
  -- Move the values to `ULift G`, which lies in a universe at least that of `F`.
  let e : G ≃L[ℝ] ULift.{uF} G := (LinearIsometryEquiv.ulift ℝ G).symm.toContinuousLinearEquiv
  have hg' : ContDiffOn ℝ (k + 1) (fun x => e (g x)) W := e.contDiff.comp_contDiffOn hg
  intro K hKΩ hK
  have h := tendsto_eLpNormWkp_succ_comp_sub_aux hp k (g := fun x => e (g x)) hu₀ hW hg' hu₀W
    huc hunif hlim K hKΩ hK
  have hle (n : ι) : eLpNormWkp p K (k + 1) (g ∘ u n - g ∘ u₀) ≤
      ‖(e.symm : ULift.{uF} G →L[ℝ] G)‖ₑ *
        eLpNormWkp p K (k + 1) ((fun x => e (g x)) ∘ u n - (fun x => e (g x)) ∘ u₀) := by
    convert eLpNormWkp_clm_comp_le (e.symm : ULift.{uF} G →L[ℝ] G) using 2
    ext z
    simp
  have h' := ENNReal.Tendsto.const_mul (a := ‖(e.symm : ULift.{uF} G →L[ℝ] G)‖ₑ) h
    (Or.inr eNorm_ne_top)
  rw [mul_zero] at h'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h' (fun _ => zero_le) hle

end TauCeti
