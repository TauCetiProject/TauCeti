/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.ExitTime
public import TauCeti.Geometry.Symplectic.Annulus.Exit
import TauCeti.Dynamics.Flow.Deriv
import TauCeti.Dynamics.Flow.ExitTime.Deriv
import TauCeti.Geometry.Symplectic.Annulus.Block.Face

/-!
# The exit time of the negative gradient flow from the block

Let `S_k`, `k ∈ ℤ/N`, be generating functions of a chain of twist maps of the strip `ℝ × [0, 1]`,
in the convention `y = -∂₁ S_k(x, X)`, `Y = ∂₂ S_k(x, X)`. A configuration `q : ℤ/N → ℝ` has the
input momenta `y_k = -∂₁ S_k(q_k, q_(k+1))` and output momenta `Y_k = ∂₂ S_k(q_k, q_(k+1))`, and
the negative gradient flow of the cyclic action `W(q) = Σ_k S_k(q_k, q_(k+1))` moves the positions
with velocities `dq_k/dt = y_k - Y_(k-1)`. In the generating-function proof of the
Poincaré–Birkhoff theorem, the block `K` of configurations whose momenta all lie in `[0, 1]` is an
isolating block for this flow, and its *exit set* is the set `L` of configurations of `K` with the
momentum of some *negative* factor on a face `y_k ∈ {0, 1}`. In Conley's theory the pair `(K, L)`
is used through the exit time of the flow from `K` (`Flow.exitTime`), which must be continuous on
`K` and vanish exactly on `L`.

This file proves these properties for every flow `ϕ` on the configuration space whose velocity is
`y_k - Y_(k-1)` on an open set `U` containing `K`, such as the flow of a complete vector field equal
to the negative gradient near the block. The momenta and the second derivatives of the `S_k` satisfy
at every configuration of `K` the pointwise hypotheses of
`TauCeti.eventually_nhdsGT_exists_stripGeneratingSource_snd_notMem_Icc`: the output momenta lie in
`[0, 1]` and are on a face exactly when the input momenta are, the face identity of the second
derivatives holds, the mixed second derivative `∂₁∂₂ S_k` is negative for the positive factors
`k ∈ P` and positive for the others, no two consecutive factors are positive, and no face carries
all the momenta.

* **The exit set.** A configuration of `K` leaves `K` at once exactly when it lies in `L`
  (`TauCeti.exitTime_eq_zero_iff_exists_stripGeneratingSource_snd_mem`).
* **Interior trajectories.** Before its exit time, the trajectory of a configuration of `K` lies in
  the interior of `K` at every positive time
  (`TauCeti.apply_mem_interior_of_lt_exitTime_of_hasDerivAt_stripGeneratingSource`). At a
  boundary point reached at a positive time, a momentum of a negative factor on a face would make
  the trajectory leave `K` at once, and if only positive factors have momenta on faces, the
  trajectory was outside `K` just before, by
  `TauCeti.eventually_nhdsLT_stripGeneratingSource_snd_notMem_Icc`.
* **Continuity.** If `K` is closed, the exit time is continuous on `K` as a map to `[0, ∞]`
  (`TauCeti.continuousOn_exitTime_of_hasDerivAt_stripGeneratingSource`). Off `L` every momentum on
  a face belongs to a positive factor and has a velocity pointing strictly into `K`
  (`TauCeti.exists_hasDerivAt_stripGeneratingSource_snd_and_mul_pos`). By continuity of the second
  derivatives the velocities at nearby configurations point into `K` too, so the configurations of
  `K` near a point off `L` stay in `K` during a common time interval
  (`Flow.exists_pos_eventually_forall_apply_mem_of_hasDerivAt_nonneg`). With the interior
  trajectories, this is the criterion `Flow.continuousOn_exitTime`.

Consequently the flow stopped at the exit from `K` is a continuous self-map of `K` homotopic to the
identity relative to `L` (`Flow.homotopicRel_stopAtExitMap`), carrying the configurations which
leave `K` by time `t` into `L`.

## Main results

* `TauCeti.exitTime_eq_zero_iff_exists_stripGeneratingSource_snd_mem`: the exit time vanishes
  exactly on `L`.
* `TauCeti.apply_mem_interior_of_lt_exitTime_of_hasDerivAt_stripGeneratingSource`: trajectories
  lie in the interior of the block before their exit.
* `TauCeti.continuousOn_exitTime_of_hasDerivAt_stripGeneratingSource`: the exit time is continuous
  on the block.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
* C. Conley, *Isolated Invariant Sets and the Morse Index*, CBMS Regional Conference Series in
  Mathematics 38, American Mathematical Society, 1978 (exit times of isolating blocks).
-/

open Filter Set Topology

public section

namespace TauCeti

variable {N : ℕ} [NeZero N] {S : ZMod N → ℝ × ℝ → ℝ} {ϕ : Flow ℝ (ZMod N → ℝ)}
  {U K : Set (ZMod N → ℝ)} {P : Set (ZMod N)} {x : ZMod N → ℝ}

variable (hU : IsOpen U) (hKU : K ⊆ U)
  (hK : ∀ q ∈ U, q ∈ K ↔ ∀ k, (stripGeneratingSource (S k) (q k, q (k + 1))).2 ∈ Icc (0 : ℝ) 1)
  (hS : ∀ q ∈ U, ∀ k, ContDiffAt ℝ 2 (S k) (q k, q (k + 1)))
  (hϕ : ∀ q ∈ U, HasDerivAt (fun t ↦ ϕ t q) (fun i ↦
    (stripGeneratingSource (S i) (q i, q (i + 1))).2 -
      (stripGeneratingTarget (S (i - 1)) (q (i - 1), q i)).2) 0)
  (htgt : ∀ q ∈ K, ∀ k, (stripGeneratingTarget (S k) (q k, q (k + 1))).2 ∈ Icc (0 : ℝ) 1)
  (hiff : ∀ q ∈ K, ∀ k, ∀ c ∈ ({0, 1} : Set ℝ),
    (stripGeneratingTarget (S k) (q k, q (k + 1))).2 = c ↔
      (stripGeneratingSource (S k) (q k, q (k + 1))).2 = c)
  (hface : ∀ q ∈ K, ∀ k, (stripGeneratingSource (S k) (q k, q (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
    ∃ B, 0 < B ∧ ∀ v, B * fderiv ℝ (fderiv ℝ (S k)) (q k, q (k + 1)) v (0, 1) =
      -fderiv ℝ (fderiv ℝ (S k)) (q k, q (k + 1)) v (1, 0))
  (hpos : ∀ q ∈ K, ∀ k ∈ P,
    (stripGeneratingSource (S k) (q k, q (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      fderiv ℝ (fderiv ℝ (S k)) (q k, q (k + 1)) (0, 1) (1, 0) < 0)
  (hneg : ∀ q ∈ K, ∀ k ∉ P,
    (stripGeneratingSource (S k) (q k, q (k + 1))).2 ∈ ({0, 1} : Set ℝ) →
      0 < fderiv ℝ (fderiv ℝ (S k)) (q k, q (k + 1)) (0, 1) (1, 0))
  (hP : ∀ k ∈ P, k + 1 ∉ P)
  (hfull : ∀ q ∈ K, ∀ c ∈ ({0, 1} : Set ℝ),
    ∃ k, (stripGeneratingSource (S k) (q k, q (k + 1))).2 ≠ c)

/-! ### Trajectories near the block -/

include hU hϕ in
/-- A trajectory of the flow solves `dq_k/dt = y_k - Y_(k-1)` near every time at which it lies in
`U`. -/
private theorem eventually_hasDerivAt_apply {t₀ : ℝ} (hx : ϕ t₀ x ∈ U) :
    ∀ᶠ t in 𝓝 t₀, HasDerivAt (fun t ↦ ϕ t x) (fun i ↦
      (stripGeneratingSource (S i) (ϕ t x i, ϕ t x (i + 1))).2 -
        (stripGeneratingTarget (S (i - 1)) (ϕ t x (i - 1), ϕ t x i)).2) t := by
  have hc : Continuous fun t ↦ ϕ t x := ϕ.continuous continuous_id continuous_const
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)] with t ht
  exact Flow.hasDerivAt_apply_flow_iff (g := id).2 (hϕ _ ht)

include hU hK hS in
/-- A configuration of `U` whose momenta all lie in `(0, 1)` is an interior point of the block. -/
private theorem mem_interior_of_forall_mem_Ioo {z : ZMod N → ℝ} (hz : z ∈ U)
    (h : ∀ k, (stripGeneratingSource (S k) (z k, z (k + 1))).2 ∈ Ioo (0 : ℝ) 1) :
    z ∈ interior K := by
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [hU.mem_nhds hz, eventually_all.2 fun k ↦
    (contDiffAt_stripGeneratingSource_snd (n := 1) (hS z hz k)).continuousAt.eventually
      (isOpen_Ioo.mem_nhds (h k))] with q hq hqk
  exact (hK q hq).2 fun k ↦ Ioo_subset_Icc_self (hqk k)

include hU hKU hK hS hϕ htgt hiff hface hpos hneg hP hfull in
/-- **Exit through the faces of negative factors.** If at `z = ϕ t₀ x ∈ K` the momentum of a
negative factor is on a face, the trajectory of `x` lies outside the block just after `t₀`. -/
private theorem eventually_nhdsGT_apply_notMem {t₀ : ℝ} {z : ZMod N → ℝ} (hz : ϕ t₀ x = z)
    (hzK : z ∈ K)
    (hk : ∃ k ∉ P, (stripGeneratingSource (S k) (z k, z (k + 1))).2 ∈ ({0, 1} : Set ℝ)) :
    ∀ᶠ t in 𝓝[>] t₀, ϕ t x ∉ K := by
  subst hz
  filter_upwards [eventually_nhdsGT_exists_stripGeneratingSource_snd_notMem_Icc
    (γ := fun t ↦ ϕ t x) (hS _ (hKU hzK)) (eventually_hasDerivAt_apply hU hϕ (hKU hzK))
    ((hK _ (hKU hzK)).1 hzK) (htgt _ hzK) (hiff _ hzK) (hface _ hzK) (hpos _ hzK) (hneg _ hzK) hP
    (hfull _ hzK) hk] with t ⟨k, hk⟩ ht
  exact hk ((hK _ (hKU ht)).1 ht k)

include hU hKU hK hS hϕ htgt hiff hface hpos hP in
/-- **Entry through the faces of positive factors.** If every momentum on a face at
`z = ϕ t₀ x ∈ K` belongs to a positive factor, the trajectory of `x` lies in the block just after
`t₀`. -/
private theorem eventually_nhdsGT_apply_mem {t₀ : ℝ} {z : ZMod N → ℝ} (hz : ϕ t₀ x = z)
    (hzK : z ∈ K)
    (hall : ∀ k, (stripGeneratingSource (S k) (z k, z (k + 1))).2 ∈ ({0, 1} : Set ℝ) → k ∈ P) :
    ∀ᶠ t in 𝓝[>] t₀, ϕ t x ∈ K := by
  subst hz
  have hc : Continuous fun t ↦ ϕ t x := ϕ.continuous continuous_id continuous_const
  filter_upwards [eventually_nhdsGT_forall_stripGeneratingSource_snd_mem_Ioo
    (γ := fun t ↦ ϕ t x) (hS _ (hKU hzK)) (eventually_hasDerivAt_apply hU hϕ (hKU hzK))
    ((hK _ (hKU hzK)).1 hzK) (htgt _ hzK) (hiff _ hzK) (hface _ hzK) (hpos _ hzK) hP hall,
    nhdsWithin_le_nhds (hc.continuousAt.preimage_mem_nhds (hU.mem_nhds (hKU hzK)))] with t ht htU
  exact (hK _ htU).2 fun k ↦ Ioo_subset_Icc_self (ht k)

include hU hKU hK hS hϕ htgt hiff hface hpos hP in
/-- **Trajectories reach the faces of positive factors from outside.** In the setting of
`eventually_nhdsGT_apply_mem`, the trajectory of `x` lies outside the block just before `t₀` if
some momentum is on a face at `z`. -/
private theorem eventually_nhdsLT_apply_notMem {t₀ : ℝ} {z : ZMod N → ℝ} (hz : ϕ t₀ x = z)
    (hzK : z ∈ K)
    (hall : ∀ k, (stripGeneratingSource (S k) (z k, z (k + 1))).2 ∈ ({0, 1} : Set ℝ) → k ∈ P)
    {k : ZMod N} (hk : (stripGeneratingSource (S k) (z k, z (k + 1))).2 ∈ ({0, 1} : Set ℝ)) :
    ∀ᶠ t in 𝓝[<] t₀, ϕ t x ∉ K := by
  subst hz
  filter_upwards [eventually_nhdsLT_stripGeneratingSource_snd_notMem_Icc
    (γ := fun t ↦ ϕ t x) (hS _ (hKU hzK)) (eventually_hasDerivAt_apply hU hϕ (hKU hzK))
    ((hK _ (hKU hzK)).1 hzK) (htgt _ hzK) (hiff _ hzK) (hface _ hzK) (hpos _ hzK) hP hall hk]
    with t ht htK
  exact ht ((hK _ (hKU htK)).1 htK k)

/-! ### The exit set -/

include hU hKU hK hS hϕ htgt hiff hface hpos hneg hP hfull in
/-- **The exit set of the block.** Let `ϕ` be a flow with velocity `y_k - Y_(k-1)` on an open set
`U` containing the block `K` of configurations with momenta in `[0, 1]`, and let the face
hypotheses of `TauCeti.eventually_nhdsGT_exists_stripGeneratingSource_snd_notMem_Icc` hold at every
configuration of `K`. A configuration of `K` leaves `K` at once, that is, has exit time zero,
exactly when the momentum of some negative factor is on a face. -/
theorem exitTime_eq_zero_iff_exists_stripGeneratingSource_snd_mem (hx : x ∈ K) :
    ϕ.exitTime K x = 0 ↔
      ∃ k ∉ P, (stripGeneratingSource (S k) (x k, x (k + 1))).2 ∈ ({0, 1} : Set ℝ) := by
  refine ⟨fun h ↦ by_contra fun hno ↦ ?_, fun hk ↦ Flow.exitTime_eq_zero_of_eventually_notMem
    (eventually_nhdsGT_apply_notMem hU hKU hK hS hϕ htgt hiff hface hpos hneg hP hfull
      (ϕ.map_zero_apply x) hx hk)⟩
  -- otherwise the trajectory stays in the block at time `0` and just after
  have hmem : ∀ᶠ s in 𝓝[≥] (0 : ℝ), ϕ s x ∈ K := by
    rw [← insert_Ioi, nhdsWithin_insert]
    exact eventually_sup.2 ⟨eventually_pure.2 (by rwa [ϕ.map_zero_apply]),
      eventually_nhdsGT_apply_mem hU hKU hK hS hϕ htgt hiff hface hpos hP (ϕ.map_zero_apply x) hx
        fun k hk ↦ by_contra fun hkP ↦ hno ⟨k, hkP, hk⟩⟩
  obtain ⟨s, hs, hsK⟩ := ((Flow.exitTime_eq_zero_iff_frequently.1 h).and_eventually hmem).exists
  exact hs hsK

/-! ### Interior trajectories -/

include hU hKU hK hS hϕ htgt hiff hface hpos hneg hP hfull in
/-- **Trajectories are interior before their exit.** In the setting of
`TauCeti.exitTime_eq_zero_iff_exists_stripGeneratingSource_snd_mem`, the trajectory of a
configuration lies in the interior of the block `K` at every positive time before its exit time
from `K`. -/
theorem apply_mem_interior_of_lt_exitTime_of_hasDerivAt_stripGeneratingSource {s : ℝ}
    (hs : 0 < s) (hsx : ENNReal.ofReal s < ϕ.exitTime K x) : ϕ s x ∈ interior K := by
  have hzK : ϕ s x ∈ K := Flow.apply_mem_of_lt_exitTime hs.le hsx
  by_cases hneg' : ∃ k ∉ P,
      (stripGeneratingSource (S k) (ϕ s x k, ϕ s x (k + 1))).2 ∈ ({0, 1} : Set ℝ)
  · -- the trajectory would leave the block just after `s`, before its exit time
    obtain ⟨t, ⟨htK, htx⟩, hst⟩ := ((eventually_nhdsGT_apply_notMem hU hKU hK hS hϕ htgt hiff
      hface hpos hneg hP hfull rfl hzK hneg').and (nhdsWithin_le_nhds
        ((ENNReal.continuous_ofReal.tendsto s).eventually (gt_mem_nhds hsx)))).and
      eventually_mem_nhdsWithin |>.exists
    exact (htK (Flow.apply_mem_of_lt_exitTime (hs.le.trans (le_of_lt hst)) htx)).elim
  have hall : ∀ k, (stripGeneratingSource (S k) (ϕ s x k, ϕ s x (k + 1))).2 ∈
      ({0, 1} : Set ℝ) → k ∈ P := fun k hk ↦ by_contra fun hkP ↦ hneg' ⟨k, hkP, hk⟩
  by_cases hface' : ∃ k,
      (stripGeneratingSource (S k) (ϕ s x k, ϕ s x (k + 1))).2 ∈ ({0, 1} : Set ℝ)
  · -- the trajectory would have been outside the block just before `s`
    obtain ⟨k, hk⟩ := hface'
    obtain ⟨t, htK, ht⟩ := ((eventually_nhdsLT_apply_notMem hU hKU hK hS hϕ htgt hiff hface hpos
      hP rfl hzK hall hk).and (Ioo_mem_nhdsLT hs)).exists
    exact (htK (Flow.apply_mem_of_lt_exitTime ht.1.le
      ((ENNReal.ofReal_le_ofReal ht.2.le).trans_lt hsx))).elim
  -- every momentum lies in `(0, 1)`
  refine mem_interior_of_forall_mem_Ioo hU hK hS (hKU hzK) fun k ↦ ?_
  have hk := (hK _ (hKU hzK)).1 hzK k
  exact ⟨hk.1.lt_of_ne fun h ↦ hface' ⟨k, Or.inl h.symm⟩,
    hk.2.lt_of_ne fun h ↦ hface' ⟨k, Or.inr h⟩⟩

/-! ### Continuity of the exit time -/

/-- The input momentum `y_k = -∂₁ S_k(q_k, q_(k+1))` of a configuration. -/
private noncomputable def momentum (S : ZMod N → ℝ × ℝ → ℝ) (k : ZMod N) (q : ZMod N → ℝ) : ℝ :=
  (stripGeneratingSource (S k) (q k, q (k + 1))).2

/-- The velocity `y_k - Y_(k-1)` of the negative gradient flow at a configuration. -/
private noncomputable def velocity (S : ZMod N → ℝ × ℝ → ℝ) (q : ZMod N → ℝ) : ZMod N → ℝ :=
  fun i ↦ (stripGeneratingSource (S i) (q i, q (i + 1))).2 -
    (stripGeneratingTarget (S (i - 1)) (q (i - 1), q i)).2

include hS in
private theorem contDiffAt_momentum {q : ZMod N → ℝ} (hq : q ∈ U) (k : ZMod N) :
    ContDiffAt ℝ 1 (momentum S k) q := by
  unfold momentum
  exact contDiffAt_stripGeneratingSource_snd (hS q hq k)

include hS hϕ in
/-- Along the flow, the momentum `y_k` has derivative `dy_k(y - Y)` at every configuration of
`U`. -/
private theorem hasDerivAt_momentum_apply {q : ZMod N → ℝ} (hq : q ∈ U) (k : ZMod N) :
    HasDerivAt (fun t ↦ momentum S k (ϕ t q)) (fderiv ℝ (momentum S k) q (velocity S q)) 0 :=
  ((contDiffAt_momentum hS hq k).differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (by unfold velocity; exact hϕ q hq) (ϕ.map_zero_apply q).symm

include hS in
/-- The derivative `dy_k(y - Y)` of a momentum along the flow is continuous on `U`. -/
private theorem continuousAt_fderiv_momentum_apply (hx : x ∈ U) (k : ZMod N) :
    ContinuousAt (fun q ↦ fderiv ℝ (momentum S k) q (velocity S q)) x := by
  have hv : ContinuousAt (velocity S) x := continuousAt_pi.2 fun i ↦
    (contDiffAt_momentum hS hx i).continuousAt.sub (by
      simpa only [sub_add_cancel] using
        (contDiffAt_stripGeneratingTarget_snd (n := 1) (hS x hx (i - 1))).continuousAt)
  exact ((contDiffAt_momentum hS hx k).continuousAt_fderiv one_ne_zero).clm_apply hv

include hU hKU hK hS hϕ htgt hiff hface hpos hP in
/-- If every momentum on a face at `x ∈ K` belongs to a positive factor, the derivative along the
flow of a momentum on a face `c ∈ {0, 1}` points strictly into the block. -/
private theorem mul_fderiv_momentum_apply_pos (hx : x ∈ K)
    (hall : ∀ k, momentum S k x ∈ ({0, 1} : Set ℝ) → k ∈ P) {k : ZMod N}
    (hk : momentum S k x ∈ ({0, 1} : Set ℝ)) :
    0 < (1 - 2 * momentum S k x) * fderiv ℝ (momentum S k) x (velocity S x) := by
  have hx₀ : ϕ 0 x ∈ K := by rwa [ϕ.map_zero_apply]
  have hm := hasDerivAt_momentum_apply hS hϕ (hKU hx) k
  unfold momentum at hm hall hk ⊢
  obtain ⟨y', hy', hy'pos⟩ := exists_hasDerivAt_stripGeneratingSource_snd_and_mul_pos
    (γ := fun t ↦ ϕ t x) (hS _ (hKU hx₀)) (eventually_hasDerivAt_apply hU hϕ (hKU hx₀))
    ((hK _ (hKU hx₀)).1 hx₀) (htgt _ hx₀) (hiff _ hx₀) (hface _ hx₀) (hpos _ hx₀) hP
    (by simpa only [ϕ.map_zero_apply] using hall) (by simpa only [ϕ.map_zero_apply] using hk)
  rw [hy'.unique hm] at hy'pos
  simpa only [ϕ.map_zero_apply] using hy'pos

include hU hKU hK hS hϕ htgt hiff hface hpos hP in
/-- **Inflow off the exit set.** If every momentum on a face at `x ∈ K` belongs to a positive
factor, the configurations of the block near `x` stay in it during a common time interval. -/
private theorem exists_pos_eventually_forall_apply_mem (hx : x ∈ K)
    (hall : ∀ k, (stripGeneratingSource (S k) (x k, x (k + 1))).2 ∈ ({0, 1} : Set ℝ) → k ∈ P) :
    ∃ δ > 0, ∀ᶠ y in 𝓝[K] x, ∀ s ∈ Icc (0 : ℝ) δ, ϕ s y ∈ K := by
  have hxU := hKU hx
  -- near `x` the block is cut out by the inequalities `0 ≤ (1 - 2c) (y_k - c)`, `c ∈ {0, 1}`
  refine Flow.exists_pos_eventually_forall_apply_mem_of_hasDerivAt_nonneg
    (ι := ZMod N × ({0, 1} : Set ℝ)) (g := fun i q ↦ (1 - 2 * (i.2 : ℝ)) * (momentum S i.1 q - i.2))
    (g' := fun i q ↦ (1 - 2 * (i.2 : ℝ)) * fderiv ℝ (momentum S i.1) q (velocity S q)) ?_
    fun ⟨k, c, hc⟩ ↦ ?_
  · filter_upwards [hU.mem_nhds hxU] with q hq
    rw [hK q hq]
    refine ⟨fun h ⟨k, c, hc⟩ ↦ ?_, fun h k ↦ ?_⟩
    · rcases hc with rfl | rfl <;> dsimp only [momentum] <;> linarith [(h k).1, (h k).2]
    · have h₀ := h (k, ⟨0, by simp⟩)
      have h₁ := h (k, ⟨1, by simp⟩)
      dsimp only [momentum] at h₀ h₁
      constructor <;> linarith
  dsimp only
  have hmx : momentum S k x ∈ Icc (0 : ℝ) 1 := (hK x hxU).1 hx k
  by_cases hkc : momentum S k x = c
  · -- the momentum is on the face `c`, and its velocity points into the block near `x`
    have hcpos := hkc ▸ mul_fderiv_momentum_apply_pos hU hKU hK hS hϕ htgt hiff hface hpos hP hx
      hall (hkc ▸ hc)
    right
    filter_upwards [hU.mem_nhds hxU, (continuousAt_const.mul
      (continuousAt_fderiv_momentum_apply hS hxU k)).eventually (lt_mem_nhds hcpos)] with q hq hqpos
    exact ⟨((hasDerivAt_momentum_apply hS hϕ hq k).sub_const c).const_mul (1 - 2 * c), hqpos.le⟩
  · -- the momentum is off the face `c`, and stays off it near `x`
    have hgx : 0 < (1 - 2 * c) * (momentum S k x - c) := by
      rcases hc with rfl | rfl
      · linarith [hmx.1.lt_of_ne' hkc]
      · linarith [hmx.2.lt_of_ne hkc]
    left
    exact ((continuousAt_const.mul ((contDiffAt_momentum hS hxU k).continuousAt.sub
      continuousAt_const)).eventually (lt_mem_nhds hgx)).mono fun _ h ↦ h.le

include hU hKU hK hS hϕ htgt hiff hface hpos hneg hP hfull in
/-- **Continuity of the exit time.** In the setting of
`TauCeti.exitTime_eq_zero_iff_exists_stripGeneratingSource_snd_mem`, if the block `K` is closed,
the exit time from `K` is continuous on `K` as a map to `[0, ∞]`. -/
theorem continuousOn_exitTime_of_hasDerivAt_stripGeneratingSource (hKc : IsClosed K) :
    ContinuousOn (ϕ.exitTime K) K := by
  refine Flow.continuousOn_exitTime hKc (fun x hx hτ ↦ ?_) fun _ _ _ hs hsx ↦ ?_
  · -- off the exit set, every momentum on a face belongs to a positive factor
    have hτ' := mt (exitTime_eq_zero_iff_exists_stripGeneratingSource_snd_mem hU hKU hK hS hϕ htgt
      hiff hface hpos hneg hP hfull hx).2 hτ
    exact exists_pos_eventually_forall_apply_mem hU hKU hK hS hϕ htgt hiff hface hpos hP hx
      fun k hk ↦ by_contra fun hkP ↦ hτ' ⟨k, hkP, hk⟩
  · exact apply_mem_interior_of_lt_exitTime_of_hasDerivAt_stripGeneratingSource hU hKU hK hS hϕ
      htgt hiff hface hpos hneg hP hfull hs hsx

end TauCeti
