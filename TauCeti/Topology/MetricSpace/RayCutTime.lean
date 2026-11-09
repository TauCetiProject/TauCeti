/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Semicontinuity.Basic
public import TauCeti.Topology.MetricSpace.HausdorffDistance
public import TauCeti.Topology.MetricSpace.Pseudo.Defs

/-!
# Cut times of `1`-Lipschitz rays

Let `γ : ℝ → X` be a curve in a pseudo-emetric space that starts on a set `S`. If `γ` is
`1`-Lipschitz on `[0, R]`, then `infEDist (γ t) S ≤ t` for `t ∈ [0, R]`. A time `t` is
*minimizing* when equality holds, that is, when the ray realizes the distance from `γ t` back to
`S`. Equality at some time forces equality at every earlier time, and makes the ray an isometric
segment up to that time.

The ray may only be relevant on a time domain `T`, for instance the times at which a geodesic is
defined and stays in a given region. `TauCeti.rayMinimizingTimes γ S T R` is the set of minimizing
times `t ∈ [0, R]` whose whole prefix `[0, t]` lies in `T`, and the cut time
`TauCeti.rayCutTime γ S T R` is its supremum. The cap `R` keeps the cut time finite without
any boundedness assumption on `X`, and the extended metric allows intrinsic metrics with infinite
distances. For a general time domain, the `1`-Lipschitz condition is only needed on the prefixes
`[0, u] ⊆ T` with `u ≤ R`; the results for the times spent in a closed set assume it on all of
`[0, R]`.

Every nonnegative time before the cut time is minimizing, and so is the cut time itself as
soon as it lies in `T`. Past the cut time, either the prefix leaves `T` or the distance to `S` is
strictly smaller than the elapsed time. When `T` is the set of times spent in a closed set and the
rays depend continuously on a parameter, the cut time is upper semicontinuous in that parameter.
Measurability of the cut time is in `TauCeti.MeasureTheory.MeasurableSpace.RayCutTime`.

## Main definitions

* `TauCeti.rayMinimizingTimes γ S T R`: the minimizing times in `[0, R]` with prefix in `T`.
* `TauCeti.rayCutTime γ S T R`: the supremum of these times.

## Main results

* `LipschitzOnWith.infEDist_ray_eq_of_le`: the minimizing times of a ray form an initial interval.
* `LipschitzOnWith.edist_ray_eq_of_infEDist_eq`: a ray that is minimizing at time `R` is an
  isometric segment on `[0, R]`.
* `TauCeti.mem_rayMinimizingTimes_of_lt_rayCutTime` and
  `TauCeti.rayCutTime_mem_rayMinimizingTimes`: the nonnegative times before the cut time are
  minimizing, and so is the cut time when it lies in `T`.
* `TauCeti.not_subset_or_infEDist_lt_of_rayCutTime_lt`: the alternative past the cut time.
* `TauCeti.upperSemicontinuous_rayCutTime_preimage`: upper semicontinuity of the cut time of
  a continuous family of rays, with time domain the times spent in a closed set `D`.
-/

public section

open Metric Set

noncomputable section

namespace LipschitzOnWith

section Ray

variable {X : Type*} [PseudoEMetricSpace X] {γ : ℝ → X} {S : Set X} {R t u : ℝ}

/-- Along a ray that starts on `S` and is `1`-Lipschitz on `[0, R]`, the extended distance to `S`
at a time `t ∈ [0, R]` is at most `t`. -/
theorem infEDist_ray_le (hγ : LipschitzOnWith 1 γ (Icc 0 R)) (h0 : γ 0 ∈ S)
    (ht : t ∈ Icc 0 R) : infEDist (γ t) S ≤ ENNReal.ofReal t := by
  have hd := hγ ht (left_mem_Icc.mpr (ht.1.trans ht.2))
  simpa only [ENNReal.coe_one, one_mul, Real.edist_eq_ofReal_sub_of_le ht.1, sub_zero] using
    (infEDist_le_edist_of_mem h0).trans hd

/-- If a ray that starts on `S` and is `1`-Lipschitz on `[0, R]` realizes the extended distance to
`S` at a time `u`, then it realizes it at every time `t ∈ [0, u]`. -/
theorem infEDist_ray_eq_of_le (hγ : LipschitzOnWith 1 γ (Icc 0 R)) (h0 : γ 0 ∈ S)
    (ht : t ∈ Icc 0 R) (hu : u ∈ Icc 0 R) (htu : t ≤ u)
    (hu_eq : infEDist (γ u) S = ENNReal.ofReal u) : infEDist (γ t) S = ENNReal.ofReal t := by
  refine le_antisymm (hγ.infEDist_ray_le h0 ht) (not_lt.1 fun hlt ↦ ?_)
  have hd := hγ hu ht
  simp only [ENNReal.coe_one, one_mul, Real.edist_eq_ofReal_sub_of_le htu] at hd
  have hi := infEDist_le_infEDist_add_edist (x := γ u) (y := γ t) (s := S)
  rw [hu_eq] at hi
  have hsum : ENNReal.ofReal t + ENNReal.ofReal (u - t) = ENNReal.ofReal u := by
    rw [← ENNReal.ofReal_add ht.1 (sub_nonneg.mpr htu), add_sub_cancel]
  have hstrict := ENNReal.add_lt_add_right
    (ENNReal.ofReal_ne_top : ENNReal.ofReal (u - t) ≠ ⊤) hlt
  rw [hsum] at hstrict
  exact hstrict.not_ge (hi.trans (add_le_add le_rfl hd))

/-- A ray that starts on `S`, is `1`-Lipschitz on `[0, R]` and realizes the extended distance to
`S` at time `R` is an isometric segment on `[0, R]`. -/
theorem edist_ray_eq_of_infEDist_eq (hγ : LipschitzOnWith 1 γ (Icc 0 R)) (h0 : γ 0 ∈ S)
    (hR : infEDist (γ R) S = ENNReal.ofReal R) (ht : t ∈ Icc 0 R) (hu : u ∈ Icc 0 R) :
    edist (γ t) (γ u) = ENNReal.ofReal |t - u| := by
  wlog htu : t ≤ u generalizing t u
  · rw [edist_comm, abs_sub_comm]
    exact this hu ht (le_of_not_ge htu)
  rw [abs_of_nonpos (sub_nonpos.mpr htu), neg_sub]
  have heq : edist t u = ENNReal.ofReal (u - t) := by
    rw [edist_comm]
    exact Real.edist_eq_ofReal_sub_of_le htu
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul, heq] using hγ ht hu
  · apply ENNReal.le_of_add_le_add_left (a := ENNReal.ofReal t) ENNReal.ofReal_ne_top
    rw [← ENNReal.ofReal_add ht.1 (sub_nonneg.mpr htu), add_sub_cancel]
    have htd := hγ.infEDist_ray_eq_of_le h0 ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2 hR
    have hud := hγ.infEDist_ray_eq_of_le h0 hu ⟨hu.1.trans hu.2, le_rfl⟩ hu.2 hR
    have hi := infEDist_le_infEDist_add_edist (x := γ u) (y := γ t) (s := S)
    rwa [htd, hud, edist_comm (γ u) (γ t)] at hi

end Ray

section MetricRay

variable {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X} {S : Set X} {R t u : ℝ}

/-- Along a ray that starts on `S` and is `1`-Lipschitz on `[0, R]`, the distance to `S` at a time
`t ∈ [0, R]` is at most `t`. -/
theorem infDist_ray_le (hγ : LipschitzOnWith 1 γ (Icc 0 R)) (h0 : γ 0 ∈ S)
    (ht : t ∈ Icc 0 R) : infDist (γ t) S ≤ t :=
  ENNReal.toReal_le_of_le_ofReal ht.1 (hγ.infEDist_ray_le h0 ht)

/-- If a ray that starts on `S` and is `1`-Lipschitz on `[0, R]` realizes the distance to `S` at a
time `u`, then it realizes it at every time `t ∈ [0, u]`. -/
theorem infDist_ray_eq_of_le (hγ : LipschitzOnWith 1 γ (Icc 0 R)) (h0 : γ 0 ∈ S)
    (ht : t ∈ Icc 0 R) (hu : u ∈ Icc 0 R) (htu : t ≤ u) (hu_eq : infDist (γ u) S = u) :
    infDist (γ t) S = t :=
  (infEDist_eq_ofReal_iff ⟨_, h0⟩ ht.1).1 (hγ.infEDist_ray_eq_of_le h0 ht hu htu
    ((infEDist_eq_ofReal_iff ⟨_, h0⟩ hu.1).2 hu_eq))

/-- A ray that starts on `S`, is `1`-Lipschitz on `[0, R]` and realizes the distance to `S` at
time `R` is an isometric segment on `[0, R]`. -/
theorem dist_ray_eq_of_infDist_eq (hγ : LipschitzOnWith 1 γ (Icc 0 R)) (h0 : γ 0 ∈ S)
    (hR : infDist (γ R) S = R) (ht : t ∈ Icc 0 R) (hu : u ∈ Icc 0 R) :
    dist (γ t) (γ u) = |t - u| := by
  have h := hγ.edist_ray_eq_of_infEDist_eq h0
    ((infEDist_eq_ofReal_iff ⟨_, h0⟩ (ht.1.trans ht.2)).2 hR) ht hu
  rwa [edist_dist, ENNReal.ofReal_eq_ofReal_iff dist_nonneg (abs_nonneg _)] at h

end MetricRay

end LipschitzOnWith

namespace TauCeti

section CutTime

variable {X : Type*} [PseudoEMetricSpace X] {γ : ℝ → X} {S : Set X} {T : Set ℝ} {R t u : ℝ}

/-- The minimizing times of the ray `γ` from `S` within the time domain `T`, capped at `R`: the
times `t ∈ [0, R]` such that `[0, t] ⊆ T` and `γ` realizes the extended distance from `γ t` to `S`
at time `t`. -/
def rayMinimizingTimes (γ : ℝ → X) (S : Set X) (T : Set ℝ) (R : ℝ) : Set ℝ :=
  {t | t ∈ Icc 0 R ∧ Icc 0 t ⊆ T ∧ infEDist (γ t) S = ENNReal.ofReal t}

/-- The cut time of the ray `γ` from `S` within the time domain `T`, capped at `R`: the supremum
of its minimizing times `TauCeti.rayMinimizingTimes γ S T R`. -/
def rayCutTime (γ : ℝ → X) (S : Set X) (T : Set ℝ) (R : ℝ) : ℝ :=
  sSup (rayMinimizingTimes γ S T R)

@[simp]
theorem mem_rayMinimizingTimes :
    t ∈ rayMinimizingTimes γ S T R ↔
      t ∈ Icc 0 R ∧ Icc 0 t ⊆ T ∧ infEDist (γ t) S = ENNReal.ofReal t :=
  Iff.rfl

theorem rayCutTime_def : rayCutTime γ S T R = sSup (rayMinimizingTimes γ S T R) := by
  rfl

/-- The starting time is minimizing. -/
theorem zero_mem_rayMinimizingTimes (hR : 0 ≤ R) (h0T : 0 ∈ T) (h0S : γ 0 ∈ S) :
    0 ∈ rayMinimizingTimes γ S T R :=
  ⟨⟨le_rfl, hR⟩, by simpa only [Icc_self, singleton_subset_iff] using h0T,
    by rw [infEDist_zero_of_mem h0S, ENNReal.ofReal_zero]⟩

/-- The minimizing times are bounded above by the cap. -/
theorem bddAbove_rayMinimizingTimes : BddAbove (rayMinimizingTimes γ S T R) :=
  ⟨R, fun _ ht ↦ ht.1.2⟩

/-- The minimizing times grow with the time domain and the cap. -/
theorem rayMinimizingTimes_mono {T' : Set ℝ} {R' : ℝ} (hT : T ⊆ T') (hRR : R ≤ R') :
    rayMinimizingTimes γ S T R ⊆ rayMinimizingTimes γ S T' R' :=
  fun _ ⟨ht, htT, he⟩ ↦ ⟨⟨ht.1, ht.2.trans hRR⟩, htT.trans hT, he⟩

/-- Every minimizing time is at most the cut time. -/
theorem le_rayCutTime (ht : t ∈ rayMinimizingTimes γ S T R) : t ≤ rayCutTime γ S T R :=
  le_csSup bddAbove_rayMinimizingTimes ht

/-- The cut time grows with the time domain and the cap. -/
theorem rayCutTime_mono {T' : Set ℝ} {R' : ℝ} (hR : 0 ≤ R) (h0T : 0 ∈ T) (h0S : γ 0 ∈ S)
    (hT : T ⊆ T') (hRR : R ≤ R') : rayCutTime γ S T R ≤ rayCutTime γ S T' R' :=
  csSup_le_csSup bddAbove_rayMinimizingTimes ⟨0, zero_mem_rayMinimizingTimes hR h0T h0S⟩
    (rayMinimizingTimes_mono hT hRR)

/-- The cut time lies between `0` and the cap. -/
theorem rayCutTime_mem_Icc (hR : 0 ≤ R) (h0T : 0 ∈ T) (h0S : γ 0 ∈ S) :
    rayCutTime γ S T R ∈ Icc 0 R :=
  ⟨le_rayCutTime (zero_mem_rayMinimizingTimes hR h0T h0S),
    csSup_le ⟨0, zero_mem_rayMinimizingTimes hR h0T h0S⟩ fun _ ht ↦ ht.1.2⟩

/-- If the ray is minimizing up to the cap, the cut time is the cap. -/
theorem rayCutTime_eq_of_mem_rayMinimizingTimes (hR : R ∈ rayMinimizingTimes γ S T R) :
    rayCutTime γ S T R = R :=
  le_antisymm (csSup_le ⟨R, hR⟩ fun _ ht ↦ ht.1.2) (le_rayCutTime hR)

/-- Every nonnegative time before a minimizing time is minimizing. -/
theorem mem_rayMinimizingTimes_of_le
    (hγ : ∀ u ≤ R, Icc 0 u ⊆ T → LipschitzOnWith 1 γ (Icc 0 u)) (h0S : γ 0 ∈ S)
    (hu : u ∈ rayMinimizingTimes γ S T R) (ht : 0 ≤ t) (htu : t ≤ u) :
    t ∈ rayMinimizingTimes γ S T R := by
  obtain ⟨huR, huT, huEq⟩ := hu
  refine ⟨⟨ht, htu.trans huR.2⟩, (Icc_subset_Icc_right htu).trans huT, ?_⟩
  exact (hγ u huR.2 huT).infEDist_ray_eq_of_le h0S ⟨ht, htu⟩ ⟨huR.1, le_rfl⟩ htu huEq

/-- Every nonnegative time before the cut time is minimizing. -/
theorem mem_rayMinimizingTimes_of_lt_rayCutTime
    (hγ : ∀ u ≤ R, Icc 0 u ⊆ T → LipschitzOnWith 1 γ (Icc 0 u)) (hR : 0 ≤ R) (h0T : 0 ∈ T)
    (h0S : γ 0 ∈ S) (ht : 0 ≤ t) (hcut : t < rayCutTime γ S T R) :
    t ∈ rayMinimizingTimes γ S T R := by
  obtain ⟨u, hu, htu⟩ :=
    exists_lt_of_lt_csSup ⟨0, zero_mem_rayMinimizingTimes hR h0T h0S⟩ hcut
  exact mem_rayMinimizingTimes_of_le hγ h0S hu ht htu.le

/-- If the cut time lies in the time domain, it is a minimizing time. -/
theorem rayCutTime_mem_rayMinimizingTimes
    (hγ : ∀ u ≤ R, Icc 0 u ⊆ T → LipschitzOnWith 1 γ (Icc 0 u)) (hR : 0 ≤ R) (h0T : 0 ∈ T)
    (h0S : γ 0 ∈ S) (hcut : rayCutTime γ S T R ∈ T) :
    rayCutTime γ S T R ∈ rayMinimizingTimes γ S T R := by
  have hτ := rayCutTime_mem_Icc hR h0T h0S
  rcases hτ.1.eq_or_lt with hτ0 | hτp
  · rw [← hτ0]
    exact zero_mem_rayMinimizingTimes hR h0T h0S
  have hlt {v : ℝ} (hv : v ∈ Ico 0 (rayCutTime γ S T R)) : v ∈ rayMinimizingTimes γ S T R :=
    mem_rayMinimizingTimes_of_lt_rayCutTime hγ hR h0T h0S hv.1 hv.2
  have hprefix : Icc 0 (rayCutTime γ S T R) ⊆ T := by
    intro v hv
    rcases hv.2.lt_or_eq with hv' | rfl
    · exact (hlt ⟨hv.1, hv'⟩).2.1 (right_mem_Icc.mpr hv.1)
    · exact hcut
  refine ⟨hτ, hprefix, ?_⟩
  have he : EqOn (fun v ↦ infEDist (γ v) S) ENNReal.ofReal (Ioo 0 (rayCutTime γ S T R)) :=
    fun v hv ↦ (hlt ⟨hv.1.le, hv.2⟩).2.2
  refine he.of_subset_closure
    (continuous_infEDist.comp_continuousOn (hγ _ hτ.2 hprefix).continuousOn)
    ENNReal.continuous_ofReal.continuousOn Ioo_subset_Icc_self ?_ (right_mem_Icc.mpr hτ.1)
  rw [closure_Ioo hτp.ne]

/-- If the cut time lies in the time domain, a nonnegative time is minimizing if and only if it
is at most the cut time. -/
theorem le_rayCutTime_iff
    (hγ : ∀ u ≤ R, Icc 0 u ⊆ T → LipschitzOnWith 1 γ (Icc 0 u)) (hR : 0 ≤ R) (h0T : 0 ∈ T)
    (h0S : γ 0 ∈ S) (hcut : rayCutTime γ S T R ∈ T) (ht : 0 ≤ t) :
    t ≤ rayCutTime γ S T R ↔ t ∈ rayMinimizingTimes γ S T R :=
  ⟨mem_rayMinimizingTimes_of_le hγ h0S (rayCutTime_mem_rayMinimizingTimes hγ hR h0T h0S hcut)
    ht, le_rayCutTime⟩

/-- Past the cut time and before the cap, either the prefix leaves the time domain or the
extended distance to `S` is strictly smaller than the elapsed time. -/
theorem not_subset_or_infEDist_lt_of_rayCutTime_lt
    (hγ : ∀ u ≤ R, Icc 0 u ⊆ T → LipschitzOnWith 1 γ (Icc 0 u)) (h0S : γ 0 ∈ S)
    (ht : t ∈ Icc 0 R) (hcut : rayCutTime γ S T R < t) :
    ¬Icc 0 t ⊆ T ∨ infEDist (γ t) S < ENNReal.ofReal t := by
  by_cases hprefix : Icc 0 t ⊆ T
  · refine Or.inr (((hγ t ht.2 hprefix).infEDist_ray_le h0S ⟨ht.1, le_rfl⟩).lt_of_ne ?_)
    exact fun he ↦ hcut.not_ge (le_rayCutTime ⟨ht, hprefix, he⟩)
  · exact Or.inl hprefix

end CutTime

section ClosedSet

variable {X : Type*} [PseudoEMetricSpace X] {γ : ℝ → X} {S D : Set X} {R : ℝ}

/-- Let `γ` start on `S ∩ D` and be `1`-Lipschitz on `[0, R]`, and take as time domain the times
spent in a closed set `D`. Then the cut time is a minimizing time. -/
theorem rayCutTime_preimage_mem_rayMinimizingTimes (hD : IsClosed D) (hR : 0 ≤ R)
    (hγ : LipschitzOnWith 1 γ (Icc 0 R)) (h0S : γ 0 ∈ S) (h0D : γ 0 ∈ D) :
    rayCutTime γ S (γ ⁻¹' D) R ∈ rayMinimizingTimes γ S (γ ⁻¹' D) R := by
  have hγ' : ∀ u ≤ R, Icc 0 u ⊆ γ ⁻¹' D → LipschitzOnWith 1 γ (Icc 0 u) :=
    fun u hu _ ↦ hγ.mono (Icc_subset_Icc_right hu)
  refine rayCutTime_mem_rayMinimizingTimes hγ' hR h0D h0S ?_
  have hτ := rayCutTime_mem_Icc (S := S) (T := γ ⁻¹' D) hR h0D h0S
  rcases hτ.1.eq_or_lt with hτ0 | hτp
  · rw [mem_preimage, ← hτ0]
    exact h0D
  have hsub : γ '' Ioo 0 (rayCutTime γ S (γ ⁻¹' D) R) ⊆ D := by
    rintro _ ⟨v, hv, rfl⟩
    exact (mem_rayMinimizingTimes_of_lt_rayCutTime hγ' hR h0D h0S hv.1.le hv.2).2.1
      ⟨hv.1.le, le_rfl⟩
  have hcont : ContinuousWithinAt γ (Ioo 0 (rayCutTime γ S (γ ⁻¹' D) R))
      (rayCutTime γ S (γ ⁻¹' D) R) :=
    (hγ.continuousOn _ hτ).mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc_right hτ.2))
  have hmem : rayCutTime γ S (γ ⁻¹' D) R ∈ closure (Ioo 0 (rayCutTime γ S (γ ⁻¹' D) R)) := by
    rw [closure_Ioo hτp.ne]
    exact right_mem_Icc.mpr hτp.le
  exact hD.closure_subset_iff.mpr hsub (hcont.mem_closure_image hmem)

/-- The cut time of a continuous family of rays, with time domain the times spent in a closed set
`D`, is upper semicontinuous in the parameter. -/
theorem upperSemicontinuous_rayCutTime_preimage {P : Type*} [TopologicalSpace P]
    {Γ : P → ℝ → X} (hD : IsClosed D) (hR : 0 ≤ R) (hΓ : ∀ p, LipschitzOnWith 1 (Γ p) (Icc 0 R))
    (h0S : ∀ p, Γ p 0 ∈ S) (h0D : ∀ p, Γ p 0 ∈ D)
    (hc : ∀ t ∈ Icc 0 R, Continuous fun p ↦ Γ p t) :
    UpperSemicontinuous fun p ↦ rayCutTime (Γ p) S (Γ p ⁻¹' D) R := by
  have hI (p : P) : rayCutTime (Γ p) S (Γ p ⁻¹' D) R ∈ Icc 0 R :=
    rayCutTime_mem_Icc (T := Γ p ⁻¹' D) hR (h0D p) (h0S p)
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro t
  rcases le_or_gt t 0 with ht0 | ht0
  · convert isClosed_univ
    exact eq_univ_of_forall fun p ↦ ht0.trans (hI p).1
  rcases le_or_gt t R with htR | htR
  · have ht : t ∈ Icc 0 R := ⟨ht0.le, htR⟩
    have heq : (fun p ↦ rayCutTime (Γ p) S (Γ p ⁻¹' D) R) ⁻¹' Ici t =
        (⋂ u ∈ Icc 0 t, (fun p ↦ Γ p u) ⁻¹' D) ∩ {p | infEDist (Γ p t) S = ENNReal.ofReal t} := by
      ext p
      have hmem := rayCutTime_preimage_mem_rayMinimizingTimes hD hR (hΓ p) (h0S p) (h0D p)
      rw [mem_preimage, mem_Ici, le_rayCutTime_iff
        (fun u hu _ ↦ (hΓ p).mono (Icc_subset_Icc_right hu)) hR (h0D p) (h0S p)
        (hmem.2.1 (right_mem_Icc.mpr hmem.1.1)) ht0.le]
      simp only [mem_rayMinimizingTimes, ht, true_and, mem_inter_iff, mem_iInter₂,
        mem_preimage, mem_ofPred_eq, subset_def]
    rw [heq]
    exact (isClosed_biInter fun u (hu : u ∈ Icc 0 t) ↦
      hD.preimage (hc u ⟨hu.1, hu.2.trans htR⟩)).inter
      (isClosed_eq (continuous_infEDist.comp (hc t ht)) continuous_const)
  · convert isClosed_empty
    exact eq_empty_of_forall_notMem fun p hp ↦
      (htR.trans_le hp).not_ge (hI p).2

end ClosedSet

/-- In a pseudometric space, the minimizing times of a ray from a nonempty set can be read off the
real distance to the set. -/
theorem mem_rayMinimizingTimes_iff_infDist {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X}
    {S : Set X} {T : Set ℝ} {R t : ℝ} (hS : S.Nonempty) :
    t ∈ rayMinimizingTimes γ S T R ↔ t ∈ Icc 0 R ∧ Icc 0 t ⊆ T ∧ infDist (γ t) S = t := by
  rw [mem_rayMinimizingTimes]
  exact and_congr_right fun ht ↦ and_congr_right fun _ ↦ infEDist_eq_ofReal_iff hS ht.1

end TauCeti
