/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Cut radii of unit-speed rays

Let `γ : ℝ → X` be a curve in a pseudo-emetric space that starts on a set `S`. If `γ` is
`1`-Lipschitz on `[0, R]`, then `infEDist (γ t) S ≤ t` for `t ∈ [0, R]`. A time `t` is
*minimizing* when equality holds, that is, when the ray realizes the distance from `γ t` back to
`S`. Equality at some time forces equality at every earlier time, and makes the ray an isometric
segment up to that time.

The ray may only be relevant on a time domain `T`, for instance the times at which a geodesic is
defined and stays in a given region. `TauCeti.rayMinimizingTimes γ S T R` is the set of minimizing
times `t ∈ [0, R]` whose whole prefix `[0, t]` lies in `T`, and the cut radius
`TauCeti.rayCutRadius γ S T R` is its supremum. The cap `R` keeps the cut radius finite without
any boundedness assumption on `X`, and the extended metric allows intrinsic metrics with infinite
distances. The unit-speed condition is only needed on prefixes contained in `T`.

Every nonnegative time before the cut radius is minimizing, and so is the cut radius itself as
soon as it lies in `T`. Past the cut radius, either the prefix leaves `T` or the distance to `S` is
strictly smaller than the elapsed time. For a family of rays, the cut radius is measurable as soon
as the minimizing condition is measurable at rational times. When `T` is the set of times spent
in a closed set and the rays depend continuously on a parameter, the cut radius is upper
semicontinuous in that parameter, hence measurable.

## Main definitions

* `TauCeti.rayMinimizingTimes γ S T R`: the minimizing times in `[0, R]` with prefix in `T`.
* `TauCeti.rayCutRadius γ S T R`: the supremum of these times.

## Main results

* `TauCeti.infEDist_ray_eq_of_le`: the minimizing times of a ray form an initial interval.
* `TauCeti.edist_ray_eq_of_infEDist_eq`: a ray that is minimizing at time `R` is an isometric
  segment on `[0, R]`.
* `TauCeti.mem_rayMinimizingTimes_of_lt_rayCutRadius` and
  `TauCeti.rayCutRadius_mem_rayMinimizingTimes`: the nonnegative times before the cut radius are
  minimizing, and so is the cut radius when it lies in `T`.
* `TauCeti.not_subset_or_infEDist_lt_of_rayCutRadius_lt`: the alternative past the cut radius.
* `TauCeti.measurable_rayCutRadius`: measurability of the cut radius of a family of rays.
* `TauCeti.upperSemicontinuous_rayCutRadius_preimage`: upper semicontinuity of the cut radius of
  a continuous family of rays constrained to a closed set.
-/

public section

open Metric Set

noncomputable section

namespace TauCeti

section Ray

variable {X : Type*} [PseudoEMetricSpace X] {γ : ℝ → X} {S : Set X} {R t u : ℝ}

/-- Along a ray that starts on `S` and is `1`-Lipschitz on `[0, R]`, the extended distance to `S`
at a time `t ∈ [0, R]` is at most `t`. -/
theorem infEDist_ray_le (hγ : LipschitzOnWith 1 γ (Icc 0 R)) (h0 : γ 0 ∈ S)
    (ht : t ∈ Icc 0 R) : infEDist (γ t) S ≤ ENNReal.ofReal t := by
  have hd := hγ ht (show (0 : ℝ) ∈ Icc 0 R from ⟨le_rfl, ht.1.trans ht.2⟩)
  have heq : edist t 0 = ENNReal.ofReal t := by
    rw [edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
  simpa only [ENNReal.coe_one, one_mul, heq] using (infEDist_le_edist_of_mem h0).trans hd

/-- If a ray that starts on `S` and is `1`-Lipschitz on `[0, R]` realizes the extended distance to
`S` at a time `u`, then it realizes it at every time `t ∈ [0, u]`. -/
theorem infEDist_ray_eq_of_le (hγ : LipschitzOnWith 1 γ (Icc 0 R)) (h0 : γ 0 ∈ S)
    (ht : t ∈ Icc 0 R) (hu : u ∈ Icc 0 R) (htu : t ≤ u)
    (hu_eq : infEDist (γ u) S = ENNReal.ofReal u) : infEDist (γ t) S = ENNReal.ofReal t := by
  refine le_antisymm (infEDist_ray_le hγ h0 ht) (not_lt.1 fun hlt ↦ ?_)
  have hd := hγ hu ht
  have heq : edist u t = ENNReal.ofReal (u - t) := by
    rw [edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr htu)]
  simp only [ENNReal.coe_one, one_mul, heq] at hd
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
    rw [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr htu), neg_sub]
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul, heq] using hγ ht hu
  · apply ENNReal.le_of_add_le_add_left (a := ENNReal.ofReal t) ENNReal.ofReal_ne_top
    rw [← ENNReal.ofReal_add ht.1 (sub_nonneg.mpr htu), add_sub_cancel]
    have htd := infEDist_ray_eq_of_le hγ h0 ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2 hR
    have hud := infEDist_ray_eq_of_le hγ h0 hu ⟨hu.1.trans hu.2, le_rfl⟩ hu.2 hR
    have hi := infEDist_le_infEDist_add_edist (x := γ u) (y := γ t) (s := S)
    rwa [htd, hud, edist_comm (γ u) (γ t)] at hi

end Ray

section MetricRay

variable {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X} {S : Set X} {R t u : ℝ}

/-- Along a ray that starts on `S` and is `1`-Lipschitz on `[0, R]`, the distance to `S` at a time
`t ∈ [0, R]` is at most `t`. -/
theorem infDist_ray_le (hγ : LipschitzOnWith 1 γ (Icc 0 R)) (h0 : γ 0 ∈ S)
    (ht : t ∈ Icc 0 R) : infDist (γ t) S ≤ t := by
  have hd := hγ.dist_le_mul t ht 0 ⟨le_rfl, ht.1.trans ht.2⟩
  rw [NNReal.coe_one, one_mul, Real.dist_eq, sub_zero, abs_of_nonneg ht.1] at hd
  exact (infDist_le_dist_of_mem h0).trans hd

/-- If a ray that starts on `S` and is `1`-Lipschitz on `[0, R]` realizes the distance to `S` at a
time `u`, then it realizes it at every time `t ∈ [0, u]`. -/
theorem infDist_ray_eq_of_le (hγ : LipschitzOnWith 1 γ (Icc 0 R)) (h0 : γ 0 ∈ S)
    (ht : t ∈ Icc 0 R) (hu : u ∈ Icc 0 R) (htu : t ≤ u) (hu_eq : infDist (γ u) S = u) :
    infDist (γ t) S = t := by
  refine le_antisymm (infDist_ray_le hγ h0 ht) ?_
  have hd := hγ.dist_le_mul u hu t ht
  rw [NNReal.coe_one, one_mul, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr htu)] at hd
  have hi := infDist_le_infDist_add_dist (x := γ u) (y := γ t) (s := S)
  linarith

end MetricRay

section CutRadius

variable {X : Type*} [PseudoEMetricSpace X] {γ : ℝ → X} {S : Set X} {T : Set ℝ} {R t u : ℝ}

/-- The minimizing times of the ray `γ` from `S` within the time domain `T`, capped at `R`: the
times `t ∈ [0, R]` such that `[0, t] ⊆ T` and `γ` realizes the extended distance from `γ t` to `S`
at time `t`. -/
def rayMinimizingTimes (γ : ℝ → X) (S : Set X) (T : Set ℝ) (R : ℝ) : Set ℝ :=
  {t | t ∈ Icc 0 R ∧ Icc 0 t ⊆ T ∧ infEDist (γ t) S = ENNReal.ofReal t}

/-- The cut radius of the ray `γ` from `S` within the time domain `T`, capped at `R`: the supremum
of its minimizing times `TauCeti.rayMinimizingTimes γ S T R`. -/
def rayCutRadius (γ : ℝ → X) (S : Set X) (T : Set ℝ) (R : ℝ) : ℝ :=
  sSup (rayMinimizingTimes γ S T R)

@[simp]
theorem mem_rayMinimizingTimes :
    t ∈ rayMinimizingTimes γ S T R ↔
      t ∈ Icc 0 R ∧ Icc 0 t ⊆ T ∧ infEDist (γ t) S = ENNReal.ofReal t :=
  Iff.rfl

theorem rayCutRadius_def : rayCutRadius γ S T R = sSup (rayMinimizingTimes γ S T R) := by
  rfl

/-- The starting time is minimizing. -/
theorem zero_mem_rayMinimizingTimes (hR : 0 ≤ R) (h0T : 0 ∈ T) (h0S : γ 0 ∈ S) :
    0 ∈ rayMinimizingTimes γ S T R :=
  ⟨⟨le_rfl, hR⟩, by simpa only [Icc_self, singleton_subset_iff] using h0T,
    by rw [infEDist_zero_of_mem h0S, ENNReal.ofReal_zero]⟩

/-- The minimizing times are bounded above by the cap. -/
theorem bddAbove_rayMinimizingTimes : BddAbove (rayMinimizingTimes γ S T R) :=
  ⟨R, fun _ ht ↦ ht.1.2⟩

/-- Every minimizing time is at most the cut radius. -/
theorem le_rayCutRadius (ht : t ∈ rayMinimizingTimes γ S T R) : t ≤ rayCutRadius γ S T R :=
  le_csSup bddAbove_rayMinimizingTimes ht

/-- The cut radius lies between `0` and the cap. -/
theorem rayCutRadius_mem_Icc (hR : 0 ≤ R) (h0T : 0 ∈ T) (h0S : γ 0 ∈ S) :
    rayCutRadius γ S T R ∈ Icc 0 R :=
  ⟨le_rayCutRadius (zero_mem_rayMinimizingTimes hR h0T h0S),
    csSup_le ⟨0, zero_mem_rayMinimizingTimes hR h0T h0S⟩ fun _ ht ↦ ht.1.2⟩

/-- If the ray is minimizing up to the cap, the cut radius is the cap. -/
theorem rayCutRadius_eq_of_mem_rayMinimizingTimes (hR : R ∈ rayMinimizingTimes γ S T R) :
    rayCutRadius γ S T R = R :=
  le_antisymm (csSup_le ⟨R, hR⟩ fun _ ht ↦ ht.1.2) (le_rayCutRadius hR)

/-- Every nonnegative time before a minimizing time is minimizing. -/
theorem mem_rayMinimizingTimes_of_le
    (hγ : ∀ u ≤ R, Icc 0 u ⊆ T → LipschitzOnWith 1 γ (Icc 0 u)) (h0S : γ 0 ∈ S)
    (hu : u ∈ rayMinimizingTimes γ S T R) (ht : 0 ≤ t) (htu : t ≤ u) :
    t ∈ rayMinimizingTimes γ S T R := by
  obtain ⟨huR, huT, huEq⟩ := hu
  refine ⟨⟨ht, htu.trans huR.2⟩, (Icc_subset_Icc_right htu).trans huT, ?_⟩
  exact infEDist_ray_eq_of_le (hγ u huR.2 huT) h0S ⟨ht, htu⟩ ⟨huR.1, le_rfl⟩ htu huEq

/-- Every nonnegative time before the cut radius is minimizing. -/
theorem mem_rayMinimizingTimes_of_lt_rayCutRadius
    (hγ : ∀ u ≤ R, Icc 0 u ⊆ T → LipschitzOnWith 1 γ (Icc 0 u)) (hR : 0 ≤ R) (h0T : 0 ∈ T)
    (h0S : γ 0 ∈ S) (ht : 0 ≤ t) (hcut : t < rayCutRadius γ S T R) :
    t ∈ rayMinimizingTimes γ S T R := by
  obtain ⟨u, hu, htu⟩ :=
    exists_lt_of_lt_csSup ⟨0, zero_mem_rayMinimizingTimes hR h0T h0S⟩ hcut
  exact mem_rayMinimizingTimes_of_le hγ h0S hu ht htu.le

/-- If the cut radius lies in the time domain, it is a minimizing time. -/
theorem rayCutRadius_mem_rayMinimizingTimes
    (hγ : ∀ u ≤ R, Icc 0 u ⊆ T → LipschitzOnWith 1 γ (Icc 0 u)) (hR : 0 ≤ R) (h0T : 0 ∈ T)
    (h0S : γ 0 ∈ S) (hcut : rayCutRadius γ S T R ∈ T) :
    rayCutRadius γ S T R ∈ rayMinimizingTimes γ S T R := by
  have hτ := rayCutRadius_mem_Icc hR h0T h0S
  rcases hτ.1.eq_or_lt with hτ0 | hτp
  · rw [← hτ0]
    exact zero_mem_rayMinimizingTimes hR h0T h0S
  have hlt {v : ℝ} (hv : v ∈ Ico 0 (rayCutRadius γ S T R)) : v ∈ rayMinimizingTimes γ S T R :=
    mem_rayMinimizingTimes_of_lt_rayCutRadius hγ hR h0T h0S hv.1 hv.2
  have hprefix : Icc 0 (rayCutRadius γ S T R) ⊆ T := by
    intro v hv
    rcases hv.2.lt_or_eq with hv' | rfl
    · exact (hlt ⟨hv.1, hv'⟩).2.1 (right_mem_Icc.mpr hv.1)
    · exact hcut
  refine ⟨hτ, hprefix, ?_⟩
  have he : EqOn (fun v ↦ infEDist (γ v) S) ENNReal.ofReal (Ioo 0 (rayCutRadius γ S T R)) :=
    fun v hv ↦ (hlt ⟨hv.1.le, hv.2⟩).2.2
  refine he.of_subset_closure
    (continuous_infEDist.comp_continuousOn (hγ _ hτ.2 hprefix).continuousOn)
    ENNReal.continuous_ofReal.continuousOn Ioo_subset_Icc_self ?_ (right_mem_Icc.mpr hτ.1)
  rw [closure_Ioo hτp.ne]

/-- If the cut radius lies in the time domain, a nonnegative time is minimizing if and only if it
is at most the cut radius. -/
theorem le_rayCutRadius_iff
    (hγ : ∀ u ≤ R, Icc 0 u ⊆ T → LipschitzOnWith 1 γ (Icc 0 u)) (hR : 0 ≤ R) (h0T : 0 ∈ T)
    (h0S : γ 0 ∈ S) (hcut : rayCutRadius γ S T R ∈ T) (ht : 0 ≤ t) :
    t ≤ rayCutRadius γ S T R ↔ t ∈ rayMinimizingTimes γ S T R :=
  ⟨mem_rayMinimizingTimes_of_le hγ h0S (rayCutRadius_mem_rayMinimizingTimes hγ hR h0T h0S hcut)
    ht, le_rayCutRadius⟩

/-- Past the cut radius and before the cap, either the prefix leaves the time domain or the
extended distance to `S` is strictly smaller than the elapsed time. -/
theorem not_subset_or_infEDist_lt_of_rayCutRadius_lt
    (hγ : ∀ u ≤ R, Icc 0 u ⊆ T → LipschitzOnWith 1 γ (Icc 0 u)) (h0S : γ 0 ∈ S)
    (ht : t ∈ Icc 0 R) (hcut : rayCutRadius γ S T R < t) :
    ¬Icc 0 t ⊆ T ∨ infEDist (γ t) S < ENNReal.ofReal t := by
  by_cases hprefix : Icc 0 t ⊆ T
  · refine Or.inr ((infEDist_ray_le (hγ t ht.2 hprefix) h0S ⟨ht.1, le_rfl⟩).lt_of_ne ?_)
    exact fun he ↦ hcut.not_ge (le_rayCutRadius ⟨ht, hprefix, he⟩)
  · exact Or.inl hprefix

/-- The cut radius of a family of rays is measurable in the parameter as soon as, at every rational
time, the set of parameters for which that time is minimizing is measurable. -/
theorem measurable_rayCutRadius {P : Type*} [MeasurableSpace P] {Γ : P → ℝ → X}
    {T : P → Set ℝ} (hΓ : ∀ p, ∀ u ≤ R, Icc 0 u ⊆ T p → LipschitzOnWith 1 (Γ p) (Icc 0 u))
    (hR : 0 ≤ R) (h0T : ∀ p, 0 ∈ T p) (h0S : ∀ p, Γ p 0 ∈ S)
    (hmin : ∀ q : ℚ, MeasurableSet {p | (q : ℝ) ∈ rayMinimizingTimes (Γ p) S (T p) R}) :
    Measurable fun p ↦ rayCutRadius (Γ p) S (T p) R := by
  refine measurable_of_Ioi fun a ↦ ?_
  have heq : (fun p ↦ rayCutRadius (Γ p) S (T p) R) ⁻¹' Ioi a =
      ⋃ q : {q : ℚ // a < q}, {p | (q : ℝ) ∈ rayMinimizingTimes (Γ p) S (T p) R} := by
    ext p
    simp only [mem_preimage, mem_Ioi, mem_iUnion, Subtype.exists, exists_prop]
    constructor
    · intro hcut
      rcases lt_or_ge a 0 with ha | ha
      · exact ⟨0, by exact_mod_cast ha,
          by exact_mod_cast zero_mem_rayMinimizingTimes hR (h0T p) (h0S p)⟩
      · obtain ⟨q, haq, hqc⟩ := exists_rat_btwn hcut
        exact ⟨q, haq, mem_rayMinimizingTimes_of_lt_rayCutRadius (hΓ p) hR (h0T p) (h0S p)
          (ha.trans haq.le) hqc⟩
    · rintro ⟨q, haq, hq⟩
      exact haq.trans_le (le_rayCutRadius hq)
  rw [heq]
  exact MeasurableSet.iUnion fun q ↦ hmin q

end CutRadius

section ClosedSet

variable {X : Type*} [PseudoEMetricSpace X] {γ : ℝ → X} {S D : Set X} {R : ℝ}

/-- Let `γ` start on `S ∩ D` and be `1`-Lipschitz on `[0, R]`, and take as time domain the times
spent in a closed set `D`. Then the cut radius is a minimizing time. -/
theorem rayCutRadius_preimage_mem_rayMinimizingTimes (hD : IsClosed D) (hR : 0 ≤ R)
    (hγ : LipschitzOnWith 1 γ (Icc 0 R)) (h0S : γ 0 ∈ S) (h0D : γ 0 ∈ D) :
    rayCutRadius γ S (γ ⁻¹' D) R ∈ rayMinimizingTimes γ S (γ ⁻¹' D) R := by
  have hγ' : ∀ u ≤ R, Icc 0 u ⊆ γ ⁻¹' D → LipschitzOnWith 1 γ (Icc 0 u) :=
    fun u hu _ ↦ hγ.mono (Icc_subset_Icc_right hu)
  refine rayCutRadius_mem_rayMinimizingTimes hγ' hR h0D h0S ?_
  have hτ := rayCutRadius_mem_Icc (S := S) (T := γ ⁻¹' D) hR h0D h0S
  rcases hτ.1.eq_or_lt with hτ0 | hτp
  · rw [mem_preimage, ← hτ0]
    exact h0D
  have hsub : γ '' Ioo 0 (rayCutRadius γ S (γ ⁻¹' D) R) ⊆ D := by
    rintro _ ⟨v, hv, rfl⟩
    exact (mem_rayMinimizingTimes_of_lt_rayCutRadius hγ' hR h0D h0S hv.1.le hv.2).2.1
      ⟨hv.1.le, le_rfl⟩
  have hcont : ContinuousWithinAt γ (Ioo 0 (rayCutRadius γ S (γ ⁻¹' D) R))
      (rayCutRadius γ S (γ ⁻¹' D) R) :=
    (hγ.continuousOn _ hτ).mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc_right hτ.2))
  have hmem : rayCutRadius γ S (γ ⁻¹' D) R ∈ closure (Ioo 0 (rayCutRadius γ S (γ ⁻¹' D) R)) := by
    rw [closure_Ioo hτp.ne]
    exact right_mem_Icc.mpr hτp.le
  exact hD.closure_subset_iff.mpr hsub (hcont.mem_closure_image hmem)

/-- The cut radius of a continuous family of rays constrained to a closed set is upper
semicontinuous in the parameter. -/
theorem upperSemicontinuous_rayCutRadius_preimage {P : Type*} [TopologicalSpace P]
    {Γ : P → ℝ → X} (hD : IsClosed D) (hR : 0 ≤ R) (hΓ : ∀ p, LipschitzOnWith 1 (Γ p) (Icc 0 R))
    (h0S : ∀ p, Γ p 0 ∈ S) (h0D : ∀ p, Γ p 0 ∈ D)
    (hc : ∀ t ∈ Icc 0 R, Continuous fun p ↦ Γ p t) :
    UpperSemicontinuous fun p ↦ rayCutRadius (Γ p) S (Γ p ⁻¹' D) R := by
  have hI (p : P) : rayCutRadius (Γ p) S (Γ p ⁻¹' D) R ∈ Icc 0 R :=
    rayCutRadius_mem_Icc (T := Γ p ⁻¹' D) hR (h0D p) (h0S p)
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro t
  rcases le_or_gt t 0 with ht0 | ht0
  · convert isClosed_univ
    exact eq_univ_of_forall fun p ↦ ht0.trans (hI p).1
  rcases le_or_gt t R with htR | htR
  · have ht : t ∈ Icc 0 R := ⟨ht0.le, htR⟩
    have heq : (fun p ↦ rayCutRadius (Γ p) S (Γ p ⁻¹' D) R) ⁻¹' Ici t =
        (⋂ u ∈ Icc 0 t, (fun p ↦ Γ p u) ⁻¹' D) ∩ {p | infEDist (Γ p t) S = ENNReal.ofReal t} := by
      ext p
      have hmem := rayCutRadius_preimage_mem_rayMinimizingTimes hD hR (hΓ p) (h0S p) (h0D p)
      rw [mem_preimage, mem_Ici, le_rayCutRadius_iff
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

/-- The cut radius of a continuous family of rays constrained to a closed set is measurable in the
parameter. -/
theorem measurable_rayCutRadius_preimage {P : Type*} [TopologicalSpace P] [MeasurableSpace P]
    [OpensMeasurableSpace P] {Γ : P → ℝ → X} (hD : IsClosed D) (hR : 0 ≤ R)
    (hΓ : ∀ p, LipschitzOnWith 1 (Γ p) (Icc 0 R)) (h0S : ∀ p, Γ p 0 ∈ S)
    (h0D : ∀ p, Γ p 0 ∈ D) (hc : ∀ t ∈ Icc 0 R, Continuous fun p ↦ Γ p t) :
    Measurable fun p ↦ rayCutRadius (Γ p) S (Γ p ⁻¹' D) R :=
  (upperSemicontinuous_rayCutRadius_preimage hD hR hΓ h0S h0D hc).measurable

end ClosedSet

/-- In a pseudometric space, the minimizing times of a ray from a nonempty set can be read off the
real distance to the set. -/
theorem mem_rayMinimizingTimes_iff_infDist {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X}
    {S : Set X} {T : Set ℝ} {R t : ℝ} (hS : S.Nonempty) :
    t ∈ rayMinimizingTimes γ S T R ↔ t ∈ Icc 0 R ∧ Icc 0 t ⊆ T ∧ infDist (γ t) S = t := by
  rw [mem_rayMinimizingTimes]
  refine and_congr_right fun ht ↦ and_congr_right fun _ ↦ ?_
  constructor
  · intro h
    rw [infDist, h, ENNReal.toReal_ofReal ht.1]
  · intro h
    have he : ENNReal.ofReal (infDist (γ t) S) = infEDist (γ t) S := by
      rw [infDist, ENNReal.ofReal_toReal (infEDist_ne_top hS)]
    rw [← he, h]

end TauCeti
