/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Scalar lattice gauges

Let `K` be a normed field and `s` a subset of a `K`-module `M`. The *scalar lattice gauge* of `s`
is
`latticeGauge K s x = inf {‖c‖ | c ∈ Kˣ, x ∈ c • s}`.
It is the nonarchimedean analogue of the Minkowski functional `gauge`: the scaling factors are
scalars of `K` rather than positive reals, and convexity of `s` is replaced by closure of `s`
under addition. Thus `s` plays the role of a lattice over the closed unit ball of `K`, as for
the unit ball `A₀` of a Banach algebra over a complete valued field, or a bounded open
`A₀`-submodule `M₀` of a Banach module over it.

Over any normed field the gauge scales exactly by nonzero scalars,
`latticeGauge K s (a • x) = ‖a‖ * latticeGauge K s x` for `a ≠ 0`, and rescaling `s` by a nonzero
scalar `c` divides the gauge by `‖c‖`. The remaining results assume that `K` is nontrivially
normed. Then the gauge scales exactly by every scalar, and for a balanced absorbent `s` with
`s + s ⊆ s` it is ultrametric, so it is a seminorm `TauCeti.latticeGaugeSeminorm`. Its open unit
ball lies in `s`, and `s` lies in its closed unit ball. On the scalar line the gauge of the closed
unit ball is the norm.
If `M` is a topological module and `s` is a balanced bounded neighbourhood of zero, the open gauge
balls are a basis of neighbourhoods of zero, so the gauge induces the topology of `M` and its
uniform structure, so it is complete when `M` is; its zero set is the closure of zero, so it
separates points exactly when `M` is Hausdorff. If moreover `s + s ⊆ s` and `M` is
Hausdorff, the gauge is bundled as an ultrametric norm
`TauCeti.latticeGaugeNormedAddCommGroup` inducing the uniform structure of `M`, complete when `M`
is.
Finally, the gauges of a lattice `A₀` in an algebra `A` and of a lattice `M₀` in an `A`-module
are compatible: `A₀ • M₀ ⊆ M₀` gives
`latticeGauge K M₀ (a • m) ≤ latticeGauge K A₀ a * latticeGauge K M₀ m`; in particular the gauge
of a multiplicatively closed lattice is submultiplicative, and it takes the value one at one in
a nonzero Hausdorff algebra.

## Main definitions

* `TauCeti.latticeGauge`: the scalar lattice gauge of a subset of a module over a normed field.
* `TauCeti.latticeGaugeSeminorm`: over a nontrivially normed field, the gauge of a balanced
  absorbent set closed under addition, as a seminorm.
* `TauCeti.latticeGaugeNormedAddCommGroup`, `TauCeti.latticeGaugeNormedSpace`: in a Hausdorff
  uniform module, the gauge of a balanced bounded neighbourhood of zero closed under addition, as
  a norm inducing the given uniform structure.

## Main results

* `TauCeti.latticeGauge_smul`: exact scaling by every scalar of a nontrivially normed field.
* `TauCeti.latticeGauge_smul_left`, `TauCeti.latticeGauge_mono`: dependence on the lattice.
* `TauCeti.isNonarchimedean_latticeGauge`: the gauge is ultrametric.
* `TauCeti.hasBasis_latticeGauge`, `TauCeti.withSeminorms_latticeGaugeSeminorm`: the gauge of a
  balanced bounded neighbourhood of zero (closed under addition, for the seminorm) induces the
  topology.
* `TauCeti.hasBasis_uniformity_latticeGauge`, `TauCeti.exists_tendsto_latticeGauge_sub`: it also
  induces the uniform structure, and is complete when `M` is.
* `TauCeti.latticeGauge_eq_zero_iff`, `TauCeti.t2Space_iff_forall_latticeGauge_eq_zero_iff`: its
  zero set is the closure of zero, so it separates points exactly in the Hausdorff case.
* `TauCeti.isUltrametricDist_latticeGaugeNormedAddCommGroup`,
  `TauCeti.completeSpace_latticeGaugeNormedAddCommGroup`: the bundled norm is ultrametric, and
  complete when `M` is.
* `TauCeti.latticeGauge_smul_le`, `TauCeti.latticeGauge_mul_le`, `TauCeti.latticeGauge_one`:
  compatibility with module and algebra structures.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §1.
* W. H. Schikhof, *Ultrametric Calculus*, Cambridge University Press, 1984.
-/

public section

open Filter Set Topology Bornology Pointwise Uniformity

namespace TauCeti

section NormedField

variable (K : Type*) {M : Type*} [NormedField K] [AddCommGroup M] [Module K M]

/-- The scalar lattice gauge `inf {‖c‖ | c ≠ 0, x ∈ c • s}` of a subset `s` of a `K`-module.
It is the nonarchimedean counterpart of the Minkowski functional `gauge`, with nonzero scalars
of `K` in place of positive reals. Its value is `0` when `x ∉ c • s` for every nonzero `c` (the
infimum of the empty set). -/
noncomputable def latticeGauge (s : Set M) (x : M) : ℝ :=
  sInf (norm '' {c : K | c ≠ 0 ∧ x ∈ c • s})

variable {K} {s : Set M} {x : M}

theorem latticeGauge_def (s : Set M) (x : M) :
    latticeGauge K s x = sInf (norm '' {c : K | c ≠ 0 ∧ x ∈ c • s}) :=
  (rfl)

theorem latticeGauge_nonneg (s : Set M) (x : M) : 0 ≤ latticeGauge K s x := by
  rw [latticeGauge_def]
  exact Real.sInf_nonneg <| by
    rintro _ ⟨c, -, rfl⟩
    exact norm_nonneg c

private theorem bddBelow_norm_image (s : Set M) (x : M) :
    BddBelow (norm '' {c : K | c ≠ 0 ∧ x ∈ c • s}) :=
  ⟨0, by rintro _ ⟨d, -, rfl⟩; exact norm_nonneg d⟩

/-- A nonzero scalar `c` with `x ∈ c • s` bounds the gauge of `x` by `‖c‖`. -/
theorem latticeGauge_le_norm {c : K} (hc : c ≠ 0) (hx : x ∈ c • s) : latticeGauge K s x ≤ ‖c‖ :=
  (latticeGauge_def s x).trans_le <| csInf_le (bddBelow_norm_image s x) ⟨c, ⟨hc, hx⟩, rfl⟩

/-- Points of `s` have gauge at most one. -/
theorem latticeGauge_le_one (hx : x ∈ s) : latticeGauge K s x ≤ 1 := by
  simpa using latticeGauge_le_norm (K := K) one_ne_zero (by simpa using hx)

/-- The gauge scales exactly by nonzero scalars. -/
theorem latticeGauge_smul_of_ne_zero {a : K} (ha : a ≠ 0) (s : Set M) (x : M) :
    latticeGauge K s (a • x) = ‖a‖ * latticeGauge K s x := by
  have h : norm '' {c : K | c ≠ 0 ∧ a • x ∈ c • s} =
      ‖a‖ • (norm '' {c : K | c ≠ 0 ∧ x ∈ c • s}) := by
    ext r
    simp only [mem_image, mem_ofPred_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨c, ⟨hc, y, hy, hyx⟩, rfl⟩
      refine ⟨‖a⁻¹ * c‖, ⟨a⁻¹ * c, ⟨by simp [ha, hc], y, hy, ?_⟩, rfl⟩, ?_⟩
      · rw [mul_smul, hyx, inv_smul_smul₀ ha]
      · rw [← norm_mul, mul_inv_cancel_left₀ ha]
    · rintro ⟨_, ⟨c, ⟨hc, y, hy, rfl⟩, rfl⟩, rfl⟩
      exact ⟨a * c, ⟨mul_ne_zero ha hc, y, hy, mul_smul a c y⟩, norm_mul a c⟩
  rw [latticeGauge_def, h, Real.sInf_smul_of_nonneg (norm_nonneg a), smul_eq_mul,
    latticeGauge_def]

/-- Rescaling the lattice by a nonzero scalar `c` divides the gauge by `‖c‖`. -/
theorem latticeGauge_smul_left {c : K} (hc : c ≠ 0) (s : Set M) (x : M) :
    latticeGauge K (c • s) x = ‖c‖⁻¹ * latticeGauge K s x := by
  have h : {d : K | d ≠ 0 ∧ x ∈ d • c • s} = {d : K | d ≠ 0 ∧ c⁻¹ • x ∈ d • s} := by
    ext d
    simp only [mem_ofPred_eq, smul_comm d c s, mem_smul_set_iff_inv_smul_mem₀ hc]
  rw [latticeGauge_def, h, ← latticeGauge_def, latticeGauge_smul_of_ne_zero (inv_ne_zero hc),
    norm_inv]

@[simp]
theorem latticeGauge_neg (s : Set M) (x : M) : latticeGauge K s (-x) = latticeGauge K s x := by
  simpa using latticeGauge_smul_of_ne_zero (K := K) (neg_ne_zero.2 one_ne_zero) s x

end NormedField

section NontriviallyNormedField

variable {K M : Type*} [NontriviallyNormedField K] [AddCommGroup M] [Module K M] {s : Set M}
  {x : M}

@[simp]
theorem latticeGauge_zero (s : Set M) : latticeGauge K s 0 = 0 := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
  have h := latticeGauge_smul_of_ne_zero (norm_pos_iff.1 (one_pos.trans hc)) s (0 : M)
  rw [smul_zero] at h
  nlinarith [latticeGauge_nonneg (K := K) s 0]

/-- An absorbent set absorbs every point by a nonzero scalar, so the set whose infimum defines
the gauge is nonempty. -/
private theorem nonempty_norm_image (hs : Absorbent K s) (x : M) :
    (norm '' {c : K | c ≠ 0 ∧ x ∈ c • s}).Nonempty := by
  obtain ⟨c, hx, hc⟩ := ((hs x).and (eventually_ne_cobounded 0)).exists
  exact ⟨‖c‖, c, ⟨hc, hx rfl⟩, rfl⟩

/-- For an absorbent set, the gauge of `x` is below `r` exactly when `x ∈ c • s` for some
nonzero scalar `c` of norm below `r`. -/
theorem latticeGauge_lt_iff (hs : Absorbent K s) {r : ℝ} :
    latticeGauge K s x < r ↔ ∃ c : K, c ≠ 0 ∧ x ∈ c • s ∧ ‖c‖ < r := by
  refine ⟨fun h ↦ ?_, fun ⟨c, hc, hx, hcr⟩ ↦ (latticeGauge_le_norm hc hx).trans_lt hcr⟩
  rw [latticeGauge_def] at h
  obtain ⟨_, ⟨c, ⟨hc, hx⟩, rfl⟩, hcr⟩ := exists_lt_of_csInf_lt (nonempty_norm_image hs x) h
  exact ⟨c, hc, hx, hcr⟩

/-- Enlarging an absorbent set decreases its gauge. -/
theorem latticeGauge_mono {t : Set M} (hs : Absorbent K s) (hst : s ⊆ t) :
    latticeGauge K t ≤ latticeGauge K s := fun x ↦ by
  rw [latticeGauge_def, latticeGauge_def]
  exact csInf_le_csInf (bddBelow_norm_image t x) (nonempty_norm_image hs x)
    (image_mono fun c hc ↦ ⟨hc.1, smul_set_mono hst hc.2⟩)

/-- The gauge scales exactly by every scalar. -/
theorem latticeGauge_smul (s : Set M) (a : K) (x : M) :
    latticeGauge K s (a • x) = ‖a‖ * latticeGauge K s x := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · exact latticeGauge_smul_of_ne_zero ha s x

/-- For a balanced set, gauge less than one forces membership. -/
theorem mem_of_latticeGauge_lt_one (hb : Balanced K s) (hs : Absorbent K s)
    (hx : latticeGauge K s x < 1) : x ∈ s := by
  obtain ⟨c, -, hx, hc⟩ := (latticeGauge_lt_iff hs).1 hx
  exact hb c hc.le hx

/-- The gauge of a balanced absorbent set closed under addition is ultrametric. -/
theorem isNonarchimedean_latticeGauge (hb : Balanced K s) (hadd : s + s ⊆ s)
    (hs : Absorbent K s) : IsNonarchimedean (latticeGauge K s) := by
  -- Both summands lie in `d • s` for the larger of two near-optimal scalars `c, d`.
  have key : ∀ {x y : M} {c d : K}, d ≠ 0 → ‖c‖ ≤ ‖d‖ → x ∈ c • s → y ∈ d • s →
      latticeGauge K s (x + y) ≤ ‖d‖ := fun hd hcd hx hy ↦
    latticeGauge_le_norm hd <| by
      obtain ⟨x', hx', rfl⟩ := hb.smul_mono hcd hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨x' + y', hadd (add_mem_add hx' hy'), smul_add _ x' y'⟩
  intro x y
  refine le_of_forall_gt_imp_ge_of_dense fun r hr ↦ ?_
  obtain ⟨c, hc, hx, hcr⟩ := (latticeGauge_lt_iff hs).1 ((le_max_left _ _).trans_lt hr)
  obtain ⟨d, hd, hy, hdr⟩ := (latticeGauge_lt_iff hs).1 ((le_max_right _ _).trans_lt hr)
  rcases le_total ‖c‖ ‖d‖ with hcd | hdc
  · exact (key hd hcd hx hy).trans hdr.le
  · exact (add_comm x y ▸ key hc hdc hy hx).trans hcr.le

variable (K) in
/-- The scalar lattice gauge of a balanced absorbent set closed under addition, as a seminorm. -/
noncomputable def latticeGaugeSeminorm (hb : Balanced K s) (hadd : s + s ⊆ s)
    (hs : Absorbent K s) : Seminorm K M where
  toFun := latticeGauge K s
  map_zero' := latticeGauge_zero s
  add_le' x y := (isNonarchimedean_latticeGauge hb hadd hs x y).trans <|
    max_le_add_of_nonneg (latticeGauge_nonneg s x) (latticeGauge_nonneg s y)
  neg' := latticeGauge_neg s
  smul' := latticeGauge_smul s

@[simp]
theorem coe_latticeGaugeSeminorm (hb : Balanced K s) (hadd : s + s ⊆ s) (hs : Absorbent K s) :
    ⇑(latticeGaugeSeminorm K hb hadd hs) = latticeGauge K s :=
  (rfl)

section Topology

variable [TopologicalSpace M] [ContinuousSMul K M]

/-- The open gauge balls of a balanced bounded neighbourhood of zero form a basis of
neighbourhoods of zero. -/
theorem hasBasis_latticeGauge (hb : Balanced K s) (hs₀ : s ∈ 𝓝 0) (hbd : IsVonNBounded K s) :
    (𝓝 (0 : M)).HasBasis (fun r : ℝ ↦ 0 < r) fun r ↦ {x | latticeGauge K s x < r} := by
  refine ⟨fun U ↦ ⟨fun hU ↦ ?_, fun ⟨r, hr, hrU⟩ ↦ mem_of_superset ?_ hrU⟩⟩
  · -- A bounded `s` is absorbed by `U`, so some `a⁻¹ • s` lies in `U`.
    obtain ⟨a, ha, ha₀⟩ := ((hbd hU).and (eventually_ne_cobounded 0)).exists
    refine ⟨‖a⁻¹‖, norm_pos_iff.2 (inv_ne_zero ha₀), fun x hx ↦ ?_⟩
    obtain ⟨c, -, hx, hc⟩ := (latticeGauge_lt_iff (absorbent_nhds_zero hs₀)).1 hx
    rw [← smul_set_subset_smul_set_iff₀ (inv_ne_zero ha₀), inv_smul_smul₀ ha₀] at ha
    exact ha (hb.smul_mono hc.le hx)
  · obtain ⟨c, hc₀, hcr⟩ := NormedField.exists_norm_lt K hr
    have hc : c ≠ 0 := norm_pos_iff.1 hc₀
    exact mem_of_superset ((set_smul_mem_nhds_zero_iff hc).2 hs₀) fun x hx ↦
      (latticeGauge_le_norm hc hx).trans_lt hcr

/-- The gauge of a balanced bounded neighbourhood of zero closed under addition induces the
topology of `M`. -/
theorem withSeminorms_latticeGaugeSeminorm [IsTopologicalAddGroup M] (hb : Balanced K s)
    (hadd : s + s ⊆ s) (hs₀ : s ∈ 𝓝 0) (hbd : IsVonNBounded K s) :
    WithSeminorms fun _ : Unit ↦ latticeGaugeSeminorm K hb hadd (absorbent_nhds_zero hs₀) := by
  refine withSeminorms_iff_mem_nhds_isVonNBounded.2 ⟨?_, hbd.subset fun x hx ↦ ?_⟩
  · simpa [Seminorm.ball_zero_eq] using (hasBasis_latticeGauge hb hs₀ hbd).mem_of_mem one_pos
  · rw [Seminorm.mem_ball_zero, coe_latticeGaugeSeminorm] at hx
    exact mem_of_latticeGauge_lt_one hb (absorbent_nhds_zero hs₀) hx

/-- The zero set of the gauge of a balanced bounded neighbourhood of zero is the closure of
zero. -/
theorem latticeGauge_eq_zero_iff [IsTopologicalAddGroup M] (hb : Balanced K s) (hs₀ : s ∈ 𝓝 0)
    (hbd : IsVonNBounded K s) :
    latticeGauge K s x = 0 ↔ x ∈ closure ({0} : Set M) := by
  rw [R0Space.closure_singleton, (hasBasis_latticeGauge hb hs₀ hbd).ker]
  simp only [mem_iInter, mem_ofPred_eq]
  exact ⟨fun h r hr ↦ h ▸ hr, fun h ↦ le_antisymm (le_of_forall_gt_imp_ge_of_dense
    fun r hr ↦ (h r hr).le) (latticeGauge_nonneg s x)⟩

/-- The gauge of a balanced bounded neighbourhood of zero separates points exactly when `M` is
Hausdorff. -/
theorem t2Space_iff_forall_latticeGauge_eq_zero_iff [IsTopologicalAddGroup M] (hb : Balanced K s)
    (hs₀ : s ∈ 𝓝 0) (hbd : IsVonNBounded K s) :
    T2Space M ↔ ∀ x, (latticeGauge K s x = 0 ↔ x = 0) := by
  simp_rw [latticeGauge_eq_zero_iff hb hs₀ hbd, IsTopologicalAddGroup.t2Space_iff_zero_closed,
    ← closure_subset_iff_isClosed, Set.subset_def, Set.mem_singleton_iff]
  exact ⟨fun h x ↦ ⟨h x, fun hx ↦ hx ▸ subset_closure rfl⟩, fun h x ↦ (h x).1⟩

end Topology

section Uniformity

variable [UniformSpace M] [IsUniformAddGroup M] [ContinuousSMul K M]

/-- The gauge of a balanced bounded neighbourhood of zero also induces the uniform structure of
`M`: the entourages `{(x, y) | latticeGauge K s (y - x) < r}` form a basis of the uniformity. -/
theorem hasBasis_uniformity_latticeGauge (hb : Balanced K s) (hs₀ : s ∈ 𝓝 0)
    (hbd : IsVonNBounded K s) :
    (𝓤 M).HasBasis (fun r : ℝ ↦ 0 < r) fun r ↦ {p | latticeGauge K s (p.2 - p.1) < r} :=
  (hasBasis_latticeGauge hb hs₀ hbd).uniformity_of_nhds_zero

/-- If `M` is complete, then so is the gauge of a balanced bounded neighbourhood of zero: a
sequence which is Cauchy for the gauge converges to some `x` in the gauge. -/
theorem exists_tendsto_latticeGauge_sub [CompleteSpace M] (hb : Balanced K s) (hs₀ : s ∈ 𝓝 0)
    (hbd : IsVonNBounded K s) {u : ℕ → M}
    (hu : ∀ r > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, latticeGauge K s (u n - u m) < r) :
    ∃ x, Tendsto (fun n ↦ latticeGauge K s (u n - x)) atTop (𝓝 0) := by
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete <|
    (hasBasis_uniformity_latticeGauge hb hs₀ hbd).cauchySeq_iff.2 hu
  refine ⟨x, tendsto_order.2 ⟨fun r hr ↦ .of_forall fun n ↦
    hr.trans_le (latticeGauge_nonneg _ _), fun r hr ↦ ?_⟩⟩
  exact (hasBasis_latticeGauge hb hs₀ hbd).tendsto_right_iff.1 (tendsto_sub_nhds_zero_iff.2 hx)
    r hr

variable [T2Space M]

variable (K) in
/-- In a Hausdorff uniform module, the gauge of a balanced bounded neighbourhood `s` of zero closed
under addition, as a norm whose uniform structure is the given one of `M`. This is not an
instance: see note [reducible non-instances]. -/
noncomputable abbrev latticeGaugeNormedAddCommGroup (hb : Balanced K s) (hadd : s + s ⊆ s)
    (hs₀ : s ∈ 𝓝 0) (hbd : IsVonNBounded K s) : NormedAddCommGroup M :=
  letI : Norm M := ⟨latticeGauge K s⟩
  have core : NormedSpace.Core K M :=
    { norm_nonneg := latticeGauge_nonneg s
      norm_smul := latticeGauge_smul s
      norm_triangle x y := (isNonarchimedean_latticeGauge hb hadd (absorbent_nhds_zero hs₀) x
        y).trans <| max_le_add_of_nonneg (latticeGauge_nonneg s x) (latticeGauge_nonneg s y)
      norm_eq_zero_iff := (t2Space_iff_forall_latticeGauge_eq_zero_iff hb hs₀ hbd).1 inferInstance }
  .ofCoreReplaceUniformity core <| (hasBasis_uniformity_latticeGauge hb hs₀ hbd).eq_of_same_basis <|
    (@Metric.uniformity_basis_dist M (.ofSeminormedSpaceCore core.toCore)).congr (fun _ ↦ .rfl)
      -- `PseudoMetricSpace.ofSeminormedSpaceCore` defines `dist x y` as `‖-x + y‖`, which
      -- `neg_add_eq_sub` turns into `‖y - x‖`; the closing `rfl` unfolds the local `Norm`
      -- instance above, whose norm is `latticeGauge K s` by definition.
      fun _ _ ↦ by simp only [dist, neg_add_eq_sub]; rfl

/-- The norm of `TauCeti.latticeGaugeNormedAddCommGroup` is the lattice gauge. -/
theorem latticeGaugeNormedAddCommGroup_norm (hb : Balanced K s) (hadd : s + s ⊆ s)
    (hs₀ : s ∈ 𝓝 0) (hbd : IsVonNBounded K s) (x : M) :
    letI := latticeGaugeNormedAddCommGroup K hb hadd hs₀ hbd
    ‖x‖ = latticeGauge K s x :=
  (rfl)

variable (K) in
/-- The bundled lattice gauge norm `TauCeti.latticeGaugeNormedAddCommGroup` scales exactly by
scalars of `K`, so it makes `M` a normed `K`-space. This is not an instance: see note
[reducible non-instances]. -/
noncomputable abbrev latticeGaugeNormedSpace (hb : Balanced K s) (hadd : s + s ⊆ s)
    (hs₀ : s ∈ 𝓝 0) (hbd : IsVonNBounded K s) :
    letI := latticeGaugeNormedAddCommGroup K hb hadd hs₀ hbd
    NormedSpace K M :=
  letI := latticeGaugeNormedAddCommGroup K hb hadd hs₀ hbd
  { norm_smul_le a x := (latticeGauge_smul s a x).le }

/-- The bundled lattice gauge norm is ultrametric. -/
theorem isUltrametricDist_latticeGaugeNormedAddCommGroup (hb : Balanced K s) (hadd : s + s ⊆ s)
    (hs₀ : s ∈ 𝓝 0) (hbd : IsVonNBounded K s) :
    letI := latticeGaugeNormedAddCommGroup K hb hadd hs₀ hbd
    IsUltrametricDist M :=
  letI := latticeGaugeNormedAddCommGroup K hb hadd hs₀ hbd
  .isUltrametricDist_of_isNonarchimedean_norm <|
    isNonarchimedean_latticeGauge hb hadd (absorbent_nhds_zero hs₀)

/-- The bundled lattice gauge norm is complete when `M` is, since it induces the uniform structure
of `M`. -/
theorem completeSpace_latticeGaugeNormedAddCommGroup [CompleteSpace M] (hb : Balanced K s)
    (hadd : s + s ⊆ s) (hs₀ : s ∈ 𝓝 0) (hbd : IsVonNBounded K s) :
    @CompleteSpace M (latticeGaugeNormedAddCommGroup K hb hadd hs₀ hbd).toUniformSpace :=
  ‹_›

end Uniformity

/-- On the scalar line, the gauge of the closed unit ball is the norm. -/
@[simp]
theorem latticeGauge_closedBall_one (x : K) :
    latticeGauge K (Metric.closedBall (0 : K) 1) x = ‖x‖ := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  refine le_antisymm (latticeGauge_le_norm hx ⟨1, by simp, by simp⟩) (not_lt.1 fun h ↦ ?_)
  obtain ⟨c, -, ⟨y, hy, rfl⟩, hc⟩ :=
    (latticeGauge_lt_iff (absorbent_nhds_zero (Metric.closedBall_mem_nhds 0 one_pos))).1 h
  rw [mem_closedBall_zero_iff] at hy
  simp only [smul_eq_mul, norm_mul] at hc
  nlinarith [norm_nonneg c, norm_nonneg y]

end NontriviallyNormedField

section Algebra

variable {K A M : Type*} [NontriviallyNormedField K] [AddCommGroup A] [Module K A]
  [AddCommGroup M] [Module K M] [SMul A M] [IsScalarTower K A M] [SMulCommClass K A M]
  {A₀ : Set A} {M₀ : Set M}

/-- Gauges of lattices `A₀ ⊆ A` and `M₀ ⊆ M` with `A₀ • M₀ ⊆ M₀` are compatible with the scalar
action of `A` on `M`. -/
theorem latticeGauge_smul_le (hA : Absorbent K A₀) (hM : Absorbent K M₀) (hsmul : A₀ • M₀ ⊆ M₀)
    (a : A) (m : M) : latticeGauge K M₀ (a • m) ≤ latticeGauge K A₀ a * latticeGauge K M₀ m := by
  -- Writing `a = c • a'` and `m = d • m'` gives `a • m = (c * d) • (a' • m')`.
  have key : ∀ {c d : K}, c ≠ 0 → a ∈ c • A₀ → d ≠ 0 → m ∈ d • M₀ →
      latticeGauge K M₀ (a • m) ≤ ‖c‖ * ‖d‖ := by
    rintro c d hc ⟨a', ha', rfl⟩ hd ⟨m', hm', rfl⟩
    rw [← norm_mul]
    refine latticeGauge_le_norm (mul_ne_zero hc hd) ⟨a' • m', hsmul (smul_mem_smul ha' hm'), ?_⟩
    rw [smul_assoc, ← smul_comm d a' m']
    exact mul_smul c d _
  rw [latticeGauge_def M₀ m, ← smul_eq_mul, ← Real.sInf_smul_of_nonneg (latticeGauge_nonneg _ _)]
  refine le_csInf (nonempty_norm_image hM m).smul_set ?_
  rintro _ ⟨_, ⟨d, ⟨hd, hm⟩, rfl⟩, rfl⟩
  dsimp only
  rw [smul_eq_mul, mul_comm, latticeGauge_def A₀ a, ← smul_eq_mul,
    ← Real.sInf_smul_of_nonneg (norm_nonneg d)]
  refine le_csInf (nonempty_norm_image hA a).smul_set ?_
  rintro _ ⟨_, ⟨c, ⟨hc, ha⟩, rfl⟩, rfl⟩
  dsimp only
  rw [smul_eq_mul, mul_comm]
  exact key hc ha hd hm

end Algebra

section Ring

variable {K A : Type*} [NontriviallyNormedField K] [Ring A] [Algebra K A] {A₀ : Set A}

/-- The gauge of a multiplicatively closed absorbent set is submultiplicative. -/
theorem latticeGauge_mul_le (hA : Absorbent K A₀) (hmul : A₀ * A₀ ⊆ A₀) (a b : A) :
    latticeGauge K A₀ (a * b) ≤ latticeGauge K A₀ a * latticeGauge K A₀ b :=
  latticeGauge_smul_le hA hA hmul a b

/-- In a nonzero Hausdorff topological algebra, the gauge of a balanced bounded neighbourhood
`A₀` of zero which contains one and is closed under multiplication takes the value one at one. -/
theorem latticeGauge_one [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul K A]
    [T2Space A] [Nontrivial A] (hb : Balanced K A₀) (hmul : A₀ * A₀ ⊆ A₀) (h1 : 1 ∈ A₀)
    (hs₀ : A₀ ∈ 𝓝 0) (hbd : IsVonNBounded K A₀) : latticeGauge K A₀ (1 : A) = 1 := by
  have hpos : 0 < latticeGauge K A₀ (1 : A) :=
    (latticeGauge_nonneg _ _).lt_of_ne' fun h ↦ one_ne_zero <|
      ((t2Space_iff_forall_latticeGauge_eq_zero_iff hb hs₀ hbd).1 inferInstance 1).1 h
  have hle := latticeGauge_mul_le (absorbent_nhds_zero (𝕜 := K) hs₀) hmul (1 : A) 1
  rw [one_mul] at hle
  exact le_antisymm (latticeGauge_le_one h1) (by nlinarith)

end Ring

end TauCeti
