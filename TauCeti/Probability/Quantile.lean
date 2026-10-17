/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.MeasureTheory.Measure.Mod0MeasureIso
public import TauCeti.Probability.Cdf

/-!
# The quantile function of a real law

The *quantile function*, or generalized inverse cumulative distribution function, of a measure
`μ` on `ℝ` sends a level `t` to the least point at which `ProbabilityTheory.cdf μ` reaches `t`:

`μ.quantile t = sInf {x | t ≤ cdf μ x}`.

Because `cdf μ` is monotone and right continuous with limits `0` at `-∞` and `1` at `+∞`, that
infimum is attained for every level `t` strictly between `0` and `1`, and the defining set is
exactly the closed ray to the right of the quantile. The quantile is therefore characterized by
the Galois property `μ.quantile t ≤ x ↔ t ≤ cdf μ x`. At levels `t ≤ 0` and `1 < t` the infimum
ranges over all of `ℝ` or over the empty set, so the value there is the junk value `0`. The
endpoint level `t = 1` is not junk: the quantile there is the least point of full cumulative mass
when such a point exists (for instance `(dirac a).quantile 1 = a`), and `0` when the law has
unbounded support to the right. The inverse characterizations below use levels in `Ioo 0 1`,
which is also the interval the uniform law is taken on.

The *upper quantile* uses the strict threshold
`μ.upperQuantile t = sInf {x | t < cdf μ x}`. It selects the right endpoint of a cdf plateau,
whereas `quantile` selects the left endpoint. Its natural characterization uses the left limit of
the cdf: `μ.upperQuantile t < x ↔ t < leftLim (cdf μ) x`. This distinction is essential when a
decreasing map transports a law with atoms or gaps in its support.

The main result is **inverse transform sampling**: for a probability measure `μ` the quantile
function pushes the uniform law on the open unit interval forward to `μ`. It presents every real
law as the law of one explicit measurable function of a single uniform variable, and it is what
makes the monotone rearrangement of two real laws a transport plan between them.

## Main definitions

* `MeasureTheory.Measure.quantile` — the generalized inverse of the cumulative distribution
  function.
* `MeasureTheory.Measure.upperQuantile` — the strict-threshold generalized inverse.

## Main statements

* `MeasureTheory.Measure.quantile_le_iff` — the Galois characterization of the quantile, with
  `MeasureTheory.Measure.setOf_le_cdf_eq_Ici` its set-level form and
  `MeasureTheory.Measure.lt_quantile_iff` its negation;
* `MeasureTheory.Measure.cdf_quantile` and `MeasureTheory.Measure.quantile_cdf` — the exact
  inverse laws, when the cumulative distribution function is continuous, respectively strictly
  increasing where its values lie strictly between `0` and `1`; together they give
  `MeasureTheory.Measure.quantile_lt_iff`, `MeasureTheory.Measure.strictMonoOn_quantile` and
  `MeasureTheory.Measure.continuousOn_quantile`;
* `MeasureTheory.Measure.upperQuantile_lt_iff` and
  `MeasureTheory.Measure.le_upperQuantile_iff` — the strict-level characterizations of the upper
  quantile through the left limit of the cdf;
* `MeasureTheory.Measure.quantile_le_upperQuantile`,
  `MeasureTheory.Measure.leftLim_cdf_quantile_le` and
  `MeasureTheory.Measure.leftLim_cdf_upperQuantile_le` — the lower/upper quantile bounds;
* `MeasureTheory.Measure.quantile_eq_of_le_cdf_iff` — two quantiles agree when their defining cdf
  level sets agree;
* `MeasureTheory.Measure.map_quantile_volume_Ioo` — inverse transform sampling: the quantile
  function pushes the uniform law on `Ioo 0 1` forward to the original law, packaged as
  `MeasureTheory.Measure.measurePreserving_quantile`;
* `MeasureTheory.Measure.quantile_map_volume_Ioo_ae` — conversely, the law of a monotone function
  of a uniform variable has that function as its quantile function, almost everywhere;
* `MeasureTheory.Measure.cdf_map_eq_volume_restrict` — the probability integral transform for an
  atomless real law;
* `MeasureTheory.Measure.cdf_quantile_ae` and
  `MeasureTheory.Measure.quantile_cdf_ae` — the two almost-everywhere inverse laws, the first
  for an atomless law and the second for every law;
* `MeasureTheory.Measure.realMod0MeasureIso` — for an atomless real law, the pair
  (`cdf ν`, `ν.quantile`) as a `TauCeti.Mod0MeasureIso` between `ν` and Lebesgue measure
  restricted to `[0, 1]`.

## References

* R. B. Nelsen, *An Introduction to Copulas*, Springer 2006, §2.3, for the generalized inverse
  and its Galois property.
* P. Embrechts and M. Hofert, *A note on generalized inverses*, Mathematical Methods of
  Operations Research 77 (2013), 423--432.

## Adapted from

The probability integral transform `cdf_map_eq_volume_restrict`, the inverse laws
`cdf_quantile_ae` and `quantile_cdf_ae`, the inverse transform sampling theorem
`map_quantile_volume_Ioo` and the resulting `realMod0MeasureIso` instance are adapted from
Cameron Freer's independent implementation in `Graphon/MeasureIso.lean` at commit
`9f7be59fa754d260a544b4cfd83d6a5b94f7552e`:
<https://github.com/cameronfreer/graphon/commit/9f7be59fa754d260a544b4cfd83d6a5b94f7552e>,
where they appear as `cdf_map_eq_volume_restrict`, `cdf_cdfQuantile_ae`,
`cdfQuantile_cdf_ae`, `map_cdfQuantile_volume_restrict` and `realMod0MeasureIso`, with the
generalized inverse called `cdfQuantile` rather than `quantile`; the graphon-specific packaging
was removed. The original work is copyright Cameron Freer and licensed under Apache 2.0.

The measure-preserving equivalence that this file realizes on the real line is the classical
transport of an atomless standard-Borel space to the unit interval, proved as Theorem A.7 in
S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, Arkiv för
Matematik 52 (2014); see also `TauCeti.MeasureTheory.Measure.exists_mpModNull_equiv_unitInterval`
in `TauCeti.MeasureTheory.Measure.AtomlessStandardBorel`, which composes it with
`TauCeti.embeddingRealMod0MeasureIso`.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Function Topology

namespace MeasureTheory.Measure

/-- The **quantile function** of a measure on `ℝ`: the least point at which its cumulative
distribution function reaches the level `t`.

This is the honest generalized inverse of `ProbabilityTheory.cdf μ` for `t` in `Set.Ioo 0 1`. At
levels `t ≤ 0` and `1 < t` the defining infimum ranges over all of `ℝ` or over the empty set, and
the value is the junk value `0` (`quantile_of_nonpos`, `quantile_of_one_lt`). At the endpoint
level `t = 1` the value is the least point where the cumulative distribution function reaches `1`
if there is one, and `0` otherwise. -/
def quantile (μ : Measure ℝ) (t : ℝ) : ℝ := sInf {x : ℝ | t ≤ cdf μ x}

/-- The **upper quantile function** of a measure on `ℝ`: the infimum of the points at which its
cumulative distribution function is strictly above the level `t`.

For `t` in `Set.Ioo 0 1`, this selects the right endpoint of a plateau of the cumulative
distribution function, while `Measure.quantile` selects its left endpoint. At levels `t < 0` and
`1 ≤ t` the value is the junk value `0` (`upperQuantile_of_neg`,
`upperQuantile_of_one_le`). -/
def upperQuantile (μ : Measure ℝ) (t : ℝ) : ℝ := sInf {x : ℝ | t < cdf μ x}

/-- The quantile function is the infimum of the points at which the cumulative distribution
function reaches the level. The definition's body is not exposed, so this is the lemma downstream
modules should rewrite with. -/
theorem quantile_def (μ : Measure ℝ) (t : ℝ) :
    μ.quantile t = sInf {x : ℝ | t ≤ cdf μ x} := (rfl)

/-- The upper quantile is the infimum of the points at which the cumulative distribution
function is strictly above the level. -/
theorem upperQuantile_def (μ : Measure ℝ) (t : ℝ) :
    μ.upperQuantile t = sInf {x : ℝ | t < cdf μ x} := (rfl)

/-- Quantiles of two measures at two levels agree when the corresponding cdf level sets agree. -/
theorem quantile_eq_of_le_cdf_iff (ν μ : Measure ℝ) {u t : ℝ}
    (h : ∀ x, u ≤ cdf ν x ↔ t ≤ cdf μ x) : ν.quantile u = μ.quantile t := by
  rw [quantile_def, quantile_def]
  apply congrArg sInf
  ext x
  exact h x

/-- Upper quantiles of two measures at two levels agree when the corresponding strict cdf level
sets agree. -/
theorem upperQuantile_eq_of_lt_cdf_iff (ν μ : Measure ℝ) {u t : ℝ}
    (h : ∀ x, u < cdf ν x ↔ t < cdf μ x) : ν.upperQuantile u = μ.upperQuantile t := by
  rw [upperQuantile_def, upperQuantile_def]
  apply congrArg sInf
  ext x
  exact h x

variable {t x : ℝ}

/-- Below the level `1` some point has cumulative mass at least the level, because the cumulative
distribution function tends to `1` at `+∞`. -/
theorem nonempty_setOf_le_cdf (μ : Measure ℝ) (ht : t < 1) : {x : ℝ | t ≤ cdf μ x}.Nonempty :=
  ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds ht)).exists.imp fun _ h ↦ h.le

/-- Above the level `0` the points whose cumulative mass reaches the level are bounded below,
because the cumulative distribution function tends to `0` at `-∞`. -/
theorem bddBelow_setOf_le_cdf (μ : Measure ℝ) (ht : 0 < t) : BddBelow {x : ℝ | t ≤ cdf μ x} := by
  obtain ⟨a, ha⟩ :=
    eventually_atBot.mp ((tendsto_cdf_atBot μ).eventually (eventually_lt_nhds ht))
  refine ⟨a, fun x hx ↦ ?_⟩
  by_contra hxa
  exact absurd (ha x (not_le.mp hxa).le) (not_lt.mpr hx)

/-- Below the level `1` some point has cumulative mass strictly above the level. -/
theorem nonempty_setOf_lt_cdf (μ : Measure ℝ) (ht : t < 1) :
    {x : ℝ | t < cdf μ x}.Nonempty :=
  ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds ht)).exists

/-- Above the level `0` the points whose cumulative mass is strictly above the level are bounded
below. -/
theorem bddBelow_setOf_lt_cdf (μ : Measure ℝ) (ht : 0 < t) :
    BddBelow {x : ℝ | t < cdf μ x} := by
  obtain ⟨a, ha⟩ :=
    eventually_atBot.mp ((tendsto_cdf_atBot μ).eventually (eventually_lt_nhds ht))
  refine ⟨a, fun x hx ↦ ?_⟩
  by_contra hxa
  exact (ha x (not_le.mp hxa).le).asymm hx

/-- At a nonpositive level the quantile function takes the junk value `0`: every point has
cumulative mass at least the level. -/
@[simp]
theorem quantile_of_nonpos (μ : Measure ℝ) (ht : t ≤ 0) : μ.quantile t = 0 := by
  have hset : {x : ℝ | t ≤ cdf μ x} = univ := eq_univ_of_forall fun x ↦ ht.trans (cdf_nonneg μ x)
  rw [quantile_def, hset, Real.sInf_univ]

/-- Above the level `1` the quantile function takes the junk value `0`: no point has cumulative
mass that large. -/
@[simp]
theorem quantile_of_one_lt (μ : Measure ℝ) (ht : 1 < t) : μ.quantile t = 0 := by
  have hset : {x : ℝ | t ≤ cdf μ x} = ∅ :=
    eq_empty_of_forall_notMem fun x hx ↦ absurd (hx.trans (cdf_le_one μ x)) (not_le.2 ht)
  rw [quantile_def, hset, Real.sInf_empty]

/-- Below the level `0` the upper quantile function takes the junk value `0`: every point has
cumulative mass strictly above the level. -/
@[simp]
theorem upperQuantile_of_neg (μ : Measure ℝ) (ht : t < 0) : μ.upperQuantile t = 0 := by
  have hset : {x : ℝ | t < cdf μ x} = univ :=
    eq_univ_of_forall fun x ↦ ht.trans_le (cdf_nonneg μ x)
  rw [upperQuantile_def, hset, Real.sInf_univ]

/-- At and above the level `1` the upper quantile function takes the junk value `0`: no point has
cumulative mass strictly above the level. -/
@[simp]
theorem upperQuantile_of_one_le (μ : Measure ℝ) (ht : 1 ≤ t) : μ.upperQuantile t = 0 := by
  have hset : {x : ℝ | t < cdf μ x} = ∅ :=
    eq_empty_of_forall_notMem fun x hx ↦ (not_lt_of_ge ((cdf_le_one μ x).trans ht)) hx
  rw [upperQuantile_def, hset, Real.sInf_empty]

/-- The cumulative distribution function at the quantile reaches every level strictly below
`1`. -/
theorem le_cdf_quantile (μ : Measure ℝ) (h1 : t < 1) : t ≤ cdf μ (μ.quantile t) := by
  have key : ∀ r : Ioi (μ.quantile t), t ≤ cdf μ r := by
    rintro ⟨r, hr⟩
    obtain ⟨y, hy, hyr⟩ := exists_lt_of_csInf_lt (nonempty_setOf_le_cdf μ h1) hr
    exact hy.trans (monotone_cdf μ hyr.le)
  have h := le_ciInf key
  rwa [StieltjesFunction.iInf_Ioi_eq] at h

/-- **The Galois characterization of the quantile.** For a level strictly between `0` and `1`,
the quantile lies below a point exactly when the cumulative distribution function at that point
reaches the level. -/
@[simp]
theorem quantile_le_iff (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    μ.quantile t ≤ x ↔ t ≤ cdf μ x :=
  ⟨fun h ↦ (le_cdf_quantile μ h1).trans (monotone_cdf μ h),
    fun h ↦ csInf_le (bddBelow_setOf_le_cdf μ h0) h⟩

/-- The set of points whose cumulative mass reaches a level strictly between `0` and `1` is the
closed ray to the right of the quantile at that level. -/
theorem setOf_le_cdf_eq_Ici (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    {x : ℝ | t ≤ cdf μ x} = Ici (μ.quantile t) := by
  ext x
  exact (quantile_le_iff μ h0 h1).symm

/-- A point lies strictly below the quantile at a level exactly when its cumulative mass has not
yet reached that level. -/
@[simp]
theorem lt_quantile_iff (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    x < μ.quantile t ↔ cdf μ x < t := by
  simpa only [not_le] using (quantile_le_iff (x := x) μ h0 h1).not

/-- The quantile function is monotone on the levels where it is the honest generalized
inverse. -/
theorem monotoneOn_quantile (μ : Measure ℝ) : MonotoneOn μ.quantile (Ioo 0 1) := by
  rintro s ⟨hs0, hs1⟩ t ⟨_, ht1⟩ hst
  exact (quantile_le_iff μ hs0 hs1).mpr (hst.trans (le_cdf_quantile μ ht1))

/-- The upper quantile lies strictly below a point exactly when the cdf's left limit at that point
is strictly above the level. -/
@[simp]
theorem upperQuantile_lt_iff (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    μ.upperQuantile t < x ↔ t < leftLim (cdf μ) x := by
  constructor
  · intro hqx
    obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt (nonempty_setOf_lt_cdf μ h1) hqx
    exact hy.trans_le ((monotone_cdf μ).le_leftLim hyx)
  · intro hleft
    have hevent : ∀ᶠ y in 𝓝[<] x, t < cdf μ y :=
      ((monotone_cdf μ).tendsto_leftLim x).eventually (eventually_gt_nhds hleft)
    obtain ⟨y, hy, hyx⟩ := (hevent.and self_mem_nhdsWithin).exists
    exact lt_of_le_of_lt (csInf_le (bddBelow_setOf_lt_cdf μ h0) hy) hyx

/-- A point lies below the upper quantile exactly when the cdf's left limit there has not exceeded
the level. -/
@[simp]
theorem le_upperQuantile_iff (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    x ≤ μ.upperQuantile t ↔ leftLim (cdf μ) x ≤ t := by
  simpa only [not_lt] using (upperQuantile_lt_iff (x := x) μ h0 h1).not

/-- For a probability law, the strict upper-quantile characterization says that the mass strictly
below `x` exceeds the level. -/
theorem upperQuantile_lt_iff_measureReal_Iio (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h0 : 0 < t) (h1 : t < 1) : μ.upperQuantile t < x ↔ t < μ.real (Iio x) := by
  rw [upperQuantile_lt_iff μ h0 h1, leftLim_cdf_eq_measureReal_Iio]

/-- For a probability law, a point lies below the upper quantile exactly when the mass strictly
below it is at most the level. -/
theorem le_upperQuantile_iff_measureReal_Iio (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h0 : 0 < t) (h1 : t < 1) : x ≤ μ.upperQuantile t ↔ μ.real (Iio x) ≤ t := by
  rw [le_upperQuantile_iff μ h0 h1, leftLim_cdf_eq_measureReal_Iio]

/-- The points whose cdf left limit is strictly above an interior level form the open ray to the
right of the upper quantile. -/
theorem setOf_lt_leftLim_cdf_eq_Ioi (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    {x : ℝ | t < leftLim (cdf μ) x} = Ioi (μ.upperQuantile t) := by
  ext x
  exact (upperQuantile_lt_iff μ h0 h1).symm

/-- The upper quantile function is monotone on the levels where it is the strict generalized
inverse. -/
theorem monotoneOn_upperQuantile (μ : Measure ℝ) : MonotoneOn μ.upperQuantile (Ioo 0 1) := by
  rintro s hs t ht hst
  rw [upperQuantile_def, upperQuantile_def]
  exact csInf_le_csInf (bddBelow_setOf_lt_cdf μ hs.1) (nonempty_setOf_lt_cdf μ ht.2)
    (fun _ hx ↦ hst.trans_lt hx)

/-- The lower quantile never exceeds the upper quantile at an interior level. -/
theorem quantile_le_upperQuantile (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    μ.quantile t ≤ μ.upperQuantile t := by
  rw [quantile_def, upperQuantile_def]
  exact csInf_le_csInf (bddBelow_setOf_le_cdf μ h0) (nonempty_setOf_lt_cdf μ h1) fun _ hx ↦
    Set.mem_ofPred_eq.mpr hx.le

/-- The cdf's left limit at a lower quantile is at most the quantile level. -/
theorem leftLim_cdf_quantile_le (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    leftLim (cdf μ) (μ.quantile t) ≤ t := by
  refine le_of_tendsto ((monotone_cdf μ).tendsto_leftLim (μ.quantile t)) ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ((lt_quantile_iff μ h0 h1).1 hx).le

/-- For a probability law, the mass strictly below a lower quantile is at most its level. -/
theorem measureReal_Iio_quantile_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h0 : 0 < t) (h1 : t < 1) : μ.real (Iio (μ.quantile t)) ≤ t := by
  rw [← leftLim_cdf_eq_measureReal_Iio]
  exact leftLim_cdf_quantile_le μ h0 h1

/-- The cdf at an upper quantile reaches the quantile level. -/
theorem le_cdf_upperQuantile (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    t ≤ cdf μ (μ.upperQuantile t) :=
  (le_cdf_quantile μ h1).trans (monotone_cdf μ (quantile_le_upperQuantile μ h0 h1))

/-- The cdf's left limit at an upper quantile is at most the quantile level. -/
theorem leftLim_cdf_upperQuantile_le (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    leftLim (cdf μ) (μ.upperQuantile t) ≤ t :=
  (le_upperQuantile_iff μ h0 h1).1 le_rfl

/-- For a probability law, the mass strictly below an upper quantile is at most its level. -/
theorem measureReal_Iio_upperQuantile_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h0 : 0 < t) (h1 : t < 1) : μ.real (Iio (μ.upperQuantile t)) ≤ t := by
  rw [← leftLim_cdf_eq_measureReal_Iio]
  exact leftLim_cdf_upperQuantile_le μ h0 h1

/-- For a law with continuous cumulative distribution function, the quantile is an exact right
inverse of the cumulative distribution function at every level strictly between `0` and `1`. -/
@[simp]
theorem cdf_quantile (μ : Measure ℝ) (hμ : Continuous (cdf μ)) (h0 : 0 < t) (h1 : t < 1) :
    cdf μ (μ.quantile t) = t := by
  refine le_antisymm ?_ (le_cdf_quantile μ h1)
  -- To the left of the quantile the cumulative distribution function stays below `t`, so by
  -- continuity it is at most `t` at the quantile itself.
  refine le_of_tendsto ((hμ.tendsto _).mono_left (nhdsWithin_le_nhds (s := Iio (μ.quantile t))))
    ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact ((lt_quantile_iff μ h0 h1).1 hy).le

/-- For a law with continuous cumulative distribution function, the quantile function is strictly
increasing on the levels strictly between `0` and `1`. -/
theorem strictMonoOn_quantile (μ : Measure ℝ) (hμ : Continuous (cdf μ)) :
    StrictMonoOn μ.quantile (Ioo 0 1) := fun s hs t ht hst => by
  rwa [lt_quantile_iff μ ht.1 ht.2, cdf_quantile μ hμ hs.1 hs.2]

/-- If the cumulative distribution function is strictly increasing where its values lie strictly
between `0` and `1`, the quantile is a left inverse of it there. -/
@[simp]
theorem quantile_cdf (μ : Measure ℝ) (hmono : StrictMonoOn (cdf μ) (cdf μ ⁻¹' Ioo 0 1))
    (hx : cdf μ x ∈ Ioo 0 1) : μ.quantile (cdf μ x) = x := by
  refine le_antisymm ((quantile_le_iff μ hx.1 hx.2).2 le_rfl) (not_lt.1 fun h => ?_)
  have hle := le_cdf_quantile μ hx.2
  have hq : cdf μ (μ.quantile (cdf μ x)) ∈ Ioo 0 1 :=
    ⟨hx.1.trans_le hle, (monotone_cdf μ h.le).trans_lt hx.2⟩
  exact (hmono hq hx h).not_ge hle

/-- The strict form of `MeasureTheory.Measure.quantile_le_iff`, for a law whose cumulative
distribution function is continuous, and strictly increasing where its values lie strictly between
`0` and `1`. -/
theorem quantile_lt_iff (μ : Measure ℝ) (hμ : Continuous (cdf μ))
    (hmono : StrictMonoOn (cdf μ) (cdf μ ⁻¹' Ioo 0 1)) (h0 : 0 < t) (h1 : t < 1) :
    μ.quantile t < x ↔ t < cdf μ x := by
  have hq := cdf_quantile μ hμ h0 h1
  refine ⟨fun h => ?_, fun h => not_le.1 fun hx => ?_⟩
  · rcases lt_or_ge (cdf μ x) 1 with hx1 | hx1
    · have hle : t ≤ cdf μ x := hq ▸ monotone_cdf μ h.le
      rw [← hq]
      exact hmono (by rw [mem_preimage, hq]; exact ⟨h0, h1⟩) ⟨h0.trans_le hle, hx1⟩ h
    · exact h1.trans_le hx1
  · exact (hq ▸ monotone_cdf μ hx).not_gt h

/-- For a law whose cumulative distribution function is continuous, and strictly increasing where
its values lie strictly between `0` and `1`, the quantile function is continuous on the levels
strictly between `0` and `1`. -/
theorem continuousOn_quantile (μ : Measure ℝ) (hμ : Continuous (cdf μ))
    (hmono : StrictMonoOn (cdf μ) (cdf μ ⁻¹' Ioo 0 1)) :
    ContinuousOn μ.quantile (Ioo 0 1) := fun t ht => by
  -- A monotone function whose image of a neighbourhood is a neighbourhood is continuous; here the
  -- image of `Ioo 0 1` is the open set where the cumulative distribution function lies in
  -- `Ioo 0 1`.
  have hmem : μ.quantile t ∈ cdf μ ⁻¹' Ioo 0 1 := by
    rw [mem_preimage, cdf_quantile μ hμ ht.1 ht.2]
    exact ht
  exact (continuousAt_of_monotoneOn_of_image_mem_nhds (monotoneOn_quantile μ)
    (isOpen_Ioo.mem_nhds ht) (mem_of_superset ((isOpen_Ioo.preimage hμ).mem_nhds hmem)
      fun y hy => ⟨cdf μ y, hy, quantile_cdf μ hmono hy⟩)).continuousWithinAt

/-- Off `Ioo 0 1` the quantile function is constant equal to its junk value `0`, except possibly
at the single level `1`; that is enough for the part of a sublevel set living there to be
measurable. -/
private theorem measurableSet_quantile_preimage_Iic_inter_compl (μ : Measure ℝ) (x : ℝ) :
    MeasurableSet (μ.quantile ⁻¹' Iic x ∩ (Ioo (0 : ℝ) 1)ᶜ) := by
  have hzero : ∀ ⦃s : ℝ⦄, s ∈ Iic (0 : ℝ) ∪ Ioi 1 → μ.quantile s = 0 := by
    rintro s (hs | hs)
    · exact quantile_of_nonpos μ hs
    · exact quantile_of_one_lt μ hs
  have hcover : (Ioo (0 : ℝ) 1)ᶜ = (Iic (0 : ℝ) ∪ Ioi 1) ∪ {(1 : ℝ)} := by
    ext s
    simp only [mem_compl_iff, mem_Ioo, not_and_or, not_lt, mem_union, mem_Iic, mem_Ioi,
      mem_singleton_iff]
    grind
  rw [hcover, inter_union_distrib_left]
  refine MeasurableSet.union ?_ ((subsingleton_singleton.anti inter_subset_right).measurableSet)
  by_cases hx : (0 : ℝ) ≤ x
  · have hall : μ.quantile ⁻¹' Iic x ∩ (Iic (0 : ℝ) ∪ Ioi 1) = Iic (0 : ℝ) ∪ Ioi 1 :=
      inter_eq_right.mpr fun s hs ↦ by simp [mem_preimage, hzero hs, hx]
    rw [hall]
    exact measurableSet_Iic.union measurableSet_Ioi
  · have hnone : μ.quantile ⁻¹' Iic x ∩ (Iic (0 : ℝ) ∪ Ioi 1) = ∅ := by
      refine eq_empty_of_forall_notMem fun s hs ↦ hx ?_
      have hqs := hs.1
      rwa [mem_preimage, hzero hs.2, mem_Iic] at hqs
    rw [hnone]
    exact MeasurableSet.empty

/-- The quantile function is measurable. -/
@[fun_prop]
theorem measurable_quantile (μ : Measure ℝ) : Measurable μ.quantile := by
  refine measurable_of_Iic fun x ↦ ?_
  have hsplit : μ.quantile ⁻¹' Iic x =
      (Ioo (0 : ℝ) 1 ∩ Iic (cdf μ x)) ∪ (μ.quantile ⁻¹' Iic x ∩ (Ioo (0 : ℝ) 1)ᶜ) := by
    ext s
    by_cases hs : s ∈ Ioo (0 : ℝ) 1
    · simp [hs, quantile_le_iff μ hs.1 hs.2]
    · simp [hs]
  rw [hsplit]
  exact (measurableSet_Ioo.inter measurableSet_Iic).union
    (measurableSet_quantile_preimage_Iic_inter_compl μ x)

/-- Off `Ioo 0 1` the upper quantile is constant at its junk value `0`, except possibly at the
single level `0`; consequently the part of any strict sublevel set living there is measurable. -/
private theorem measurableSet_upperQuantile_preimage_Iio_inter_compl (μ : Measure ℝ) (x : ℝ) :
    MeasurableSet (μ.upperQuantile ⁻¹' Iio x ∩ (Ioo (0 : ℝ) 1)ᶜ) := by
  have hzero : ∀ ⦃s : ℝ⦄, s ∈ Iio (0 : ℝ) ∪ Ici 1 → μ.upperQuantile s = 0 := by
    rintro s (hs | hs)
    · exact upperQuantile_of_neg μ hs
    · exact upperQuantile_of_one_le μ hs
  have hcover : (Ioo (0 : ℝ) 1)ᶜ = (Iio (0 : ℝ) ∪ Ici 1) ∪ {(0 : ℝ)} := by
    ext s
    simp only [mem_compl_iff, mem_Ioo, not_and_or, not_lt, mem_union, mem_Iio, mem_Ici,
      mem_singleton_iff]
    grind
  rw [hcover, inter_union_distrib_left]
  refine MeasurableSet.union ?_ ((subsingleton_singleton.anti inter_subset_right).measurableSet)
  by_cases hx : (0 : ℝ) < x
  · have hall : μ.upperQuantile ⁻¹' Iio x ∩ (Iio (0 : ℝ) ∪ Ici 1) =
        Iio (0 : ℝ) ∪ Ici 1 := inter_eq_right.mpr fun s hs ↦ by
      simp [mem_preimage, hzero hs, hx]
    rw [hall]
    exact measurableSet_Iio.union measurableSet_Ici
  · have hnone : μ.upperQuantile ⁻¹' Iio x ∩ (Iio (0 : ℝ) ∪ Ici 1) = ∅ := by
      refine eq_empty_of_forall_notMem fun s hs ↦ hx ?_
      have hqs := hs.1
      rwa [mem_preimage, hzero hs.2, mem_Iio] at hqs
    rw [hnone]
    exact MeasurableSet.empty

/-- The upper quantile function is measurable. -/
@[fun_prop]
theorem measurable_upperQuantile (μ : Measure ℝ) : Measurable μ.upperQuantile := by
  refine measurable_of_Iio fun x ↦ ?_
  have hsplit : μ.upperQuantile ⁻¹' Iio x =
      (Ioo (0 : ℝ) 1 ∩ Iio (leftLim (cdf μ) x)) ∪
        (μ.upperQuantile ⁻¹' Iio x ∩ (Ioo (0 : ℝ) 1)ᶜ) := by
    ext s
    by_cases hs : s ∈ Ioo (0 : ℝ) 1
    · simp [hs, upperQuantile_lt_iff μ hs.1 hs.2]
    · simp [hs]
  rw [hsplit]
  exact (measurableSet_Ioo.inter measurableSet_Iio).union
    (measurableSet_upperQuantile_preimage_Iio_inter_compl μ x)

/-- **Inverse transform sampling.** The quantile function of a probability law on `ℝ` pushes the
uniform law on the open unit interval forward to that law. -/
theorem map_quantile_volume_Ioo (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (volume.restrict (Ioo (0 : ℝ) 1)).map μ.quantile = μ := by
  have huniform : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  have _ : IsProbabilityMeasure ((volume.restrict (Ioo (0 : ℝ) 1)).map μ.quantile) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_quantile μ).aemeasurable).mpr huniform
  refine Measure.ext_of_Iic _ _ fun x ↦ ?_
  rw [Measure.map_apply (measurable_quantile μ) measurableSet_Iic,
    Measure.restrict_apply (measurable_quantile μ measurableSet_Iic), ← ofReal_cdf μ x]
  have hsub : μ.quantile ⁻¹' Iic x ∩ Ioo (0 : ℝ) 1 = Ioc (0 : ℝ) (cdf μ x) \ {(1 : ℝ)} := by
    ext s
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo, Set.mem_sdiff, mem_Ioc,
      mem_singleton_iff]
    constructor
    · rintro ⟨hq, hs0, hs1⟩
      exact ⟨⟨hs0, (quantile_le_iff μ hs0 hs1).mp hq⟩, hs1.ne⟩
    · rintro ⟨⟨hs0, hsc⟩, hs1⟩
      have hlt : s < 1 := lt_of_le_of_ne (hsc.trans (cdf_le_one μ x)) hs1
      exact ⟨(quantile_le_iff μ hs0 hlt).mpr hsc, hs0, hlt⟩
  rw [hsub, measure_sdiff_null (measure_singleton _), Real.volume_Ioc, sub_zero]

/-- Inverse transform sampling, as a measure-preserving map from the uniform law on the open unit
interval. -/
theorem measurePreserving_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MeasurePreserving μ.quantile (volume.restrict (Ioo (0 : ℝ) 1)) μ :=
  ⟨measurable_quantile μ, map_quantile_volume_Ioo μ⟩

/-- **The quantile of a monotone rearrangement.** The law of `f (U)`, for `U` uniform on the open
unit interval and `f` monotone there, has quantile function `f` at almost every level: they can
differ only at the countably many levels where `f` jumps. -/
theorem quantile_map_volume_Ioo_ae {f : ℝ → ℝ} (hf : MonotoneOn f (Ioo 0 1)) :
    ((volume.restrict (Ioo (0 : ℝ) 1)).map f).quantile =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] f := by
  set U := volume.restrict (Ioo (0 : ℝ) 1)
  have : IsProbabilityMeasure U := ⟨by simp [U]⟩
  have hfm : AEMeasurable f U := aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hf
  set ν := U.map f
  -- The cumulative mass of `ν` below `x` is the length of the levels sent at most to `x`.
  have hcdf (x : ℝ) : ENNReal.ofReal (cdf ν x) = volume (f ⁻¹' Iic x ∩ Ioo 0 1) := by
    rw [ofReal_cdf, map_apply_of_aemeasurable hfm measurableSet_Iic,
      restrict_apply' measurableSet_Ioo]
  refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
  filter_upwards [hf.countable_not_continuousWithinAt.ae_notMem volume] with t hct ht
  have hc : ContinuousAt f t := by
    by_contra h
    exact hct ⟨ht, fun h' ↦ h (h'.continuousAt (Ioo_mem_nhds ht.1 ht.2))⟩
  refine le_antisymm ((quantile_le_iff ν ht.1 ht.2).2 ?_) (le_of_forall_lt fun x hx ↦ ?_)
  · -- Every level in `(0, t]` is sent at most to `f t`.
    rw [← ENNReal.ofReal_le_ofReal_iff (cdf_nonneg ν _), hcdf]
    calc ENNReal.ofReal t = volume (Ioc 0 t) := by simp
      _ ≤ volume (f ⁻¹' Iic (f t) ∩ Ioo 0 1) := measure_mono fun s hs ↦
          ⟨hf ⟨hs.1, hs.2.trans_lt ht.2⟩ ht hs.2, hs.1, hs.2.trans_lt ht.2⟩
  · -- Below `f t`, continuity at `t` produces a level `s₀ < t` already sent above `x`.
    obtain ⟨s₀, ⟨hs₀x, hs₀⟩, hs₀t⟩ : ∃ s₀, (x < f s₀ ∧ s₀ ∈ Ioo 0 1) ∧ s₀ < t :=
      (((hc.eventually (eventually_gt_nhds hx)).and (Ioo_mem_nhds ht.1 ht.2)).filter_mono
        nhdsWithin_le_nhds |>.and self_mem_nhdsWithin).exists (f := 𝓝[<] t)
    rw [lt_quantile_iff ν ht.1 ht.2, ← ENNReal.ofReal_lt_ofReal_iff ht.1, hcdf]
    calc volume (f ⁻¹' Iic x ∩ Ioo 0 1) ≤ volume (Ioo 0 s₀) := measure_mono fun s hs ↦
          ⟨hs.2.1, lt_of_not_ge fun h ↦ (hs₀x.trans_le (hf hs₀ hs.2 h)).not_ge hs.1⟩
      _ < ENNReal.ofReal t := by simpa using (ENNReal.ofReal_lt_ofReal_iff ht.1).2 hs₀t

/-- **The probability integral transform.** The CDF of an atomless probability measure on
`ℝ` pushes the measure forward to Lebesgue measure restricted to `[0, 1]`. -/
@[simp]
theorem cdf_map_eq_volume_restrict (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] :
    Measure.map (cdf ν) ν = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  have hmeas : Measurable (cdf ν) := (cdf ν).mono.measurable
  refine Measure.ext_of_Iic _ _ (fun y => ?_)
  rw [Measure.map_apply hmeas measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge y 1 with hy1 | hy1
  · have hrset : Iic y ∩ Icc (0 : ℝ) 1 = Icc 0 y := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨hxy, hx0, _⟩; exact ⟨hx0, hxy⟩
      · rintro ⟨hx0, hxy⟩; exact ⟨hxy, hx0, le_of_lt (lt_of_le_of_lt hxy hy1)⟩
    rw [hrset, Real.volume_Icc, sub_zero]
    exact cdf_sublevel_measure ν y hy1
  · have hset : cdf ν ⁻¹' Iic y = univ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact le_trans (cdf_le_one ν x) hy1
    have hrset : Iic y ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc, and_iff_right_iff_imp]
      rintro ⟨_, hx1⟩; exact le_trans hx1 hy1
    rw [hset, hrset, measure_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]

/-- On the closed unit interval, the CDF and quantile are inverse almost everywhere. -/
theorem cdf_quantile_ae (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    (fun u => cdf ν (ν.quantile u)) =ᵐ[volume.restrict (Set.Icc 0 1)] id := by
  refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
  filter_upwards [Set.Countable.ae_notMem
      ((Set.countable_singleton (1 : ℝ)).insert 0) volume] with u hu huIcc
  have hu0 : u ≠ 0 := fun h => hu (by simp [h])
  have hu1 : u ≠ 1 := fun h => hu (by simp [h])
  have h0 : 0 < u := lt_of_le_of_ne huIcc.1 (Ne.symm hu0)
  have h1 : u < 1 := lt_of_le_of_ne huIcc.2 hu1
  exact cdf_quantile ν (continuous_cdf_of_noAtoms ν) h0 h1

/-- The part of the plateau of `cdf ν` that lies strictly to the right of a point `y` whose
level `cdf ν y` is still below `1` is null. Equivalently: the atom of a real law sits at the *left*
end of its plateau and never strictly inside one, so above a point of level `< 1` the cumulative
function is not constant on a set of positive mass. -/
private theorem ae_not_of_lt_of_cdf_eq {ν : Measure ℝ} [IsProbabilityMeasure ν] {y : ℝ}
    (hy : cdf ν y < 1) : ∀ᶠ x in ae ν, ¬ (y < x ∧ cdf ν y = cdf ν x) := by
  -- `S` is the plateau of `cdf ν` at the level `cdf ν y`, cut off at `y`. The goal is `ν S = 0`,
  -- once `ae_iff` and `hnotMem` below have turned it into a measure-zero statement.
  set S : Set ℝ := {z | y < z ∧ cdf ν y = cdf ν z} with hSdef
  -- `cdf ν` rises to `1 > cdf ν y`, so it eventually leaves the level `cdf ν y` for good, and no
  -- plateau point can lie above the bound that this produces.
  have hbdd : BddAbove S := by
    obtain ⟨M, hM⟩ :=
      eventually_atTop.mp ((tendsto_cdf_atTop ν).eventually (eventually_gt_nhds hy))
    refine ⟨M, fun z hz ↦ le_of_not_gt fun hzM ↦ ?_⟩
    exact absurd (hM z (le_of_lt hzM)) (not_lt_of_ge hz.2.symm.le)
  have hnotMem : {z : ℝ | ¬ ¬ (y < z ∧ cdf ν y = cdf ν z)} = S := by
    ext z
    simp only [Set.mem_ofPred_eq, not_not, hSdef]
  -- Case split on whether the plateau has any points at all. If it has none it is null outright.
  -- If it does, let `b` be its top point: `hle` below puts all of `S` inside `(y, b]`, and `hstab`
  -- shows the cumulative function is still exactly `cdf ν y` at every point of the open interval
  -- `(y, b)`. Each subcase of the next split then makes `S` null, and `measure_mono_null` turns
  -- that into the goal.
  by_cases hSne : S.Nonempty
  · set b : ℝ := sSup S with hbdef
    have hle : ∀ z : ℝ, z ∈ S → z ≤ b := fun z hz ↦ le_csSup hbdd hz
    have hstab : ∀ z : ℝ, y < z → z < b → cdf ν y = cdf ν z := by
      rintro z hz1 hz2
      obtain ⟨w, hw, hzw⟩ := exists_lt_of_lt_csSup (s := S) (b := z) hSne (hbdef ▸ hz2)
      have hupper : cdf ν z ≤ cdf ν y :=
        (monotone_cdf ν hzw.le).trans (le_of_eq ((hSdef ▸ hw).2).symm)
      exact le_antisymm (monotone_cdf ν hz1.le) hupper
    -- If the top of the plateau has the same level as `y`, the plateau is precisely the atom at
    -- `b`, whose mass is the increment `cdf ν b - cdf ν y = 0`; `S ⊆ Ioc y b` is then null as well.
    by_cases hb : cdf ν b = cdf ν y
    · have hnull : ν (Ioc y b) = 0 := by
        rw [← measure_cdf ν, StieltjesFunction.measure_Ioc, hb, sub_self, ENNReal.ofReal_zero]
      refine ae_iff.mpr ?_
      rw [hnotMem]
      exact measure_mono_null (s := S) (t := Ioc y b) (fun z hz ↦ ⟨hz.1, hle z hz⟩) hnull
    -- Otherwise `b` is above the level of the plateau, so `b` itself is no plateau point (`hne`
    -- below) while every point of `(y, b)` still sits at the level `cdf ν y` by `hstab`. The
    -- interval `(y, b)` would therefore carry the whole atom at `b`, which a constant interval
    -- cannot do. The countable cover below is what rules it out: the half-open intervals
    -- `Ioc y (b - (b - y) / (n + 2))` climb towards `b` while staying inside `(y, b)`, so each has
    -- the null increment `cdf ν y - cdf ν y = 0`, and together they cover `(y, b)`. Since
    -- `S ⊆ Ioo y b` by `hle` and `hne`, `measure_mono_null` then finishes.
    · have hyb : y < b := by
        obtain ⟨z, hzS⟩ := hSne
        exact lt_of_lt_of_le hzS.1 (hle z hzS)
      have hneS : (0 : ℝ) < b - y := sub_pos.2 hyb
      have hne : ∀ z : ℝ, z ∈ S → z ≠ b := by
        rintro z hz rfl
        exact hb ((hSdef ▸ hz).2).symm
      -- The cover: given `z` in `(y, b)`, take `n` with `(b - y) / (b - z) < n`, which pushes the
      -- right endpoint `b - (b - y) / (n + 2)` strictly between `z` and `b`, so `z` belongs to the
      -- `n`-th interval.
      have hsub : Ioo y b ⊆ ⋃ n : ℕ, Ioc y (b - (b - y) / (n + 2)) := by
        intro z hz
        obtain ⟨n, hn⟩ := exists_nat_gt ((b - y) / (b - z))
        have h1 : (b - y) / (b - z) < n + 1 := by linarith
        have h2pos : (0 : ℝ) < b - z := sub_pos.2 hz.2
        have h2 : (b - y) / (n + 2) < b - z := by
          rw [div_lt_iff₀ (by positivity : (0 : ℝ) < n + 2)]
          rw [div_lt_iff₀ h2pos] at h1
          linarith
        have hmem : y < z ∧ z < b - (b - y) / (n + 2) := ⟨hz.1, by linarith [h2, hz.1]⟩
        exact mem_iUnion.2 ⟨n, hmem.1, le_of_lt hmem.2⟩
      refine ae_iff.mpr ?_
      rw [hnotMem]
      refine measure_mono_null (s := S) (t := Ioo y b)
        (fun z hz ↦ ⟨hz.1, lt_of_le_of_ne (hle z hz) (hne z hz)⟩) ?_
      refine le_antisymm ?_ bot_le
      -- Countable subadditivity bounds the interval by the sum of the increments of the covering
      -- intervals, and each increment vanishes because `hstab` makes the cumulative function
      -- constant at the level `cdf ν y` throughout `(y, b)`.
      calc ν (Ioo y b) ≤ ν (⋃ n : ℕ, Ioc y (b - (b - y) / (n + 2))) := measure_mono hsub
        _ ≤ ∑' n : ℕ, ν (Ioc y (b - (b - y) / (n + 2))) := measure_iUnion_le _
        _ = 0 := ENNReal.tsum_eq_zero.2 fun n ↦ by
          have h1div : (1 : ℝ) / (n + 2) < 1 :=
            (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 2)).2 (by
              have _h : (1 : ℝ) ≤ n + 1 := by
                exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
              linarith)
          have hlow : (b - y) / (n + 2) < b - y := by
            rw [div_eq_mul_one_div]
            simpa using mul_lt_mul_of_pos_left h1div hneS
          have hpos : (0 : ℝ) < (b - y) / (n + 2) := div_pos hneS (by positivity)
          have hmem : y < b - (b - y) / (n + 2) ∧ b - (b - y) / (n + 2) < b :=
            ⟨by linarith, by simpa using sub_lt_sub_left hpos b⟩
          rw [← measure_cdf ν, StieltjesFunction.measure_Ioc, (hstab _ hmem.1 hmem.2).symm,
            sub_self, ENNReal.ofReal_zero]
  · refine ae_iff.mpr ?_
    rw [hnotMem, not_nonempty_iff_eq_empty.mp hSne, measure_empty]

/-- The quantile of the CDF is the identity almost everywhere, for every real probability measure.
The cumulative distribution function of a law with atoms has plateaus, but the part of a plateau
strictly to the right of a point whose cumulative mass is below `1` is null, so almost every
point is the least point reaching its own level. -/
theorem quantile_cdf_ae (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (fun x => ν.quantile (cdf ν x)) =ᵐ[ν] id := by
  have hplat : ∀ q : ℚ, cdf ν q < 1 → ∀ᵐ (x : ℝ) ∂ν, ¬ (q < x ∧ cdf ν q = cdf ν x) :=
    fun q hq ↦ ae_not_of_lt_of_cdf_eq hq
  have htop : ∀ q : ℚ, cdf ν q = 1 → ∀ᵐ (x : ℝ) ∂ν, ¬ (q < x ∧ cdf ν q = cdf ν x) := by
    intro q hq
    have hnull : ν (Ioi (q : ℝ)) = 0 := by
      have hIic : ν (Iic (q : ℝ)) = 1 := by rw [← ofReal_cdf ν q, hq]; simp
      rw [← compl_Iic, measure_compl measurableSet_Iic (by rw [hIic]; simp), hIic]
      simp
    have hmem : ∀ᶠ (x : ℝ) in ae ν, x ∉ Ioi (q : ℝ) := by
      refine ae_iff.2 ?_
      have hset : {a : ℝ | ¬ a ∉ Ioi (q : ℝ)} = Ioi (q : ℝ) := by
        ext a
        simp
      rw [hset]
      exact hnull
    filter_upwards [hmem] with x hx
    exact fun hqx ↦ hx hqx.1
  have hplateau : ∀ᵐ (x : ℝ) ∂ν, ∀ q : ℚ, ¬ (q < x ∧ cdf ν q = cdf ν x) :=
    (eventually_countable_forall (l := ae ν) (ι := ℚ) (α := ℝ)
      (p := fun x q ↦ ¬ (q < x ∧ cdf ν q = cdf ν x))).2 fun q ↦ by
        by_cases hq : cdf ν q < 1
        · exact hplat q hq
        · exact htop q (le_antisymm (cdf_le_one ν q) (le_of_not_gt hq))
  have hpos : ∀ᵐ (x : ℝ) ∂ν, 0 < cdf ν x := by
    filter_upwards [hplateau] with x hx
    have hne0 : cdf ν x ≠ 0 := by
      rintro h0
      obtain ⟨q, _, hq2⟩ := exists_rat_btwn (show x - 1 < x from by linarith)
      have hq0 : cdf ν q = 0 := by
        refine le_antisymm ?_ (cdf_nonneg ν _)
        simpa [h0] using monotone_cdf ν hq2.le
      exact hx q ⟨hq2, h0 ▸ hq0⟩
    exact lt_of_le_of_ne (cdf_nonneg ν x) (Ne.symm hne0)
  filter_upwards [hpos, hplateau] with x hx hqx
  simp only [id_eq]
  rw [quantile_def]
  have hmem : (x : ℝ) ∈ {z | cdf ν x ≤ cdf ν z} := Set.mem_ofPred_eq.mpr le_rfl
  refine le_antisymm (csInf_le (bddBelow_setOf_le_cdf ν hx) hmem) ?_
  refine le_csInf ⟨x, hmem⟩ ?_
  intro z hz
  by_contra hzx
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_of_not_ge hzx)
  have hqc : cdf ν q = cdf ν x :=
    le_antisymm (monotone_cdf ν hq2.le) (hz.trans (monotone_cdf ν hq1.le))
  exact hqx q ⟨hq2, hqc⟩

/-- **The CDF/quantile transport of an atomless real law.** The cumulative distribution function
and the quantile function of an atomless probability measure `ν` on `ℝ` push `ν` and Lebesgue
measure restricted to `[0, 1]` forward onto one another, and are mutually inverse almost
everywhere; together they are a mod-zero isomorphism between `ν` and the unit interval. -/
def realMod0MeasureIso (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : TauCeti.Mod0MeasureIso ℝ ℝ ν (volume.restrict (Set.Icc 0 1)) where
  toFun := cdf ν
  invFun := ν.quantile
  measurable_toFun := (cdf ν).mono.measurable
  measurable_invFun := measurable_quantile ν
  map_toFun := cdf_map_eq_volume_restrict ν
  map_invFun := by
    simpa only [MeasureTheory.restrict_Ioo_eq_restrict_Icc] using (map_quantile_volume_Ioo ν)
  left_inv_ae := quantile_cdf_ae ν
  right_inv_ae := cdf_quantile_ae ν

@[simp]
theorem realMod0MeasureIso_toFun (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : (realMod0MeasureIso ν).toFun = cdf ν :=
  (rfl)

@[simp]
theorem realMod0MeasureIso_invFun (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : (realMod0MeasureIso ν).invFun = ν.quantile :=
  (rfl)

end MeasureTheory.Measure
