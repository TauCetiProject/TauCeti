/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticStatistics.ArithmeticFamily.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Relative densities in arithmetic families

For subfamilies `S` and `T` of an arithmetic family, `ratio S T X` is the proportion of the
members of `T` of height at most `X` that lie in `S`, read as `0` when there are none. The
upper and lower relative densities are its `limsup` and `liminf` as the real cutoff tends to
infinity, and `HasDensity S T d` says that the proportion tends to `d`. Statements such as
"density one" or "half of all squarefree integers" in arithmetic statistics are relative
densities in this sense, with the reference family `T` named explicitly.

## Main results

* `hasDensity_iff_lowerDensity_eq_and_upperDensity_eq`,
  `exists_hasDensity_iff_lowerDensity_eq_upperDensity`: a relative density is the common value
  of the lower and upper relative densities, and exists exactly when they agree.
* `HasDensity.sdiff`, `HasDensity.union`: complements and disjoint unions.
* `hasDensity_zero_of_finite`, `HasDensity.congr_finite`: finite sets are negligible in an
  infinite reference family.
* `hasDensity_iff_tendsto_ratioLT`: the inclusive and the strict cutoffs give the same
  densities.
* `hasDensity_rescale_iff`: rescaling the height by a positive constant does not change
  densities.
* `HasDensity.mul`: relative densities multiply in towers.
* `hasDensity_inter_one_of_lowerDensity_pos`: a density-one subfamily has density one in every
  subfamily of positive lower density.

## References

* M. Bhargava, A. Shankar, *Binary quartic forms having bounded invariants, and the
  boundedness of the average rank of elliptic curves*, Ann. of Math. 181 (2015), §2.
* A. Burungale, Y. Tian, *A rank zero p-converse to a theorem of Gross–Zagier, Kolyvagin and
  Rubin*, Ann. of Math. 203 (2026), Theorem 1.2 and Proposition 1.3.
-/

public section

namespace TauCeti

namespace ArithmeticFamily

open Filter Topology

variable {ι : Type*} (F : ArithmeticFamily ι)

/-- The proportion of the members of `T` of height at most `X` that lie in `S`, read as `0`
when `T` has no member of height at most `X`. -/
noncomputable def ratio (S T : Set ι) (X : ℝ) : ℝ :=
  (F.count (S ∩ T) X : ℝ) / F.count T X

/-- The proportion of the members of `T` of height less than `X` that lie in `S`, read as `0`
when `T` has no member of height less than `X`. -/
noncomputable def ratioLT (S T : Set ι) (X : ℝ) : ℝ :=
  (F.countLT (S ∩ T) X : ℝ) / F.countLT T X

/-- The upper relative density of `S` in `T`: the `limsup` of the proportion `ratio S T X` as
the cutoff `X` tends to infinity. -/
noncomputable def upperDensity (S T : Set ι) : ℝ :=
  limsup (F.ratio S T) atTop

/-- The lower relative density of `S` in `T`: the `liminf` of the proportion `ratio S T X` as
the cutoff `X` tends to infinity. -/
noncomputable def lowerDensity (S T : Set ι) : ℝ :=
  liminf (F.ratio S T) atTop

/-- `S` has relative density `d` in `T`: the proportion of the members of `T` of height at
most `X` that lie in `S` tends to `d` as the cutoff `X` tends to infinity. -/
def HasDensity (S T : Set ι) (d : ℝ) : Prop :=
  Tendsto (F.ratio S T) atTop (𝓝 d)

variable {F} {S S' T U : Set ι} {d d' : ℝ}

/-- Evaluate the inclusive proportion as a quotient of counts. -/
theorem ratio_apply (S T : Set ι) (X : ℝ) :
    F.ratio S T X = (F.count (S ∩ T) X : ℝ) / F.count T X := (rfl)

/-- Evaluate the strict proportion as a quotient of strict counts. -/
theorem ratioLT_apply (S T : Set ι) (X : ℝ) :
    F.ratioLT S T X = (F.countLT (S ∩ T) X : ℝ) / F.countLT T X := (rfl)

/-- The upper relative density is the `limsup` of the inclusive proportion. -/
theorem upperDensity_def (S T : Set ι) :
    F.upperDensity S T = limsup (F.ratio S T) atTop := (rfl)

/-- The lower relative density is the `liminf` of the inclusive proportion. -/
theorem lowerDensity_def (S T : Set ι) :
    F.lowerDensity S T = liminf (F.ratio S T) atTop := (rfl)

/-- A relative density is a limit of the inclusive proportion. -/
theorem hasDensity_iff_tendsto_ratio :
    F.HasDensity S T d ↔ Tendsto (F.ratio S T) atTop (𝓝 d) := .rfl

alias ⟨HasDensity.tendsto, _⟩ := hasDensity_iff_tendsto_ratio

/-! ### Bounds on the proportion -/

variable (F) in
/-- Proportions are nonnegative. -/
theorem ratio_nonneg (S T : Set ι) (X : ℝ) : 0 ≤ F.ratio S T X := by
  rw [ratio_apply]
  positivity

variable (F) in
/-- Proportions are at most one. -/
theorem ratio_le_one (S T : Set ι) (X : ℝ) : F.ratio S T X ≤ 1 := by
  rw [ratio_apply]
  exact div_le_one_of_le₀ (by exact_mod_cast F.count_mono_set Set.inter_subset_right X)
    (by positivity)

variable (F) in
/-- Strict proportions are nonnegative. -/
theorem ratioLT_nonneg (S T : Set ι) (X : ℝ) : 0 ≤ F.ratioLT S T X := by
  rw [ratioLT_apply]
  positivity

variable (F) in
/-- Strict proportions are at most one. -/
theorem ratioLT_le_one (S T : Set ι) (X : ℝ) : F.ratioLT S T X ≤ 1 := by
  rw [ratioLT_apply]
  exact div_le_one_of_le₀ (by exact_mod_cast F.countLT_mono_set Set.inter_subset_right X)
    (by positivity)

variable (F) in
/-- The proportion is bounded above along every filter. -/
theorem isBoundedUnder_le_ratio (S T : Set ι) (l : Filter ℝ) :
    l.IsBoundedUnder (· ≤ ·) (F.ratio S T) :=
  isBoundedUnder_of ⟨1, F.ratio_le_one S T⟩

variable (F) in
/-- The proportion is bounded below along every filter. -/
theorem isBoundedUnder_ge_ratio (S T : Set ι) (l : Filter ℝ) :
    l.IsBoundedUnder (· ≥ ·) (F.ratio S T) :=
  isBoundedUnder_of ⟨0, F.ratio_nonneg S T⟩

variable (F) in
/-- Lower relative densities are nonnegative. -/
theorem lowerDensity_nonneg (S T : Set ι) : 0 ≤ F.lowerDensity S T :=
  le_liminf_of_le (F.isBoundedUnder_le_ratio S T atTop).isCoboundedUnder_ge
    (.of_forall (F.ratio_nonneg S T))

variable (F) in
/-- Upper relative densities are at most one. -/
theorem upperDensity_le_one (S T : Set ι) : F.upperDensity S T ≤ 1 :=
  limsup_le_of_le (F.isBoundedUnder_ge_ratio S T atTop).isCoboundedUnder_le
    (.of_forall (F.ratio_le_one S T))

variable (F) in
/-- The lower relative density never exceeds the upper relative density. -/
theorem lowerDensity_le_upperDensity (S T : Set ι) : F.lowerDensity S T ≤ F.upperDensity S T :=
  liminf_le_limsup (F.isBoundedUnder_le_ratio S T atTop) (F.isBoundedUnder_ge_ratio S T atTop)

/-! ### Limits and the lower and upper densities -/

/-- A relative density is the common value of the lower and upper relative densities. -/
theorem hasDensity_iff_lowerDensity_eq_and_upperDensity_eq :
    F.HasDensity S T d ↔ F.lowerDensity S T = d ∧ F.upperDensity S T = d :=
  ⟨fun h ↦ ⟨h.liminf_eq, h.limsup_eq⟩, fun h ↦ tendsto_of_liminf_eq_limsup h.1 h.2
    (F.isBoundedUnder_le_ratio S T atTop) (F.isBoundedUnder_ge_ratio S T atTop)⟩

/-- A relative density is the lower relative density. -/
theorem HasDensity.lowerDensity_eq (h : F.HasDensity S T d) : F.lowerDensity S T = d :=
  (hasDensity_iff_lowerDensity_eq_and_upperDensity_eq.mp h).1

/-- A relative density is the upper relative density. -/
theorem HasDensity.upperDensity_eq (h : F.HasDensity S T d) : F.upperDensity S T = d :=
  (hasDensity_iff_lowerDensity_eq_and_upperDensity_eq.mp h).2

/-- A relative density is unique. -/
theorem HasDensity.unique (h : F.HasDensity S T d) (h' : F.HasDensity S T d') : d = d' :=
  tendsto_nhds_unique h h'

/-- A relative density exists exactly when the lower and upper relative densities agree. -/
theorem exists_hasDensity_iff_lowerDensity_eq_upperDensity :
    (∃ d, F.HasDensity S T d) ↔ F.lowerDensity S T = F.upperDensity S T :=
  ⟨fun ⟨_, h⟩ ↦ h.lowerDensity_eq.trans h.upperDensity_eq.symm,
    fun h ↦ ⟨_, hasDensity_iff_lowerDensity_eq_and_upperDensity_eq.mpr ⟨h, rfl⟩⟩⟩

/-- Relative densities are nonnegative. -/
theorem HasDensity.nonneg (h : F.HasDensity S T d) : 0 ≤ d :=
  h.lowerDensity_eq ▸ F.lowerDensity_nonneg S T

/-- Relative densities are at most one. -/
theorem HasDensity.le_one (h : F.HasDensity S T d) : d ≤ 1 :=
  h.upperDensity_eq ▸ F.upperDensity_le_one S T

/-! ### Elementary densities -/

/-- No member of a reference family lies in the empty subfamily. -/
@[simp]
theorem ratio_empty_left (T : Set ι) (X : ℝ) : F.ratio ∅ T X = 0 := by
  simp [ratio_apply]

/-- The proportion in the empty reference family is zero by convention. -/
@[simp]
theorem ratio_empty_right (S : Set ι) (X : ℝ) : F.ratio S ∅ X = 0 := by
  simp [ratio_apply]

/-- A reference family with a member of height at most `X` has proportion one in itself. -/
theorem ratio_self {X : ℝ} (hT : 0 < F.count T X) : F.ratio T T X = 1 := by
  rw [ratio_apply, Set.inter_self]
  exact div_self (by positivity)

/-- The empty subfamily has density zero in every reference family. -/
theorem hasDensity_empty (T : Set ι) : F.HasDensity ∅ T 0 := by
  rw [hasDensity_iff_tendsto_ratio, funext (ratio_empty_left (F := F) T)]
  exact tendsto_const_nhds

/-- A nonempty subfamily has density one in itself. -/
theorem hasDensity_self (hT : T.Nonempty) : F.HasDensity T T 1 :=
  tendsto_const_nhds.congr' <| (F.eventually_count_pos hT).mono fun _ hX ↦ (ratio_self hX).symm

/-- Proportions add on disjoint subfamilies. -/
theorem ratio_union (h : Disjoint S S') (T : Set ι) (X : ℝ) :
    F.ratio (S ∪ S') T X = F.ratio S T X + F.ratio S' T X := by
  simp only [ratio_apply, Set.union_inter_distrib_right,
    F.count_union_of_disjoint (h.mono Set.inter_subset_left Set.inter_subset_left)]
  push_cast
  exact add_div _ _ _

/-- Proportions are subadditive. -/
theorem ratio_union_le (S S' T : Set ι) (X : ℝ) :
    F.ratio (S ∪ S') T X ≤ F.ratio S T X + F.ratio S' T X := by
  simp only [ratio_apply, Set.union_inter_distrib_right, ← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast F.count_union_le _ _ X) (by positivity)

/-- Enlarging a subfamily enlarges its proportion. -/
theorem ratio_mono_left (h : S ⊆ S') (T : Set ι) (X : ℝ) : F.ratio S T X ≤ F.ratio S' T X := by
  simp only [ratio_apply]
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast F.count_mono_set (Set.inter_subset_inter_left T h) X) (by positivity)

/-- Within a reference family with a member of height at most `X`, the proportion of the
complement is one minus the proportion. -/
theorem ratio_sdiff {X : ℝ} (hT : 0 < F.count T X) (S : Set ι) :
    F.ratio (T \ S) T X = 1 - F.ratio S T X := by
  have h := F.count_inter_add_count_sdiff T S X
  rw [ratio_apply, ratio_apply, Set.inter_eq_left.mpr Set.sdiff_subset, Set.inter_comm,
    eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq (by positivity)]
  exact_mod_cast (add_comm _ _).trans h

/-- The complement of a subfamily of density `d` in a nonempty reference family `T` has
density `1 - d` in `T`. -/
theorem HasDensity.sdiff (hT : T.Nonempty) (h : F.HasDensity S T d) :
    F.HasDensity (T \ S) T (1 - d) :=
  (tendsto_const_nhds.sub h).congr' <|
    (F.eventually_count_pos hT).mono fun _ hX ↦ (ratio_sdiff hX S).symm

/-- Relative densities add on disjoint subfamilies. -/
theorem HasDensity.union (hS : Disjoint S S') (h : F.HasDensity S T d)
    (h' : F.HasDensity S' T d') : F.HasDensity (S ∪ S') T (d + d') := by
  rw [hasDensity_iff_tendsto_ratio, funext (ratio_union hS T)]
  exact h.add h'

/-- A finite subfamily has density zero in an infinite reference family. -/
theorem hasDensity_zero_of_finite (hS : S.Finite) (hT : T.Infinite) : F.HasDensity S T 0 := by
  have hle (X : ℝ) : F.ratio S T X ≤ S.ncard / F.count T X := by
    rw [ratio_apply]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact_mod_cast (F.count_le_ncard (hS.subset Set.inter_subset_left) X).trans
      (Set.ncard_le_ncard Set.inter_subset_left hS)
  exact squeeze_zero (F.ratio_nonneg S T) hle
    (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (F.tendsto_count_atTop hT)))

/-- Changing a subfamily by finitely many members does not change its density in an infinite
reference family. -/
theorem HasDensity.congr_finite (hSS' : (symmDiff S S').Finite) (hT : T.Infinite)
    (h : F.HasDensity S T d) : F.HasDensity S' T d := by
  have h₀ := (hasDensity_zero_of_finite (F := F) hSS' hT).tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using h.tendsto.sub h₀)
    (by simpa using h.tendsto.add h₀) (fun X ↦ ?_) (fun X ↦ ?_)
  · rw [sub_le_iff_le_add]
    refine (ratio_mono_left (fun x hx ↦ ?_) T X).trans (ratio_union_le S' _ T X)
    by_cases hx' : x ∈ S'
    · exact .inl hx'
    · exact .inr (.inl ⟨hx, hx'⟩)
  · refine (ratio_mono_left (fun x hx ↦ ?_) T X).trans (ratio_union_le S _ T X)
    by_cases hx' : x ∈ S
    · exact .inl hx'
    · exact .inr (.inr ⟨hx, hx'⟩)

/-! ### Strict and inclusive cutoffs -/

variable (F) in
/-- Around every cutoff `X` there is a gap `δ ∈ (0, 1]` free of heights, except possibly `X`
itself, so that strict and inclusive counts at `X` are inclusive and strict counts at
`X - δ` and `X + δ`. -/
theorem exists_countLT_eq_count_sub_and_count_eq_countLT_add (X : ℝ) :
    ∃ δ, 0 < δ ∧ δ ≤ 1 ∧ ∀ S : Set ι,
      F.countLT S X = F.count S (X - δ) ∧ F.count S X = F.countLT S (X + δ) := by
  have hsub : {i | F.height i ≤ X + 1 ∧ F.height i ≠ X} ⊆ {i | F.height i ≤ X + 1} :=
    fun _ hi ↦ hi.1
  have hfin : (F.height '' {i | F.height i ≤ X + 1 ∧ F.height i ≠ X}).Finite :=
    ((F.finite_height_le (X + 1)).subset hsub).image _
  have hX : X ∉ F.height '' {i | F.height i ≤ X + 1 ∧ F.height i ≠ X} := by
    rintro ⟨i, ⟨-, hi⟩, rfl⟩
    exact hi rfl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hfin.isClosed.isOpen_compl X hX
  -- every height `h ≤ X + 1` other than `X` satisfies `|h - X| ≥ ε`
  have hgap : ∀ i, F.height i ≤ X + 1 → F.height i ≠ X → ε ≤ |F.height i - X| := by
    intro i hi hiX
    by_contra! hlt
    exact hball (Metric.mem_ball.mpr hlt) ⟨i, ⟨hi, hiX⟩, rfl⟩
  refine ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, fun S ↦ ⟨?_, ?_⟩⟩
  · rw [countLT_eq_ncard, count_eq_ncard]
    congr 1
    ext i
    simp only [Set.mem_ofPred_eq, and_congr_right_iff]
    intro _
    refine ⟨fun hi ↦ ?_, fun hi ↦ hi.trans_lt (by linarith [lt_min hε one_pos])⟩
    have := hgap i (by linarith) hi.ne
    rw [abs_of_neg (by linarith)] at this
    linarith [min_le_left ε 1]
  · rw [countLT_eq_ncard, count_eq_ncard]
    congr 1
    ext i
    simp only [Set.mem_ofPred_eq, and_congr_right_iff]
    intro _
    refine ⟨fun hi ↦ hi.trans_lt (by linarith [lt_min hε one_pos]), fun hi ↦ ?_⟩
    by_contra! hXi
    have := hgap i (by linarith [min_le_right ε 1]) hXi.ne'
    rw [abs_of_pos (by linarith)] at this
    linarith [min_le_left ε 1]

/-- The inclusive and strict cutoffs give the same relative densities. -/
theorem hasDensity_iff_tendsto_ratioLT :
    F.HasDensity S T d ↔ Tendsto (F.ratioLT S T) atTop (𝓝 d) := by
  choose δ hδ₀ hδ₁ hδ using F.exists_countLT_eq_count_sub_and_count_eq_countLT_add
  constructor
  · intro h
    have : Tendsto (fun X ↦ X - δ X) atTop atTop :=
      tendsto_atTop_mono (fun X ↦ by dsimp only [id]; linarith [hδ₁ X])
        (tendsto_atTop_add_const_right _ (-1) tendsto_id)
    refine (h.tendsto.comp this).congr fun X ↦ ?_
    simp [ratio_apply, ratioLT_apply, (hδ X _).1]
  · intro h
    have : Tendsto (fun X ↦ X + δ X) atTop atTop :=
      tendsto_atTop_mono (fun X ↦ by dsimp only [id]; linarith [hδ₀ X]) tendsto_id
    refine (h.comp this).congr fun X ↦ ?_
    simp [ratio_apply, ratioLT_apply, (hδ X _).2]

/-! ### Rescaling the height -/

/-- The proportion for a rescaled height is the original proportion at the divided cutoff. -/
@[simp]
theorem ratio_rescale (c : ℝ) (hc : 0 < c) (S T : Set ι) (X : ℝ) :
    (F.rescale c hc).ratio S T X = F.ratio S T (X / c) := by
  simp [ratio_apply, count_rescale]

/-- Rescaling the height by a positive constant does not change relative densities. -/
theorem hasDensity_rescale_iff (c : ℝ) (hc : 0 < c) :
    (F.rescale c hc).HasDensity S T d ↔ F.HasDensity S T d := by
  constructor
  · intro h
    refine (h.tendsto.comp (tendsto_id.atTop_mul_const hc)).congr fun X ↦ ?_
    simp [ratio_rescale, hc.ne']
  · intro h
    refine (h.tendsto.comp (tendsto_id.atTop_div_const hc)).congr fun X ↦ ?_
    simp [ratio_rescale]

/-! ### Towers and restriction -/

/-- In a tower `T ⊆ U`, the proportion of `U` lying in `S ∩ T` is the product of the
proportion of `T` lying in `S` and the proportion of `U` lying in `T`. -/
theorem ratio_mul_ratio (hTU : T ⊆ U) (S : Set ι) (X : ℝ) :
    F.ratio S T X * F.ratio T U X = F.ratio (S ∩ T) U X := by
  simp only [ratio_apply, Set.inter_eq_left.mpr hTU, Set.inter_assoc]
  rcases (Nat.zero_le (F.count T X)).eq_or_lt with h | h
  · have : F.count (S ∩ T) X = 0 :=
      Nat.eq_zero_of_le_zero (h ▸ F.count_mono_set Set.inter_subset_right X)
    simp [← h, this]
  · exact div_mul_div_cancel₀ (by positivity)

/-- Relative densities multiply in towers: if `S` has density `α` in `T` and `T ⊆ U` has
density `β` in `U`, then `S ∩ T` has density `α * β` in `U`. -/
theorem HasDensity.mul {α β : ℝ} (hTU : T ⊆ U) (hS : F.HasDensity S T α)
    (hT : F.HasDensity T U β) : F.HasDensity (S ∩ T) U (α * β) := by
  rw [hasDensity_iff_tendsto_ratio, ← funext (ratio_mul_ratio hTU S)]
  exact hS.tendsto.mul hT.tendsto

/-- A subfamily `A` of density one in `T` has density one in every subfamily `U ⊆ T` of
positive lower density in `T`. -/
theorem hasDensity_inter_one_of_lowerDensity_pos {A : Set ι} (hA : F.HasDensity A T 1)
    (hUT : U ⊆ T) (hU : 0 < F.lowerDensity U T) : F.HasDensity (A ∩ U) U 1 := by
  have hpos : ∀ᶠ X in atTop, F.lowerDensity U T / 2 < F.ratio U T X :=
    eventually_lt_of_lt_liminf (by rw [← lowerDensity_def]; linarith)
      (F.isBoundedUnder_ge_ratio U T atTop)
  obtain ⟨X₀, hX₀⟩ := hpos.exists
  rcases U.eq_empty_or_nonempty with rfl | hU₀
  · simp at hX₀
    linarith
  -- the proportion of `U` outside `A` is controlled by the proportion of `T` outside `A`
  have hbound : ∀ᶠ X in atTop,
      F.ratio (U \ A) U X ≤ F.ratio (T \ A) T X / (F.lowerDensity U T / 2) := by
    filter_upwards [hpos] with X hX
    rw [le_div_iff₀ (by linarith)]
    calc F.ratio (U \ A) U X * (F.lowerDensity U T / 2)
        ≤ F.ratio (U \ A) U X * F.ratio U T X :=
          mul_le_mul_of_nonneg_left hX.le (F.ratio_nonneg _ _ X)
      _ = F.ratio (U \ A) T X := by
          rw [ratio_mul_ratio hUT, Set.inter_eq_left.mpr Set.sdiff_subset]
      _ ≤ F.ratio (T \ A) T X := ratio_mono_left (Set.sdiff_subset_sdiff_left hUT) T X
  have hzero : F.HasDensity (U \ A) U 0 := by
    have hTA := (hA.sdiff (hU₀.mono hUT)).tendsto
    rw [sub_self] at hTA
    refine squeeze_zero' (.of_forall (F.ratio_nonneg _ U)) hbound ?_
    simpa using hTA.div_const (F.lowerDensity U T / 2)
  simpa [Set.sdiff_sdiff_right_self, Set.inter_comm] using hzero.sdiff hU₀

end ArithmeticFamily

end TauCeti
