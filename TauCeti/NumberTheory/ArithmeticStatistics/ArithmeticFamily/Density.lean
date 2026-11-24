/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticStatistics.ArithmeticFamily.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Relative densities in arithmetic families

For subfamilies `S` and `T` of an arithmetic family, the proportion of `T` lying in `S` at the
inclusive cutoff `X` is

```text
  ratio S T X = count (S ∩ T) X / count T X,
```

read as `0` when the denominator vanishes. The upper and lower relative densities are the
`limsup` and `liminf` of this proportion as `X → ∞`, and `HasDensity S T d` says that the
proportion tends to `d`. The reference family `T` is always explicit: a statement such as
*density one among squarefree integers* is `HasDensity A T 1` for that `T`.

## Main results

* `ArithmeticFamily.hasDensity_iff_lowerDensity_eq_upperDensity`: a density exists exactly when
  the lower and upper densities agree.
* `ArithmeticFamily.hasDensity_self`: a nonempty subfamily has density one in itself.
* `ArithmeticFamily.HasDensity.union`, `ArithmeticFamily.HasDensity.diff`: densities add on
  disjoint subfamilies and complement inside a nonempty reference family.
* `ArithmeticFamily.hasDensity_zero_of_finite`, `ArithmeticFamily.HasDensity.congr_finite`:
  finite sets are negligible in an infinite reference family.
* `ArithmeticFamily.hasDensity_iff_tendsto_ratioLT`: strict and inclusive cutoffs give the same
  densities.
* `ArithmeticFamily.hasDensity_rescale_iff`: a positive constant multiple of the height gives
  the same densities.
* `ArithmeticFamily.HasDensity.trans`: densities multiply in towers `S ⊆ T ⊆ U`.

## References

* M. Bhargava, A. Shankar, *Binary quartic forms having bounded invariants, and the
  boundedness of the average rank of elliptic curves*, Ann. of Math. 181 (2015), 191–242,
  Theorem 1.8 (densities of families of elliptic curves ordered by height).
* A. Burungale, Y. Tian, *A rank zero p-converse to a theorem of Gross–Zagier, Kolyvagin and
  Rubin*, Ann. of Math. 203 (2026), 1–13, Theorem 1.2 and Proposition 1.3 (density one and
  lower densities among squarefree integers).
-/

public section

open Filter Topology

namespace TauCeti

namespace ArithmeticFamily

variable {ι : Type*} (F : ArithmeticFamily ι)

/-! ### Proportions at a cutoff -/

/-- The proportion of `T` lying in `S` at the inclusive cutoff `X`, with `0 / 0 = 0`. -/
noncomputable def ratio (S T : Set ι) (X : ℝ) : ℝ :=
  (F.count (S ∩ T) X : ℝ) / F.count T X

/-- The proportion of `T` lying in `S` at the strict cutoff `X`, with `0 / 0 = 0`. -/
noncomputable def ratioLT (S T : Set ι) (X : ℝ) : ℝ :=
  (F.countLT (S ∩ T) X : ℝ) / F.countLT T X

/-- The upper relative density of `S` in `T`. -/
noncomputable def upperDensity (S T : Set ι) : ℝ :=
  limsup (F.ratio S T) atTop

/-- The lower relative density of `S` in `T`, the lower limiting proportion. -/
noncomputable def lowerDensity (S T : Set ι) : ℝ :=
  liminf (F.ratio S T) atTop

/-- `S` has relative density `d` in `T` when the proportion of `T` lying in `S` tends to `d`
as the inclusive cutoff tends to infinity. -/
def HasDensity (S T : Set ι) (d : ℝ) : Prop :=
  Tendsto (F.ratio S T) atTop (𝓝 d)

variable {F} {S S' T U : Set ι} {d d' : ℝ}

/-- Evaluate the inclusive proportion as a quotient of counts. -/
theorem ratio_apply (S T : Set ι) (X : ℝ) :
    F.ratio S T X = (F.count (S ∩ T) X : ℝ) / F.count T X := by
  rw [ratio]

/-- Evaluate the strict proportion as a quotient of strict counts. -/
theorem ratioLT_apply (S T : Set ι) (X : ℝ) :
    F.ratioLT S T X = (F.countLT (S ∩ T) X : ℝ) / F.countLT T X := by
  rw [ratioLT]

/-- The upper relative density is the `limsup` of the proportions. -/
theorem upperDensity_def (S T : Set ι) : F.upperDensity S T = limsup (F.ratio S T) atTop := by
  rw [upperDensity]

/-- The lower relative density is the `liminf` of the proportions. -/
theorem lowerDensity_def (S T : Set ι) : F.lowerDensity S T = liminf (F.ratio S T) atTop := by
  rw [lowerDensity]

/-- Having a relative density is convergence of the proportions. -/
theorem hasDensity_iff : F.HasDensity S T d ↔ Tendsto (F.ratio S T) atTop (𝓝 d) := by
  rw [HasDensity]

/-- Proportions are nonnegative. -/
theorem ratio_nonneg (S T : Set ι) (X : ℝ) : 0 ≤ F.ratio S T X := by
  rw [ratio_apply]
  positivity

/-- Proportions are at most one. -/
theorem ratio_le_one (S T : Set ι) (X : ℝ) : F.ratio S T X ≤ 1 := by
  rw [ratio_apply]
  exact div_le_one_of_le₀ (mod_cast F.count_mono_set Set.inter_subset_right X) (by positivity)

/-- The empty subfamily has proportion zero. -/
@[simp]
theorem ratio_empty (T : Set ι) (X : ℝ) : F.ratio ∅ T X = 0 := by
  simp [ratio_apply]

/-- The proportion of `T` lying in `S` only depends on `S ∩ T`. -/
@[simp]
theorem ratio_inter_right (S T : Set ι) (X : ℝ) : F.ratio (S ∩ T) T X = F.ratio S T X := by
  rw [ratio_apply, ratio_apply, Set.inter_assoc, Set.inter_self]

/-- Proportions add on disjoint subfamilies, at every cutoff. -/
theorem ratio_union_of_disjoint (h : Disjoint S S') (T : Set ι) (X : ℝ) :
    F.ratio (S ∪ S') T X = F.ratio S T X + F.ratio S' T X := by
  rw [ratio_apply, ratio_apply, ratio_apply, Set.union_inter_distrib_right,
    F.count_union_of_disjoint (h.mono Set.inter_subset_left Set.inter_subset_left), Nat.cast_add,
    add_div]

/-- Proportions multiply in towers `S ⊆ T ⊆ U`, at every cutoff. -/
theorem ratio_mul_ratio_of_subset (hST : S ⊆ T) (hTU : T ⊆ U) (X : ℝ) :
    F.ratio S T X * F.ratio T U X = F.ratio S U X := by
  rw [ratio_apply, ratio_apply, ratio_apply, Set.inter_eq_left.mpr hST,
    Set.inter_eq_left.mpr hTU, Set.inter_eq_left.mpr (hST.trans hTU)]
  rcases Nat.eq_zero_or_pos (F.count T X) with hT | hT
  · have hS : F.count S X = 0 := Nat.eq_zero_of_le_zero (hT ▸ F.count_mono_set hST X)
    simp [hS, hT]
  · rw [div_mul_div_comm, mul_comm (F.count S X : ℝ),
      mul_div_mul_left _ _ (by positivity : (F.count T X : ℝ) ≠ 0)]

/-! ### Upper and lower densities -/

private theorem isBoundedUnder_le_ratio (S T : Set ι) :
    IsBoundedUnder (· ≤ ·) atTop (F.ratio S T) :=
  isBoundedUnder_of ⟨1, F.ratio_le_one S T⟩

private theorem isBoundedUnder_ge_ratio (S T : Set ι) :
    IsBoundedUnder (· ≥ ·) atTop (F.ratio S T) :=
  isBoundedUnder_of ⟨0, F.ratio_nonneg S T⟩

/-- The lower relative density never exceeds the upper one. -/
theorem lowerDensity_le_upperDensity (S T : Set ι) : F.lowerDensity S T ≤ F.upperDensity S T :=
  liminf_le_limsup (isBoundedUnder_le_ratio S T) (isBoundedUnder_ge_ratio S T)

/-- A relative density is the lower relative density. -/
theorem HasDensity.lowerDensity_eq (h : F.HasDensity S T d) : F.lowerDensity S T = d :=
  (hasDensity_iff.mp h).liminf_eq

/-- A relative density is the upper relative density. -/
theorem HasDensity.upperDensity_eq (h : F.HasDensity S T d) : F.upperDensity S T = d :=
  (hasDensity_iff.mp h).limsup_eq

/-- A relative density exists exactly when the lower and upper relative densities agree. -/
theorem hasDensity_iff_lowerDensity_eq_upperDensity :
    F.HasDensity S T d ↔ F.lowerDensity S T = d ∧ F.upperDensity S T = d :=
  ⟨fun h ↦ ⟨h.lowerDensity_eq, h.upperDensity_eq⟩, fun h ↦
    hasDensity_iff.mpr <| tendsto_of_liminf_eq_limsup h.1 h.2 (isBoundedUnder_le_ratio S T)
      (isBoundedUnder_ge_ratio S T)⟩

/-- A relative density is unique. -/
theorem HasDensity.unique (h : F.HasDensity S T d) (h' : F.HasDensity S T d') : d = d' :=
  tendsto_nhds_unique (hasDensity_iff.mp h) (hasDensity_iff.mp h')

/-- A relative density is nonnegative. -/
theorem HasDensity.nonneg (h : F.HasDensity S T d) : 0 ≤ d :=
  ge_of_tendsto' (hasDensity_iff.mp h) (F.ratio_nonneg S T)

/-- A relative density is at most one. -/
theorem HasDensity.le_one (h : F.HasDensity S T d) : d ≤ 1 :=
  le_of_tendsto' (hasDensity_iff.mp h) (F.ratio_le_one S T)

/-! ### Basic densities -/

/-- The empty subfamily has density zero in every reference family. -/
theorem hasDensity_empty (T : Set ι) : F.HasDensity ∅ T 0 := by
  rw [hasDensity_iff]
  exact tendsto_const_nhds.congr fun X ↦ (F.ratio_empty T X).symm

/-- A nonempty subfamily has density one in itself. The empty subfamily has density zero in
itself by the `0 / 0 = 0` convention. -/
theorem hasDensity_self (hT : T.Nonempty) : F.HasDensity T T 1 := by
  rw [hasDensity_iff]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [F.eventually_count_pos hT] with X hX
  rw [ratio_apply, Set.inter_self, div_self (by positivity)]

/-- Densities add on disjoint subfamilies. -/
theorem HasDensity.union (h : Disjoint S S') (hS : F.HasDensity S T d)
    (hS' : F.HasDensity S' T d') : F.HasDensity (S ∪ S') T (d + d') := by
  rw [hasDensity_iff]
  exact ((hasDensity_iff.mp hS).add (hasDensity_iff.mp hS')).congr fun X ↦
    (F.ratio_union_of_disjoint h T X).symm

/-- The complement of a subfamily in a nonempty reference family has the complementary
density. -/
theorem HasDensity.diff (hT : T.Nonempty) (h : F.HasDensity S T d) :
    F.HasDensity (T \ S) T (1 - d) := by
  rw [hasDensity_iff]
  refine (tendsto_const_nhds.sub (hasDensity_iff.mp h)).congr' ?_
  filter_upwards [F.eventually_count_pos hT] with X hX
  have hsplit := F.ratio_union_of_disjoint (S := T ∩ S) (S' := T \ S)
    Set.disjoint_sdiff_inter.symm T X
  rw [Set.inter_union_sdiff, ratio_apply T, Set.inter_self, div_self (by positivity)] at hsplit
  rw [Set.inter_comm, ratio_inter_right] at hsplit
  linarith

/-- A finite subfamily has density zero in an infinite reference family. -/
theorem hasDensity_zero_of_finite (hS : S.Finite) (hT : T.Infinite) : F.HasDensity S T 0 := by
  rw [hasDensity_iff]
  refine squeeze_zero (g := fun X ↦ (S.ncard : ℝ) / F.count T X) (F.ratio_nonneg S T)
    (fun X ↦ ?_)
    (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (F.tendsto_count_atTop hT)))
  rw [ratio_apply, count_eq_ncard]
  exact div_le_div_of_nonneg_right
    (mod_cast Set.ncard_le_ncard (fun _ hi ↦ hi.1.1) hS) (Nat.cast_nonneg _)

/-- Changing a subfamily by finitely many members does not change its density in an infinite
reference family. -/
theorem HasDensity.congr_finite (hSS' : (symmDiff S S').Finite) (hT : T.Infinite)
    (h : F.HasDensity S T d) : F.HasDensity S' T d := by
  have h₁ : F.HasDensity (S \ S') T 0 := hasDensity_zero_of_finite
    (hSS'.subset fun _ hx ↦ Set.mem_symmDiff.mpr (Or.inl hx)) hT
  have h₂ : F.HasDensity (S' \ S) T 0 := hasDensity_zero_of_finite
    (hSS'.subset fun _ hx ↦ Set.mem_symmDiff.mpr (Or.inr hx)) hT
  have hinter : F.HasDensity (S ∩ S') T d := by
    rw [hasDensity_iff]
    convert (hasDensity_iff.mp h).sub (hasDensity_iff.mp h₁) using 1
    · ext X
      rw [eq_sub_iff_add_eq, ← F.ratio_union_of_disjoint
        Set.disjoint_sdiff_inter.symm, Set.inter_union_sdiff]
    · rw [sub_zero]
  have hdisj : Disjoint (S ∩ S') (S' \ S) := by
    rw [Set.inter_comm]
    exact Set.disjoint_sdiff_inter.symm
  simpa [Set.inter_comm S S', Set.inter_union_sdiff] using hinter.union hdisj h₂

/-! ### Strict cutoffs -/

/-- Strict and inclusive cutoffs give the same relative densities. -/
theorem hasDensity_iff_tendsto_ratioLT :
    F.HasDensity S T d ↔ Tendsto (F.ratioLT S T) atTop (𝓝 d) := by
  choose δ hδ hδeq using F.exists_countLT_eq_count_sub
  choose ε hε hεeq using F.exists_count_eq_countLT_add
  rw [hasDensity_iff]
  constructor
  · intro h
    have hg : Tendsto (fun X ↦ X - δ X) atTop atTop :=
      tendsto_atTop_mono (fun X ↦ by simp only [id]; linarith [(hδ X).2])
        (tendsto_atTop_add_const_right _ (-1) tendsto_id)
    refine (h.comp hg).congr fun X ↦ ?_
    simp [ratio_apply, ratioLT_apply, hδeq]
  · intro h
    have hg : Tendsto (fun X ↦ X + ε X) atTop atTop :=
      tendsto_atTop_mono (fun X ↦ by simp only [id]; linarith [(hε X).1]) tendsto_id
    refine (h.comp hg).congr fun X ↦ ?_
    simp [ratio_apply, ratioLT_apply, hεeq]

/-! ### Rescaling and towers -/

/-- Rescaling the height by `c > 0` divides the cutoff of every proportion by `c`. -/
theorem ratio_rescale (c : ℝ) (hc : 0 < c) (S T : Set ι) (X : ℝ) :
    (F.rescale c hc).ratio S T X = F.ratio S T (X / c) := by
  simp [ratio_apply, count_rescale]

/-- Rescaling the height by `c > 0` does not change relative densities. -/
theorem hasDensity_rescale_iff (c : ℝ) (hc : 0 < c) :
    (F.rescale c hc).HasDensity S T d ↔ F.HasDensity S T d := by
  rw [hasDensity_iff, hasDensity_iff, funext (F.ratio_rescale c hc S T)]
  conv_rhs => rw [← map_div_atTop_eq c hc, tendsto_map'_iff, Function.comp_def]

/-- Relative densities multiply in towers: if `S ⊆ T ⊆ U`, `S` has density `α` in `T` and `T`
has density `β` in `U`, then `S` has density `α * β` in `U`. -/
theorem HasDensity.trans {α β : ℝ} (hST : S ⊆ T) (hTU : T ⊆ U) (hS : F.HasDensity S T α)
    (hT : F.HasDensity T U β) : F.HasDensity S U (α * β) := by
  rw [hasDensity_iff]
  exact ((hasDensity_iff.mp hS).mul (hasDensity_iff.mp hT)).congr
    (F.ratio_mul_ratio_of_subset hST hTU)

end ArithmeticFamily

end TauCeti
