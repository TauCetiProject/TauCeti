/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField

/-!
# The affine height of a tuple

Mathlib's `Height.mulHeight` is a height on projective space: it is invariant under scaling
(`Height.mulHeight_smul_eq_mulHeight`), so it is a function of the line through a tuple rather
than of the tuple. Quantities that are not homogeneous in the tuple, such as the value
`∑ i, a i * x i` of a linear form or the determinant of a matrix, scale with their arguments, so
no bound on their height can be stated in terms of the projective heights of the arguments, which
are scale-invariant. This file defines the **affine
height** of a tuple `x : ι → K`, the projective height of the tuple with a coordinate `1`
appended:

`Height.mulHeightAff x = Height.mulHeight fun o : Option ι ↦ o.elim 1 x`,

and its logarithm `Height.logHeightAff`. At each place the local factor is
`max (⨆ i, v (x i)) 1` (`Height.mulHeightAff_eq`), so the affine height is the tuple analogue
of `Height.mulHeight₁` and agrees with it on a one-element tuple
(`Height.mulHeightAff_unique`, `Height.mulHeightAff_fin_one`).

The affine height is deliberately not invariant under scaling
(`Height.exists_mulHeightAff_smul_ne`). What it gains is domination: it bounds the projective
height of the tuple and the height of every coordinate, and it can only drop under re-indexing.

## Main definitions

* `Height.mulHeightAff`: the multiplicative affine height of a tuple.
* `Height.logHeightAff`: its logarithm.

## Main results

* `Height.mulHeightAff_eq`: the affine height as a product of the local factors
  `max (⨆ i, v (x i)) 1`.
* `Height.mulHeight_le_mulHeightAff`, `Height.mulHeight₁_le_mulHeightAff`: the affine height
  dominates the projective height of the tuple and the height of each coordinate. The second
  fails for `Height.mulHeight`.
* `Height.mulHeightAff_comp_le`, `Height.mulHeightAff_comp_equiv`: monotonicity under
  re-indexing, with equality for a bijection.
* `Height.mulHeightAff_zero`: the zero tuple has affine height `1`.
* `Height.mulHeightAff_unique`, `Height.mulHeightAff_fin_one`: on a one-element tuple the
  affine height is `Height.mulHeight₁`.
* `Height.exists_mulHeightAff_smul_ne`: the affine height is not invariant under scaling.

## Implementation notes

The appended coordinate is indexed by `none : Option ι`. The type `Option ι` is finite when `ι`
is, and re-indexing along `f : ι → ι'` becomes re-indexing along `Option.map f`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press,
  2006, §1.5.
* The statements and proofs follow `ArithmeticHeights/Affine.lean` of `rwst/Subspace-Theorems`
  (commit `e443c24`, Apache 2.0), restated against Mathlib's height API.
-/

public section

open Real

namespace Height

open AdmissibleAbsValues

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι ι' : Type*}

/-- The **affine height** of a tuple `x : ι → K`: the projective height `Height.mulHeight` of
the tuple with a coordinate `1` appended.

Unlike `Height.mulHeight` it is not invariant under scaling
(`Height.exists_mulHeightAff_smul_ne`); it dominates the projective height
(`Height.mulHeight_le_mulHeightAff`) and the height of every coordinate
(`Height.mulHeight₁_le_mulHeightAff`). -/
noncomputable def mulHeightAff (x : ι → K) : ℝ :=
  mulHeight fun o : Option ι ↦ o.elim 1 x

/-- The **affine logarithmic height** of a tuple, the logarithm of `Height.mulHeightAff`. -/
noncomputable def logHeightAff (x : ι → K) : ℝ :=
  log (mulHeightAff x)

lemma mulHeightAff_def (x : ι → K) :
    mulHeightAff x = mulHeight fun o : Option ι ↦ o.elim 1 x :=
  (rfl)

lemma logHeightAff_eq_log_mulHeightAff (x : ι → K) : logHeightAff x = log (mulHeightAff x) :=
  (rfl)

/-- The affine height does not change under a bijective re-indexing. -/
lemma mulHeightAff_comp_equiv (e : ι ≃ ι') (x : ι' → K) :
    mulHeightAff (x ∘ e) = mulHeightAff x := by
  have h : (fun o : Option ι ↦ o.elim 1 (x ∘ e)) =
      (fun o : Option ι' ↦ o.elim 1 x) ∘ Equiv.optionCongr e := by
    funext o
    cases o <;> rfl
  rw [mulHeightAff_def, mulHeightAff_def, h, mulHeight_comp_equiv]

/-- The logarithmic form of `Height.mulHeightAff_comp_equiv`. -/
lemma logHeightAff_comp_equiv (e : ι ≃ ι') (x : ι' → K) :
    logHeightAff (x ∘ e) = logHeightAff x := by
  rw [logHeightAff_eq_log_mulHeightAff, logHeightAff_eq_log_mulHeightAff,
    mulHeightAff_comp_equiv]

section Finite

variable [Finite ι] [Finite ι']

/-- The affine height as a product of local factors: at each place `v` the factor is
`max (⨆ i, v (x i)) 1`, the tuple analogue of the local factor `max (v x) 1` of
`Height.mulHeight₁`. -/
lemma mulHeightAff_eq (x : ι → K) :
    mulHeightAff x = (archAbsVal.map fun v ↦ max (⨆ i, v (x i)) 1).prod *
      ∏ᶠ v : nonarchAbsVal, max (⨆ i, v.val (x i)) 1 := by
  -- At each place, the supremum over the appended tuple is `max (⨆ i, v (x i)) 1`.
  have key (v : AbsoluteValue K ℝ) : ⨆ o : Option ι, v (o.elim 1 x) = max (⨆ i, v (x i)) 1 := by
    refine le_antisymm (ciSup_le fun o ↦ ?_) (max_le ?_ ?_)
    · cases o with
      | none => simp
      | some i => exact le_max_of_le_left (Finite.le_ciSup_of_le i le_rfl)
    · exact Real.iSup_le (fun i ↦ Finite.le_ciSup_of_le (some i) le_rfl)
        (Real.iSup_nonneg_of_nonnegHomClass v _)
    · exact Finite.le_ciSup_of_le none (by simp)
  have hx : (fun o : Option ι ↦ o.elim 1 x) ≠ 0 := fun h ↦ one_ne_zero (congrFun h none)
  simp only [mulHeightAff_def, mulHeight_eq hx, key]

lemma one_le_mulHeightAff (x : ι → K) : 1 ≤ mulHeightAff x :=
  one_le_mulHeight _

lemma mulHeightAff_pos (x : ι → K) : 0 < mulHeightAff x :=
  mulHeight_pos _

lemma mulHeightAff_ne_zero (x : ι → K) : mulHeightAff x ≠ 0 :=
  mulHeight_ne_zero _

lemma logHeightAff_nonneg (x : ι → K) : 0 ≤ logHeightAff x :=
  logHeight_nonneg _

/-- The projective height of a tuple is at most its affine height. -/
lemma mulHeight_le_mulHeightAff (x : ι → K) : mulHeight x ≤ mulHeightAff x :=
  mulHeight_comp_le some fun o : Option ι ↦ o.elim 1 x

/-- The logarithmic form of `Height.mulHeight_le_mulHeightAff`. -/
lemma logHeight_le_logHeightAff (x : ι → K) : logHeight x ≤ logHeightAff x :=
  log_le_log (mulHeight_pos _) (mulHeight_le_mulHeightAff x)

/-- The affine height of `x ∘ f` is at most that of `x`, for any re-indexing `f`. -/
lemma mulHeightAff_comp_le (f : ι → ι') (x : ι' → K) :
    mulHeightAff (x ∘ f) ≤ mulHeightAff x := by
  have h : (fun o : Option ι ↦ o.elim 1 (x ∘ f)) =
      (fun o : Option ι' ↦ o.elim 1 x) ∘ Option.map f := by
    funext o
    cases o <;> rfl
  rw [mulHeightAff_def, mulHeightAff_def, h]
  exact mulHeight_comp_le _ _

/-- The logarithmic form of `Height.mulHeightAff_comp_le`. -/
lemma logHeightAff_comp_le (f : ι → ι') (x : ι' → K) :
    logHeightAff (x ∘ f) ≤ logHeightAff x :=
  log_le_log (mulHeightAff_pos _) (mulHeightAff_comp_le f x)

/-- The zero tuple has affine height `1`. -/
@[simp]
lemma mulHeightAff_zero : mulHeightAff (0 : ι → K) = 1 := by
  simp [mulHeightAff_eq]

@[simp]
lemma logHeightAff_zero : logHeightAff (0 : ι → K) = 0 := by
  simp [logHeightAff_eq_log_mulHeightAff]

end Finite

/-- On a one-element tuple the affine height is the height `Height.mulHeight₁` of the unique
coordinate. -/
lemma mulHeightAff_unique [Unique ι] (x : ι → K) : mulHeightAff x = mulHeight₁ (x default) := by
  simp [mulHeightAff_eq, mulHeight₁_eq]

/-- The logarithmic form of `Height.mulHeightAff_unique`. -/
lemma logHeightAff_unique [Unique ι] (x : ι → K) : logHeightAff x = logHeight₁ (x default) := by
  rw [logHeightAff_eq_log_mulHeightAff, logHeight₁_eq_log_mulHeight₁, mulHeightAff_unique]

/-- The affine height of `![x]` is `Height.mulHeight₁ x`. This is the check that the appended
coordinate is the right one: appending another constant, or normalizing by a degree, would break
it. -/
@[simp]
lemma mulHeightAff_fin_one (x : K) : mulHeightAff ![x] = mulHeight₁ x :=
  mulHeightAff_unique _

/-- The logarithmic form of `Height.mulHeightAff_fin_one`. -/
@[simp]
lemma logHeightAff_fin_one (x : K) : logHeightAff ![x] = logHeight₁ x :=
  logHeightAff_unique _

/-- The height of each coordinate is at most the affine height of the tuple. The analogous
bound for `Height.mulHeight` is false, since the projective height is invariant under scaling. -/
lemma mulHeight₁_le_mulHeightAff [Finite ι] (x : ι → K) (i : ι) :
    mulHeight₁ (x i) ≤ mulHeightAff x := by
  simpa [mulHeightAff_unique] using mulHeightAff_comp_le (fun _ : Unit ↦ i) x

/-- The logarithmic form of `Height.mulHeight₁_le_mulHeightAff`. -/
lemma logHeight₁_le_logHeightAff [Finite ι] (x : ι → K) (i : ι) :
    logHeight₁ (x i) ≤ logHeightAff x :=
  log_le_log (mulHeight₁_pos _) (mulHeight₁_le_mulHeightAff x i)

/-- **The affine height is not invariant under scaling.** Over `ℚ`, doubling the tuple `![1]`
changes its affine height from `1` to `2`, while the projective height of every tuple is
unchanged by scaling (`Height.mulHeight_smul_eq_mulHeight`). -/
theorem exists_mulHeightAff_smul_ne :
    ∃ (c : ℚ) (x : Fin 1 → ℚ), c ≠ 0 ∧ mulHeightAff (c • x) ≠ mulHeightAff x := by
  refine ⟨2, ![1], two_ne_zero, ?_⟩
  have h2 : mulHeight₁ (2 : ℚ) = 2 := by exact_mod_cast Rat.mulHeight₁_natCast 2
  simp [Matrix.smul_cons, h2]

/-! ### Examples -/

/-- Over `ℚ`, the tuples `![1]` and `![2]` have affine heights `1` and `2` but the same
projective height `1`. -/
example :
    mulHeightAff (![1] : Fin 1 → ℚ) = 1 ∧ mulHeightAff (![2] : Fin 1 → ℚ) = 2 ∧
      mulHeight (![1] : Fin 1 → ℚ) = 1 ∧ mulHeight (![2] : Fin 1 → ℚ) = 1 := by
  have h2 : mulHeight₁ (2 : ℚ) = 2 := by exact_mod_cast Rat.mulHeight₁_natCast 2
  simp [h2]

end Height
