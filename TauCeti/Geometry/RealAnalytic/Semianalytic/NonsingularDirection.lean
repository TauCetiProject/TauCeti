/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAnalytic.Semianalytic.Basic

/-!
# Nonsingular directions of semianalytic sets

A direction `v` is *singular* for a function `f` analytic at `x` if `f` vanishes identically on
the line through `x` in the direction `v`, near `x`: `f (x + ξ • v) = 0` for all small `ξ`. Along a
nonsingular direction the restriction of `f` to that line has a zero of finite order at `x`, so
Weierstrass preparation applies in the direction `v`.

Following Łojasiewicz, `v` is a *nonsingular direction* for a set `s` at `x`
(`TauCeti.IsNonsingularDirectionAt s v x`) if, near `x`, the set `s` is a finite Boolean combination
of zero sets and positivity sets of functions analytic at `x` for which `v` is not singular at `x`.
A set with a nonsingular direction at `x` is semianalytic at `x`. The direction `v` is nonsingular
for `s` (`TauCeti.IsNonsingularDirection s v`) if it is nonsingular for `s` at every point.

The vertical direction of a cylinder `E × (Unit → ℝ)` is used in Łojasiewicz's triangulation of
semianalytic sets: a bounded set for which it is nonsingular is partially semialgebraic in the
vertical coordinate (`TauCeti.IsNonsingularDirection.isPartiallySemialgebraic`).

## Main declarations

* `TauCeti.IsNonsingularDirectionAt s v x`: `v` is a nonsingular direction for `s` at `x`.
* `TauCeti.IsNonsingularDirection s v`: `v` is a nonsingular direction for `s` at every point.

## Main results

* `TauCeti.isSetAlgebra_setOf_isNonsingularDirectionAt`: the sets for which `v` is a nonsingular
  direction at `x` form an algebra of sets.
* `TauCeti.IsNonsingularDirectionAt.semianalyticAt`: such a set is semianalytic at `x`.

## References

S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di Pisa
(3) 18 (1964), 449–474, §2, Lemmas 3–5.
-/

public section

open Filter MeasureTheory Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The direction `v` is a *nonsingular direction* for the set `s` at `x` if, near `x`, the set `s`
agrees with a finite Boolean combination of zero sets `{y | f y = 0}` and positivity sets
`{y | 0 < f y}` of real functions `f` analytic at `x` which do not vanish identically on the line
`ξ ↦ x + ξ • v` near `ξ = 0`. -/
def IsNonsingularDirectionAt (s : Set E) (v x : E) : Prop :=
  ∃ t ∈ generateSetAlgebra
      ({t | ∃ f : E → ℝ, AnalyticAt ℝ f x ∧ (¬ ∀ᶠ ξ in 𝓝 (0 : ℝ), f (x + ξ • v) = 0) ∧
          t = {y | f y = 0}} ∪
        {t | ∃ f : E → ℝ, AnalyticAt ℝ f x ∧ (¬ ∀ᶠ ξ in 𝓝 (0 : ℝ), f (x + ξ • v) = 0) ∧
          t = {y | 0 < f y}}),
    s =ᶠ[𝓝 x] t

/-- The direction `v` is nonsingular for `s` at `x` if and only if, near `x`, the set `s` agrees
with a finite Boolean combination of zero sets and positivity sets of functions analytic at `x`
which do not vanish identically on the line through `x` in the direction `v`. -/
theorem isNonsingularDirectionAt_def {s : Set E} {v x : E} :
    IsNonsingularDirectionAt s v x ↔ ∃ t ∈ generateSetAlgebra
      ({t | ∃ f : E → ℝ, AnalyticAt ℝ f x ∧ (¬ ∀ᶠ ξ in 𝓝 (0 : ℝ), f (x + ξ • v) = 0) ∧
          t = {y | f y = 0}} ∪
        {t | ∃ f : E → ℝ, AnalyticAt ℝ f x ∧ (¬ ∀ᶠ ξ in 𝓝 (0 : ℝ), f (x + ξ • v) = 0) ∧
          t = {y | 0 < f y}}),
      s =ᶠ[𝓝 x] t :=
  Iff.rfl

/-- The direction `v` is nonsingular at `x` for the zero set of a function analytic at `x` which
does not vanish identically on the line through `x` in the direction `v`. -/
theorem _root_.AnalyticAt.isNonsingularDirectionAt_setOf_eq_zero {f : E → ℝ} {v x : E}
    (hf : AnalyticAt ℝ f x) (hv : ¬ ∀ᶠ ξ in 𝓝 (0 : ℝ), f (x + ξ • v) = 0) :
    IsNonsingularDirectionAt {y | f y = 0} v x :=
  ⟨_, self_subset_generateSetAlgebra (Or.inl ⟨f, hf, hv, rfl⟩), EventuallyEqSet.rfl⟩

/-- The direction `v` is nonsingular at `x` for the positivity set of a function analytic at `x`
which does not vanish identically on the line through `x` in the direction `v`. -/
theorem _root_.AnalyticAt.isNonsingularDirectionAt_setOf_pos {f : E → ℝ} {v x : E}
    (hf : AnalyticAt ℝ f x) (hv : ¬ ∀ᶠ ξ in 𝓝 (0 : ℝ), f (x + ξ • v) = 0) :
    IsNonsingularDirectionAt {y | 0 < f y} v x :=
  ⟨_, self_subset_generateSetAlgebra (Or.inr ⟨f, hf, hv, rfl⟩), EventuallyEqSet.rfl⟩

/-- Whether `v` is a nonsingular direction for `s` at `x` only depends on the germ of `s` at
`x`. -/
theorem IsNonsingularDirectionAt.congr {s s' : Set E} {v x : E}
    (hs : IsNonsingularDirectionAt s v x) (h : s =ᶠ[𝓝 x] s') : IsNonsingularDirectionAt s' v x :=
  let ⟨t, ht, hst⟩ := hs
  ⟨t, ht, h.symm.trans hst⟩

/-- The sets for which `v` is a nonsingular direction at `x` form an algebra of sets. -/
theorem isSetAlgebra_setOf_isNonsingularDirectionAt (v x : E) :
    IsSetAlgebra {s : Set E | IsNonsingularDirectionAt s v x} where
  empty_mem := ⟨∅, isSetAlgebra_generateSetAlgebra.empty_mem, EventuallyEqSet.rfl⟩
  compl_mem := fun _ ⟨t, ht, hst⟩ =>
    ⟨tᶜ, isSetAlgebra_generateSetAlgebra.compl_mem ht, hst.compl⟩
  union_mem := fun _ _ ⟨t, ht, hst⟩ ⟨t', ht', hst'⟩ =>
    ⟨t ∪ t', isSetAlgebra_generateSetAlgebra.union_mem ht ht', hst.union hst'⟩

section IsNonsingularDirectionAt

variable {s s' : Set E} {v x : E}

/-- Every direction is nonsingular for the empty set. -/
@[simp]
theorem isNonsingularDirectionAt_empty : IsNonsingularDirectionAt (∅ : Set E) v x :=
  (isSetAlgebra_setOf_isNonsingularDirectionAt v x).empty_mem

/-- Every direction is nonsingular for the whole space. -/
@[simp]
theorem isNonsingularDirectionAt_univ : IsNonsingularDirectionAt (univ : Set E) v x :=
  (isSetAlgebra_setOf_isNonsingularDirectionAt v x).univ_mem

/-- A nonsingular direction for a set is nonsingular for its complement. -/
theorem IsNonsingularDirectionAt.compl (hs : IsNonsingularDirectionAt s v x) :
    IsNonsingularDirectionAt sᶜ v x :=
  (isSetAlgebra_setOf_isNonsingularDirectionAt v x).compl_mem hs

/-- A direction is nonsingular for the complement of a set if and only if it is nonsingular for
the set. -/
@[simp]
theorem isNonsingularDirectionAt_compl_iff :
    IsNonsingularDirectionAt sᶜ v x ↔ IsNonsingularDirectionAt s v x :=
  ⟨fun hs => compl_compl s ▸ hs.compl, IsNonsingularDirectionAt.compl⟩

/-- A direction nonsingular for two sets is nonsingular for their union. -/
theorem IsNonsingularDirectionAt.union (hs : IsNonsingularDirectionAt s v x)
    (hs' : IsNonsingularDirectionAt s' v x) : IsNonsingularDirectionAt (s ∪ s') v x :=
  (isSetAlgebra_setOf_isNonsingularDirectionAt v x).union_mem hs hs'

/-- A direction nonsingular for two sets is nonsingular for their intersection. -/
theorem IsNonsingularDirectionAt.inter (hs : IsNonsingularDirectionAt s v x)
    (hs' : IsNonsingularDirectionAt s' v x) : IsNonsingularDirectionAt (s ∩ s') v x :=
  (isSetAlgebra_setOf_isNonsingularDirectionAt v x).inter_mem hs hs'

/-- A set with a nonsingular direction at `x` is semianalytic at `x`. -/
theorem IsNonsingularDirectionAt.semianalyticAt (hs : IsNonsingularDirectionAt s v x) :
    SemianalyticAt s x := by
  obtain ⟨t, ht, hst⟩ := hs
  refine SemianalyticAt.congr ?_ hst.symm
  refine (isSetAlgebra_setOf_semianalyticAt x).generateSetAlgebra_subset ?_ ht
  rintro _ (⟨f, hf, -, rfl⟩ | ⟨f, hf, -, rfl⟩)
  exacts [hf.semianalyticAt_setOf_eq_zero, hf.semianalyticAt_setOf_pos]

end IsNonsingularDirectionAt

/-- The direction `v` is a *nonsingular direction* for the set `s` if it is a nonsingular direction
for `s` at every point of `E`, including the points outside `s`. -/
def IsNonsingularDirection (s : Set E) (v : E) : Prop :=
  ∀ x, IsNonsingularDirectionAt s v x

/-- The direction `v` is nonsingular for `s` if and only if it is nonsingular for `s` at every
point. -/
theorem isNonsingularDirection_iff {s : Set E} {v : E} :
    IsNonsingularDirection s v ↔ ∀ x, IsNonsingularDirectionAt s v x :=
  Iff.rfl

/-- The sets for which `v` is a nonsingular direction form an algebra of sets. -/
theorem isSetAlgebra_setOf_isNonsingularDirection (v : E) :
    IsSetAlgebra {s : Set E | IsNonsingularDirection s v} where
  empty_mem _ := isNonsingularDirectionAt_empty
  compl_mem _ hs x := (hs x).compl
  union_mem _ _ hs hs' x := (hs x).union (hs' x)

/-- A set with a nonsingular direction is semianalytic. -/
theorem IsNonsingularDirection.isSemianalytic {s : Set E} {v : E}
    (hs : IsNonsingularDirection s v) : IsSemianalytic s :=
  isSemianalytic_iff.2 fun x => (hs x).semianalyticAt

end TauCeti
