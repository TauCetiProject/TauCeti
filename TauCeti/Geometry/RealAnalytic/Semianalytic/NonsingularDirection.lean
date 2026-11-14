/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAnalytic.Semianalytic.Basic
import TauCeti.Analysis.Analytic.SingularDirection

/-!
# Nonsingular directions of semianalytic sets

A direction `v` is *singular* for a function `f` analytic at `x` if `f` vanishes identically on
the line through `x` in the direction `v`, near `x`: `f (x + ξ • v) = 0` for all small `ξ`. Along a
nonsingular direction the restriction of `f` to that line has a zero of finite order at `x`, so
Weierstrass preparation applies in the direction `v`.

Following Łojasiewicz, `v` is a *nonsingular direction* for a set `s` at `x`
(`TauCeti.IsNonsingularDirectionAt s v x`) if, near `x`, the set `s` is a finite Boolean combination
of zero sets and positivity sets of functions analytic at `x` for which `v` is not singular at `x`.
A set with a nonsingular direction at `x` is semianalytic at `x`. Conversely, at any point `x` where
`s` is semianalytic, the directions nonsingular for `s` at `x` have dense interior
(`TauCeti.SemianalyticAt.dense_interior_setOf_isNonsingularDirectionAt`), so every finite family of
germs semianalytic at `x` shares a dense open set of nonsingular directions and, in any nontrivial
space, a nonzero one (`TauCeti.exists_ne_zero_forall_isNonsingularDirectionAt`). The direction `v`
is nonsingular for `s` (`TauCeti.IsNonsingularDirection s v`) if it is nonsingular for `s` at every
point.

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
* `TauCeti.SemianalyticAt.dense_interior_setOf_isNonsingularDirectionAt`,
  `TauCeti.SemianalyticAt.exists_ne_zero_isNonsingularDirectionAt`: at any point where `s` is
  semianalytic, its nonsingular directions have dense interior, hence include a nonzero direction
  when `E` is nontrivial.
* `TauCeti.dense_interior_setOf_forall_isNonsingularDirectionAt`,
  `TauCeti.exists_ne_zero_forall_isNonsingularDirectionAt`: common nonsingular directions for finite
  families of semianalytic germs.

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

/-- The direction `v` is nonsingular at `x` for the prescribed-sign set `{y | sign (f y) = ε}` of a
function analytic at `x` which does not vanish identically on the line through `x` in the direction
`v`. -/
theorem _root_.AnalyticAt.isNonsingularDirectionAt_setOf_sign_eq {f : E → ℝ} {v x : E}
    (hf : AnalyticAt ℝ f x) (hv : ¬ ∀ᶠ ξ in 𝓝 (0 : ℝ), f (x + ξ • v) = 0) (ε : SignType) :
    IsNonsingularDirectionAt {y | SignType.sign (f y) = ε} v x := by
  rcases ε with _ | _ | _
  · simpa only [SignType.zero_eq_zero, sign_eq_zero_iff] using
      hf.isNonsingularDirectionAt_setOf_eq_zero hv
  · simpa only [SignType.neg_eq_neg_one, sign_eq_neg_one_iff, Pi.neg_apply, neg_pos] using
      hf.neg.isNonsingularDirectionAt_setOf_pos (by simpa using hv)
  · simpa only [SignType.pos_eq_one, sign_eq_one_iff] using
      hf.isNonsingularDirectionAt_setOf_pos hv

/-- Rescaling a direction by a nonzero scalar preserves `IsNonsingularDirectionAt`. -/
theorem isNonsingularDirectionAt_smul_iff {s : Set E} {v x : E} {c : ℝ} (hc : c ≠ 0) :
    IsNonsingularDirectionAt s (c • v) x ↔ IsNonsingularDirectionAt s v x := by
  simp only [isNonsingularDirectionAt_def, eventually_apply_add_smul_smul_eq_zero_iff hc]

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

/-- At any point `x` where `s` is semianalytic, the directions nonsingular for `s` at `x` have
dense interior. -/
theorem SemianalyticAt.dense_interior_setOf_isNonsingularDirectionAt (hs : SemianalyticAt s x) :
    Dense (interior {v | IsNonsingularDirectionAt s v x}) := by
  classical
  obtain ⟨U, hU, t, ht, hst⟩ := semianalyticAt_def.1 hs
  obtain ⟨m, f, hf, Φ, rfl⟩ := ht.exists_eq_setOf_sign
  let ι₁ := {i : Fin m // ¬ f i =ᶠ[𝓝 x] 0}
  let Ψ : (ι₁ → SignType) → Prop :=
    fun σ ↦ Φ fun i ↦ if hi : f i =ᶠ[𝓝 x] 0 then 0 else σ ⟨i, hi⟩
  -- Discard the germs vanishing near `x`, whose sign is locally `0`.
  have hgerm : {y | Ψ fun j : ι₁ ↦ SignType.sign (f j.1 y)} =ᶠ[𝓝 x] s := by
    have hzero : ∀ᶠ y in 𝓝 x, ∀ i : Fin m, f i =ᶠ[𝓝 x] 0 → f i y = 0 :=
      eventually_all.2 fun i ↦ by
        by_cases hi : f i =ᶠ[𝓝 x] 0
        exacts [hi.mono fun _ hy _ ↦ hy, .of_forall fun _ h ↦ (hi h).elim]
    refine eventuallyEqSet_iff.2 ?_
    filter_upwards [hU, hzero] with y hyU hy0
    have hmem := Set.ext_iff.1 hst y
    simp only [mem_inter_iff, hyU, and_true, mem_ofPred_eq] at hmem ⊢
    rw [hmem]
    refine iff_of_eq (congrArg Φ (funext fun i ↦ ?_))
    split_ifs with hi
    · simp [hy0 i hi]
    · rfl
  have hfx (j : ι₁) : AnalyticAt ℝ (f j.1) x := hf j.1 x (mem_of_mem_nhds hU)
  set W := {v : E | ∀ j : ι₁, ¬ ∀ᶠ ξ in 𝓝 (0 : ℝ), f j.1 (x + ξ • v) = 0}
  have hWsub : W ⊆ {v | IsNonsingularDirectionAt s v x} := by
    intro v hv
    refine IsNonsingularDirectionAt.congr ?_ hgerm
    rw [setOf_apply_eq_biUnion_iInter (fun (j : ι₁) (y : E) ↦ SignType.sign (f j.1 y))]
    have halg := isSetAlgebra_setOf_isNonsingularDirectionAt v x
    simpa [mem_ofPred_eq] using halg.biUnion_mem (toFinite (ofPred Ψ)).toFinset fun σ _ ↦
      halg.biInter_mem Finset.univ fun j _ ↦
        (hfx j).isNonsingularDirectionAt_setOf_sign_eq (hv j) (σ j)
  exact (dense_setOf_forall_not_eventually_apply_add_smul_eq_zero hfx fun j ↦ j.2).mono
    (interior_maximal hWsub (isOpen_setOf_forall_not_eventually_apply_add_smul_eq_zero hfx))

/-- At any point `x` where `s` is semianalytic, the directions nonsingular for `s` at `x` are
dense in `E`. -/
theorem SemianalyticAt.dense_setOf_isNonsingularDirectionAt (hs : SemianalyticAt s x) :
    Dense {v | IsNonsingularDirectionAt s v x} :=
  hs.dense_interior_setOf_isNonsingularDirectionAt.mono interior_subset

/-- Every finite family of germs semianalytic at `x` shares a set of nonsingular directions at `x`
with dense interior. -/
theorem dense_interior_setOf_forall_isNonsingularDirectionAt {ι : Type*} [Finite ι]
    {s : ι → Set E} (hs : ∀ i, SemianalyticAt (s i) x) :
    Dense (interior {v | ∀ i, IsNonsingularDirectionAt (s i) v x}) := by
  classical
  cases nonempty_fintype ι
  suffices ∀ I : Finset ι,
      Dense (interior {v | ∀ i ∈ I, IsNonsingularDirectionAt (s i) v x}) by
    simpa using this Finset.univ
  intro I
  induction I using Finset.induction_on with
  | empty => simp [dense_univ]
  | insert i I _ ih =>
    have heq : {v | ∀ j ∈ insert i I, IsNonsingularDirectionAt (s j) v x} =
        {v | IsNonsingularDirectionAt (s i) v x} ∩
          {v | ∀ j ∈ I, IsNonsingularDirectionAt (s j) v x} := by
      ext v
      simp
    rw [heq, interior_inter]
    exact (hs i).dense_interior_setOf_isNonsingularDirectionAt.inter_of_isOpen_left ih
      isOpen_interior

/-- In a nontrivial real normed space, every finite family of germs semianalytic at `x` admits a
common nonzero nonsingular direction at `x`. -/
theorem exists_ne_zero_forall_isNonsingularDirectionAt [Nontrivial E] {ι : Type*} [Finite ι]
    {s : ι → Set E} (hs : ∀ i, SemianalyticAt (s i) x) :
    ∃ v ≠ 0, ∀ i, IsNonsingularDirectionAt (s i) v x := by
  obtain ⟨v, hv, hv0⟩ := (dense_interior_setOf_forall_isNonsingularDirectionAt hs).exists_mem_open
    isOpen_compl_singleton (Set.nonempty_compl_of_nontrivial 0)
  exact ⟨v, hv0, interior_subset hv⟩

/-- In a nontrivial real normed space, every germ semianalytic at `x` admits a nonzero nonsingular
direction at `x`. -/
theorem SemianalyticAt.exists_ne_zero_isNonsingularDirectionAt [Nontrivial E]
    (hs : SemianalyticAt s x) :
    ∃ v ≠ 0, IsNonsingularDirectionAt s v x := by
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_forall_isNonsingularDirectionAt fun _ : Unit ↦ hs
  exact ⟨v, hv0, hv ()⟩

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

/-- Rescaling a direction by a nonzero scalar preserves `IsNonsingularDirection`. -/
theorem isNonsingularDirection_smul_iff {s : Set E} {v : E} {c : ℝ} (hc : c ≠ 0) :
    IsNonsingularDirection s (c • v) ↔ IsNonsingularDirection s v :=
  forall_congr' fun _ ↦ isNonsingularDirectionAt_smul_iff hc

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
