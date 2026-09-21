/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.Sum
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Renaming the variables of a multivariate power series

Gaps in Mathlib's `rename` API, in three groups. The first compares a renaming with another
operation on the same series — substitution, evaluation, or reading a single-variable
coefficient — together with one consequence of those comparisons: that reindexing a two-variable
series along `unitSumUnitEquivFinTwo` carries an associativity identity with it. The second says
where a renamed series *vanishes*: at every exponent that is nonzero at a variable outside the
image of the renaming. The third is about two renamings at once — along embeddings with disjoint
images, a common value forces both series to be the same constant.

Substituting after renaming is the substitution along the renamed index, and evaluating after
renaming is the evaluation at the reindexed family: Mathlib has all these operations and the law
that lets them be compared — `rename_eq_subst`, which says a renaming *is* the substitution
sending each variable to a variable — but not the comparisons themselves, which is what a caller
reindexing a series needs.

Reading the coefficient of a single-variable monomial through a renaming along an embedding is
likewise available only through `coeff_embDomain_rename`, which speaks about `Finsupp.embDomain`;
at one variable raised to an arbitrary power the `single (e i) n` spelling is the more usable one.

Associativity is where the two spellings of a two-variable series genuinely diverge: the named
form substitutes an already-substituted series through `pairSubstitution`, the `Fin 2` form
through a `Matrix.cons` family over `Fin 3`. Transporting the identity therefore means
reindexing the three-variable ambient ring as well, along `unitSumUnitSumUnitEquivFinThree`.

## Main results

* `MvPowerSeries.subst_rename`: substituting into `rename e p` reindexes the family, i.e. it is
  substituting `g ∘ e` into `p`.
* `MvPowerSeries.coeff_single_rename`: the coefficient of `rename e p` at the single-variable
  monomial `single (e i) n` is the coefficient of `p` at `single i n`, for any exponent `n`.
* `MvPowerSeries.aeval_rename`: evaluating `rename e p` at a family reindexes the family, i.e. it
  is evaluating `p` at that family precomposed with `e`.
* `MvPowerSeries.rename_unitSumUnitEquivFinTwo_assoc`: reindexing a two-variable associative
  series from `Unit ⊕ Unit` to `Fin 2` preserves its associativity identity.
* `MvPowerSeries.coeff_rename_eq_zero_of_apply_ne_zero`: a renamed series vanishes at every
  exponent that is nonzero at a variable outside the image of the renaming.
* `MvPowerSeries.eq_C_of_rename_eq_rename` and
  `MvPowerSeries.right_eq_C_of_rename_eq_rename`: renamings along embeddings with disjoint images
  agree only when both series are the same constant.

## Provenance

No external source. The first three statements are gaps in Mathlib's `MvPowerSeries` API and each
proof is a few steps of that same API; the fourth is the reindexing they were extracted for, and
its proof rewrites both sides of the identity through the three-variable renaming. The vanishing
and disjointness lemmas are likewise gaps in that API. All of them are recorded here rather than
inside their callers because they carry no content beyond `rename`.
-/

public section

namespace MvPowerSeries

open Filter Finsupp

variable {σ τ υ R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- **A single-variable monomial's coefficient survives a renaming along an embedding**, for any
exponent `n`. Mathlib's `coeff_embDomain_rename` states this through `Finsupp.embDomain`; at one
variable the `single (e i) n` spelling is the one a caller meets. -/
@[simp]
theorem coeff_single_rename (e : σ ↪ τ) (p : MvPowerSeries σ R) (i : σ) (n : ℕ) :
    coeff (single (e i) n) (rename e p) = coeff (single i n) p := by
  rw [← embDomain_single, coeff_embDomain_rename]

/-- **A renamed series has no exponent outside the image of `e`**: if `ν` is nonzero at a variable
`j` that `e` misses, then `ν` is not in the range of `Finsupp.mapDomain e`, so the coefficient
vanishes. This is Mathlib's `MvPowerSeries.coeff_rename_eq_zero` with the witness of
non-membership supplied by a single variable. -/
theorem coeff_rename_eq_zero_of_apply_ne_zero (e : σ ↪ τ) (p : MvPowerSeries σ R) {ν : τ →₀ ℕ}
    {j : τ} (hj : j ∉ Set.range e) (hν : ν j ≠ 0) : coeff ν (rename e p) = 0 :=
  coeff_rename_eq_zero _ _ fun ⟨s, hs⟩ ↦ hν (hs ▸ mapDomain_of_notMem_range s j hj)

section Disjoint

variable {σ₁ σ₂ : Type*} {e₁ : σ₁ ↪ τ} {e₂ : σ₂ ↪ τ} {a : MvPowerSeries σ₁ R}
  {b : MvPowerSeries σ₂ R}

/-- **Renamings along embeddings with disjoint images agree only on constants**: if
`rename e₁ a = rename e₂ b` and no `e₁ i` is an `e₂ j`, then `a` is the constant series at its own
constant coefficient. `MvPowerSeries.right_eq_C_of_rename_eq_rename` is the companion for `b`,
which is the constant series at the *same* constant. The two series need not be indexed by the
same type: only the images of `e₁` and `e₂` inside `τ` have to be disjoint. -/
theorem eq_C_of_rename_eq_rename (hdisj : ∀ i j, e₁ i ≠ e₂ j) (h : rename e₁ a = rename e₂ b) :
    a = C (constantCoeff a) := by
  classical
  ext s
  rw [coeff_C]
  split_ifs with hs
  · rw [hs, coeff_zero_eq_constantCoeff_apply]
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hs
  rw [← coeff_embDomain_rename e₁, h, coeff_rename_eq_zero_of_apply_ne_zero e₂ b
    (j := e₁ i) (fun ⟨j, hj⟩ ↦ hdisj i j hj.symm) (by simpa using hi)]

/-- **Both sides are the same constant**: the companion of
`MvPowerSeries.eq_C_of_rename_eq_rename` for `b`. Reading the constant coefficient through the
renamings identifies the two constants, so the two series are equal as well. -/
theorem right_eq_C_of_rename_eq_rename (hdisj : ∀ i j, e₁ i ≠ e₂ j)
    (h : rename e₁ a = rename e₂ b) : b = C (constantCoeff a) := by
  have hconst : constantCoeff b = constantCoeff a := by
    rw [← constantCoeff_rename (f := e₂) b, ← h, constantCoeff_rename]
  rw [← hconst]
  exact eq_C_of_rename_eq_rename (fun i j ↦ (hdisj j i).symm) h.symm

end Disjoint

end CommSemiring

section CommRing

variable [CommRing R]

private theorem rename_unitSumUnitEquivFinTwo_assoc_left_family
    (p : MvPowerSeries (Unit ⊕ Unit) R) :
    (![subst (![X 0, X 1] ∘ unitSumUnitEquivFinTwo) p, X 2] ∘
        unitSumUnitEquivFinTwo) =
      (fun s ↦ subst (X (R := R) ∘ unitSumUnitSumUnitEquivFinThree)
        (pairSubstitution (subst
            (pairSubstitution (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R)
              (X (Sum.inr (Sum.inl ())))) p) (X (Sum.inr (Sum.inr ()))) s)) := by
  have h₀₁ : HasSubst
      (pairSubstitution (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R)
        (X (Sum.inr (Sum.inl ())))) := hasSubst_pair (by simp) (by simp)
  have hrename : HasSubst
      (X (R := R) ∘ unitSumUnitSumUnitEquivFinThree) := HasSubst.X_comp _
  funext s
  rcases s with u | u <;> cases u
  · simp only [Function.comp_apply, unitSumUnitEquivFinTwo_inl, Matrix.cons_val_zero,
      Sum.elim_inl]
    rw [subst_comp_subst_apply h₀₁ hrename]
    congr 1
    funext t
    rcases t with v | v <;> cases v
    · simp [subst_X hrename]
    · simp [subst_X hrename]
  · simp [subst_X hrename]

private theorem rename_unitSumUnitEquivFinTwo_assoc_right_family
    (p : MvPowerSeries (Unit ⊕ Unit) R) :
    (![X 0, subst (![X 1, X 2] ∘ unitSumUnitEquivFinTwo) p] ∘
        unitSumUnitEquivFinTwo) =
      (fun s ↦ subst (X (R := R) ∘ unitSumUnitSumUnitEquivFinThree)
        (pairSubstitution (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R) (subst
            (pairSubstitution (X (Sum.inr (Sum.inl ()))) (X (Sum.inr (Sum.inr ())))) p) s)) := by
  have h₁₂ : HasSubst
      (pairSubstitution (X (Sum.inr (Sum.inl ())) :
        MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R) (X (Sum.inr (Sum.inr ())))) :=
    hasSubst_pair (by simp) (by simp)
  have hrename : HasSubst
      (X (R := R) ∘ unitSumUnitSumUnitEquivFinThree) := HasSubst.X_comp _
  funext s
  rcases s with u | u <;> cases u
  · simp [subst_X hrename]
  · simp only [Function.comp_apply, unitSumUnitEquivFinTwo_inr, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Sum.elim_inr]
    rw [subst_comp_subst_apply h₁₂ hrename]
    congr 1
    funext t
    rcases t with v | v <;> cases v
    · simp [subst_X hrename]
    · simp [subst_X hrename]

/-- **Substituting into a renamed series reindexes the family**: `rename e p` followed by
substituting `g` is `p` with `g ∘ e` substituted.

Both hypotheses are the ones the two operations already carry: `rename` needs `e` to have finite
fibres (`TendstoCofinite`) for the renamed coefficients to be well defined, and `subst` needs
`HasSubst g`. Nothing is assumed about `e` beyond that — in particular it need not be injective,
since a collision merely substitutes the same series for two variables. -/
theorem subst_rename (e : σ → τ) [TendstoCofinite e] (p : MvPowerSeries σ R)
    {g : τ → MvPowerSeries υ R} (hg : HasSubst g) :
    (rename e p).subst g = p.subst (g ∘ e) := by
  rw [rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hg]
  simp [subst_X hg, Function.comp_def]

/-- Reindexing an associative two-variable series from `Unit ⊕ Unit` to `Fin 2` preserves
associativity in Mathlib's three-variable convention.

The source identity uses the named left, middle, and right variables supplied by the nested sum;
the target is exactly the identity expected by `FormalGroup.assoc`. -/
theorem rename_unitSumUnitEquivFinTwo_assoc (p : MvPowerSeries (Unit ⊕ Unit) R)
    (hp : constantCoeff p = 0)
    (hassoc :
      subst (pairSubstitution
          (subst (pairSubstitution (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R)
            (X (Sum.inr (Sum.inl ())))) p)
          (X (Sum.inr (Sum.inr ())))) p =
        subst (pairSubstitution (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R)
          (subst (pairSubstitution (X (Sum.inr (Sum.inl ())))
            (X (Sum.inr (Sum.inr ())))) p)) p) :
    subst ![subst ![(X 0 : MvPowerSeries (Fin 3) R), X 1]
        (rename unitSumUnitEquivFinTwo p), X 2]
        (rename unitSumUnitEquivFinTwo p) =
      subst ![(X 0 : MvPowerSeries (Fin 3) R),
        subst ![X 1, X 2] (rename unitSumUnitEquivFinTwo p)]
        (rename unitSumUnitEquivFinTwo p) := by
  have hzero : constantCoeff (rename unitSumUnitEquivFinTwo p) = 0 := by simp [hp]
  obtain hleft := HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 hzero
  obtain hright := HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 hzero
  rw [subst_rename unitSumUnitEquivFinTwo _ hleft,
    subst_rename unitSumUnitEquivFinTwo _ hright]
  rw [subst_rename unitSumUnitEquivFinTwo _ HasSubst.X_X,
    subst_rename unitSumUnitEquivFinTwo _ HasSubst.X_X]
  have h₀₁ : HasSubst
      (pairSubstitution (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R)
        (X (Sum.inr (Sum.inl ())))) := hasSubst_pair (by simp) (by simp)
  have h₁₂ : HasSubst
      (pairSubstitution (X (Sum.inr (Sum.inl ())) :
        MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R) (X (Sum.inr (Sum.inr ())))) :=
    hasSubst_pair (by simp) (by simp)
  have hz₀₁ : constantCoeff (subst
      (pairSubstitution (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R)
        (X (Sum.inr (Sum.inl ())))) p) = 0 :=
    constantCoeff_subst_eq_zero h₀₁ (by rintro (u | u) <;> simp) hp
  have hz₁₂ : constantCoeff (subst
      (pairSubstitution (X (Sum.inr (Sum.inl ())) :
        MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R) (X (Sum.inr (Sum.inr ())))) p) = 0 :=
    constantCoeff_subst_eq_zero h₁₂ (by rintro (u | u) <;> simp) hp
  have hsourceLeft : HasSubst
      (pairSubstitution (subst
          (pairSubstitution (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R)
            (X (Sum.inr (Sum.inl ())))) p) (X (Sum.inr (Sum.inr ())))) :=
              hasSubst_pair hz₀₁ (by simp)
  have hsourceRight : HasSubst
      (pairSubstitution (X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) R) (subst
          (pairSubstitution (X (Sum.inr (Sum.inl ()))) (X (Sum.inr (Sum.inr ())))) p)) :=
            hasSubst_pair (by simp) hz₁₂
  have hrename : HasSubst
      (X (R := R) ∘ unitSumUnitSumUnitEquivFinThree) := HasSubst.X_comp _
  have h := congrArg (rename unitSumUnitSumUnitEquivFinThree) hassoc
  simp only [rename_eq_subst] at h
  rw [subst_comp_subst_apply hsourceLeft hrename,
    subst_comp_subst_apply hsourceRight hrename] at h
  rw [rename_unitSumUnitEquivFinTwo_assoc_left_family p,
    rename_unitSumUnitEquivFinTwo_assoc_right_family p]
  exact h

end CommRing

section Eval

open WithPiTopology

variable [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalSemiring R]
variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [IsTopologicalRing S]
  [IsLinearTopology S S] [T2Space S] [CompleteSpace S] [Algebra R S] [ContinuousSMul R S]

/-- **Evaluating a renamed series reindexes the family**: evaluating `rename e p` at `a` is
evaluating `p` at `a` precomposed with `e`. This is the evaluation counterpart of `subst_rename`,
and Mathlib has neither.

The reindexed family is a separate argument `b` together with the pointwise equation
`b s = a (e s)`, rather than the composite `a ∘ e` itself, because `aeval` carries its family in
the type of its `HasEval` argument: a caller who knows the reindexed family in a simplified form
cannot rewrite it under `aeval` afterwards, and supplying it here is the only way to state the
evaluation it actually wants. -/
theorem aeval_rename (e : σ → τ) [TendstoCofinite e] {a : τ → S} {b : σ → S} (ha : HasEval a)
    (hab : ∀ s, b s = a (e s)) (p : MvPowerSeries σ R) :
    aeval ha (rename e p) = eval₂ (algebraMap R S) b p := by
  have hb : HasEval b := by
    rw [show b = a ∘ e from funext hab]
    exact ⟨fun s ↦ ha.hpow (e s), ha.tendsto_zero.comp (TendstoCofinite.tendsto_cofinite e)⟩
  have hfam : (fun s ↦ (aeval ha) ((X ∘ e) s : MvPowerSeries τ R)) = b := by
    funext s
    rw [coe_aeval, Function.comp_apply, eval₂_X, hab]
  have hb' : HasEval fun s ↦ (aeval ha) ((X ∘ e) s : MvPowerSeries τ R) := by
    rw [hfam]; exact hb
  rw [rename_eq_subst, aeval_subst (HasSubst.X_comp e) (continuous_aeval ha) hb' p]
  calc (aeval hb') p
      = eval₂ (algebraMap R S) (fun s ↦ (aeval ha) ((X ∘ e) s : MvPowerSeries τ R)) p :=
        congrFun (coe_aeval hb') p
    _ = eval₂ (algebraMap R S) b p := by rw [hfam]

end Eval

end MvPowerSeries
