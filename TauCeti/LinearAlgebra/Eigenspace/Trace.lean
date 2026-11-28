/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import TauCeti.LinearAlgebra.Eigenspace.Decomposition
import TauCeti.LinearAlgebra.LinearIndependent.MonoidHom
import TauCeti.LinearAlgebra.Matrix.Charpoly.Newton
import TauCeti.LinearAlgebra.Trace.Basic

/-!
# Traces along the generalized eigenspaces of an endomorphism

Let `f` and `X` be commuting endomorphisms of a finite-dimensional vector space `V`. Then `X`
preserves every generalized eigenspace `V_μ` of `f`, and `f` acts on `V_μ` as `μ` plus a nilpotent
endomorphism commuting with `X`, so the trace of `f ^ l * X` on `V_μ` is `μ ^ l` times the trace
of `X` there. Over an algebraically closed field the `V_μ` decompose `V`, and summing over them
gives

`tr (f ^ l * X) = ∑ μ, μ ^ l * tr (X|V_μ)`,

the sum running over any finite set of scalars containing the eigenvalues of `f`. For `X = 1` the
trace of `X|V_μ` is the dimension of `V_μ`.

Together with the independence of the sequences `l ↦ μ ^ l` for distinct `μ`
(`Finset.apply_eq_of_forall_sum_pow_succ_mul_eq`), these formulas read off the dimensions of the
generalized eigenspaces of nonzero eigenvalue from the traces of the positive powers of `f`. An
injective endomorphism has no generalized eigenvectors of eigenvalue `0`, so in characteristic
zero the traces of its positive powers determine its dimension, and then, by Newton's identities
(`LinearMap.charpoly_eq_of_trace_pow_eq`), its characteristic polynomial; the trace of the identity
`f ^ 0` is not needed. Base change to an algebraic closure removes the algebraic closedness from
this last statement.

## Main results

* `Module.End.trace_restrict_mul_maxGenEigenspace`: on the generalized `μ`-eigenspace of `f`,
  `tr (f * Y) = μ * tr Y` for `Y` commuting with `f`.
* `Module.End.trace_restrict_pow_mul_maxGenEigenspace`: on the generalized `μ`-eigenspace of `f`,
  `tr (f ^ l * X) = μ ^ l * tr X` for `X` commuting with `f`.
* `Module.End.trace_pow_mul_eq_sum`: `tr (f ^ l * X) = ∑ μ ∈ s, μ ^ l * tr (X|V_μ)` over an
  algebraically closed field.
* `Module.End.trace_pow_eq_sum_finrank`: `tr (f ^ l) = ∑ μ ∈ s, μ ^ l * dim V_μ`.
* `Module.End.trace_restrict_maxGenEigenspace_eq_of_trace_pow_succ_mul_eq`: the traces of
  `f ^ l * X` for `l ≥ 1` determine the trace of `X` on each generalized eigenspace of `f` of
  nonzero eigenvalue; `Module.End.finrank_maxGenEigenspace_eq_of_trace_pow_succ_eq` is the case
  `X = 1`, for the dimensions.
* `LinearMap.charpoly_eq_of_injective_of_trace_pow_succ_eq`: over a field of characteristic zero,
  injective endomorphisms of possibly different spaces whose positive powers
  have the same traces have the same characteristic polynomial.
-/

public section

open Module LinearMap

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- On the generalized `μ`-eigenspace of `f`, an endomorphism `Y` commuting with `f` satisfies
`tr (f * Y) = μ * tr Y`: there `f` is `μ` plus a nilpotent endomorphism commuting with `Y`. -/
theorem trace_restrict_mul_maxGenEigenspace {f Y : End K V} (h : Commute f Y) (μ : K) :
    trace K (f.maxGenEigenspace μ)
        ((f * Y).restrict (f.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).mul_right h) μ)) =
      μ * trace K (f.maxGenEigenspace μ) (Y.restrict (f.mapsTo_maxGenEigenspace_of_comm h μ)) := by
  have hf := f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ
  have hY := f.mapsTo_maxGenEigenspace_of_comm h μ
  have hfY : (f * Y).restrict (f.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).mul_right h) μ) =
      Y.restrict hY ∘ₗ f.restrict hf :=
    LinearMap.ext fun x ↦ Subtype.ext (LinearMap.congr_fun h.eq x)
  rw [hfY, trace_comp_eq_mul_of_commute_of_isNilpotent μ (restrict_commute h.symm hY hf)
      (f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ)]

/-- On the generalized `μ`-eigenspace of `f`, an endomorphism `X` commuting with `f` satisfies
`tr (f ^ l * X) = μ ^ l * tr X`. -/
theorem trace_restrict_pow_mul_maxGenEigenspace {f X : End K V} (h : Commute f X) (μ : K)
    (l : ℕ) :
    trace K (f.maxGenEigenspace μ)
        ((f ^ l * X).restrict
          (f.mapsTo_maxGenEigenspace_of_comm (((Commute.refl f).pow_right l).mul_right h) μ)) =
      μ ^ l *
        trace K (f.maxGenEigenspace μ) (X.restrict (f.mapsTo_maxGenEigenspace_of_comm h μ)) := by
  induction l with
  | zero =>
    simp only [pow_zero, one_mul]
  | succ l ih =>
    have hl : Commute f (f ^ l * X) := ((Commute.refl f).pow_right l).mul_right h
    simp only [pow_succ', mul_assoc]
    rw [trace_restrict_mul_maxGenEigenspace hl μ, ih, ← mul_assoc]

/-- The trace of the identity on a generalized eigenspace is its dimension, written for the
restriction of `1` that `Module.End.trace_pow_mul_eq_sum` produces. -/
theorem trace_restrict_one_maxGenEigenspace (f : End K V) (μ : K) :
    trace K (f.maxGenEigenspace μ)
        ((1 : End K V).restrict (f.mapsTo_maxGenEigenspace_of_comm (Commute.one_right f) μ)) =
      finrank K (f.maxGenEigenspace μ) := by
  have h1 : (1 : End K V).restrict (f.mapsTo_maxGenEigenspace_of_comm (Commute.one_right f) μ) =
      1 := LinearMap.ext fun x ↦ Subtype.ext <|
    (coe_restrict_apply _ x).trans (by rw [one_apply_eq_self, one_apply_eq_self])
  rw [h1, trace_one]

variable [IsAlgClosed K]

/-- **The trace of `f ^ l * X` along the generalized eigenspaces of `f`.** For `X` commuting
with `f`, over an algebraically closed field,
`tr (f ^ l * X) = ∑ μ ∈ s, μ ^ l * tr (X|V_μ)`, where `V_μ` is the generalized `μ`-eigenspace of
`f` and `s` is any finite set of scalars containing the eigenvalues of `f`. -/
theorem trace_pow_mul_eq_sum {f X : End K V} (h : Commute f X) (s : Finset K)
    (hs : ∀ μ, f.HasEigenvalue μ → μ ∈ s) (l : ℕ) :
    trace K V (f ^ l * X) = ∑ μ ∈ s, μ ^ l *
      trace K (f.maxGenEigenspace μ) (X.restrict (f.mapsTo_maxGenEigenspace_of_comm h μ)) := by
  classical
  have hl : Commute f (f ^ l * X) := ((Commute.refl f).pow_right l).mul_right h
  have hfin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
  rw [trace_eq_sum_trace_restrict' (isInternal_maxGenEigenspace f) hfin
    (f.mapsTo_maxGenEigenspace_of_comm hl)]
  refine Finset.sum_subset (fun μ hμ ↦ hs μ ?_) (fun μ _ hμ ↦ ?_) |>.trans
    (Finset.sum_congr rfl fun μ _ ↦ trace_restrict_pow_mul_maxGenEigenspace h μ l)
  · rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hμ
    exact (hasUnifEigenvalue_iff_hasUnifEigenvalue_one (k := ⊤) WithTop.top_pos).mp hμ
  · rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hμ
    have : Subsingleton (f.maxGenEigenspace μ) := by
      rw [hμ]
      infer_instance
    exact LinearMap.trace_eq_zero_of_subsingleton _

/-- **The trace of `f ^ l` from the dimensions of the generalized eigenspaces.** Over an
algebraically closed field, `tr (f ^ l) = ∑ μ ∈ s, μ ^ l * dim V_μ` for any finite set `s`
containing the eigenvalues of `f`. -/
theorem trace_pow_eq_sum_finrank (f : End K V) (s : Finset K)
    (hs : ∀ μ, f.HasEigenvalue μ → μ ∈ s) (l : ℕ) :
    trace K V (f ^ l) = ∑ μ ∈ s, μ ^ l * (finrank K (f.maxGenEigenspace μ) : K) := by
  rw [← mul_one (f ^ l), trace_pow_mul_eq_sum (Commute.one_right f) s hs l]
  simp only [trace_restrict_one_maxGenEigenspace]

variable {V' : Type*} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']

/-- **Traces on the generalized eigenspaces from the traces of `f ^ l * X`.** Let `X` commute
with `f` on `V` and `X'` with `f'` on `V'`, over an algebraically closed field. If
`tr (f ^ l * X) = tr (f' ^ l * X')` for every `l ≥ 1`, then for every `μ ≠ 0` the traces of `X` on
the generalized `μ`-eigenspace of `f` and of `X'` on that of `f'` agree. -/
theorem trace_restrict_maxGenEigenspace_eq_of_trace_pow_succ_mul_eq {f X : End K V}
    {f' X' : End K V'} (h : Commute f X) (h' : Commute f' X')
    (htr : ∀ l : ℕ, trace K V (f ^ (l + 1) * X) = trace K V' (f' ^ (l + 1) * X')) {μ : K}
    (hμ : μ ≠ 0) :
    trace K (f.maxGenEigenspace μ) (X.restrict (f.mapsTo_maxGenEigenspace_of_comm h μ)) =
      trace K (f'.maxGenEigenspace μ) (X'.restrict (f'.mapsTo_maxGenEigenspace_of_comm h' μ)) := by
  classical
  let s := insert μ (f.finite_hasEigenvalue.toFinset ∪ f'.finite_hasEigenvalue.toFinset)
  have hs : ∀ ν, f.HasEigenvalue ν → ν ∈ s := fun ν hν ↦ Finset.mem_insert_of_mem
    (Finset.mem_union_left _ (f.finite_hasEigenvalue.mem_toFinset.mpr hν))
  have hs' : ∀ ν, f'.HasEigenvalue ν → ν ∈ s := fun ν hν ↦ Finset.mem_insert_of_mem
    (Finset.mem_union_right _ (f'.finite_hasEigenvalue.mem_toFinset.mpr hν))
  refine s.apply_eq_of_forall_sum_pow_succ_mul_eq
    (f := fun ν ↦
      trace K (f.maxGenEigenspace ν) (X.restrict (f.mapsTo_maxGenEigenspace_of_comm h ν)))
    (g := fun ν ↦
      trace K (f'.maxGenEigenspace ν) (X'.restrict (f'.mapsTo_maxGenEigenspace_of_comm h' ν)))
    (fun l ↦ ?_) (Finset.mem_insert_self μ _) hμ
  rw [← trace_pow_mul_eq_sum h s hs, ← trace_pow_mul_eq_sum h' s hs', htr]

/-- **Dimensions of the generalized eigenspaces from the traces of the positive powers.** Over an
algebraically closed field of characteristic zero, if `tr (f ^ l) = tr (f' ^ l)` for every
`l ≥ 1`, then the generalized `μ`-eigenspaces of `f` and of `f'` have the same dimension for every
`μ ≠ 0`. -/
theorem finrank_maxGenEigenspace_eq_of_trace_pow_succ_eq [CharZero K] {f : End K V}
    {f' : End K V'} (htr : ∀ l : ℕ, trace K V (f ^ (l + 1)) = trace K V' (f' ^ (l + 1)))
    {μ : K} (hμ : μ ≠ 0) :
    finrank K (f.maxGenEigenspace μ) = finrank K (f'.maxGenEigenspace μ) := by
  have h := trace_restrict_maxGenEigenspace_eq_of_trace_pow_succ_mul_eq (Commute.one_right f)
    (Commute.one_right f') (fun l ↦ by rw [mul_one, mul_one, htr]) hμ
  rw [trace_restrict_one_maxGenEigenspace, trace_restrict_one_maxGenEigenspace] at h
  exact_mod_cast h

end Module.End

namespace LinearMap

variable {K V V' : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']

/-- The algebraically closed case of `LinearMap.charpoly_eq_of_injective_of_trace_pow_succ_eq`,
from which the general case follows by base change to an algebraic closure. -/
private theorem charpoly_eq_of_injective_of_trace_pow_succ_eq_of_isAlgClosed [IsAlgClosed K]
    {f : Module.End K V} {g : Module.End K V'} (hf : Function.Injective f)
    (hg : Function.Injective g) (h : ∀ k : ℕ, trace K V (f ^ (k + 1)) = trace K V' (g ^ (k + 1))) :
    f.charpoly = g.charpoly := by
  classical
  let s := f.finite_hasEigenvalue.toFinset ∪ g.finite_hasEigenvalue.toFinset
  have hdim (μ : K) :
      (finrank K (f.maxGenEigenspace μ) : K) = finrank K (g.maxGenEigenspace μ) := by
    rcases eq_or_ne μ 0 with rfl | hμ
    · rw [Module.End.maxGenEigenspace_zero_eq_bot_of_injective hf,
        Module.End.maxGenEigenspace_zero_eq_bot_of_injective hg, finrank_bot, finrank_bot]
    · rw [Module.End.finrank_maxGenEigenspace_eq_of_trace_pow_succ_eq h hμ]
  have hf₀ := Module.End.trace_pow_eq_sum_finrank f s
    (fun μ hμ ↦ Finset.mem_union_left _ (f.finite_hasEigenvalue.mem_toFinset.mpr hμ)) 0
  have hg₀ := Module.End.trace_pow_eq_sum_finrank g s
    (fun μ hμ ↦ Finset.mem_union_right _ (g.finite_hasEigenvalue.mem_toFinset.mpr hμ)) 0
  simp only [pow_zero, trace_one, one_mul] at hf₀ hg₀
  have hrank : finrank K V = finrank K V' := by
    exact_mod_cast hf₀.trans ((Finset.sum_congr rfl fun μ _ ↦ hdim μ).trans hg₀.symm)
  refine charpoly_eq_of_trace_pow_eq hrank fun k hk _ ↦ ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk.ne'
  exact h k

/-- **The traces of the positive powers of an injective endomorphism determine its characteristic
polynomial.** Over a field of characteristic zero, if injective endomorphisms `f` of `V` and `g`
of `V'` satisfy `tr (f ^ k) = tr (g ^ k)` for every `k ≥ 1`, then `f` and `g` have the same
characteristic polynomial (in particular `V` and `V'` have the same dimension). Over an
algebraically closed field this reads the dimensions of the generalized eigenspaces of nonzero
eigenvalue off the traces; the general case follows by base change to an algebraic closure. -/
theorem charpoly_eq_of_injective_of_trace_pow_succ_eq {f : Module.End K V}
    {g : Module.End K V'} (hf : Function.Injective f) (hg : Function.Injective g)
    (h : ∀ k : ℕ, trace K V (f ^ (k + 1)) = trace K V' (g ^ (k + 1))) :
    f.charpoly = g.charpoly := by
  let L := AlgebraicClosure K
  have hfL : Function.Injective (f.baseChange L) := by
    rw [baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap f hf
  have hgL : Function.Injective (g.baseChange L) := by
    rw [baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap g hg
  have hL : (f.baseChange L).charpoly = (g.baseChange L).charpoly :=
    charpoly_eq_of_injective_of_trace_pow_succ_eq_of_isAlgClosed hfL hgL fun k ↦ by
      rw [← baseChange_pow, ← baseChange_pow, trace_baseChange, trace_baseChange, h]
  rw [charpoly_baseChange, charpoly_baseChange] at hL
  exact Polynomial.map_injective _ (algebraMap K L).injective hL

end LinearMap
