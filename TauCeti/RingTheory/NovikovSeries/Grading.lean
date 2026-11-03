/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Multiplication
public import Mathlib.Algebra.MonoidAlgebra.Grading

/-!
# Homogeneous Novikov series

Let `f : H → ι` be a degree function on the exponents of Novikov series. A Novikov series is
*homogeneous of degree `i`* when its support lies in the fibre `f ⁻¹' {i}`. These series form the
submodule `TauCeti.NovikovSeries.gradeBy R N f i`, the Novikov analogue of Mathlib's
`AddMonoidAlgebra.gradeBy`. For an additive degree function the pieces multiply as a graded
monoid, and they are independent.

Unlike the group ring, the Novikov ring is in general *not* the direct sum of its homogeneous
pieces: a series whose support meets infinitely many fibres is not a finite sum of homogeneous
series. The homogeneous pieces span exactly the finitely supported series as soon as the period
`N` is bounded above on every fibre of `f`, for instance when `f` is injective. In that case the
graded ring spanned by homogeneous series is the group ring `R[H]`, and the Novikov ring is its
period completion. This is the situation of the coefficient ring of capped Hamiltonian Floer
theory on a spherically monotone symplectic manifold, graded by twice the first Chern number.

## Main definitions

* `TauCeti.NovikovSeries.supported R N s`: the Novikov series supported in the set `s`.
* `TauCeti.NovikovSeries.gradeBy R N f i`: the Novikov series of degree `i` for the degree
  function `f`.

## Main results

* `TauCeti.NovikovSeries.gradeBy.gradedMonoid`: for an additive degree function, the homogeneous
  pieces form a graded monoid.
* `TauCeti.NovikovSeries.iSupIndep_gradeBy`: the homogeneous pieces are independent.
* `TauCeti.NovikovSeries.ofAddMonoidAlgebra_mem_gradeBy_iff`: the inclusion of the group ring
  preserves and reflects the degree.
* `TauCeti.NovikovSeries.finite_support_of_mem_gradeBy`: a homogeneous series is finitely
  supported when the period is bounded above on its fibre.
* `TauCeti.NovikovSeries.mem_iSup_gradeBy_iff`: if the period is bounded above on every fibre,
  the homogeneous pieces span exactly the finitely supported series.
* `TauCeti.NovikovSeries.eq_single_of_mem_gradeBy`: for an injective degree function, every
  homogeneous series is a monomial.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the construction of
  the Novikov ring in the chapter on quantum cohomology.
-/

public section

noncomputable section

open Function Set

namespace TauCeti

namespace NovikovSeries

variable {R H ι : Type*}

section Semiring

variable [Semiring R]

section AddZeroClass

variable [AddZeroClass H] {N : H →+ ℝ}

variable (R N) in
/-- The Novikov series supported in the set `s`, the Novikov analogue of `Finsupp.supported`. -/
def supported (s : Set H) : Submodule R (NovikovSeries R H N) where
  carrier := {a | a.support ⊆ s}
  zero_mem' := by simp
  add_mem' ha hb := (support_add_subset _ _).trans (union_subset ha hb)
  smul_mem' r _ ha := (support_smul_subset r _).trans ha

/-- A series lies in `supported R N s` exactly when its support lies in `s`. -/
theorem mem_supported {s : Set H} {a : NovikovSeries R H N} :
    a ∈ supported R N s ↔ a.support ⊆ s :=
  Iff.rfl

variable (R N) in
/-- The Novikov series of degree `i` for the degree function `f`: those whose support lies in
the fibre `f ⁻¹' {i}`. -/
def gradeBy (f : H → ι) (i : ι) : Submodule R (NovikovSeries R H N) :=
  supported R N (f ⁻¹' {i})

/-- A series has degree `i` exactly when its support lies in the fibre over `i`. -/
theorem mem_gradeBy_iff {f : H → ι} {i : ι} {a : NovikovSeries R H N} :
    a ∈ gradeBy R N f i ↔ a.support ⊆ f ⁻¹' {i} :=
  Iff.rfl

/-- The monomial `r e^h` has degree `f h`. -/
theorem single_mem_gradeBy (f : H → ι) (h : H) (r : R) :
    (single h r : NovikovSeries R H N) ∈ gradeBy R N f (f h) := fun _ hg => by
  rw [mem_singleton_iff.1 (support_single_subset h r hg), mem_preimage, mem_singleton_iff]

/-- There are no nonzero series of a degree that no exponent has. -/
theorem gradeBy_eq_bot {f : H → ι} {i : ι} (hi : i ∉ range f) : gradeBy R N f i = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun a ha => support_eq_empty.1 ?_
  exact eq_empty_of_forall_notMem fun h hh => hi ⟨h, ha hh⟩

/-- If every exponent has degree `i`, every series is homogeneous of degree `i`. -/
theorem gradeBy_eq_top {f : H → ι} {i : ι} (hf : ∀ h, f h = i) : gradeBy R N f i = ⊤ :=
  Submodule.eq_top_iff'.2 fun _ h _ => hf h

/-- Homogeneous series of different degrees span independent submodules. -/
theorem iSupIndep_gradeBy (f : H → ι) : iSupIndep (gradeBy R N f) := by
  intro i
  -- Every homogeneous piece of degree `j ≠ i` consists of series avoiding the fibre over `i`.
  have hle : ⨆ (j) (_ : j ≠ i), gradeBy R N f j ≤ supported R N (f ⁻¹' {i})ᶜ :=
    iSup₂_le fun j hj a ha h hh => by
      rw [mem_compl_iff, mem_preimage, mem_singleton_iff, (ha hh : f h = j)]
      exact hj
  refine (Submodule.disjoint_def.2 fun a ha ha' => support_eq_empty.1 ?_).mono_right hle
  exact eq_empty_of_forall_notMem fun h hh => ha' hh (ha hh)

/-- A homogeneous series is finitely supported if the period is bounded above on its fibre. -/
theorem finite_support_of_mem_gradeBy {f : H → ι} {i : ι} (hf : BddAbove (N '' (f ⁻¹' {i})))
    {a : NovikovSeries R H N} (ha : a ∈ gradeBy R N f i) : a.support.Finite := by
  obtain ⟨C, hC⟩ := hf
  exact (a.finite_le C).subset fun h hh => ⟨mem_support.1 hh, hC ⟨h, ha hh, rfl⟩⟩

/-- A finitely supported series is a finite sum of homogeneous series. -/
theorem ofFinsupp_mem_iSup_gradeBy (f : H → ι) (x : H →₀ R) :
    ofFinsupp x ∈ ⨆ i, gradeBy R N f i := by
  induction x using Finsupp.induction with
  | zero => simp
  | single_add h r x _ _ hx =>
    rw [map_add, ofFinsupp_single]
    exact add_mem (Submodule.mem_iSup_of_mem (f h) (single_mem_gradeBy f h r)) hx

/-- If the period is bounded above on every fibre of the degree function, the homogeneous series
span exactly the finitely supported series. -/
theorem mem_iSup_gradeBy_iff {f : H → ι} (hf : ∀ i, BddAbove (N '' (f ⁻¹' {i})))
    {a : NovikovSeries R H N} : a ∈ ⨆ i, gradeBy R N f i ↔ a.support.Finite := by
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · exact Submodule.iSup_induction (motive := fun b => b.support.Finite) _ ha
      (fun i _ hb => finite_support_of_mem_gradeBy (hf i) hb) (by simp)
      fun _ _ hb hc => (hb.union hc).subset (support_add_subset _ _)
  · obtain ⟨x, rfl⟩ := mem_range_ofFinsupp_iff.2 ha
    exact ofFinsupp_mem_iSup_gradeBy f x

/-- For an injective degree function, a series of the degree of `h` is the monomial at `h`
with its own coefficient. -/
theorem eq_single_of_mem_gradeBy {f : H → ι} (hf : Injective f) {h : H}
    {a : NovikovSeries R H N} (ha : a ∈ gradeBy R N f (f h)) : a = single h (a.coeff h) := by
  ext g
  by_cases hg : g = h
  · rw [hg, coeff_single_same]
  · rw [coeff_single_of_ne hg]
    by_contra hag
    exact hg (hf (ha (mem_support.2 hag)))

end AddZeroClass

/-- For an additive degree function, the homogeneous Novikov series form a graded monoid. -/
instance gradeBy.gradedMonoid [AddMonoid H] {N : H →+ ℝ} [AddMonoid ι] (f : H →+ ι) :
    SetLike.GradedMonoid (gradeBy R N f) where
  one_mem h hh := by
    rw [← single_zero_one] at hh
    rw [mem_preimage, mem_singleton_iff, mem_singleton_iff.1 (support_single_subset 0 1 hh),
      map_zero]
  mul_mem i j a b ha hb h hh := by
    obtain ⟨u, hu, v, hv, rfl⟩ := support_mul_subset a b hh
    rw [mem_preimage, mem_singleton_iff, map_add, (ha hu : f u = i), (hb hv : f v = j)]

end Semiring

/-- The inclusion of the group ring into the Novikov series preserves and reflects the degree. -/
theorem ofAddMonoidAlgebra_mem_gradeBy_iff [CommSemiring R] [AddMonoid H] {N : H →+ ℝ}
    {f : H → ι} {i : ι} {x : AddMonoidAlgebra R H} :
    (ofAddMonoidAlgebra x : NovikovSeries R H N) ∈ gradeBy R N f i ↔
      x ∈ AddMonoidAlgebra.gradeBy R f i := by
  simp only [mem_gradeBy_iff, AddMonoidAlgebra.mem_gradeBy_iff, subset_def, mem_support,
    coeff_ofAddMonoidAlgebra, Finset.mem_coe, Finsupp.mem_support_iff]

end NovikovSeries

end TauCeti
