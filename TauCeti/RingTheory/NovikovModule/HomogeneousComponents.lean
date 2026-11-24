/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Residue
public import TauCeti.RingTheory.NovikovModule.Topology
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Homogeneous components of completed combinations

Let `d : S → D` be a degree function on the generators of the completed module
`NovikovModule R F`. Its homogeneous pieces `TauCeti.NovikovModule.gradeBy R F d k` are
independent (`TauCeti.NovikovModule.iSupIndep_gradeBy`), and when `d` takes finitely many values
the completion is their internal direct sum (`TauCeti.NovikovModule.isInternal_gradeBy`). In
general it is not: a completed combination may meet infinitely many degrees, as an
integer-graded capped Floer chain does when recapping changes the grading. This file shows that
the completion is nevertheless recovered from the homogeneous pieces through the potential-cutoff
topology of `TauCeti.RingTheory.NovikovModule.Topology`, for every coefficient ring, every
potential `F : S → ℝ` and every degree function.

* The homogeneous component `TauCeti.NovikovModule.homogeneousComponent R F d k`, defined in
  `TauCeti.RingTheory.NovikovModule.Grading`, does not raise potentials, so it is continuous
  (`TauCeti.NovikovModule.continuous_homogeneousComponent`), and every homogeneous piece is
  closed (`TauCeti.NovikovModule.isClosed_gradeBy`).
* Every completed combination is the sum, unconditionally convergent in the potential-cutoff
  topology, of its homogeneous components
  (`TauCeti.NovikovModule.hasSum_homogeneousComponent`), and this is its only decomposition into a
  convergent sum of homogeneous combinations
  (`TauCeti.NovikovModule.hasSum_iff_forall_homogeneousComponent_eq`). By
  `TauCeti.NovikovModule.summable_iff_finite_setOf_notMem_potentialFiltration`, such a family is
  summable exactly when only finitely many of its members have a nonzero coefficient above each
  potential cutoff. Hence the sum of the homogeneous pieces is dense
  (`TauCeti.NovikovModule.dense_iSup_gradeBy`).
* A completed combination is a finite sum of homogeneous combinations exactly when it meets
  finitely many degrees (`TauCeti.NovikovModule.mem_iSup_gradeBy_iff_finite`). So the sum of the
  homogeneous pieces is closed exactly when it is everything, and the completion is the internal
  direct sum of its homogeneous pieces exactly when every completed combination meets finitely many
  degrees (`TauCeti.NovikovModule.isClosed_iSup_gradeBy_iff`,
  `TauCeti.NovikovModule.isInternal_gradeBy_iff`). Closedness of each piece does not give
  closedness of their sum: on `S = ℕ` with potential `n ↦ -n` and degree `n ↦ n`, the pieces are
  the lines through the generators, and the combination with every coefficient `1` is a limit of
  finite combinations outside their span.

These are the statements needed to work with homogeneous pieces of a completed graded module
without asserting that it is the direct sum of its homogeneous pieces: for graded Novikov modules
of capped generators, with degree given by a Conley–Zehnder or Chern grading, a completed state
module, or a completed Floer chain module, is the filtered completion of its homogeneous part, and
the homogeneous parts of a limit can be read off coefficientwise. The corresponding results for the
Novikov series themselves are in `TauCeti.RingTheory.NovikovSeries.HomogeneousComponents`.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the grading of Floer complexes over Novikov rings.
-/

public section

noncomputable section

open Filter Function Set Topology

namespace TauCeti.NovikovModule

variable {R S D : Type*} [Ring R] {F : S → ℝ} {d : S → D} {a : NovikovModule R F}

/-- The component of degree `k` does not raise potentials: it maps `U_C` into `U_C`. -/
theorem homogeneousComponent_mem_potentialFiltration {C : ℝ} (k : D)
    (ha : a ∈ potentialFiltration R F C) :
    homogeneousComponent R F d k a ∈ potentialFiltration R F C := by
  classical
  exact mem_potentialFiltration.2 fun s hs => by
    simp [mem_potentialFiltration.1 ha s hs]

/-- The homogeneous components are continuous for the potential-cutoff topology. -/
theorem continuous_homogeneousComponent (d : S → D) (k : D) :
    Continuous (homogeneousComponent R F d k) :=
  continuous_of_forall_mem_potentialFiltration _ fun C =>
    ⟨C, fun _ ha => homogeneousComponent_mem_potentialFiltration k ha⟩

/-- Each homogeneous piece is closed in the potential-cutoff topology. -/
theorem isClosed_gradeBy (d : S → D) (k : D) :
    IsClosed (gradeBy R F d k : Set (NovikovModule R F)) := by
  have h : (gradeBy R F d k : Set (NovikovModule R F)) =
      {a | homogeneousComponent R F d k a = a} :=
    Set.ext fun _ => mem_gradeBy_iff_homogeneousComponent_eq
  rw [h]
  exact isClosed_eq (continuous_homogeneousComponent d k) continuous_id

/-- **Every completed combination is the sum of its homogeneous components**, unconditionally
convergent in the potential-cutoff topology: above any potential cutoff only finitely many degrees
occur among the nonzero coefficients. -/
theorem hasSum_homogeneousComponent (d : S → D) (a : NovikovModule R F) :
    HasSum (fun k => homogeneousComponent R F d k a) a := by
  classical
  rw [HasSum, SummationFilter.unconditional_filter, tendsto_nhds_iff]
  intro C
  -- Above `C` the coefficients of `a` occur in the finitely many degrees of this set.
  have hfin := (finite_gt a C).image d
  filter_upwards [eventually_ge_atTop hfin.toFinset] with T hT s hs
  rw [sum_homogeneousComponent_apply_val]
  split_ifs with hdT
  · rfl
  · by_contra h
    exact hdT (hT (hfin.mem_toFinset.2 ⟨s, ⟨Ne.symm h, hs⟩, rfl⟩))

/-- If homogeneous combinations `b k` of degree `k` sum to `a`, then `b k` is the component of
`a` of degree `k`. -/
theorem homogeneousComponent_eq_of_hasSum {b : D → NovikovModule R F}
    (hb : ∀ k, b k ∈ gradeBy R F d k) (h : HasSum b a) (k : D) :
    homogeneousComponent R F d k a = b k := by
  classical
  have hk : (homogeneousComponent R F d k ∘ b) = fun j => if j = k then b k else 0 := by
    funext j
    split_ifs with hj
    · exact hj ▸ homogeneousComponent_of_mem_gradeBy (hb j)
    · exact homogeneousComponent_eq_zero_of_mem_gradeBy (hb j) hj
  have h' := h.map (homogeneousComponent R F d k) (continuous_homogeneousComponent d k)
  rw [hk] at h'
  exact h'.unique (hasSum_ite_eq k (b k))

/-- **Uniqueness of the homogeneous decomposition.** A family of combinations `b k`, homogeneous
of degree `k`, sums to `a` exactly when each `b k` is the component of `a` of degree `k`. -/
theorem hasSum_iff_forall_homogeneousComponent_eq {b : D → NovikovModule R F}
    (hb : ∀ k, b k ∈ gradeBy R F d k) :
    HasSum b a ↔ ∀ k, homogeneousComponent R F d k a = b k :=
  ⟨fun h => homogeneousComponent_eq_of_hasSum hb h, fun h =>
    (funext h : (fun k => homogeneousComponent R F d k a) = b) ▸ hasSum_homogeneousComponent d a⟩

/-- The span of the homogeneous pieces is dense: it contains the finite combinations. -/
theorem dense_iSup_gradeBy (d : S → D) :
    Dense ((⨆ k, gradeBy R F d k : Submodule R (NovikovModule R F)) : Set (NovikovModule R F)) :=
  denseRange_ofFinsupp.mono <| by
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, mem_iSup_gradeBy_iff_finite,
      show (ofFinsupp F x).val = x from funext (ofFinsupp_apply_val x)]
    exact x.hasFiniteSupport.image d

/-- The sum of the homogeneous pieces is closed in the potential-cutoff topology exactly when it
is everything, that is, when every completed combination meets only finitely many degrees. -/
theorem isClosed_iSup_gradeBy_iff :
    IsClosed ((⨆ k, gradeBy R F d k : Submodule R (NovikovModule R F)) :
      Set (NovikovModule R F)) ↔
      ∀ a : NovikovModule R F, (d '' Function.support a.val).Finite := by
  rw [← iSup_gradeBy_eq_top_iff]
  exact ⟨fun h => SetLike.coe_injective ((h.dense_iff.1 (dense_iSup_gradeBy d)).trans
    Submodule.top_coe.symm), fun h => h ▸ isClosed_univ⟩

end TauCeti.NovikovModule
