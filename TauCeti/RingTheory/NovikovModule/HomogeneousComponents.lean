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
independent, and when `d` takes finitely many values the completion is their internal direct sum
(`TauCeti.NovikovModule.isInternal_gradeBy`). In general it is not: a completed combination may
meet infinitely many degrees, as an integer-graded capped Floer chain does when recapping changes
the grading. This file shows that the completion is nevertheless recovered from the homogeneous
pieces through the potential-cutoff topology of `TauCeti.RingTheory.NovikovModule.Topology`.

* Taking the homogeneous part of degree `k` (`TauCeti.NovikovModule.gradeProj`) is continuous
  (`TauCeti.NovikovModule.continuous_gradeProj`), and every homogeneous piece is closed
  (`TauCeti.NovikovModule.isClosed_gradeBy`).
* Every completed combination is the sum, convergent in the potential-cutoff topology, of its
  homogeneous parts (`TauCeti.NovikovModule.hasSum_gradeProj`), and this is its only decomposition
  into a convergent sum of homogeneous combinations
  (`TauCeti.NovikovModule.hasSum_iff_eq_gradeProj`). Hence the sum of the homogeneous pieces is
  dense (`TauCeti.NovikovModule.dense_iSup_gradeBy`).
* A completed combination is a finite sum of homogeneous combinations exactly when it meets
  finitely many degrees (`TauCeti.NovikovModule.mem_iSup_gradeBy_iff_finite`). So the sum of the
  homogeneous pieces is closed exactly when it is everything, and the completion is the internal
  direct sum of its homogeneous pieces exactly when every completed combination meets finitely many
  degrees (`TauCeti.NovikovModule.isClosed_iSup_gradeBy_iff`,
  `TauCeti.NovikovModule.isInternal_gradeBy_iff`).

These are the statements needed to work with homogeneous pieces of a completed graded module
without asserting that it is the direct sum of its homogeneous pieces. The corresponding results
for the Novikov series themselves are in `TauCeti.RingTheory.NovikovSeries.HomogeneousComponents`.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the grading of Floer complexes over Novikov rings.
-/

public section

noncomputable section

open Filter Function Set Topology

namespace TauCeti.NovikovModule

variable {R S D : Type*} [Ring R] {F : S → ℝ} {d : S → D}

/-- Every homogeneous piece is closed in the potential-cutoff topology: it is cut out by the
vanishing of the coefficients at the generators of other degrees, each of which is locally
constant. -/
theorem isClosed_gradeBy (d : S → D) (k : D) :
    IsClosed (gradeBy R F d k : Set (NovikovModule R F)) := by
  have heq : (gradeBy R F d k : Set (NovikovModule R F)) =
      ⋂ s ∈ (d ⁻¹' {k})ᶜ, {a | a.val s = 0} := by
    ext a
    simp only [SetLike.mem_coe, mem_gradeBy_iff, mem_iInter, mem_ofPred_eq]
    exact ⟨fun ha s hs => by_contra fun hne => hs (ha s hne),
      fun ha s hs => by_contra fun hne => hs (ha s hne)⟩
  rw [heq]
  exact isClosed_biInter fun s _ => (isLocallyConstant_apply_val s).isClosed_fiber 0

/-- A completed combination is a finite sum of homogeneous combinations exactly when its nonzero
coefficients occur at generators of only finitely many degrees. -/
theorem mem_iSup_gradeBy_iff_finite {a : NovikovModule R F} :
    a ∈ ⨆ k, gradeBy R F d k ↔ (d '' Function.support a.val).Finite := by
  classical
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · refine Submodule.iSup_induction (motive := fun b => (d '' Function.support b.val).Finite) _ ha
      (fun k b hb => (finite_singleton k).subset ?_) (by simp) fun b c hb hc => ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact mem_gradeBy_iff.1 hb s hs
    · exact (hb.union hc).subset
        ((image_mono (Function.support_add b.val c.val)).trans (image_union d _ _).subset)
  · -- `a` is the sum of its homogeneous parts of the finitely many degrees it meets.
    have hsum : ∑ k ∈ ha.toFinset, gradeProj R F d k a = a := by
      ext s
      simp only [Submodule.coe_sum, Finset.sum_apply, gradeProj_val, Finset.sum_ite_eq]
      split_ifs with hs
      · rfl
      · by_contra hne
        exact hs (ha.mem_toFinset.2 ⟨s, Ne.symm hne, rfl⟩)
    rw [← hsum]
    exact Submodule.sum_mem _ fun k _ => Submodule.mem_iSup_of_mem k (gradeProj_mem_gradeBy d k a)

section Proj

variable [DecidableEq D]

/-- Taking a homogeneous part preserves every subgroup `U_C` of the potential filtration. -/
theorem gradeProj_mem_potentialFiltration (d : S → D) (k : D) {C : ℝ} {a : NovikovModule R F}
    (ha : a ∈ potentialFiltration R F C) : gradeProj R F d k a ∈ potentialFiltration R F C :=
  mem_potentialFiltration.2 fun s hs => by
    rw [gradeProj_val, mem_potentialFiltration.1 ha s hs, ite_self]

/-- Taking a homogeneous part is continuous in the potential-cutoff topology. -/
theorem continuous_gradeProj (d : S → D) (k : D) : Continuous (gradeProj R F d k) :=
  continuous_of_mem_potentialFiltration_add (C := 0) fun D a ha => by
    simpa using gradeProj_mem_potentialFiltration d k ha

/-- **Every completed combination is the sum of its homogeneous parts**, convergent in the
potential-cutoff topology: above any potential cutoff only finitely many degrees occur among the
nonzero coefficients. -/
theorem hasSum_gradeProj (d : S → D) (a : NovikovModule R F) :
    HasSum (fun k => gradeProj R F d k a) a := by
  rw [HasSum, SummationFilter.unconditional_filter, tendsto_nhds_iff]
  intro C
  filter_upwards [eventually_ge_atTop ((finite_gt a C).toFinset.image d)] with T hT s hs
  simp only [Submodule.coe_sum, Finset.sum_apply, gradeProj_val, Finset.sum_ite_eq]
  split_ifs with hsT
  · rfl
  · by_contra hne
    exact hsT (hT (Finset.mem_image_of_mem d ((finite_gt a C).mem_toFinset.2 ⟨Ne.symm hne, hs⟩)))

/-- **Uniqueness of the homogeneous decomposition.** A family of completed combinations of the
respective degrees sums to `a` exactly when it is the family of homogeneous parts of `a`. -/
theorem hasSum_iff_eq_gradeProj {b : D → NovikovModule R F} (hb : ∀ k, b k ∈ gradeBy R F d k)
    {a : NovikovModule R F} : HasSum b a ↔ ∀ k, b k = gradeProj R F d k a := by
  refine ⟨fun h k => ?_, fun h => funext h ▸ hasSum_gradeProj d a⟩
  -- The part of degree `k` of the sum is the sum of the parts of degree `k`, which is `b k`.
  have hk : HasSum (fun j => gradeProj R F d k (b j)) (b k) := by
    convert hasSum_ite_eq k (b k) using 2 with j
    by_cases hj : j = k
    · rw [ite_eq_left hj, hj, gradeProj_eq_self_of_mem_gradeBy (hb k)]
    · rw [ite_eq_right hj, gradeProj_eq_zero_of_mem_gradeBy hj (hb j)]
  exact hk.unique (h.map (gradeProj R F d k) (continuous_gradeProj d k))

end Proj

/-- The finite sums of homogeneous combinations are dense in the potential-cutoff topology. -/
theorem dense_iSup_gradeBy (d : S → D) :
    Dense ((⨆ k, gradeBy R F d k : Submodule R (NovikovModule R F)) :
      Set (NovikovModule R F)) := fun a => by
  classical
  have ha := hasSum_gradeProj d a
  rw [HasSum, SummationFilter.unconditional_filter] at ha
  exact mem_closure_of_tendsto ha (Eventually.of_forall fun T =>
    Submodule.sum_mem _ fun k _ => Submodule.mem_iSup_of_mem k (gradeProj_mem_gradeBy d k a))

/-- The homogeneous combinations span the completed module exactly when every completed
combination meets only finitely many degrees. -/
theorem iSup_gradeBy_eq_top_iff :
    ⨆ k, gradeBy R F d k = ⊤ ↔
      ∀ a : NovikovModule R F, (d '' Function.support a.val).Finite := by
  simp only [Submodule.eq_top_iff', mem_iSup_gradeBy_iff_finite]

/-- The sum of the homogeneous pieces is closed in the potential-cutoff topology exactly when it
is everything, that is, when every completed combination meets only finitely many degrees. -/
theorem isClosed_iSup_gradeBy_iff :
    IsClosed ((⨆ k, gradeBy R F d k : Submodule R (NovikovModule R F)) :
      Set (NovikovModule R F)) ↔
      ∀ a : NovikovModule R F, (d '' Function.support a.val).Finite := by
  rw [← iSup_gradeBy_eq_top_iff]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  rw [← Submodule.coe_eq_univ, ← h.closure_eq, (dense_iSup_gradeBy d).closure_eq]

/-- The completed module is the internal direct sum of its homogeneous pieces exactly when every
completed combination meets only finitely many degrees. -/
theorem isInternal_gradeBy_iff [DecidableEq D] :
    DirectSum.IsInternal (gradeBy R F d) ↔
      ∀ a : NovikovModule R F, (d '' Function.support a.val).Finite := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, iSup_gradeBy_eq_top_iff]
  exact and_iff_right (iSupIndep_of_forall_mem_iff fun _ _ => Iff.rfl)

end TauCeti.NovikovModule
