/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Residue
public import TauCeti.RingTheory.NovikovModule.Topology

/-!
# Homogeneous components in the potential-cutoff topology

A degree function `d : S → D` on generators cuts the completed module `NovikovModule R F` into
the homogeneous pieces `NovikovModule.gradeBy R F d k`. A completed combination may have nonzero
coefficients in infinitely many degrees, and then it is not a finite sum of homogeneous
combinations. This file shows that it is nevertheless the sum, convergent in the potential-cutoff
topology, of its homogeneous components `NovikovModule.gradeProj R F d k a`: above every potential
cutoff only finitely many degrees occur. Conversely, the components of a convergent sum of
homogeneous combinations are its summands, so the decomposition is unique.

The homogeneous pieces are closed, each being cut out by the vanishing of the coefficients at the
generators of the other degrees, and these coefficients are locally constant. Their sum, the
combinations meeting only finitely many degrees, contains the finite combinations and so is dense;
hence it is closed exactly when it is the whole module. Closedness of each piece does not give
closedness of their sum: for the degree `d(n) = n` on `S = ℕ` with potential `F(n) = -n`, the
pieces are the lines through the generators and their sum consists of the finite combinations.

These statements hold over every ring, for every potential and every degree function. They apply
to completed Novikov state modules graded by cohomological degree plus twice the first Chern
number, whose homogeneous components need not be finite in number.

## Main results

* `TauCeti.NovikovModule.isClosed_gradeBy`: the homogeneous pieces are closed.
* `TauCeti.NovikovModule.continuous_gradeProj`: the homogeneous components depend continuously on
  the combination.
* `TauCeti.NovikovModule.hasSum_gradeProj`: a completed combination is the convergent sum of its
  homogeneous components.
* `TauCeti.NovikovModule.hasSum_iff_forall_gradeProj_eq`: a family of homogeneous combinations sums
  to `a` exactly when it is the family of homogeneous components of `a`.
* `TauCeti.NovikovModule.dense_iSup_gradeBy`, `TauCeti.NovikovModule.isClosed_iSup_gradeBy_iff`:
  the sum of the homogeneous pieces is dense, and closed exactly when it is everything.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on the grading of Floer complexes over Novikov rings.
-/

public section

noncomputable section

namespace TauCeti.NovikovModule

open Filter Set Topology

variable {R S D : Type*} [Ring R] {F : S → ℝ} {d : S → D}

variable (R F) in
/-- The homogeneous combinations of a fixed degree form a closed subset in the potential-cutoff
topology. -/
theorem isClosed_gradeBy (d : S → D) (k : D) :
    IsClosed (gradeBy R F d k : Set (NovikovModule R F)) := by
  have h : (gradeBy R F d k : Set (NovikovModule R F)) =
      ⋂ s ∈ {s | d s ≠ k}, {a | a.val s = 0} := by
    ext a
    simp only [SetLike.mem_coe, mem_gradeBy_iff, mem_iInter, mem_ofPred_eq]
    exact ⟨fun ha s hs => by_contra fun h => hs (ha s h),
      fun ha s hs => by_contra fun h => hs (ha s h)⟩
  rw [h]
  exact isClosed_biInter fun s _ => (isLocallyConstant_apply_val s).isClosed_fiber 0

section Proj

variable [DecidableEq D]

variable (R F) in
/-- Taking the homogeneous component of a fixed degree is continuous in the potential-cutoff
topology. -/
theorem continuous_gradeProj (d : S → D) (k : D) : Continuous (gradeProj R F d k) :=
  continuous_of_mem_potentialFiltration_add (C := 0) fun _ a ha =>
    mem_potentialFiltration.2 fun s hs => by
      simp [mem_potentialFiltration.1 ha s (by simpa using hs)]

/-- A completed combination is the sum, convergent in the potential-cutoff topology, of its
homogeneous components, although infinitely many of them may be nonzero. -/
theorem hasSum_gradeProj (d : S → D) (a : NovikovModule R F) :
    HasSum (fun k => gradeProj R F d k a) a := by
  refine tendsto_nhds_iff.2 fun C => ?_
  -- Above the cutoff `C` only finitely many generators, hence degrees, carry nonzero coefficients.
  have hfin := (finite_gt a C).image d
  filter_upwards [eventually_ge_atTop hfin.toFinset] with T hT s hs
  rw [sum_gradeProj_val]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h (hT (hfin.mem_toFinset.2 ⟨s, ⟨Ne.symm hne, hs⟩, rfl⟩))

/-- If a family `f` with each `f k` homogeneous of degree `k` sums to `a`, then `f k` is the
homogeneous component of degree `k` of `a`. -/
theorem gradeProj_eq_of_hasSum {f : D → NovikovModule R F} {a : NovikovModule R F}
    (hf : ∀ k, f k ∈ gradeBy R F d k) (ha : HasSum f a) (k : D) :
    gradeProj R F d k a = f k := by
  have h := (ha.map (gradeProj R F d k) (continuous_gradeProj R F d k)).unique
    (hasSum_single k fun j hj => gradeProj_eq_zero_of_mem_gradeBy hj (hf j))
  rwa [gradeProj_eq_self_of_mem_gradeBy (hf k)] at h

/-- A family `f` with each `f k` homogeneous of degree `k` sums to `a` exactly when it is the
family of homogeneous components of `a`. -/
theorem hasSum_iff_forall_gradeProj_eq {f : D → NovikovModule R F} {a : NovikovModule R F}
    (hf : ∀ k, f k ∈ gradeBy R F d k) :
    HasSum f a ↔ ∀ k, gradeProj R F d k a = f k := by
  refine ⟨gradeProj_eq_of_hasSum hf, fun h => ?_⟩
  rw [← funext h]
  exact hasSum_gradeProj d a

end Proj

variable (R F d) in
/-- The combinations meeting only finitely many degrees are dense in the potential-cutoff
topology, since they include the finite combinations. -/
theorem dense_iSup_gradeBy :
    Dense ((⨆ k, gradeBy R F d k : Submodule R (NovikovModule R F)) : Set (NovikovModule R F)) :=
  denseRange_ofFinsupp.mono fun _ ha => range_ofFinsupp_le_iSup_gradeBy (LinearMap.mem_range.2 ha)

/-- The combinations meeting only finitely many degrees form a closed subset exactly when they are
all completed combinations. -/
theorem isClosed_iSup_gradeBy_iff :
    IsClosed ((⨆ k, gradeBy R F d k : Submodule R (NovikovModule R F)) :
      Set (NovikovModule R F)) ↔ ⨆ k, gradeBy R F d k = ⊤ := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  rw [← SetLike.coe_set_eq, Submodule.top_coe, ← h.closure_eq]
  exact (dense_iSup_gradeBy R F d).closure_eq

end TauCeti.NovikovModule
