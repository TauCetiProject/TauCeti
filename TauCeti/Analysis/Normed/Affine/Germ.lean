/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Normed.Affine.Generic
public import TauCeti.Topology.Algebra.Affine.Germ

/-!
# Generic incoming affine germs

For finitely many velocities and normal functionals, one arbitrarily small common
perturbation preserves every nonzero normal sign and makes all the velocities
transverse to the nonempty members of a finite exceptional arrangement. From every
base point, the resulting incoming germs eventually avoid the arrangement,
simultaneously for all the velocities. The base point itself may be exceptional.
Applying the result to a union of arrangements allows further finite refinements.

Empty exceptions impose no constraint, and zero normal evaluations are
left unconstrained. No finite-dimensionality assumption is required.
The general fixed-direction germ results are available from
`TauCeti.Topology.Algebra.Affine.Germ`.

Adapted from `Mei/Geometry/Affine/IncomingGerm.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).
Affine point spaces and their vector spaces are independent.
-/

public section

open Set Filter Topology

namespace TauCeti.ExceptionalArrangement

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddTorsor V P]

/-- A single arbitrarily small perturbation preserves the nonzero normal signs
of finitely many velocities and makes their incoming germs generic from every
base point. The eventual bound is simultaneous in the velocities; it may depend
on the base point. Nonempty exceptions are also transverse to every perturbed
velocity. -/
theorem exists_norm_lt_forall_eventually_isGeneric
    (E : ExceptionalArrangement ℝ P) {ι κ : Type*} [Finite ι] [Finite κ]
    (v : ι → V) (m : κ → V →L[ℝ] ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : V, ‖r‖ < ε ∧
      (∀ i j, m j (v i) ≠ 0 → 0 < m j (v i + r) * m j (v i)) ∧
      (∀ i S, S ∈ E.exceptions → (S : Set P).Nonempty → v i + r ∉ S.direction) ∧
      ∀ x : P, ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ i, E.IsGeneric (t • (v i + r) +ᵥ x) := by
  classical
  let J := {a : ι × κ // m a.2 (v a.1) ≠ 0}
  let U : Set V := Metric.ball 0 ε ∩
    ⋂ a : J, {r | 0 < m a.1.2 (v a.1.1 + r) * m a.1.2 (v a.1.1)}
  have hU : IsOpen U := by
    refine Metric.isOpen_ball.inter (isOpen_iInter_of_finite fun a => ?_)
    exact isOpen_lt continuous_const (by fun_prop)
  have hzero : (0 : V) ∈ U := by
    refine ⟨by simpa using hε, mem_iInter.mpr fun a => ?_⟩
    simpa using mul_self_pos.mpr a.2
  let K := {S : E.exceptions // (S.1 : Set P).Nonempty}
  let A : ι × K → AffineSubspace ℝ V := fun a =>
    AffineSubspace.mk' (-v a.1) a.2.1.1.direction
  have hA : ∀ a, (A a).direction ≠ ⊤ := by
    intro a hd
    simp only [A, AffineSubspace.direction_mk'] at hd
    exact E.proper _ a.2.1.2
      ((AffineSubspace.direction_eq_top_iff_of_nonempty a.2.2).mp hd)
  have hex : ∃ r ∈ U, ∀ a, r ∉ A a := by
    by_contra! hcover
    obtain ⟨a, ha⟩ := AffineSubspace.exists_direction_le_of_forall_mem
      (⊤ : AffineSubspace ℝ V) A (by trivial) (hU.mem_nhds hzero)
      (fun y _ hy => hcover y hy)
    exact hA a (top_le_iff.mp (by simpa using ha))
  obtain ⟨r, hrU, hrA⟩ := hex
  have htrans : ∀ i S, S ∈ E.exceptions → (S : Set P).Nonempty →
      v i + r ∉ S.direction := by
    intro i S hS hne hmem
    apply hrA (i, ⟨⟨S, hS⟩, hne⟩)
    simpa [A, AffineSubspace.mem_mk', add_comm] using hmem
  refine ⟨r, by simpa using hrU.1, ?_, htrans, ?_⟩
  · intro i j hne
    exact mem_iInter.mp hrU.2 ⟨(i, j), hne⟩
  · intro x
    apply eventually_all.mpr
    intro i
    simp_rw [isGeneric_iff]
    apply E.exceptions.eventually_all.mpr
    intro S hS
    by_cases hne : (S : Set P).Nonempty
    · exact S.eventually_smul_vadd_notMem (htrans i S hS hne) x
    · exact Filter.Eventually.of_forall fun t ht => hne ⟨_, ht⟩

end TauCeti.ExceptionalArrangement
