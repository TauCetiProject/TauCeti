/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Normed.Affine.Generic

/-!
# Generic incoming affine germs

For finitely many velocities and normal functionals, one arbitrarily small common
perturbation preserves every nonzero normal sign and makes all the velocities
transverse to the nonempty members of a finite exceptional arrangement. From every
base point, the resulting incoming germs eventually avoid the arrangement,
simultaneously for all the velocities. The base point itself may be exceptional.
Applying the result to a union of arrangements allows further finite refinements.

For affine families whose images together with their germ directions cover the
target, one can instead refine the source arrangement and retain the exact
straight germs. Proper affine preimages exclude parallel exceptions; transverse
exceptions are left immediately. This also applies when an affine map collapses
the source onto a hyperplane contained in the target arrangement.

The construction uses `AffineSubspace.exists_direction_le_of_forall_mem` to avoid
finitely many translates of the exceptional directions, without requiring finite
dimensionality. Empty exceptions impose no constraint, and zero normal evaluations
are deliberately left unconstrained. The source-refinement argument uses Mathlib's
`AffineSubspace.comap` and `vadd_mem_iff_mem_of_mem_direction`.

Adapted from `Mei/Geometry/Affine/IncomingGerm.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).
Affine point spaces and their vector spaces are independent.
-/

public section

open Set Filter Topology

namespace AffineSubspace

variable {k V P : Type*} [Field k] [LinearOrder k]
  [TopologicalSpace k] [T1Space k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- A transverse affine germ eventually avoids an affine subspace, even
when its base point lies in that subspace. -/
theorem eventually_smul_vadd_notMem (S : AffineSubspace k P)
    {v : V} (hv : v ∉ S.direction) (x : P) :
    ∀ᶠ t : k in 𝓝[>] 0, t • v +ᵥ x ∉ S := by
  have h := S.subsingleton_preimage_lineMap (x := x) (y := v +ᵥ x)
    (by simpa using hv)
  simpa only [Set.mem_preimage, AffineMap.lineMap_vadd_apply, AffineSubspace.mem_coe] using
    h.finite.eventually_cofinite_notMem.filter_mono
      ((nhdsGT_le_nhdsNE (0 : k)).trans (nhdsNE_le_cofinite 0))

end AffineSubspace

namespace TauCeti.ExceptionalArrangement

section AffineFamilies

variable {k U V P Q ι : Type*} [Field k] [LinearOrder k]
  [TopologicalSpace k] [T1Space k] [AddCommGroup U] [Module k U] [AddTorsor U P]
  [AddCommGroup V] [Module k V] [AddTorsor V Q] [Finite ι]

/-- If each affine family together with its germ direction covers the target,
one exceptional arrangement in the source makes all its straight germs generic.
The affine maps need not be surjective, and no perturbation of the directions
or finite-dimensionality assumption is required. -/
theorem exists_forall_eventually_isGeneric_smul_vadd
    (E : ExceptionalArrangement k Q) (g : ι → P →ᵃ[k] Q) (v : ι → V)
    (hg : ∀ j, Function.Surjective (fun z : P × k => z.2 • v j +ᵥ g j z.1)) :
    ∃ F : ExceptionalArrangement k P, ∀ x, F.IsGeneric x →
      ∀ᶠ t : k in 𝓝[>] 0, ∀ j, E.IsGeneric (t • v j +ᵥ g j x) := by
  classical
  let := Fintype.ofFinite ι
  let F : ExceptionalArrangement k P :=
    ⟨((Finset.univ.product E.exceptions).image
      (fun z : ι × AffineSubspace k Q => z.2.comap (g z.1))).erase ⊤,
      fun _ h => (Finset.mem_erase.mp h).1⟩
  refine ⟨F, fun x hx => eventually_all.mpr fun j => ?_⟩
  simp_rw [isGeneric_iff]
  apply E.exceptions.eventually_all.mpr
  intro S hS
  by_cases hv : v j ∈ S.direction
  · have hproper : S.comap (g j) ≠ ⊤ := by
      intro htop
      apply E.proper S hS
      apply top_unique
      intro y _
      obtain ⟨⟨z, t⟩, rfl⟩ := hg j y
      apply S.vadd_mem_of_mem_direction (S.direction.smul_mem t hv)
      exact AffineSubspace.mem_comap.mp (htop ▸ AffineSubspace.mem_top k U z)
    have hbase : g j x ∉ S := by
      intro hmem
      apply (isGeneric_iff.mp hx) (S.comap (g j))
      · exact Finset.mem_erase.mpr ⟨hproper, Finset.mem_image.mpr
          ⟨(j, S), Finset.mem_product.mpr ⟨Finset.mem_univ _, hS⟩, rfl⟩⟩
      · exact AffineSubspace.mem_comap.mpr hmem
    exact Eventually.of_forall fun t ht => hbase
      ((S.vadd_mem_iff_mem_of_mem_direction (S.direction.smul_mem t hv)).mp ht)
  · exact S.eventually_smul_vadd_notMem hv (g j x)

end AffineFamilies

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
