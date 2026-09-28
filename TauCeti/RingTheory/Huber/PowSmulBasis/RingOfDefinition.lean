/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.PowSmulBasis.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.SubmodulesBasis

/-!
# Independence of the ring of definition in a finite-module topology

The neighbourhood basis `ϖⁿ • M₀` of a finite module over a Tate ring can be constructed
using different rings of definition, different finite lattices, and different
pseudouniformisers. All these choices yield the same topology. The comparison uses
boundedness of a ring of definition: one fixed power of `ϖ` sends all its scalars into
the other ring of definition.

This is the ring-of-definition comparison in Wedhorn's construction of the topology on
finite modules. It does not assert completeness or uniqueness among arbitrary module
topologies.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Proposition 6.18 and Remark 6.19.
-/

public section

open Filter
open scoped Topology Pointwise

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {M : Type*} [AddCommGroup M] [Module A M]

/-- A finitely generated `Q`-submodule can be scaled into a `P`-submodule when it lies in
the ambient `A`-span of the latter. Boundedness of `Q` makes the exponent uniform over
the coefficients of its generators. -/
theorem exists_pow_smul_mem_of_fg (P Q : PairOfDefinition A) {s : A}
    (hs : IsTopologicallyNilpotent s) (hsP : s ∈ P.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) (M₁ : Submodule Q.ringOfDefinition M)
    (hspan : (M₁ : Set M) ⊆ Submodule.span A (M₀ : Set M)) (hfg : M₁.FG) :
    ∃ k : ℕ, ∀ x ∈ M₁, s ^ k • x ∈ M₀ := by
  obtain ⟨G, hG⟩ := hfg
  let N := Submodule.span P.ringOfDefinition (G : Set M)
  have hNspan : (N : Set M) ⊆ Submodule.span A (M₀ : Set M) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem g hg => exact hspan (hG ▸ Submodule.subset_span hg)
    | zero => exact (Submodule.span A (M₀ : Set M)).zero_mem
    | add x y _ _ ihx ihy => exact (Submodule.span A (M₀ : Set M)).add_mem ihx ihy
    | smul a x _ ih => exact (Submodule.span A (M₀ : Set M)).smul_mem (a : A) ih
  obtain ⟨d, hd⟩ := P.exists_pow_smul_le hs hsP M₀ N hNspan
    (Submodule.fg_span G.finite_toSet)
  obtain ⟨j, hj⟩ := Q.isBounded_ringOfDefinition.exists_pow_mul_subset hs
    (P.isOpen_ringOfDefinition.mem_nhds P.ringOfDefinition.zero_mem)
  have hQ (a : Q.ringOfDefinition) : s ^ j * (a : A) ∈ P.ringOfDefinition := by
    apply hj
    exact ⟨s ^ j, by simp, a, a.property, rfl⟩
  have hgen (g : M) (h : g ∈ (G : Set M)) : s ^ d • g ∈ M₀ := by
    have hmem := hd (Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mpr
      ⟨g, Submodule.subset_span h, rfl⟩)
    simpa only [SetLike.mem_coe, Subring.smul_def, SubmonoidClass.coe_pow] using hmem
  have key : ∀ x ∈ M₁, ∀ a : Q.ringOfDefinition,
      s ^ (j + d) • ((a : A) • x) ∈ M₀ := by
    intro x hx
    rw [← hG] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
        intro a
        have h := M₀.smul_mem (⟨s ^ j * (a : A), hQ a⟩ : P.ringOfDefinition) (hgen g hg)
        convert h using 1
        simp only [Subring.smul_def, pow_add, mul_smul]
        simp only [smul_smul]
        congr 1
        ring
    | zero => intro a; simp
    | add x y _ _ ihx ihy =>
        intro a
        simpa [smul_add] using M₀.add_mem (ihx a) (ihy a)
    | smul b x _ ih =>
        intro a
        simpa [Subring.smul_def, smul_smul] using ih (a * b)
  refine ⟨j + d, fun x hx ↦ ?_⟩
  simpa using key x hx 1

/-- If a finitely generated `Q`-submodule lies in the `A`-span of a `P`-submodule, then
every power scaling of the latter contains a power scaling of the former. -/
theorem exists_pow_smul_subset_pow_smul (P Q : PairOfDefinition A) {s : A}
    (hs : IsTopologicallyNilpotent s) (hsP : s ∈ P.ringOfDefinition)
    (hsQ : s ∈ Q.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) (M₁ : Submodule Q.ringOfDefinition M)
    (hspan : (M₁ : Set M) ⊆ Submodule.span A (M₀ : Set M)) (hfg : M₁.FG)
    (n : ℕ) : ∃ k : ℕ,
      (((⟨s, hsQ⟩ : Q.ringOfDefinition) ^ k • M₁ :
        Submodule Q.ringOfDefinition M) : Set M) ⊆
        (((⟨s, hsP⟩ : P.ringOfDefinition) ^ n • M₀ :
          Submodule P.ringOfDefinition M) : Set M) := by
  obtain ⟨d, hd⟩ := P.exists_pow_smul_mem_of_fg Q hs hsP M₀ M₁ hspan hfg
  refine ⟨n + d, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  have hmem := M₀.pow_smul_mem_pow_smul hsP (hd y hy) n
  simpa only [SetLike.mem_coe, Subring.smul_def, SubmonoidClass.coe_pow, pow_add,
    mul_smul] using hmem

/-- The topology on a finite `A`-module defined by powers of a pseudouniformiser is independent
of the ring of definition, the finite spanning lattice, and the pseudouniformiser.

The pseudouniformisers `s ∈ P.ringOfDefinition` and `t ∈ Q.ringOfDefinition` need not lie in a
common ring of definition. -/
theorem submodulesBasis_pow_smul_topology_eq_of_ringOfDefinition
    (P Q : PairOfDefinition A) {s t : A} (hs : IsPseudoUniformizer s)
    (ht : IsPseudoUniformizer t) (hsP : s ∈ P.ringOfDefinition) (htQ : t ∈ Q.ringOfDefinition)
    (M₀ : Submodule P.ringOfDefinition M) (M₁ : Submodule Q.ringOfDefinition M)
    (hspan₀ : Submodule.span A (M₀ : Set M) = ⊤)
    (hspan₁ : Submodule.span A (M₁ : Set M) = ⊤)
    (hfg₀ : M₀.FG) (hfg₁ : M₁.FG) :
    (P.submodulesBasis_pow_smul hs hsP M₀ hspan₀).topology =
      (Q.submodulesBasis_pow_smul ht htQ M₁ hspan₁).topology := by
  have hsQ := hs.eventually_pow_mem_ringOfDefinition Q
  obtain ⟨m, huQ, hm⟩ := (hsQ.and (eventually_gt_atTop 0)).exists
  have hu : IsPseudoUniformizer (s ^ m) := by
    refine isPseudoUniformizer_iff.mpr ⟨hs.isUnit.pow m, ?_⟩
    simp_rw [IsTopologicallyNilpotent, ← pow_mul]
    exact hs.isTopologicallyNilpotent.comp
      (tendsto_atTop_mono (fun n ↦ Nat.le_mul_of_pos_left n hm) tendsto_id)
  have huP : s ^ m ∈ P.ringOfDefinition := pow_mem hsP m
  refine (P.submodulesBasis_pow_smul_topology_eq_of_isPseudoUniformizer hs hu hsP huP M₀
    hspan₀).trans (Eq.trans ?_ (Q.submodulesBasis_pow_smul_topology_eq_of_isPseudoUniformizer
      hu ht huQ htQ M₁ hspan₁))
  apply IsTopologicalAddGroup.ext inferInstance inferInstance
  apply (P.submodulesBasis_pow_smul hu huP M₀ hspan₀).hasBasis_nhds_zero.ext
    (Q.submodulesBasis_pow_smul hu huQ M₁ hspan₁).hasBasis_nhds_zero
  · intro n _
    obtain ⟨k, hk⟩ := P.exists_pow_smul_subset_pow_smul Q hu.isTopologicallyNilpotent
      huP huQ M₀ M₁ (by rw [hspan₀]; exact Set.subset_univ _) hfg₁ n
    exact ⟨k, trivial, hk⟩
  · intro n _
    obtain ⟨k, hk⟩ := Q.exists_pow_smul_subset_pow_smul P hu.isTopologicallyNilpotent
      huQ huP M₁ M₀ (by rw [hspan₁]; exact Set.subset_univ _) hfg₀ n
    exact ⟨k, trivial, hk⟩

end TauCeti.Huber.PairOfDefinition

end
