/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Exists
public import TauCeti.RepresentationTheory.Irreducible

/-!
# Irreducible representations and commutative subgroups of finite index

Over an algebraically closed field, a finite-dimensional irreducible representation of a group `G`
with a commutative subgroup `A` of finite index has dimension at most the index `[G : A]`.

A common eigenvector `v` of `A` exists
(`TauCeti.exists_unitHom_jointEigenvector_of_pairwise_commute_of_isAlgClosed`). Writing an
element of `G` as `g = r a` with `r` a chosen representative of the coset `g A` and `a ∈ A`, the
vector `g v` is a multiple of `r v`, so the span of the vectors `r v`, one for each coset, is a
nonzero subrepresentation. In an irreducible representation it is everything.

## Main results

* `Representation.IsIrreducible.finrank_le_index`: an irreducible finite-dimensional
  representation over an algebraically closed field has dimension at most the index of any
  commutative subgroup of finite index.

## References

* J.-P. Serre, *Linear representations of finite groups*, Graduate Texts in Mathematics 42,
  Springer (1977), §3.1, Corollary of Theorem 9.
-/

public section

open Module

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- **Irreducible representations are no bigger than the index of a commutative subgroup.** Over
an algebraically closed field, a finite-dimensional irreducible representation of `G` has dimension
at most `[G : A]` for every commutative subgroup `A` of finite index: the translates of a common
eigenvector of `A` by representatives of the cosets of `A` span it. -/
theorem IsIrreducible.finrank_le_index [IsAlgClosed k] [FiniteDimensional k V]
    {ρ : Representation k G V} (h : ρ.IsIrreducible) (A : Subgroup G) [IsMulCommutative A]
    [A.FiniteIndex] : finrank k V ≤ A.index := by
  have := h.nontrivial
  obtain ⟨χ, v, hv0, hv⟩ :=
    TauCeti.exists_unitHom_jointEigenvector_of_pairwise_commute_of_isAlgClosed
      (ρ.comp A.subtype) fun a b _ ↦ Commute.map (IsMulCommutative.is_comm.comm a b) _
  let r : G ⧸ A → V := fun q ↦ ρ q.out v
  -- every translate of `v` is a multiple of the translate by a coset representative
  have hmem (g : G) : ρ g v ∈ Submodule.span k (Set.range r) := by
    obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul A g
    have hg : g = (g : G ⧸ A).out * a⁻¹ := by rw [ha, Subgroup.coe_inv, mul_inv_cancel_right]
    have hva : ρ ((a⁻¹ : A) : G) v = (χ a⁻¹ : k) • v := hv a⁻¹
    rw [hg, map_mul, mul_apply_eq_comp, hva, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  let σ : Subrepresentation ρ :=
    { toSubmodule := Submodule.span k (Set.range r)
      apply_mem_toSubmodule := fun g x hx ↦ by
        refine (Submodule.span_le (p := (Submodule.span k (Set.range r)).comap (ρ g))).mpr
          ?_ hx
        rintro _ ⟨q, rfl⟩
        simpa [r, ← mul_apply_eq_comp, ← map_mul] using hmem (g * q.out) }
  have hσ : σ = ⊤ := by
    refine (h.eq_bot_or_eq_top σ).resolve_left fun hbot ↦ hv0 ?_
    have hmem' : v ∈ σ.toSubmodule := by simpa only [map_one, one_apply_eq_self] using hmem 1
    rw [hbot, Subrepresentation.toSubmodule_bot, Submodule.mem_bot] at hmem'
    exact hmem'
  have htop : Submodule.span k (Set.range r) = ⊤ := by
    simpa [σ] using congrArg Subrepresentation.toSubmodule hσ
  have := A.fintypeQuotientOfFiniteIndex
  calc finrank k V = finrank k (⊤ : Submodule k V) := (finrank_top k V).symm
    _ = finrank k (Submodule.span k (Set.range r)) := by rw [htop]
    _ ≤ Fintype.card (G ⧸ A) := finrank_range_le_card r
    _ = A.index := by rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end Representation
