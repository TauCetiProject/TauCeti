/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Separating eigenspace summands

Suppose `p` is a sum `⨆ j ∈ s, W j` of subspaces on which an endomorphism `A` already
acts by scalars, one scalar `g j` per summand, and suppose the scalar `g k` of one distinguished
summand is attained by no other. Then that summand is *exactly* the `g k`-eigenspace of `A` inside
`p`: no eigenvector of eigenvalue `g k` hides in the other summands, because eigenspaces for
distinct eigenvalues are independent. This is how a weight space is recovered from an eigenspace of
a single operator once a decomposition separating the weights is available.

## Main results

* `TauCeti.biSup_inf_eigenspace_eq_self`: a summand whose scalar is attained only by itself is cut
  out by the corresponding eigenspace.
* `TauCeti.isCompl_eigenspace_one_neg_one`: the `1`- and `-1`-eigenspaces of an involution are
  complementary when `2` is nonzero in the scalar field.
-/

public section

namespace TauCeti

open Module

universe u v w

variable {K : Type u} {V : Type v} [CommRing K] [IsDomain K] [AddCommGroup V] [Module K V]
  [Module.IsTorsionFree K V]

/-- The `±1` eigenspaces of an involutive endomorphism of a vector space over a field in which
`2` is nonzero are complementary: `x` splits as
`2⁻¹ • (x + T x) + 2⁻¹ • (x - T x)`, and a vector in both eigenspaces satisfies `x = -x`. -/
theorem isCompl_eigenspace_one_neg_one {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (h2 : (2 : K) ≠ 0) {T : Module.End K V} (hT : Function.Involutive T) :
    IsCompl (T.eigenspace 1) (T.eigenspace (-1)) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [Module.End.mem_eigenspace_iff, one_smul] at hx
    rw [Module.End.mem_eigenspace_iff, neg_one_smul] at hx'
    have hxx : x = -x := hx.symm.trans hx'
    have h2x : (2 : K) • x = 0 := by
      rw [two_smul]
      calc x + x = x + -x := by rw [← hxx]
        _ = 0 := add_neg_cancel x
    exact (smul_eq_zero.mp h2x).resolve_left h2
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine Submodule.mem_sup.mpr
      ⟨(2 : K)⁻¹ • (x + T x), ?_, (2 : K)⁻¹ • (x - T x), ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, one_smul, map_smul, map_add, hT x, add_comm (T x) x]
    · rw [Module.End.mem_eigenspace_iff, map_smul, map_sub, hT x, neg_one_smul, ← smul_neg,
        neg_sub]
    · have hadd : x + T x + (x - T x) = (2 : K) • x := by
        rw [two_smul]
        abel
      rw [← smul_add, hadd, smul_smul, inv_mul_cancel₀ h2, one_smul]

/-- **Separated summands are cut out by their eigenspaces.** If every `W j`, for `j` in a set `s`,
consists of eigenvectors of `A` of eigenvalue `g j`, and if the scalar `g k` of a distinguished
index `k ∈ s` is attained by no other index of `s`, then meeting the sum `⨆ j ∈ s, W j` with the
`g k`-eigenspace of `A` returns `W k` exactly.

In particular no eigenvector of eigenvalue `g k` in the sum lies outside `W k`. -/
theorem biSup_inf_eigenspace_eq_self {ι : Type w} (A : Module.End K V) (W : ι → Submodule K V)
    (g : ι → K) {s : Set ι} (hW : ∀ j, j ∈ s → W j ≤ A.eigenspace (g j))
    {k : ι} (hk : k ∈ s)
    (hg : ∀ j ∈ s, j ≠ k → g j ≠ g k) :
    (⨆ j ∈ s, W j) ⊓ A.eigenspace (g k) = W k := by
  have hsplit : (⨆ j ∈ s, W j) = W k ⊔ ⨆ j ∈ s \ {k}, W j := by
    conv_lhs => rw [← Set.insert_sdiff_self_of_mem hk]
    rw [iSup_insert]
  have hle : (⨆ j ∈ s \ {k}, W j) ≤ ⨆ c ≠ g k, A.eigenspace c := by
    refine iSup₂_le fun j hj ↦ (hW j hj.1).trans ?_
    exact le_iSup₂ (f := fun (c : K) (_ : c ≠ g k) ↦ A.eigenspace c) (g j) (hg j hj.1 hj.2)
  have hdisj : Disjoint (⨆ j ∈ s \ {k}, W j) (A.eigenspace (g k)) :=
    ((A.eigenspaces_iSupIndep (g k)).mono_right hle).symm
  rw [hsplit, sup_inf_assoc_of_le _ (hW k hk), disjoint_iff.mp hdisj, sup_bot_eq]

end TauCeti
