/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import TauCeti.LinearAlgebra.Eigenspace.Involution

/-!
# Separating eigenspace summands

Fix an endomorphism `A` and an exponent `n : ℕ∞`. Suppose `p` is a sum `⨆ j ∈ s, W j` of
subspaces with each `W j` contained in the generalized eigenspace `A.genEigenspace (g j) n`, and
suppose the scalar `g k` of one distinguished summand is attained by no other. Then that summand is
*exactly* the part of `p` lying in `A.genEigenspace (g k) n`: over a domain, and for a torsion-free
module, generalized eigenspaces of a fixed exponent for distinct scalars are independent. For
`n = 1` the summands are subspaces on which `A` acts by the scalars `g j`, and the summand is cut
out by the `g k`-eigenspace; for `n = ⊤` the summands lie in maximal generalized eigenspaces. This
is how a weight space is recovered from an eigenspace of a single operator once a decomposition
separating the weights is available.

The two `pow_sub_smul_one` lemmas serve the situation where the ambient subspace is an arbitrary
`f`-invariant submodule `N` rather than a sum of the summands. If `u + w ∈ N`, where `f u = ν • u`
and `(f - μ • 1) ^ k` kills `w`, then applying `(f - μ • 1) ^ k` stays inside `N` and leaves
`(ν - μ) ^ k • u`; so `u ∈ N` as soon as `ν - μ` is a unit.

## Main results

* `Module.End.pow_sub_smul_one_mem`: a submodule stable under `f` is stable under every power of
  `f - μ • 1`.
* `Module.End.pow_sub_smul_one_apply_of_apply_eq_smul`: an eigenvector of `f` of eigenvalue `ν` is
  scaled by `(ν - μ) ^ k` under `(f - μ • 1) ^ k`.
* `Module.End.biSup_inf_genEigenspace_eq_of_mem`: a summand whose scalar is attained only by
  itself is cut out of the sum by the corresponding generalized eigenspace.
* `Module.End.genEigenspace_eq_of_iSup_eq_top` and
  `Module.End.genEigenspace_eq_bot_of_iSup_eq_top`: if the summands span the whole space, every
  distinct-scalar summand is a generalized eigenspace and every scalar outside their range has
  trivial generalized eigenspace.
* `Module.End.eq_zero_of_apply_eq_smul_of_span_eq_top`: an eigenvector whose eigenvalue does not
  occur in a spanning family of eigenvectors is zero.
* `TauCeti.isCompl_eigenspace_one_neg_one`: the `1`- and `-1`-eigenspaces of an involution are
  complementary over a commutative ring in which `2` is a unit.
-/

public section

universe u v w

variable {K : Type u} {V : Type v} [CommRing K] [AddCommGroup V] [Module K V]

/-- A submodule stable under an endomorphism `f` is stable under every power of `f - μ • 1`. -/
theorem Module.End.pow_sub_smul_one_mem {f : Module.End K V} {P : Submodule K V}
    (hP : ∀ m ∈ P, f m ∈ P) (μ : K) (k : ℕ) :
    ∀ m ∈ P, ((f - μ • (1 : Module.End K V)) ^ k) m ∈ P := by
  intro m hm
  rw [FunLike.coe_pow_eq_iterate]
  have hmaps : Set.MapsTo (f - μ • (1 : Module.End K V)) P P :=
    fun x hx => P.sub_mem (hP x hx) (P.smul_mem μ hx)
  exact hmaps.iterate k hm

/-- An eigenvector of `f` with eigenvalue `ν` is an eigenvector of every power of `f - μ • 1`, with
eigenvalue `(ν - μ) ^ k`. -/
theorem Module.End.pow_sub_smul_one_apply_of_apply_eq_smul {f : Module.End K V} {μ ν : K} {v : V}
    (hv : f v = ν • v) (k : ℕ) :
    ((f - μ • (1 : Module.End K V)) ^ k) v = (ν - μ) ^ k • v := by
  simpa using Module.End.aeval_apply_of_mem_apply_eq_smul (p := Polynomial.X ^ k)
    (by simp [hv, sub_smul] : (f - μ • (1 : Module.End K V)) v = (ν - μ) • v)

namespace TauCeti

open Module

/-- The `±1` eigenspaces of an involutive endomorphism of a module over a commutative ring in
which `2` is a unit are complementary. -/
theorem isCompl_eigenspace_one_neg_one (h2 : IsUnit (2 : K)) {T : Module.End K V}
    (hT : Function.Involutive T) :
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
    exact h2.smul_eq_zero.mp h2x
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    let := h2.invertible
    exact Submodule.mem_sup.mpr
      ⟨_, (Module.End.eigenProjOfInvolutive hT (one_mul 1) x).property, _,
        (Module.End.eigenProjOfInvolutive hT ((neg_mul_neg (1 : K) 1).trans
            (one_mul 1)) x).property,
        Module.End.eigenProjOfInvolutive_add_eigenProjOfInvolutive_neg hT _ _ x⟩

end TauCeti

namespace Module.End

variable [IsDomain K] [Module.IsTorsionFree K V]

/-- **Separated summands are cut out by their generalized eigenspaces.** Fix an exponent
`n : ℕ∞`. If every `W j`, for `j` in a set `s`, lies in the generalized eigenspace
`A.genEigenspace (g j) n`, and if the scalar `g k` of a distinguished index `k ∈ s` is attained by
no other index of `s`, then meeting the sum `⨆ j ∈ s, W j` with `A.genEigenspace (g k) n` returns
`W k` exactly: an element of the sum that lies in `A.genEigenspace (g k) n` already lies in `W k`.
For `n = 1` the hypotheses say that `A` acts on each `W j` as multiplication by `g j`, and the
conclusion is about the `g k`-eigenspace. -/
theorem biSup_inf_genEigenspace_eq_of_mem {ι : Type w} (A : Module.End K V)
    (W : ι → Submodule K V) (g : ι → K) {n : ℕ∞} {s : Set ι}
    (hW : ∀ j, j ∈ s → W j ≤ A.genEigenspace (g j) n) {k : ι} (hk : k ∈ s)
    (hg : ∀ j ∈ s, j ≠ k → g j ≠ g k) :
    (⨆ j ∈ s, W j) ⊓ A.genEigenspace (g k) n = W k := by
  have hsplit : (⨆ j ∈ s, W j) = W k ⊔ ⨆ j ∈ s \ {k}, W j := by
    conv_lhs => rw [← Set.insert_sdiff_self_of_mem hk]
    rw [iSup_insert]
  have hle : (⨆ j ∈ s \ {k}, W j) ≤ ⨆ c ≠ g k, A.genEigenspace c n := by
    refine iSup₂_le fun j hj ↦ (hW j hj.1).trans ?_
    exact le_iSup₂ (f := fun (c : K) (_ : c ≠ g k) ↦ A.genEigenspace c n) (g j) (hg j hj.1 hj.2)
  have hdisj : Disjoint (⨆ j ∈ s \ {k}, W j) (A.genEigenspace (g k) n) :=
    ((A.independent_genEigenspace n (g k)).mono_right hle).symm
  rw [hsplit, sup_inf_assoc_of_le _ (hW k hk), disjoint_iff.mp hdisj, sup_bot_eq]

/-- **Summands of a spanning family with distinct scalars are generalized eigenspaces.** Fix an
exponent `n : ℕ∞`. If the `W j` span `V`, every `W j` lies in the generalized eigenspace
`A.genEigenspace (g j) n`, and `g` is injective, then `A.genEigenspace (g k) n` is exactly `W k`.
For `n = 1` this says that the `g k`-eigenspace of `A` is `W k`. -/
theorem genEigenspace_eq_of_iSup_eq_top {ι : Type w} (A : Module.End K V)
    {W : ι → Submodule K V} {g : ι → K} {n : ℕ∞} (hW : ∀ j, W j ≤ A.genEigenspace (g j) n)
    (htop : ⨆ j, W j = ⊤) (hg : Function.Injective g) (k : ι) :
    A.genEigenspace (g k) n = W k :=
  (congrFun (((A.independent_genEigenspace n).comp hg).le_iff_eq_of_iSup_eq_top htop |>.mp hW)
    k).symm

/-- **Scalars outside a spanning family of generalized eigenspaces have trivial generalized
eigenspace.** Fix an exponent `n : ℕ∞`. If the `W j` span `V` and every `W j` lies in the
generalized eigenspace `A.genEigenspace (g j) n`, then `A.genEigenspace μ n = ⊥` for every scalar
`μ` outside `Set.range g`. -/
theorem genEigenspace_eq_bot_of_iSup_eq_top {ι : Type w} (A : Module.End K V)
    {W : ι → Submodule K V} {g : ι → K} {n : ℕ∞} (hW : ∀ j, W j ≤ A.genEigenspace (g j) n)
    (htop : ⨆ j, W j = ⊤) {μ : K} (hμ : μ ∉ Set.range g) :
    A.genEigenspace μ n = ⊥ := by
  have hle : ⊤ ≤ ⨆ (c : K) (_ : c ≠ μ), A.genEigenspace c n :=
    htop ▸ iSup_le fun j ↦ (hW j).trans (le_iSup₂_of_le (g j) (fun h ↦ hμ ⟨j, h⟩) le_rfl)
  exact disjoint_top.mp ((A.independent_genEigenspace n μ).mono_right hle)

/-- **An eigenvector whose eigenvalue misses a spanning family of eigenvectors is zero.** If
`V` is spanned by vectors `b j` satisfying `A (b j) = g j • b j`, then any vector `v` with
`A v = μ • v` and `∀ j, g j ≠ μ` vanishes. -/
theorem eq_zero_of_apply_eq_smul_of_span_eq_top {ι : Type w} (A : Module.End K V)
    {b : ι → V} (hspan : Submodule.span K (Set.range b) = ⊤) {g : ι → K}
    (hb : ∀ j, A (b j) = g j • b j) {μ : K} {v : V}
    (hv : A v = μ • v) (hμ : ∀ j, g j ≠ μ) : v = 0 := by
  have hbot : A.genEigenspace μ 1 = ⊥ :=
    A.genEigenspace_eq_bot_of_iSup_eq_top (W := fun j ↦ Submodule.span K {b j})
      (fun j ↦ (Submodule.span_singleton_le_iff_mem _ _).mpr (mem_eigenspace_iff.mpr (hb j)))
      (by rwa [← Submodule.span_range_eq_iSup]) (by rintro ⟨j, rfl⟩; exact hμ j rfl)
  simpa [hbot] using (mem_eigenspace_iff.mpr hv : v ∈ A.genEigenspace μ 1)

end Module.End
