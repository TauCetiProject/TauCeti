/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.EigenspaceMap
public import TauCeti.Algebra.Lie.Weights.Basic
public import TauCeti.Algebra.Lie.Weights.Borel

/-!
# The simple root values of a dominant neutral element lie in `{0, 1, 2}`

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero, let `H` be a splitting Cartan subalgebra and let `b` be a base of the root
system `LieAlgebra.IsKilling.rootSystem H`. Call `x : H` **dominant** when every simple root takes
a natural-number value at `x`.

If `(h, e, f)` is an `sl₂` triple whose neutral element `h` lies in `H` and is dominant, then every
simple root takes one of the values `0`, `1` or `2` at `h`
(`IsSl2Triple.root_apply_eq_zero_or_eq_one_or_eq_two`). Labelling each node of the Dynkin diagram
by this value gives the **weighted Dynkin diagram** of the triple. Because the simple roots span
the dual of `H`, the labels determine `h`, so the bound leaves only finitely many possible dominant
neutral elements in `H`.

## The argument

Suppose a simple root `α` has `α h = n ≥ 3`. A nonzero vector `y` of the root space `L_{-α}` has
`h`-eigenvalue `-n`, which is not a natural number, so `⁅e, y⁆ ≠ 0`
(`IsSl2Triple.disjoint_ker_toEnd_e_eigenspace`). On the other hand `e` lies in the
`2`-eigenspace of `ad h`, which is the sum of the root spaces `L_χ` with `χ h = 2`
(`LieModule.genWeightSpaceOf_eq_iSup_genWeightSpace`), and `⁅y, L_χ⁆ ⊆ L_{χ - α}`. If `χ - α` were
a root `γ`, then `γ h = 2 - n < 0` forces `γ` to be negative, while `χ h = 2 > 0` forces `χ` to be
positive, so `α = χ + (-γ)` would be a sum of two positive roots, which a simple root is not
(`TauCeti.root_ne_add_of_mem_support`). Hence every `L_{χ - α}` vanishes and `⁅e, y⁆ = 0`, a
contradiction.

The sign information used here comes from dominance alone: a dominant element takes natural values
on the positive roots (`TauCeti.exists_nat_root_apply_of_mem_posRoots`) and the negatives of
natural values on the negative ones (`TauCeti.exists_nat_root_apply_eq_neg_of_mem_negRoots`).

## Main results

* `IsSl2Triple.root_apply_eq_zero_or_eq_one_or_eq_two`: the simple root values of a dominant
  neutral element lie in `{0, 1, 2}`.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.5.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 7–9, Chapter VIII, §11.
-/

public section

open LieAlgebra LieModule LieAlgebra.IsKilling Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  {b : (rootSystem H).Base}

namespace TauCeti

/-- With `α` simple and `α x ≥ 3` at a dominant `x`, no root `χ` with `χ x = 2` has `χ - α` as a
weight: that would write `α` as the sum of the positive roots `χ` and `α - χ`. -/
private theorem genWeightSpace_neg_add_eq_bot {x : H}
    (hx : ∀ j ∈ b.support, ∃ n : ℕ, (j : Weight K H L) x = n) {i : H.root} (hi : i ∈ b.support)
    {n : ℕ} (hn : (i : Weight K H L) x = n) (h3 : 3 ≤ n) {χ : Weight K H L} (hχ : χ x = 2) :
    genWeightSpace L (⇑(-(i : Weight K H L)) + ⇑χ) = ⊥ := by
  by_contra hne
  let γ : Weight K H L := ⟨_, hne⟩
  have hγ : γ x = 2 - n := by
    simp only [γ, Weight.coe_weight_mk, Pi.add_apply, Weight.coe_neg, Pi.neg_apply, hn, hχ]
    ring
  have hχ0 : χ.IsNonZero := fun hz ↦ by
    have := congr_fun hz x
    simp [hχ] at this
  have hγ0 : γ.IsNonZero := fun hz ↦ by
    have hcast : ((n : ℕ) : K) = ((2 : ℕ) : K) := by
      have := congr_fun hz x
      rw [Pi.zero_apply, hγ] at this
      push_cast
      linear_combination -this
    have := Nat.cast_injective hcast
    omega
  let jχ : H.root := ⟨χ, by simpa [LieSubalgebra.root] using hχ0⟩
  let jγ : H.root := ⟨γ, by simpa [LieSubalgebra.root] using hγ0⟩
  -- `χ` is positive: on a negative root `x` would take a nonpositive value, not `2`
  have hposχ : jχ ∈ posRoots (rootSystem H) b := by
    refine (mem_posRoots_or_mem_negRoots (rootSystem H) b jχ).resolve_right fun hneg ↦ ?_
    obtain ⟨m, hm⟩ := exists_nat_root_apply_eq_neg_of_mem_negRoots hx hneg
    have hcast : ((m + 2 : ℕ) : K) = 0 := by
      have hm' : (2 : K) = -m := hχ ▸ hm
      push_cast
      linear_combination hm'
    exact absurd (Nat.cast_eq_zero.mp hcast) (by omega)
  -- `γ = χ - α` is negative: on a positive root `x` would take a natural value, not `2 - n < 0`
  have hnegγ : jγ ∈ negRoots (rootSystem H) b := by
    refine (mem_posRoots_or_mem_negRoots (rootSystem H) b jγ).resolve_left fun hpos ↦ ?_
    obtain ⟨m, hm⟩ := exists_nat_root_apply_of_mem_posRoots hx hpos
    have hcast : ((n + m : ℕ) : K) = ((2 : ℕ) : K) := by
      have hm' : (2 : K) - n = m := hγ ▸ hm
      push_cast
      linear_combination -hm'
    have := Nat.cast_injective hcast
    omega
  have hposγ := (reflectionPerm_self_mem_posRoots_iff_mem_negRoots (rootSystem H) b jγ).mpr hnegγ
  refine root_ne_add_of_mem_support hi ((mem_posRoots (rootSystem H) b jχ).mp hposχ)
    ((mem_posRoots (rootSystem H) b _).mp hposγ) ?_
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  ext y
  simp [jχ, jγ, γ]

end TauCeti

namespace IsSl2Triple

/-- **The simple root values of a dominant neutral element lie in `{0, 1, 2}`.** If the neutral
element `h` of an `sl₂` triple lies in the Cartan subalgebra `H` and every simple root takes a
natural value at `h`, then each simple root takes the value `0`, `1` or `2` at `h`. These values
label the weighted Dynkin diagram of the triple. -/
theorem root_apply_eq_zero_or_eq_one_or_eq_two {h : H} {e f : L} (t : IsSl2Triple (h : L) e f)
    (hh : ∀ j ∈ b.support, ∃ n : ℕ, (j : Weight K H L) h = n) {i : H.root}
    (hi : i ∈ b.support) :
    (i : Weight K H L) h = 0 ∨ (i : Weight K H L) h = 1 ∨ (i : Weight K H L) h = 2 := by
  obtain ⟨n, hn⟩ := hh i hi
  suffices n < 3 by interval_cases n <;> simp [hn]
  by_contra! h3
  -- a nonzero vector of the root space `L_{-α}`, which has `h`-eigenvalue `-n`
  obtain ⟨y, hy, hy0⟩ := (-(i : Weight K H L)).exists_ne_zero
  have hyh : y ∈ (toEnd K L L (h : L)).eigenspace (-(n : K)) := by
    rw [Module.End.mem_eigenspace_iff, toEnd_apply_apply]
    simpa [hn] using lie_eq_smul_of_mem_rootSpace hy h
  -- the weight `-n` is not a natural number, so `e` does not kill `y`
  have hdisj := t.disjoint_ker_toEnd_e_eigenspace (M := L) (μ := -(n : K)) fun m hm ↦ by
    have hcast : ((n + m : ℕ) : K) = 0 := by
      push_cast
      linear_combination -hm
    exact absurd (Nat.cast_eq_zero.mp hcast) (by omega)
  refine hy0 (Submodule.disjoint_def.mp hdisj y ?_ hyh)
  -- but `e` lies in the sum of the root spaces `L_χ` with `χ h = 2`, each killed by `ad y`
  have he : e ∈ ⨆ (χ : Weight K H L) (_ : χ h = 2), genWeightSpace L χ := by
    rw [← genWeightSpaceOf_eq_iSup_genWeightSpace, mem_genWeightSpaceOf]
    refine ⟨1, ?_⟩
    simp [t.lie_h_e_nsmul, two_smul]
  have hle : (⨆ (χ : Weight K H L) (_ : χ h = 2), genWeightSpace L χ).toSubmodule ≤
      LinearMap.ker (ad K L y) := by
    simp only [LieSubmodule.iSup_toSubmodule]
    refine iSup₂_le fun χ hχ m hm ↦ ?_
    have hmem := lie_mem_genWeightSpace_of_mem_genWeightSpace hy hm
    rw [TauCeti.genWeightSpace_neg_add_eq_bot hh hi hn h3 hχ, LieSubmodule.mem_bot] at hmem
    simpa using hmem
  have hye : ⁅y, e⁆ = 0 := by simpa using hle he
  rw [LinearMap.mem_ker, toEnd_apply_apply, ← lie_skew, hye, neg_zero]

end IsSl2Triple
