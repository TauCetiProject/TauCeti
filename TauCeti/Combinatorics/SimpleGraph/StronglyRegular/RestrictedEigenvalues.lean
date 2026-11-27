/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.StronglyRegular.Basic

import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.LinearAlgebra.Matrix.Transpose

/-!
# Restricted eigenvalues of a strongly regular graph

The restricted eigenvalues are the adjacency eigenvalues with a nonzero eigenvector of
coordinate sum zero. For a regular graph these are the eigenvalues of the restriction to the
orthogonal complement of the all-ones vector. The degree can itself be a restricted eigenvalue,
as in a disjoint union of equally sized cliques.

A regular graph with both an edge and a distinct nonadjacent pair is strongly regular exactly
when it has two distinct restricted eigenvalues.

## References

* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Universitext, Springer, 2012,
  Theorem 9.1.2 (i) and (iii), p. 117, formulated here for regular graphs.
-/

public section

open Matrix Polynomial WithLp
open scoped BigOperators InnerProductSpace Polynomial

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

/-- The real adjacency eigenvalues of a graph with a nonzero eigenvector whose entries sum to
zero. -/
def restrictedEigenvalues (G : SimpleGraph V) [DecidableRel G.Adj] : Set ℝ :=
  {t | ∃ u : V → ℝ, u ≠ 0 ∧ (∑ i, u i) = 0 ∧ G.adjMatrix ℝ *ᵥ u = t • u}

/-- A restricted eigenvalue has a nonzero adjacency eigenvector of coordinate sum zero. -/
theorem mem_restrictedEigenvalues_iff {t : ℝ} :
    t ∈ G.restrictedEigenvalues ↔
      ∃ u : V → ℝ, u ≠ 0 ∧ (∑ i, u i) = 0 ∧ G.adjMatrix ℝ *ᵥ u = t • u := Iff.rfl

local notation "A" => G.adjMatrix ℝ
local notation "J" => (Matrix.of (fun _ _ ↦ (1 : ℝ)) : Matrix V V ℝ)

/-- A polynomial in the adjacency matrix that annihilates the restricted eigenvectors
is a scalar multiple of the all-ones matrix. -/
private theorem exists_aeval_adjMatrix_eq_smul [DecidableEq V]
    (hk : G.IsRegularOfDegree k) (p : ℝ[X])
    (h : ∀ t ∈ G.restrictedEigenvalues, p.IsRoot t) :
    ∃ d : ℝ, aeval A p = d • J := by
  let e : EuclideanSpace ℝ V := toLp 2 (1 : V → ℝ)
  let W : Submodule ℝ (EuclideanSpace ℝ V) := (ℝ ∙ e)ᗮ
  have hW (u : EuclideanSpace ℝ V) : u ∈ W ↔ ∑ i, (ofLp u) i = 0 := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, EuclideanSpace.inner_eq_star_dotProduct]
    simp [e, dotProduct]
  have hA := isSymm_adjMatrix (G := G) (α := ℝ)
  let T := toEuclideanLin A
  have hT : T.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr (isHermitian_iff_isSymm.mpr hA)
  have he : T e = (k : ℝ) • e := by
    apply WithLp.ofLp_injective 2
    ext i
    simp [T, e, hk.degree_eq i]
  have hInv : ∀ u ∈ W, T u ∈ W := by
    intro u hu
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, ← hT e u, he, real_inner_smul_left,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp hu, mul_zero]
  let M : Matrix V V ℝ := aeval A p
  let hS := hT.restrict_invariant hInv
  let basis := hS.eigenvectorBasis rfl
  have hzero : M.toEuclideanLin ∘ₗ W.subtype = 0 := by
    apply basis.toBasis.ext
    intro i
    let t := hS.eigenvalues rfl i
    have hv := hS.hasEigenvector_eigenvectorBasis rfl i
    let u : EuclideanSpace ℝ V := basis i
    have ht : T u = t • u := by
      simpa only [LinearMap.restrict_apply, SetLike.val_smul, RCLike.ofReal_real_eq_id, id_eq] using
        congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hv.1)
    have hne : ofLp u ≠ 0 := by simpa [u] using hv.2
    have hu : A *ᵥ ofLp u = t • ofLp u := by
      simpa [T] using congrArg ofLp ht
    have hr := h t (mem_restrictedEigenvalues_iff.mpr ⟨_, hne, (hW u).mp (basis i).property, hu⟩)
    have hp := Module.End.aeval_apply_of_mem_apply_eq_smul (p := p) ht
    have hM' : aeval T p = M.toEuclideanLin :=
      aeval_algHom_apply (toLpLinAlgEquiv 2).toAlgHom A p
    simpa only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.zero_apply, hM', hr.eq_zero, zero_smul] using hp
  -- Differences of coordinate vectors lie in W. All columns of M agree and M is symmetric.
  have hcol (i j l : V) : M i j = M i l := by
    let x : V → ℝ := Pi.single j 1 - Pi.single l 1
    have hx : toLp 2 x ∈ W := (hW _).mpr (by simp [x, Finset.sum_sub_distrib])
    have hz := LinearMap.congr_fun hzero ⟨toLp 2 x, hx⟩
    have hi := congrArg (fun w : EuclideanSpace ℝ V ↦ ofLp w i) hz
    simpa [x, mulVec_sub, col_apply, sub_eq_zero] using hi
  have hM : M.IsSymm := (aeval_transpose _ p).symm.trans (congrArg (fun m ↦ aeval m p) hA.eq)
  by_cases hV : Nonempty V
  · obtain ⟨v⟩ := hV
    refine ⟨M v v, Matrix.ext fun i j ↦ ?_⟩
    simpa using (hcol i j v).trans ((hM.apply v i).trans (hcol v i v))
  · exact ⟨0, Matrix.ext fun i _ ↦ (hV ⟨i⟩).elim⟩

private theorem isRoot_of_mem_restrictedEigenvalues_of_aeval_eq_smul [DecidableEq V]
    {p : ℝ[X]} {d t : ℝ} (hp : aeval A p = d • J) (ht : t ∈ G.restrictedEigenvalues) :
    p.IsRoot t := by
  obtain ⟨u, hne, hsum, hu⟩ := mem_restrictedEigenvalues_iff.mp ht
  have he : Matrix.toLinAlgEquiv' A u = t • u := by simpa using hu
  have hvalue := Module.End.aeval_apply_of_mem_apply_eq_smul (p := p) he
  have hcomm := aeval_algHom_apply Matrix.toLinAlgEquiv'.toAlgHom A p
  simp only [AlgEquiv.toAlgHom_apply] at hcomm
  rw [hcomm, Matrix.toLinAlgEquiv'_apply, hp] at hvalue
  have hzero : (d • J) *ᵥ u = 0 := by
    ext i
    simp [mulVec, dotProduct, ← Finset.mul_sum, hsum]
  exact (smul_eq_zero.mp (hvalue.symm.trans hzero)).resolve_right hne

private theorem restrictedEigenvalues_nontrivial (hk : G.IsRegularOfDegree k)
    (htop : G ≠ ⊤) (hbot : G ≠ ⊥) : G.restrictedEigenvalues.Nontrivial := by
  classical
  rw [← Set.not_subsingleton_iff]
  intro hs
  obtain ⟨t, ht⟩ : ∃ t, ∀ r ∈ G.restrictedEigenvalues, r = t := by
    rcases hs.eq_empty_or_singleton with he | ⟨t, ht⟩
    · exact ⟨0, by simp [he]⟩
    · exact ⟨t, by simp [ht]⟩
  obtain ⟨d, hd⟩ := exists_aeval_adjMatrix_eq_smul hk (X - C t) fun r hr ↦ by
    simp [IsRoot, ht r hr]
  obtain ⟨i, j, hij⟩ := ne_bot_iff_exists_adj.mp hbot
  obtain ⟨v, w, hvw, hn⟩ := ne_top_iff_exists_not_adj.mp htop
  have hd₁ : 1 = d := by
    simpa [Algebra.algebraMap_eq_smul_one, hij, hij.ne] using
      congrArg (fun m : Matrix V V ℝ ↦ m i j) hd
  have hd₀ : 0 = d := by
    simpa [Algebra.algebraMap_eq_smul_one, hn, hvw] using congrArg (fun m : Matrix V V ℝ ↦ m v w) hd
  exact one_ne_zero (hd₁.trans hd₀.symm)

/-- A regular graph with both an edge and a pair of distinct nonadjacent vertices is strongly
regular exactly when it has two distinct restricted eigenvalues. -/
theorem exists_isSRGWith_iff_ncard_restrictedEigenvalues
    (hk : G.IsRegularOfDegree k) (htop : G ≠ ⊤) (hbot : G ≠ ⊥) :
    (∃ ℓ μ : ℕ, G.IsSRGWith (Fintype.card V) k ℓ μ) ↔ G.restrictedEigenvalues.ncard = 2 := by
  classical
  rw [Set.ncard_eq_two]
  constructor
  · rintro ⟨ℓ, μ, h⟩
    let a := (ℓ : ℝ) - μ
    let b := (k : ℝ) - μ
    let p := X ^ 2 - a • X - C b
    have hA := (isSRGWith_iff_adjMatrix_sq_eq (R := ℝ)).mp h |>.2
    have hp : aeval A p = (μ : ℝ) • J := by
      simp only [p, map_sub, map_pow, map_smul, aeval_X, aeval_C,
        Algebra.algebraMap_eq_smul_one, hA, a, b]
      module
    have hroot (t : ℝ) (ht : t ∈ G.restrictedEigenvalues) : t ^ 2 - a * t - b = 0 := by
      simpa [p, IsRoot, eval_smul, smul_eq_mul] using
        isRoot_of_mem_restrictedEigenvalues_of_aeval_eq_smul hp ht
    obtain ⟨r, s, hrs, hpair⟩ := (restrictedEigenvalues_nontrivial hk htop hbot).pair_subset
    have hr := hpair (by simp : r ∈ ({r, s} : Set ℝ))
    have hs := hpair (by simp : s ∈ ({r, s} : Set ℝ))
    refine ⟨r, s, hrs, Set.Subset.antisymm ?_ hpair⟩
    intro t ht
    have hfactor : (r - s) * (r + s - a) = 0 := by
      linear_combination hroot r hr - hroot s hs
    have hsum := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hrs)
    have hprod : (t - r) * (t - s) = 0 := by
      linear_combination hroot t ht - hroot r hr - (t - r) * hsum
    simpa [sub_eq_zero] using mul_eq_zero.mp hprod
  · rintro ⟨r, s, _, hs⟩
    let p : ℝ[X] := X ^ 2 - (r + s) • X + C (r * s)
    obtain ⟨d, hd⟩ := exists_aeval_adjMatrix_eq_smul hk p (by
      intro t ht
      rw [hs, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl <;> simp [p, IsRoot, eval_smul, smul_eq_mul] <;> ring)
    have hmatrix : A ^ 2 = (r + s) • A + (-(r * s)) • (1 : Matrix V V ℝ) + d • J := by
      rw [← hd]
      simp only [p, map_sub, map_add, map_pow, map_smul, aeval_X, aeval_C,
        Algebra.algebraMap_eq_smul_one]
      module
    obtain ⟨d', ℓ, μ, h⟩ := (exists_isSRGWith_iff_exists_adjMatrix_sq_eq (R := ℝ)).mpr
      ⟨r + s, -(r * s), d, hmatrix⟩
    obtain ⟨i, _, _⟩ := ne_bot_iff_exists_adj.mp hbot
    have hdk : d' = k := (h.regular i).symm.trans (hk i)
    exact ⟨ℓ, μ, hdk ▸ h⟩

end SimpleGraph
