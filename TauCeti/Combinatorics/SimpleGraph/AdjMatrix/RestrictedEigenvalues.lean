/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.Combinatorics.SimpleGraph.AdjMatrix.Basic

import Mathlib.Analysis.Matrix.Hermitian
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.Polynomial
import TauCeti.LinearAlgebra.Matrix.Transpose

/-!
# Restricted adjacency eigenvalues

Restricted eigenvalues have an adjacency eigenvector of coordinate sum zero. For a regular
graph, they form the spectrum of the restriction to the orthogonal complement of the all-ones
vector. The degree can itself be restricted, as in a disjoint union of equally sized cliques.
-/

public section

open Matrix Polynomial WithLp
open scoped BigOperators InnerProductSpace Polynomial

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

local notation "A" => G.adjMatrix ℝ
local notation "e" => toLp 2 (1 : V → ℝ)
local notation "W" => (ℝ ∙ e)ᗮ
local notation "J" => (Matrix.of (fun _ _ ↦ (1 : ℝ)) : Matrix V V ℝ)

private theorem mem_orthogonal_ones_iff (u : EuclideanSpace ℝ V) :
    u ∈ W ↔ ∑ i, (ofLp u) i = 0 := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct]

/-- The real adjacency eigenvalues of a graph with a nonzero eigenvector whose entries sum to
zero. -/
noncomputable def restrictedEigenvalues (G : SimpleGraph V) [DecidableRel G.Adj] : Set ℝ :=
  letI := Classical.decEq V
  Module.End.restrictedPointSpectrum (toEuclideanLin (G.adjMatrix ℝ)) W

private theorem restrictedEigenvalues_eq [DecidableEq V] :
    G.restrictedEigenvalues = Module.End.restrictedPointSpectrum (toEuclideanLin A) W := by
  unfold restrictedEigenvalues
  rw [Subsingleton.elim (Classical.decEq V) (inferInstance : DecidableEq V)]

/-- A restricted eigenvalue has a nonzero adjacency eigenvector of coordinate sum zero. -/
theorem mem_restrictedEigenvalues_iff {t : ℝ} :
    t ∈ G.restrictedEigenvalues ↔
      ∃ u : V → ℝ, u ≠ 0 ∧ (∑ i, u i) = 0 ∧ A *ᵥ u = t • u := by
  classical
  rw [restrictedEigenvalues_eq, Module.End.mem_restrictedPointSpectrum_iff]
  constructor
  · rintro ⟨u, hW, hne, hu⟩
    refine ⟨ofLp u, by simpa using hne, (mem_orthogonal_ones_iff u).mp hW, ?_⟩
    simpa only [ofLp_toLpLin, toLin'_apply, ofLp_smul, RCLike.ofReal_real_eq_id, id_eq] using
      congrArg ofLp hu
  · rintro ⟨u, hne, hsum, hu⟩
    refine ⟨toLp 2 u, (mem_orthogonal_ones_iff _).mpr hsum, by simpa using hne, ?_⟩
    apply ofLp_injective 2
    simpa only [ofLp_toLpLin, toLin'_apply, ofLp_smul, ofLp_toLp, RCLike.ofReal_real_eq_id, id_eq]
      using hu

private theorem adjMatrix_toEuclideanLin_isSymmetric [DecidableEq V] :
    (toEuclideanLin A).IsSymmetric :=
  isSymmetric_toEuclideanLin_iff.mpr (isHermitian_iff_isSymm.mpr (isSymm_adjMatrix (G := G)))

private theorem adjMatrix_toEuclideanLin_apply_ones [DecidableEq V] (hk : G.IsRegularOfDegree k) :
    toEuclideanLin A e = (k : ℝ) • e := by
  apply ofLp_injective 2
  rw [ofLp_toLpLin, toLin'_apply, ofLp_smul, ofLp_toLp]
  ext i
  simp [hk i]

/-- Every restricted eigenvalue belongs to the real spectrum of the adjacency matrix. -/
theorem spectrum_adjMatrix_of_mem_restrictedEigenvalues [DecidableEq V] {t : ℝ}
    (ht : t ∈ G.restrictedEigenvalues) : t ∈ spectrum ℝ A := by
  obtain ⟨u, hne, _, hu⟩ := mem_restrictedEigenvalues_iff.mp ht
  rw [← AlgEquiv.spectrum_eq (toLpLinAlgEquiv 2) A, ← Module.End.hasEigenvalue_iff_mem_spectrum]
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := toLp 2 u) ⟨?_, by simpa using hne⟩
  rw [Module.End.mem_eigenspace_iff, toLpLinAlgEquiv, AlgEquiv.ofLinearEquiv_apply,
    toLpLin_apply, ofLp_toLp, hu, toLp_smul]

/-- In a regular graph, each adjacency eigenvalue distinct from the degree is restricted. -/
theorem mem_restrictedEigenvalues_of_mem_spectrum_adjMatrix [DecidableEq V]
    (hk : G.IsRegularOfDegree k) {t : ℝ} (ht : t ∈ spectrum ℝ A) (htk : t ≠ k) :
    t ∈ G.restrictedEigenvalues := by
  rw [← AlgEquiv.spectrum_eq (toLpLinAlgEquiv 2) A,
    ← Module.End.hasEigenvalue_iff_mem_spectrum] at ht
  obtain ⟨u, hu, hne⟩ := ht.exists_hasEigenvector
  have he : e ∈ Module.End.eigenspace (toEuclideanLin A) (k : ℝ) :=
    Module.End.mem_eigenspace_iff.mpr (adjMatrix_toEuclideanLin_apply_ones hk)
  have hW : u ∈ W := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    (Submodule.isOrtho_iff_inner_eq.mp
      ((adjMatrix_toEuclideanLin_isSymmetric (G := G)).orthogonalFamily_eigenspaces.pairwise
        htk.symm) e he u hu)
  rw [restrictedEigenvalues_eq]
  exact Module.End.mem_restrictedPointSpectrum hW hne (Module.End.mem_eigenspace_iff.mp hu)

/-- For a regular graph, a polynomial in the adjacency matrix whose roots include all the
restricted eigenvalues is a scalar multiple of the all-ones matrix. -/
theorem exists_aeval_adjMatrix_eq_smul [DecidableEq V]
    (hk : G.IsRegularOfDegree k) (p : ℝ[X])
    (h : ∀ t ∈ G.restrictedEigenvalues, p.IsRoot t) :
    ∃ d : ℝ, aeval A p = d • J := by
  let T := toEuclideanLin A
  have hT : T.IsSymmetric := adjMatrix_toEuclideanLin_isSymmetric
  have he : T e = (k : ℝ) • e := adjMatrix_toEuclideanLin_apply_ones hk
  have hspan : ℝ ∙ e ∈ Module.End.invtSubmodule T := by
    refine (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem T).mpr ?_
    intro u hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [map_smul, he]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))
  have hInv : ∀ u ∈ W, T u ∈ W :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem T).mp
      (hT.orthogonalComplement_mem_invtSubmodule hspan)
  let M := aeval A p
  let hS := hT.restrict_invariant hInv
  let basis := hS.eigenvectorBasis rfl
  have hzero : M.toEuclideanLin ∘ₗ Submodule.subtype W = 0 := by
    apply basis.toBasis.ext
    intro i
    let t := hS.eigenvalues rfl i
    let u : EuclideanSpace ℝ V := basis i
    have ht : T u = t • u := by
      simpa only [LinearMap.restrict_apply, SetLike.val_smul, RCLike.ofReal_real_eq_id, id_eq] using
        congrArg Subtype.val (hS.apply_eigenvectorBasis rfl i)
    have hu : A *ᵥ ofLp u = t • ofLp u := by
      simpa only [T, ofLp_toLpLin, toLin'_apply, ofLp_smul] using congrArg ofLp ht
    have hr : p.IsRoot t := h t (by
      rw [restrictedEigenvalues_eq]
      exact hT.eigenvalues_restrict_mem hInv i)
    have hz : M *ᵥ ofLp u = 0 := by
      rw [aeval_mulVec_of_mulVec_eq_smul hu p, hr.eq_zero, zero_smul]
    apply ofLp_injective 2
    simpa only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, Submodule.subtype_apply,
      ofLp_toLpLin, toLin'_apply, LinearMap.zero_apply, ofLp_zero] using hz
  have hM : M.IsSymm := (aeval_transpose _ p).symm.trans
    (congrArg (fun m ↦ aeval m p) (isSymm_adjMatrix (G := G) (α := ℝ)).eq)
  apply hM.exists_eq_smul_of_one_iff.mpr
  intro u hu
  have hz := LinearMap.congr_fun hzero ⟨toLp 2 u, (mem_orthogonal_ones_iff _).mpr hu⟩
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, ofLp_toLpLin, toLin'_apply,
    ofLp_toLp, LinearMap.zero_apply, ofLp_zero] using congrArg ofLp hz

/-- If a polynomial in the adjacency matrix is a scalar multiple of the all-ones matrix, each
restricted eigenvalue is a root of that polynomial. -/
theorem isRoot_of_mem_restrictedEigenvalues_of_aeval_eq_smul [DecidableEq V]
    {p : ℝ[X]} {d t : ℝ} (hp : aeval A p = d • J) (ht : t ∈ G.restrictedEigenvalues) :
    p.IsRoot t := by
  obtain ⟨u, hne, hsum, hu⟩ := mem_restrictedEigenvalues_iff.mp ht
  have hJ : (d • J).IsSymm := by
    ext i j
    simp
  have hzero := (hJ.exists_eq_smul_of_one_iff.mp ⟨d, rfl⟩) u hsum
  have hvalue := aeval_mulVec_of_mulVec_eq_smul hu p
  rw [hp, hzero] at hvalue
  exact (smul_eq_zero.mp hvalue.symm).resolve_right hne

/-- A regular graph with an edge and a pair of distinct nonadjacent vertices has at least two
restricted eigenvalues. -/
theorem restrictedEigenvalues_nontrivial (hk : G.IsRegularOfDegree k)
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

end SimpleGraph
