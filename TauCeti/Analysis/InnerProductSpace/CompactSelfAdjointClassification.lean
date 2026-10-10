/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti: unitary classification of compact self-adjoint operators.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Compact self-adjoint operators are classified by their eigenspace dimensions

A compact self-adjoint operator with trivial kernel is determined, up to unitary
equivalence, by the function `μ ↦ dim ker(T - μ)`.  That is the coordinate-free
form of "the decreasing list of eigenvalues, with multiplicity, is a complete
invariant".

## The construction

Mathlib's spectral theorem for compact self-adjoint operators
(`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`) says the
eigenspaces span densely, and
`ContinuousLinearMap.finite_dimensional_eigenspace` says each one attached to a
nonzero eigenvalue is finite-dimensional.  With trivial kernel *every* eigenspace
is finite-dimensional, so each is isometric to `EuclideanSpace 𝕜 (Fin d)` for
`d` its dimension.

The point of routing through the Euclidean model rather than through the
eigenspaces themselves is that it makes both operators Hilbert sums over the
*same* family of model spaces, so the two `IsHilbertSum.linearIsometryEquiv`s
land in a single `lp` space and compose directly.  Mathlib has no congruence
`lp G 2 ≃ₗᵢ lp G' 2` from a family of isometries `G i ≃ₗᵢ G' i`, and this
sidesteps needing one.

## Main results

* `TauCeti.euclideanSubmoduleEquiv`: a finite-dimensional subspace is isometric
  to the Euclidean space of its dimension.
* `TauCeti.exists_linearIsometryEquiv_intertwining_of_finrank_eigenspace_eq`:
  the classification.
* `TauCeti.exists_hasEigenvalue_eigenspace_not_le`: the existence half of the
  same spectral theorem — a compact self-adjoint operator has an eigenvector
  outside any subspace whose orthogonal complement is nontrivial.
-/

public section

open Module (finrank)
open Module.End (eigenspace)
open scoped InnerProductSpace

namespace TauCeti

/-! ## A finite-dimensional subspace, in Euclidean coordinates -/

/-- A finite-dimensional subspace is isometric to the Euclidean space of its
dimension.  The dimension is passed as an equation so the model index can be
chosen by the caller — which is what lets two subspaces of *different* ambient
spaces share one model. -/
noncomputable def euclideanSubmoduleEquiv {𝕜 : Type*} [RCLike 𝕜] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (K : Submodule 𝕜 H)
    [FiniteDimensional 𝕜 K] {n : ℕ} (hn : finrank 𝕜 K = n) :
    EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ[𝕜] K :=
  ((stdOrthonormalBasis 𝕜 K).reindex (finCongr hn)).repr.symm

/-! ## The classification -/

section Classification

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- With trivial kernel, *every* eigenspace of a compact operator is
finite-dimensional: the nonzero eigenvalues by Mathlib's spectral theorem, and
`0` because its eigenspace is trivial. -/
theorem finiteDimensional_eigenspace_of_isCompactOperator {A : E →L[𝕜] E}
    (hAc : IsCompactOperator A) (hA0 : eigenspace A.toLinearMap 0 = ⊥) (μ : 𝕜) :
    FiniteDimensional 𝕜 (eigenspace A.toLinearMap μ) := by
  by_cases hμ : μ = 0
  · subst hμ
    rw [hA0]
    infer_instance
  · exact ContinuousLinearMap.finite_dimensional_eigenspace hAc μ hμ

/-- **A compact self-adjoint operator has an eigenvector outside any subspace that
misses a nonzero vector.**

If every eigenspace were contained in `K`, then Mathlib's spectral theorem
(`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`) would make `K` dense,
contradicting `y ∈ Kᗮ`, `y ≠ 0`.

This is the *existence* direction the spectral theorem is usually not used for.  Taking `K`
to be the span of the eigenvectors already known — for the inverse of an unbounded operator
with compact resolvent, the kernel — turns an upper-bound-free spectral containment, which
is vacuously true of an empty spectrum, into a genuine eigenpair. -/
theorem exists_hasEigenvalue_eigenspace_not_le {A : E →L[𝕜] E}
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    {K : Submodule 𝕜 E} {y : E} (hy : y ∈ Kᗮ) (hy0 : y ≠ 0) :
    ∃ μ : 𝕜, Module.End.HasEigenvalue A.toLinearMap μ ∧
      ¬ eigenspace A.toLinearMap μ ≤ K := by
  by_contra hcon
  have hall : ∀ μ : 𝕜, eigenspace A.toLinearMap μ ≤ K := by
    intro μ
    by_cases hμ : Module.End.HasEigenvalue A.toLinearMap μ
    · by_contra hle
      exact hcon ⟨μ, hμ, hle⟩
    · rw [Module.End.hasEigenvalue_iff, not_not] at hμ
      rw [hμ]
      exact bot_le
  have hsup : (⨆ μ : 𝕜, eigenspace A.toLinearMap μ) ≤ K := iSup_le hall
  have hbot : (⨆ μ : 𝕜, eigenspace A.toLinearMap μ)ᗮ = ⊥ :=
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hAc hAs.isSymmetric
  have hmem : y ∈ (⊥ : Submodule 𝕜 E) := hbot ▸ Submodule.orthogonal_le hsup hy
  exact hy0 (Submodule.mem_bot 𝕜 |>.mp hmem)

/-- **Compact self-adjoint operators with trivial kernel are classified by their
eigenspace dimensions.**

`dim ker(A - μ) = dim ker(B - μ)` for every `μ` is exactly "the eigenvalues
agree, with multiplicity"; the conclusion is a unitary intertwining the two
operators.  The trivial-kernel hypothesis is what makes the two spaces have the
same size — without it one could pad either side with an arbitrary kernel. -/
theorem exists_linearIsometryEquiv_intertwining_of_finrank_eigenspace_eq
    {A : E →L[𝕜] E} {B : F →L[𝕜] F}
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hBc : IsCompactOperator B) (hBs : IsSelfAdjoint B)
    (hA0 : eigenspace A.toLinearMap 0 = ⊥) (hB0 : eigenspace B.toLinearMap 0 = ⊥)
    (hdim : ∀ μ : 𝕜, finrank 𝕜 (eigenspace A.toLinearMap μ) =
      finrank 𝕜 (eigenspace B.toLinearMap μ)) :
    ∃ W : E ≃ₗᵢ[𝕜] F, ∀ x, W (A x) = B (W x) := by
  classical
  have hfA : ∀ μ : 𝕜, FiniteDimensional 𝕜 (eigenspace A.toLinearMap μ) :=
    finiteDimensional_eigenspace_of_isCompactOperator hAc hA0
  have hfB : ∀ μ : 𝕜, FiniteDimensional 𝕜 (eigenspace B.toLinearMap μ) :=
    finiteDimensional_eigenspace_of_isCompactOperator hBc hB0
  -- The common model family, indexed by `μ`.
  set G : 𝕜 → Type _ := fun μ =>
    EuclideanSpace 𝕜 (Fin (finrank 𝕜 (eigenspace A.toLinearMap μ))) with hG
  -- The two coordinatizations of the eigenspaces.
  set eA : ∀ μ : 𝕜, G μ ≃ₗᵢ[𝕜] eigenspace A.toLinearMap μ := fun μ =>
    euclideanSubmoduleEquiv _ rfl with heA
  set eB : ∀ μ : 𝕜, G μ ≃ₗᵢ[𝕜] eigenspace B.toLinearMap μ := fun μ =>
    euclideanSubmoduleEquiv _ (hdim μ).symm with heB
  set VA : ∀ μ : 𝕜, G μ →ₗᵢ[𝕜] E := fun μ =>
    (eigenspace A.toLinearMap μ).subtypeₗᵢ.comp (eA μ).toLinearIsometry with hVA
  set VB : ∀ μ : 𝕜, G μ →ₗᵢ[𝕜] F := fun μ =>
    (eigenspace B.toLinearMap μ).subtypeₗᵢ.comp (eB μ).toLinearIsometry with hVB
  -- Each model maps onto the corresponding eigenspace.
  have hrangeA : ∀ μ : 𝕜, LinearMap.range (VA μ).toLinearMap =
      eigenspace A.toLinearMap μ := by
    intro μ
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact (eA μ x).2
    · intro y hy
      exact ⟨(eA μ).symm ⟨y, hy⟩, by simp [hVA]⟩
  have hrangeB : ∀ μ : 𝕜, LinearMap.range (VB μ).toLinearMap =
      eigenspace B.toLinearMap μ := by
    intro μ
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact (eB μ x).2
    · intro y hy
      exact ⟨(eB μ).symm ⟨y, hy⟩, by simp [hVB]⟩
  -- Both are Hilbert sums over the same model family.
  have horthoA : OrthogonalFamily 𝕜 G VA := by
    intro i j hij v w
    exact hAs.isSymmetric.orthogonalFamily_eigenspaces hij (eA i v) (eA j w)
  have horthoB : OrthogonalFamily 𝕜 G VB := by
    intro i j hij v w
    exact hBs.isSymmetric.orthogonalFamily_eigenspaces hij (eB i v) (eB j w)
  have htotalA : ⊤ ≤ (⨆ μ : 𝕜, LinearMap.range (VA μ).toLinearMap).topologicalClosure := by
    simp only [hrangeA]
    exact le_of_eq (Submodule.topologicalClosure_eq_top_iff.mpr
      (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hAc
        hAs.isSymmetric)).symm
  have htotalB : ⊤ ≤ (⨆ μ : 𝕜, LinearMap.range (VB μ).toLinearMap).topologicalClosure := by
    simp only [hrangeB]
    exact le_of_eq (Submodule.topologicalClosure_eq_top_iff.mpr
      (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hBc
        hBs.isSymmetric)).symm
  have hsumA : IsHilbertSum 𝕜 G VA := IsHilbertSum.mk horthoA htotalA
  have hsumB : IsHilbertSum 𝕜 G VB := IsHilbertSum.mk horthoB htotalB
  refine ⟨hsumA.linearIsometryEquiv.trans hsumB.linearIsometryEquiv.symm, ?_⟩
  set W := hsumA.linearIsometryEquiv.trans hsumB.linearIsometryEquiv.symm with hWdef
  -- `W` sends the `μ`-model to the `μ`-model, hence eigenspace onto eigenspace.
  have hWmodel : ∀ (μ : 𝕜) (x : G μ), W (VA μ x) = VB μ x := by
    intro μ x
    have hA : hsumA.linearIsometryEquiv (VA μ x) = lp.single 2 μ x := by
      rw [← hsumA.linearIsometryEquiv_symm_apply_single x,
        LinearIsometryEquiv.apply_symm_apply]
    rw [hWdef]
    simp only [LinearIsometryEquiv.trans_apply, hA]
    exact hsumB.linearIsometryEquiv_symm_apply_single x
  have hWmaps : ∀ (μ : 𝕜), ∀ y ∈ eigenspace A.toLinearMap μ,
      W y ∈ eigenspace B.toLinearMap μ := by
    intro μ y hy
    obtain ⟨x, rfl⟩ := (hrangeA μ).ge hy
    rw [show (VA μ).toLinearMap x = VA μ x from rfl, hWmodel]
    exact (hrangeB μ).le ⟨x, rfl⟩
  -- On each eigenspace both maps are multiplication by `μ`; extend by density.
  have hEq : ∀ y ∈ (⨆ μ : 𝕜, eigenspace A.toLinearMap μ), W (A y) = B (W y) := by
    intro y hy
    refine Submodule.iSup_induction (motive := fun z => W (A z) = B (W z))
      (fun μ : 𝕜 => eigenspace A.toLinearMap μ) hy ?_ ?_ ?_
    · intro μ z hz
      have hAz : A z = μ • z := Module.End.mem_eigenspace_iff.mp hz
      have hBz : B (W z) = μ • W z :=
        Module.End.mem_eigenspace_iff.mp (hWmaps μ z hz)
      rw [hAz, map_smul, hBz]
    · simp
    · intro a b ha hb
      simp only [map_add, ha, hb]
  have hdense : Dense ((⨆ μ : 𝕜, eigenspace A.toLinearMap μ : Submodule 𝕜 E) : Set E) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (Submodule.topologicalClosure_eq_top_iff.mpr
        (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hAc
          hAs.isSymmetric))
  have hcont₁ : Continuous fun x : E => W (A x) := W.continuous.comp A.continuous
  have hcont₂ : Continuous fun x : E => B (W x) := B.continuous.comp W.continuous
  exact fun x => congrFun (Continuous.ext_on hdense hcont₁ hcont₂ hEq) x

end Classification

/-! ## The eigenvalues accumulate only at zero -/

section Accumulation

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **A compact self-adjoint operator has only finitely many eigenvalues outside any disc
around `0`.**

Infinitely many of them would give an infinite family of unit eigenvectors, pairwise orthogonal
because the eigenvalues are distinct and the operator is symmetric.  Their images are then
`c`-separated — `⟪A u - A v, u⟫` is the conjugate of the eigenvalue of `u` — while all of them
lie in the totally bounded set `closure (A '' ball 0 2)`.

Mathlib proves that each eigenspace for a nonzero eigenvalue is finite-dimensional
(`ContinuousLinearMap.finite_dimensional_eigenspace`) but says nothing about how many such
eigenvalues there are; this is the missing half of Riesz–Schauder for the self-adjoint case. -/
theorem finite_setOf_hasEigenvalue_le_norm {A : E →L[𝕜] E}
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A) {c : ℝ} (hc : 0 < c) :
    {mu : 𝕜 | Module.End.HasEigenvalue A.toLinearMap mu ∧ c ≤ ‖mu‖}.Finite := by
  by_contra hcon
  have hinf : {mu : 𝕜 | Module.End.HasEigenvalue A.toLinearMap mu ∧ c ≤ ‖mu‖}.Infinite := hcon
  set em := hinf.natEmbedding with hem
  set mu : ℕ → 𝕜 := fun n => ((em n : {mu : 𝕜 | Module.End.HasEigenvalue A.toLinearMap mu ∧
    c ≤ ‖mu‖}) : 𝕜) with hmu
  have hmuinj : Function.Injective mu := by
    intro i j hij
    exact em.injective (Subtype.ext hij)
  have hmuev : ∀ n, Module.End.HasEigenvalue A.toLinearMap (mu n) := fun n => (em n).2.1
  have hmunorm : ∀ n, c ≤ ‖mu n‖ := fun n => (em n).2.2
  -- normalized eigenvectors
  have hex : ∀ n, ∃ w : E, ‖w‖ = 1 ∧ A w = mu n • w := by
    intro n
    obtain ⟨w, hw, hw0⟩ := (hmuev n).exists_hasEigenvector
    have hAw : A w = mu n • w := Module.End.mem_eigenspace_iff.mp hw
    have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    refine ⟨((‖w‖ : 𝕜))⁻¹ • w, ?_, ?_⟩
    · rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg w),
        inv_mul_cancel₀ hwn]
    · rw [map_smul, hAw, smul_comm]
  choose u hu1 hu2 using hex
  have huo : ∀ i j : ℕ, i ≠ j → (⟪u i, u j⟫_𝕜 : 𝕜) = 0 := by
    intro i j hij
    have hne : mu i ≠ mu j := fun h => hij (hmuinj h)
    have hmi : u i ∈ Module.End.eigenspace A.toLinearMap (mu i) :=
      Module.End.mem_eigenspace_iff.mpr (hu2 i)
    have hmj : u j ∈ Module.End.eigenspace A.toLinearMap (mu j) :=
      Module.End.mem_eigenspace_iff.mpr (hu2 j)
    exact hAs.isSymmetric.orthogonalFamily_eigenspaces hne ⟨u i, hmi⟩ ⟨u j, hmj⟩
  -- the images are `c`-separated
  have hsep : ∀ i j : ℕ, i ≠ j → c ≤ dist (A (u i)) (A (u j)) := by
    intro i j hij
    have hinner : (⟪A (u i) - A (u j), u i⟫_𝕜 : 𝕜) = (starRingEnd 𝕜) (mu i) := by
      rw [inner_sub_left, hu2 i, hu2 j, inner_smul_left, inner_smul_left,
        huo j i (Ne.symm hij), inner_self_eq_norm_sq_to_K, hu1 i]
      simp
    have hle : ‖(⟪A (u i) - A (u j), u i⟫_𝕜 : 𝕜)‖ ≤ ‖A (u i) - A (u j)‖ := by
      have := norm_inner_le_norm (𝕜 := 𝕜) (A (u i) - A (u j)) (u i)
      rwa [hu1 i, mul_one] at this
    rw [hinner, RCLike.norm_conj] at hle
    rw [dist_eq_norm]
    exact le_trans (hmunorm i) hle
  -- but they all lie in one totally bounded set
  have hAc' : IsCompactOperator ((A : E →ₗ[𝕜] E)) := hAc
  have hcpt : IsCompact (closure ((A : E →ₗ[𝕜] E) '' Metric.ball (0 : E) 2)) :=
    hAc'.isCompact_closure_image_ball 2
  obtain ⟨t, htfin, htcov⟩ :=
    Metric.totallyBounded_iff.mp hcpt.totallyBounded (c / 2) (by positivity)
  have hmem : ∀ n, A (u n) ∈ closure ((A : E →ₗ[𝕜] E) '' Metric.ball (0 : E) 2) := by
    intro n
    refine subset_closure ⟨u n, ?_, rfl⟩
    rw [Metric.mem_ball, dist_zero_right, hu1 n]
    norm_num
  have hchoose : ∀ n, ∃ y ∈ t, A (u n) ∈ Metric.ball y (c / 2) := by
    intro n
    have := htcov (hmem n)
    rw [Set.mem_iUnion₂] at this
    obtain ⟨y, hy, hy'⟩ := this
    exact ⟨y, hy, hy'⟩
  choose y hyt hyb using hchoose
  have : Finite t := htfin.to_subtype
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (⟨y n, hyt n⟩ : t))
  have hyy : y i = y j := congrArg Subtype.val heq
  have h1 : dist (A (u i)) (y i) < c / 2 := hyb i
  have h2 : dist (A (u j)) (y i) < c / 2 := by
    rw [hyy]
    exact hyb j
  have hd : dist (A (u i)) (A (u j)) < c := by
    have := dist_triangle (A (u i)) (y i) (A (u j))
    rw [dist_comm (y i) (A (u j))] at this
    linarith
  exact absurd hd (not_lt.mpr (hsep i j hij))

/-- **An injective compact self-adjoint operator on an infinite-dimensional space has
eigenvalues of arbitrarily small nonzero modulus.**

If every eigenvalue had modulus at least `c`, there would be finitely many of them, so the
supremum of the eigenspaces would be finite-dimensional — hence closed, hence, by the spectral
theorem, all of `E`.

This is the step that converts "the resolvent is compact" into "the operator has an unbounded
sequence of eigenvalues": the inverted values `mu⁻¹` are then unbounded. -/
theorem exists_hasEigenvalue_norm_lt {A : E →L[𝕜] E}
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hA0 : Module.End.eigenspace A.toLinearMap 0 = ⊥)
    (hE : ¬ FiniteDimensional 𝕜 E) {c : ℝ} (hc : 0 < c) :
    ∃ mu : 𝕜, Module.End.HasEigenvalue A.toLinearMap mu ∧ mu ≠ 0 ∧ ‖mu‖ < c := by
  by_contra hcon
  push Not at hcon
  have hbound : ∀ mu : 𝕜, Module.End.HasEigenvalue A.toLinearMap mu → c ≤ ‖mu‖ := by
    intro mu hev
    have hne : mu ≠ 0 := by
      intro h
      rw [h, Module.End.hasEigenvalue_iff, hA0] at hev
      exact hev rfl
    exact hcon mu hev hne
  have hfinS := finite_setOf_hasEigenvalue_le_norm hAc hAs hc
  have : Finite {mu : 𝕜 | Module.End.HasEigenvalue A.toLinearMap mu ∧ c ≤ ‖mu‖} :=
    hfinS.to_subtype
  have hfd : ∀ mu : 𝕜, FiniteDimensional 𝕜 (Module.End.eigenspace A.toLinearMap mu) :=
    finiteDimensional_eigenspace_of_isCompactOperator hAc hA0
  set K : Submodule 𝕜 E := ⨆ m : {mu : 𝕜 | Module.End.HasEigenvalue A.toLinearMap mu ∧
    c ≤ ‖mu‖}, Module.End.eigenspace A.toLinearMap (m : 𝕜) with hKdef
  have : FiniteDimensional 𝕜 K := Submodule.finiteDimensional_iSup _
  have : CompleteSpace K := (Submodule.closed_of_finiteDimensional K).completeSpace_coe
  have hle : (⨆ mu : 𝕜, Module.End.eigenspace A.toLinearMap mu) ≤ K := by
    refine iSup_le fun mu => ?_
    by_cases hev : Module.End.HasEigenvalue A.toLinearMap mu
    · exact le_iSup (fun m : {mu : 𝕜 | Module.End.HasEigenvalue A.toLinearMap mu ∧ c ≤ ‖mu‖} =>
        Module.End.eigenspace A.toLinearMap (m : 𝕜)) ⟨mu, hev, hbound mu hev⟩
    · rw [Module.End.hasEigenvalue_iff, not_not] at hev
      rw [hev]
      exact bot_le
  have hbot : (⨆ mu : 𝕜, Module.End.eigenspace A.toLinearMap mu)ᗮ = ⊥ :=
    ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hAc hAs.isSymmetric
  have hKbot : Kᗮ = ⊥ := le_bot_iff.mp (hbot ▸ Submodule.orthogonal_le hle)
  have hKtop : K = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hKbot
  have : FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 E) :=
    hKtop ▸ (inferInstance : FiniteDimensional 𝕜 K)
  exact hE (Module.Finite.equiv (Submodule.topEquiv : (⊤ : Submodule 𝕜 E) ≃ₗ[𝕜] E))

end Accumulation

end TauCeti
