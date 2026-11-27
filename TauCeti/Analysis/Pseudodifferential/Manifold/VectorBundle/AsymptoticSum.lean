/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Basic
import Mathlib.Algebra.Ring.GeomSum
import TauCeti.Analysis.Pseudodifferential.Manifold.AsymptoticSum

/-!
# Asymptotic summation of pseudodifferential operators between vector bundles

Let `M` be a compact manifold modelled on `ℝⁿ`, and let `E`, `F` be smooth complex vector bundles
over `M` with finite-dimensional model fibres. If `Pₖ : Γ(E) → Γ(F)` are classical
pseudodifferential operators of orders `m - k`
(`TauCeti.sectionClassicalPseudodifferentialOperators`), they have an **asymptotic sum**: a
classical pseudodifferential operator `Q` of order `m` such that for every `N` the remainder
`Q - ∑_{k < N} Pₖ` has order `m - N`
(`TauCeti.exists_forall_sub_sum_mem_sectionClassicalPseudodifferentialOperators`). It is unique
modulo operators of order `-∞`, that is, of every order `m - N`
(`TauCeti.forall_sub_sum_mem_sectionClassicalPseudodifferentialOperators_iff`).

The main application is the **Neumann series** on a bundle: if `R : Γ(E) → Γ(E)` has order `-1`,
then `1 - R` is invertible modulo operators of order `-∞` on both sides
(`exists_forall_one_sub_mul_sub_one_mem_sectionClassicalPseudodifferentialOperators`),
with the asymptotic sum of the powers `Rᵏ` as inverse. This turns a parametrix modulo order `-1`
of an elliptic operator between bundles, obtained by quantizing the inverse of its principal
symbol, into a parametrix modulo operators of order `-∞`.

## The argument

The class of operators between bundles is defined by matrix entries in cut-off frames
(`TauCeti.sectionEntry`), so the scalar asymptotic summation
(`TauCeti.exists_forall_sub_sum_mem_classicalPseudodifferentialOperators`) applies entrywise. To
reassemble the entries, fix once and for all finitely many trivializations `tᵢ` of `E`, smooth
functions `ρᵢ`, `ψᵢ` supported in their base sets and a basis `(bⱼ)` of the model fibre, such that
every section `u` of `E` is `∑ᵢ ∑ⱼ ρᵢ bⱼ*(tᵢ u) · ψᵢ tᵢ⁻¹ bⱼ`
(`IsCompact.exists_sum_sum_cutoffFrameCoeff_smul_cutoffFrameSection_apply` with `K = M`), and
likewise `t'ᵢ'`, `ρ'ᵢ'`, `ψ'ᵢ'`, `(b'ⱼ')` for `F`. Then for every operator `P : Γ(E) → Γ(F)`

`P u = ∑ᵢ ∑ⱼ ∑ᵢ' ∑ⱼ' Pᵢⱼᵢ'ⱼ' (ρᵢ bⱼ*(tᵢ u)) · ψ'ᵢ' t'ᵢ'⁻¹ b'ⱼ'`,

where `Pᵢⱼᵢ'ⱼ'` is the matrix entry `f ↦ ρ'ᵢ' b'ⱼ'*(t'ᵢ' (P (f ψᵢ tᵢ⁻¹ bⱼ)))` of `P`. Conversely,
this formula applied to any finite family of scalar classical pseudodifferential operators of order
`m` in place of the entries gives an operator between bundles of order `m`: its matrix entries in
any other cut-off frames are finite sums of these scalar operators multiplied by smooth functions on
both sides, and on a compact manifold every operator is properly supported
(`TauCeti.IsSectionProperlySupported.of_compactSpace`). The reassembled scalar asymptotic sums of
the entries of the `Pₖ` are the asymptotic sum of the `Pₖ`.

## Main results

* `TauCeti.exists_forall_sub_sum_mem_sectionClassicalPseudodifferentialOperators`: on a compact
  manifold, classical pseudodifferential operators between bundles of orders `m - k` have an
  asymptotic sum of order `m`.
* `TauCeti.forall_sub_sum_mem_sectionClassicalPseudodifferentialOperators_iff`: asymptotic sums
  are unique modulo operators of order `-∞`.
* `exists_forall_one_sub_mul_sub_one_mem_sectionClassicalPseudodifferentialOperators`: on a
  compact manifold, `1 - R` is invertible modulo operators of order `-∞` for every operator `R` of
  order `-1` on the sections of a bundle.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Proposition 18.1.3
  (asymptotic summation) and §18.1 (operators between vector bundles on manifolds, defined by their
  matrices in local frames).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §§4 and 8.
-/

public section

noncomputable section

open Bundle Finset
open scoped ContDiff Manifold

universe u

namespace TauCeti

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] {m : ℝ}

/-! ### Reassembling an operator from scalar entries -/

section FrameSum

variable {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
  (L : ι → κ → Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯)
  (S : ι' → κ' → Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯)

/-- The operator `u ↦ ∑ᵢ ∑ⱼ ∑ᵢ' ∑ⱼ' Aᵢⱼᵢ'ⱼ' (Lᵢⱼ u) · Sᵢ'ⱼ'` from `Γ(E)` to `Γ(F)` assembled from
a matrix `A` of operators on functions, given coefficient maps `Lᵢⱼ : Γ(E) → C^∞(M, ℂ)` and
sections `Sᵢ'ⱼ'` of `F`; it is linear in `A`. -/
private def frameSum :
    (ι → κ → ι' → κ' → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) →ₗ[ℂ]
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ where
  toFun A := ∑ i, ∑ j, ∑ i', ∑ j',
    (LinearMap.toSpanSingleton _ _ (S i' j')).restrictScalars ℂ ∘ₗ A i j i' j' ∘ₗ L i j
  map_add' A B := by
    simp only [Pi.add_apply, LinearMap.add_comp, LinearMap.comp_add, sum_add_distrib]
  map_smul' c A := by
    simp only [Pi.smul_apply, LinearMap.smul_comp, LinearMap.comp_smul, smul_sum, RingHom.id_apply]

private theorem frameSum_apply
    (A : ι → κ → ι' → κ' → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯)
    (u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :
    frameSum L S A u = ∑ i, ∑ j, ∑ i', ∑ j', A i j i' j' (L i j u) • S i' j' := by
  simp [frameSum]

/-- **Reconstruction from the entries.** If the sections of `E` expand as `u = ∑ᵢⱼ Lᵢⱼ u · Tᵢⱼ`
and those of `F` as `h = ∑ᵢ'ⱼ' L'ᵢ'ⱼ' h · Sᵢ'ⱼ'`, then every operator `P` is reassembled from its
entries `f ↦ L'ᵢ'ⱼ' (P (f Tᵢⱼ))`. -/
private theorem frameSum_eq
    {T : ι → κ → Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯}
    (hE : ∀ u, u = ∑ i, ∑ j, L i j u • T i j)
    {L' : ι' → κ' → Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hF : ∀ h, h = ∑ i', ∑ j', L' i' j' h • S i' j')
    (P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯)
    {A : ι → κ → ι' → κ' → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hA : ∀ i j i' j' f, A i j i' j' f = L' i' j' (P (f • T i j))) :
    frameSum L S A = P := by
  refine LinearMap.ext fun u ↦ ?_
  simp only [frameSum_apply, hA, ← hF]
  conv_rhs => rw [hE u]
  simp only [map_sum]

variable [T2Space M] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]

/-- **Assembled operators are pseudodifferential.** On a compact manifold, if the coefficient maps
`Lᵢⱼ` are linear over the smooth functions and every `Aᵢⱼᵢ'ⱼ'` is a scalar classical
pseudodifferential operator of order `m`, the assembled operator is a classical pseudodifferential
operator of order `m` between the bundles. Its entries are finite sums of the `Aᵢⱼᵢ'ⱼ'` multiplied
by smooth functions on both sides. -/
private theorem frameSum_mem [CompactSpace M]
    (hC : ∀ i j (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) u, L i j (f • u) = f * L i j u)
    {A : ι → κ → ι' → κ' → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hA : ∀ i j i' j', A i j i' j' ∈ classicalPseudodifferentialOperators m) :
    frameSum L S A ∈ sectionClassicalPseudodifferentialOperators m := by
  refine mem_sectionClassicalPseudodifferentialOperators_iff.2
    ⟨.of_compactSpace _, fun t _ ψ hψ v t' _ χ hχ ℓ ↦ ?_⟩
  have hentry : sectionEntry t ψ hψ v t' χ hχ ℓ (frameSum L S A) =
      ∑ i, ∑ j, ∑ i', ∑ j', LinearMap.mulLeft ℂ (t'.cutoffFrameCoeff χ hχ ℓ (S i' j')) ∘ₗ
        A i j i' j' ∘ₗ LinearMap.mulLeft ℂ (L i j (t.cutoffFrameSection ψ hψ v)) := by
    refine LinearMap.ext fun f ↦ ?_
    simp only [sectionEntry_apply_eq_cutoffFrameCoeff, frameSum_apply, map_sum,
      Trivialization.cutoffFrameCoeff_smul_of_normedAlgebra, hC, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.mulLeft_apply]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun i' _ ↦
      sum_congr rfl fun j' _ ↦ ?_
    rw [mul_comm f, mul_comm]
  rw [hentry]
  exact sum_mem fun i _ ↦ sum_mem fun j _ ↦ sum_mem fun i' _ ↦ sum_mem fun j' _ ↦
    comp_mulLeft_mem_classicalPseudodifferentialOperators
      (mulLeft_comp_mem_classicalPseudodifferentialOperators (hA i j i' j') _) _

end FrameSum

variable [T2Space M] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]

/-! ### Asymptotic summation -/

variable {P : ℕ → Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}
  {Q Q' : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}

/-- **Uniqueness of asymptotic sums.** If `Q - ∑_{k < N} Pₖ` has order `m - N` for every `N`, then
the same holds for `Q'` exactly when `Q' - Q` has order `-∞`, that is, order `m - N` for every
`N`. -/
theorem forall_sub_sum_mem_sectionClassicalPseudodifferentialOperators_iff
    (hQ : ∀ N : ℕ, Q - ∑ k ∈ range N, P k ∈ sectionClassicalPseudodifferentialOperators (m - N)) :
    (∀ N : ℕ, Q' - ∑ k ∈ range N, P k ∈ sectionClassicalPseudodifferentialOperators (m - N)) ↔
      ∀ N : ℕ, Q' - Q ∈ sectionClassicalPseudodifferentialOperators (m - N) := by
  refine forall_congr' fun N ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← sub_sub_sub_cancel_right Q' Q (∑ k ∈ range N, P k)]
    exact sub_mem h (hQ N)
  · rw [← sub_add_sub_cancel Q' Q (∑ k ∈ range N, P k)]
    exact add_mem h (hQ N)

variable [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- **Asymptotic summation between bundles** (Borel). On a compact manifold, let
`Pₖ : Γ(E) → Γ(F)` be classical pseudodifferential operators of orders `m - k` between bundles
with finite-dimensional fibres. Then there is a classical pseudodifferential operator `Q` of order
`m` such that for every `N` the remainder `Q - ∑_{k < N} Pₖ` is a classical pseudodifferential
operator of order `m - N`. -/
theorem exists_forall_sub_sum_mem_sectionClassicalPseudodifferentialOperators [CompactSpace M]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (hP : ∀ k : ℕ, P k ∈ sectionClassicalPseudodifferentialOperators (m - k)) :
    ∃ Q ∈ sectionClassicalPseudodifferentialOperators m, ∀ N : ℕ,
      Q - ∑ k ∈ range N, P k ∈ sectionClassicalPseudodifferentialOperators (m - N) := by
  -- Cut-off frames `ψᵢ tᵢ⁻¹ bⱼ` of `E`, with coefficients `ρᵢ bⱼ*(tᵢ u)`, and likewise for `F`,
  -- expanding every section.
  set b := Module.finBasis ℂ V
  set b' := Module.finBasis ℂ W
  obtain ⟨ι, _, c, ρ, ψ, hρ, hψ, hE⟩ :=
    isCompact_univ.exists_sum_sum_cutoffFrameCoeff_smul_cutoffFrameSection_apply
      (I := 𝓘(ℝ, CoordinateSpace n)) (F := E) b
  obtain ⟨ι', _, c', ρ', ψ', hρ', hψ', hF⟩ :=
    isCompact_univ.exists_sum_sum_cutoffFrameCoeff_smul_cutoffFrameSection_apply
      (I := 𝓘(ℝ, CoordinateSpace n)) (F := F) b'
  set L := fun i j ↦ (trivializationAt V E (c i)).cutoffFrameCoeff (ρ i) (hρ i)
    (b.coord j).toContinuousLinearMap
  set T := fun i j ↦ (trivializationAt V E (c i)).cutoffFrameSection (ψ i) (hψ i) (b j)
  set L' := fun i' j' ↦ (trivializationAt W F (c' i')).cutoffFrameCoeff (ρ' i') (hρ' i')
    (b'.coord j').toContinuousLinearMap
  set S := fun i' j' ↦ (trivializationAt W F (c' i')).cutoffFrameSection (ψ' i') (hψ' i') (b' j')
  have hET (u : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) : u = ∑ i, ∑ j, L i j u • T i j :=
    ContMDiffSection.ext fun x ↦ (hE u x (Set.mem_univ x)).symm
  have hFS (h : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯) : h = ∑ i', ∑ j', L' i' j' h • S i' j' :=
    ContMDiffSection.ext fun x ↦ (hF h x (Set.mem_univ x)).symm
  -- The matrix entries of `Pₖ` in these frames, and their scalar asymptotic sums `B`.
  set A := fun k i j i' j' ↦ sectionEntry (trivializationAt V E (c i)) (ψ i) (hψ i) (b j)
    (trivializationAt W F (c' i')) (ρ' i') (hρ' i') (b'.coord j').toContinuousLinearMap (P k)
  have hPA (k : ℕ) : frameSum L S (A k) = P k :=
    frameSum_eq L S hET hFS (P k) fun _ _ _ _ _ ↦ sectionEntry_apply_eq_cutoffFrameCoeff ..
  have hC i j f u : L i j (f • u) = f * L i j u :=
    Trivialization.cutoffFrameCoeff_smul_of_normedAlgebra _ _ _ _ _ _
  choose B hB hBA using fun i j i' j' ↦
    exists_forall_sub_sum_mem_classicalPseudodifferentialOperators (m := m)
      (P := fun k ↦ A k i j i' j') fun k ↦
        (mem_sectionClassicalPseudodifferentialOperators_iff.1 (hP k)).2 _ _ _ _ _ _ _ _
  refine ⟨frameSum L S B, frameSum_mem L S hC hB, fun N ↦ ?_⟩
  have hsplit : frameSum L S B - ∑ k ∈ range N, P k =
      frameSum L S fun i j i' j' ↦ B i j i' j' - ∑ k ∈ range N, A k i j i' j' := by
    simp only [← hPA, ← map_sum, ← map_sub]
    congr 1
    ext i j i' j'
    simp
  rw [hsplit]
  exact frameSum_mem L S hC fun i j i' j' ↦ hBA i j i' j' N

/-- **The Neumann series modulo order `-∞` on a bundle.** On a compact manifold, let
`R : Γ(E) → Γ(E)` be a classical pseudodifferential operator of order `-1` on the sections of a
bundle with finite-dimensional fibre. Then `1 - R` is invertible modulo operators of order `-∞`:
there is a classical pseudodifferential operator `S` of order `0` such that `(1 - R) S - 1` and
`S (1 - R) - 1` have every order `-N`. -/
theorem exists_forall_one_sub_mul_sub_one_mem_sectionClassicalPseudodifferentialOperators
    [CompactSpace M] [FiniteDimensional ℂ V]
    {R : Module.End ℂ Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯}
    (hR : R ∈ sectionClassicalPseudodifferentialOperators (-1)) :
    ∃ S ∈ sectionClassicalPseudodifferentialOperators 0, ∀ N : ℕ,
      (1 - R) * S - 1 ∈ sectionClassicalPseudodifferentialOperators (-N) ∧
        S * (1 - R) - 1 ∈ sectionClassicalPseudodifferentialOperators (-N) := by
  have hpow (k : ℕ) : R ^ k ∈ sectionClassicalPseudodifferentialOperators (0 - k) := by
    simpa using pow_mem_sectionClassicalPseudodifferentialOperators hR k
  obtain ⟨S, hS, hSN⟩ := exists_forall_sub_sum_mem_sectionClassicalPseudodifferentialOperators hpow
  have h1R : 1 - R ∈ sectionClassicalPseudodifferentialOperators 0 :=
    sub_mem
      (by simpa [Module.End.one_eq_id] using id_mem_sectionClassicalPseudodifferentialOperators)
      (sectionClassicalPseudodifferentialOperators_le 1 (by norm_num) hR)
  -- With `S_N = ∑_{k < N} Rᵏ`, `(1 - R) S_N = S_N (1 - R) = 1 - R^N`, so `(1 - R) S - 1` is
  -- `(1 - R) (S - S_N) - R^N` and `S (1 - R) - 1` is `(S - S_N) (1 - R) - R^N`, both of order
  -- `-N`.
  refine ⟨S, hS, fun N ↦ ⟨?_, ?_⟩⟩
  · rw [show (1 - R) * S - 1 = (1 - R) * (S - ∑ k ∈ range N, R ^ k) - R ^ N by
      rw [mul_sub, mul_neg_geom_sum]; abel]
    refine sub_mem ?_ (by simpa using hpow N)
    simpa [Module.End.mul_eq_comp] using
      comp_mem_sectionClassicalPseudodifferentialOperators h1R (hSN N)
  · rw [show S * (1 - R) - 1 = (S - ∑ k ∈ range N, R ^ k) * (1 - R) - R ^ N by
      rw [sub_mul, geom_sum_mul_neg]; abel]
    refine sub_mem ?_ (by simpa using hpow N)
    simpa [Module.End.mul_eq_comp] using
      comp_mem_sectionClassicalPseudodifferentialOperators (hSN N) h1R

end TauCeti
