/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Basic
public import TauCeti.Analysis.CStarAlgebra.FiniteDimensional.MultiplicityMatrix.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import TauCeti.Algebra.GroupWithZero.Pi
import TauCeti.Algebra.Star.Pi
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
import TauCeti.Analysis.CStarAlgebra.Matrix.EuclideanCLM
import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# Classification of `⋆`-homomorphisms of matrix direct sums up to unitary conjugacy

Building on `TauCeti.Analysis.CStarAlgebra.FiniteDimensional.MultiplicityMatrix.Basic`, this file
proves that `⋆`-homomorphisms between finite direct sums of full complex matrix C⋆-algebras are
classified up to unitary conjugacy (and approximate unitary equivalence) by their multiplicity
matrices, and that composition multiplies multiplicity matrices.

## Main results

* **Standard block-diagonal form**: every `⋆`-homomorphism `φ` is unitarily conjugate in the target
  to `TauCeti.cstarMatrixPiBlockHom φ.multiplicityMatrix f`
  (`NonUnitalStarAlgHom.exists_unitary_conj_cstarMatrixPiBlockHom`).
* **Unitary conjugacy and approximate unitary equivalence**: two `⋆`-homomorphisms have equal
  multiplicity matrices if and only if they are unitarily conjugate in the target
  (`NonUnitalStarAlgHom.exists_unitary_conj_iff_multiplicityMatrix_eq`,
  `StarAlgHom.exists_unitary_conj_iff_multiplicityMatrix_eq`), and if and only if they are
  approximately unitarily equivalent
  (`NonUnitalStarAlgHom.approximatelyUnitarilyEquivalent_iff_multiplicityMatrix_eq`).
* **Functoriality**: composition of `⋆`-homomorphisms multiplies their multiplicity matrices
  (`NonUnitalStarAlgHom.multiplicityMatrix_comp`, `StarAlgHom.multiplicityMatrix_comp`).
* **Single-block corollaries**: a unital `⋆`-homomorphism
  `CStarMatrix n n ℂ →⋆ₐ[ℂ] CStarMatrix m m ℂ` exists if and only if
  `Fintype.card n ∣ Fintype.card m` (`TauCeti.nonempty_starAlgHom_cstarMatrix_iff`), and any two
  such unital maps are unitarily conjugate (`StarAlgHom.exists_unitary_conj_cstarMatrix`).

## References

* Mikael Rørdam, *Classification of Nuclear C⋆-Algebras*, Section 1.1.
* Bruce Blackadar, *K-Theory for Operator Algebras*, Section 7.2.
* Kenneth R. Davidson, *C⋆-Algebras by Example*, Section III.2.
-/

public section

noncomputable section

open scoped Matrix

namespace NonUnitalStarAlgHom

section UnitaryConjugacy

variable {ι κ : Type*} {n : ι → Type*} {m : κ → Type*}

private def evalEuclideanHom [∀ i, Fintype (n i)] [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ) :
    (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ]
      (EuclideanSpace ℂ (m j) →L[ℂ] EuclideanSpace ℂ (m j)) :=
  (CStarMatrix.toEuclideanCLM (n := m j)).toNonUnitalStarAlgHom.comp
    ((Pi.evalNonUnitalStarAlgHom ℂ _ j).comp φ)

@[simp]
private theorem evalEuclideanHom_apply [∀ i, Fintype (n i)] [∀ j, Fintype (m j)]
    [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (x : ∀ i, CStarMatrix (n i) (n i) ℂ) :
    evalEuclideanHom φ j x = CStarMatrix.toEuclideanCLM (φ x j) := by
  simp [evalEuclideanHom]

private theorem finrank_range_evalEuclideanHom_single [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) (h : Nonempty (n i)) :
    Module.finrank ℂ (LinearMap.range (evalEuclideanHom φ j
      (Pi.single i (CStarMatrix.ofMatrix (Matrix.single h.some h.some 1)))).toLinearMap) =
      φ.multiplicityMatrix j i := by
  rw [evalEuclideanHom_apply, CStarMatrix.finrank_range_toEuclideanCLM,
    ← φ.multiplicityMatrix_apply_eq_rank_single j i h.some]

private def minimalRangeBasis [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) (h : Nonempty (n i)) :
    OrthonormalBasis (Fin (φ.multiplicityMatrix j i)) ℂ
      (LinearMap.range (evalEuclideanHom φ j
        (Pi.single i (CStarMatrix.ofMatrix (Matrix.single h.some h.some 1)))).toLinearMap) :=
  (stdOrthonormalBasis ℂ _).reindex
    (finCongr (finrank_range_evalEuclideanHom_single φ j i h))

private def partialBasisVec [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ) :
    (Σ i, n i × Fin (φ.multiplicityMatrix j i)) → EuclideanSpace ℂ (m j) :=
  fun ⟨i, p, t⟩ ↦
    let h : Nonempty (n i) := ⟨p⟩
    evalEuclideanHom φ j (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p h.some 1)))
      (minimalRangeBasis φ j i h t)

private theorem partialBasisVec_mk [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) (p : n i) (t : Fin (φ.multiplicityMatrix j i)) :
    partialBasisVec φ j ⟨i, p, t⟩ =
      evalEuclideanHom φ j
        (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p (⟨p⟩ : Nonempty (n i)).some 1)))
        (minimalRangeBasis φ j i ⟨p⟩ t) :=
  rfl

private theorem evalEuclideanHom_single_partialBasisVec [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) (p q : n i) (a : Σ i', n i' × Fin (φ.multiplicityMatrix j i')) :
    evalEuclideanHom φ j (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p q 1)))
        (partialBasisVec φ j a) =
      if h : i = a.1 then
        if h ▸ q = a.2.1 then partialBasisVec φ j ⟨i, p, h ▸ a.2.2⟩ else 0
      else 0 := by
  rcases a with ⟨i', q', t'⟩
  rw [partialBasisVec_mk, ← mul_apply_eq_comp, ← map_mul]
  by_cases hi : i = i'
  · subst hi
    simp only [↓reduceDIte]
    by_cases hq : q = q'
    · subst hq; simp [partialBasisVec_mk]
    · rw [CStarMatrix.piSingle_ofMatrix_single_mul_of_ne i p hq]; simp [hq]
  · rw [Pi.single_mul_single_of_ne hi]; simp [hi]

private theorem orthonormal_partialBasisVec [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ) :
    Orthonormal ℂ (partialBasisVec φ j) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i₁, p₁, t₁⟩ ⟨i₂, p₂, t₂⟩
  rw [partialBasisVec_mk φ j i₁ p₁ t₁, ← ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.star_eq_adjoint, ← map_star, CStarMatrix.star_piSingle_ofMatrix_single,
    star_one, evalEuclideanHom_single_partialBasisVec]
  by_cases hi : i₁ = i₂
  · subst hi; simp only [↓reduceDIte]
    by_cases hp : p₁ = p₂
    · subst hp; simp only [↓reduceIte, partialBasisVec_mk]
      set h : Nonempty (n i₁) := ⟨p₁⟩
      set w := minimalRangeBasis φ j i₁ h t₂
      obtain ⟨u, hu⟩ := w.prop
      have hw : evalEuclideanHom φ j
          (Pi.single i₁ (CStarMatrix.ofMatrix (Matrix.single h.some h.some 1))) w = w := by
        rw [← hu]
        simp only [ContinuousLinearMap.coe_coe, ← mul_apply_eq_comp, ← map_mul,
          CStarMatrix.piSingle_ofMatrix_single_mul_same, mul_one]
      rw [hw, ← Submodule.coe_inner,
        orthonormal_iff_ite.mp (minimalRangeBasis φ j i₁ h).orthonormal t₁ t₂]; simp
    · simp [hp]
  · simp [hi]

private theorem span_range_partialBasisVec_eq_range_one [Finite ι] [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ) :
    Submodule.span ℂ (Set.range (partialBasisVec φ j)) =
      LinearMap.range (evalEuclideanHom φ j 1).toLinearMap := by
  cases nonempty_fintype ι
  apply Submodule.eq_of_le_of_finrank_eq
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨i, p, t⟩, rfl⟩
    refine ⟨partialBasisVec φ j ⟨i, p, t⟩, ?_⟩
    simp only [ContinuousLinearMap.coe_coe, partialBasisVec_mk, ← mul_apply_eq_comp,
      ← map_mul, one_mul]
  · rw [finrank_span_eq_card (orthonormal_partialBasisVec φ j).linearIndependent,
      evalEuclideanHom_apply, CStarMatrix.finrank_range_toEuclideanCLM,
      ← φ.sum_multiplicityMatrix_mul_card_eq_rank_map_one j]
    simp [Fintype.card_sigma, Fintype.card_prod, mul_comm]

private theorem evalEuclideanHom_eq_zero_of_notMem_range [Finite ι] [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ)
    {f : (Σ i, n i × Fin (φ.multiplicityMatrix j i)) ↪ m j}
    {b : OrthonormalBasis (m j) ℂ (EuclideanSpace ℂ (m j))}
    (hb : ∀ a, b (f a) = partialBasisVec φ j a) {z : m j} (hz : z ∉ Set.range f)
    (x : ∀ i, CStarMatrix (n i) (n i) ℂ) :
    evalEuclideanHom φ j x (b z) = 0 := by
  have horth : Submodule.span ℂ (Set.range (partialBasisVec φ j)) ≤
      Submodule.orthogonal (ℂ ∙ b z) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, ← hb a]
    exact b.inner_eq_zero fun hfz ↦ hz ⟨a, hfz⟩
  have h1_mem : evalEuclideanHom φ j 1 (b z) ∈
      Submodule.span ℂ (Set.range (partialBasisVec φ j)) := by
    rw [span_range_partialBasisVec_eq_range_one]; exact ⟨b z, rfl⟩
  have h1_self : inner ℂ (evalEuclideanHom φ j 1 (b z)) (evalEuclideanHom φ j 1 (b z)) = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      ← map_star, star_one, ← mul_apply_eq_comp, ← map_mul, one_mul]
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (horth h1_mem)
  rw [← mul_one x, map_mul, mul_apply_eq_comp, inner_self_eq_zero.mp h1_self, map_zero]

private theorem toEuclideanCLM_blockHom_single_basisFun [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (n i)] {M : Type*} [Fintype M] [DecidableEq M]
    (r : ι → ℕ) (f : (Σ i, n i × Fin (r i)) ↪ M) (i : ι) [DecidableEq (n i)]
    (p q : n i) (z : M) :
    CStarMatrix.toEuclideanCLM
        (TauCeti.cstarMatrixBlockHom r f (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p q 1))))
        (EuclideanSpace.basisFun M ℂ z) =
      ∑ t : Fin (r i),
        if z = f ⟨i, q, t⟩ then EuclideanSpace.basisFun M ℂ (f ⟨i, p, t⟩) else 0 := by
  rw [TauCeti.cstarMatrixBlockHom_piSingle_single, CStarMatrix.toEuclideanCLM_apply,
    Equiv.symm_apply_apply, map_sum, sum_apply]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Matrix.toEuclideanCLM_single_basisFun, one_smul]

private theorem intertwine_single_of_basis [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) {f : (Σ i, n i × Fin (φ.multiplicityMatrix j i)) ↪ m j}
    {b : OrthonormalBasis (m j) ℂ (EuclideanSpace ℂ (m j))}
    (hb : ∀ a, b (f a) = partialBasisVec φ j a) (i : ι) (p q : n i) :
    (b.repr.symm : EuclideanSpace ℂ (m j) →L[ℂ] EuclideanSpace ℂ (m j)) *
        CStarMatrix.toEuclideanCLM
          (TauCeti.cstarMatrixBlockHom (φ.multiplicityMatrix j) f
            (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p q 1)))) =
      evalEuclideanHom φ j (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p q 1))) *
        (b.repr.symm : EuclideanSpace ℂ (m j) →L[ℂ] EuclideanSpace ℂ (m j)) := by
  have hU (z : m j) : (b.repr.symm : EuclideanSpace ℂ (m j) →L[ℂ] EuclideanSpace ℂ (m j))
      (EuclideanSpace.basisFun (m j) ℂ z) = b z := by simp [EuclideanSpace.basisFun_apply]
  have hfinj := f.injective
  apply ContinuousLinearMap.coe_injective
  refine (EuclideanSpace.basisFun (m j) ℂ).toBasis.ext fun z ↦ ?_
  simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe, mul_apply_eq_comp,
    hU z, toEuclideanCLM_blockHom_single_basisFun]
  by_cases hz : z ∈ Set.range f
  · rcases hz with ⟨⟨i', q', t'⟩, rfl⟩
    rw [hb, evalEuclideanHom_single_partialBasisVec]
    by_cases hi : i = i'
    · subst hi
      by_cases hq : q = q'
      · subst hq; rw [Fintype.sum_eq_single t' fun _ _ ↦ by grind]; simp [hb]
      · rw [Finset.sum_eq_zero fun _ _ ↦ by grind]; simp [hq]
    · rw [Finset.sum_eq_zero fun _ _ ↦ by grind]; simp [hi]
  · rw [Finset.sum_eq_zero fun _ _ ↦ by grind, map_zero,
      evalEuclideanHom_eq_zero_of_notMem_range φ j hb hz]

private theorem intertwine_of_basis [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) {f : (Σ i, n i × Fin (φ.multiplicityMatrix j i)) ↪ m j}
    {b : OrthonormalBasis (m j) ℂ (EuclideanSpace ℂ (m j))}
    (hb : ∀ a, b (f a) = partialBasisVec φ j a) (x : ∀ i, CStarMatrix (n i) (n i) ℂ) :
    (b.repr.symm : EuclideanSpace ℂ (m j) →L[ℂ] EuclideanSpace ℂ (m j)) *
        CStarMatrix.toEuclideanCLM
          (TauCeti.cstarMatrixBlockHom (φ.multiplicityMatrix j) f x) =
      evalEuclideanHom φ j x *
        (b.repr.symm : EuclideanSpace ℂ (m j) →L[ℂ] EuclideanSpace ℂ (m j)) := by
  ext w
  have key (i : ι) (p q : n i) :=
    congrFun (congrArg DFunLike.coe (intertwine_single_of_basis φ j hb i p q)) w
  simp only [mul_apply_eq_comp] at key ⊢
  conv_lhs => rw [CStarMatrix.eq_sum_smul_piSingle_ofMatrix_single_one x]
  conv_rhs => rw [CStarMatrix.eq_sum_smul_piSingle_ofMatrix_single_one x]
  simp only [map_sum, map_smul, sum_apply, smul_apply, key]

private theorem exists_orthonormalBasis_partialBasisVec [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (f : (Σ i, n i × Fin (φ.multiplicityMatrix j i)) ↪ m j) :
    ∃ b : OrthonormalBasis (m j) ℂ (EuclideanSpace ℂ (m j)),
      ∀ a, b (f a) = partialBasisVec φ j a := by
  let s : Set (m j) := Set.range f
  let v : m j → EuclideanSpace ℂ (m j) := Function.extend f (partialBasisVec φ j) 0
  have hv_apply (a : Σ i, n i × Fin (φ.multiplicityMatrix j i)) :
      v (f a) = partialBasisVec φ j a := f.injective.extend_apply _ _ a
  have hv_orth : Orthonormal ℂ (s.domRestrict v) := by
    have heq : s.domRestrict v ∘ Equiv.ofInjective f f.injective = partialBasisVec φ j :=
      funext fun a ↦ hv_apply a
    have hcomp := (orthonormal_partialBasisVec φ j).comp
      (Equiv.ofInjective f f.injective).symm (Equiv.injective _)
    simpa [← heq, Function.comp_assoc] using hcomp
  obtain ⟨b, hb_mem⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (finrank_euclideanSpace (𝕜 := ℂ) (ι := m j)) hv_orth
  exact ⟨b, fun a ↦ (hb_mem (f a) ⟨a, rfl⟩).trans (hv_apply a)⟩

private theorem exists_unitary_conj_cstarMatrixBlockHom [Fintype ι]
    [∀ i, Fintype (n i)] [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (f : (Σ i, n i × Fin (φ.multiplicityMatrix j i)) ↪ m j) :
    ∃ u : unitary (CStarMatrix (m j) (m j) ℂ), ∀ x,
      (u : CStarMatrix (m j) (m j) ℂ) * TauCeti.cstarMatrixBlockHom (φ.multiplicityMatrix j) f x *
        star (u : CStarMatrix (m j) (m j) ℂ) = φ x j := by
  let _ := Classical.decEq ι
  let _ := fun i ↦ Classical.decEq (n i)
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_partialBasisVec φ j f
  let uH : unitary (EuclideanSpace ℂ (m j) →L[ℂ] EuclideanSpace ℂ (m j)) :=
    Unitary.linearIsometryEquiv.symm b.repr.symm
  let u : unitary (CStarMatrix (m j) (m j) ℂ) :=
    ⟨CStarMatrix.toEuclideanCLM.symm uH, Unitary.map_mem CStarMatrix.toEuclideanCLM.symm uH.prop⟩
  refine ⟨u, fun x ↦ CStarMatrix.toEuclideanCLM.injective ?_⟩
  have hu : CStarMatrix.toEuclideanCLM (u : CStarMatrix (m j) (m j) ℂ) =
      (b.repr.symm : _ →L[ℂ] _) := by
    rw [StarAlgEquiv.apply_symm_apply, Unitary.coe_symm_linearIsometryEquiv_apply]
  calc CStarMatrix.toEuclideanCLM
        ((u : CStarMatrix (m j) (m j) ℂ) *
          TauCeti.cstarMatrixBlockHom (φ.multiplicityMatrix j) f x *
          star (u : CStarMatrix (m j) (m j) ℂ))
      = ((b.repr.symm : _ →L[ℂ] _) *
          CStarMatrix.toEuclideanCLM
            (TauCeti.cstarMatrixBlockHom (φ.multiplicityMatrix j) f x)) *
          star (uH : _ →L[ℂ] _) := by
        rw [map_mul, map_mul, map_star, hu, Unitary.coe_symm_linearIsometryEquiv_apply, mul_assoc]
    _ = evalEuclideanHom φ j x * ((uH : _ →L[ℂ] _) * star (uH : _ →L[ℂ] _)) := by
        rw [intertwine_of_basis φ j hb x, mul_assoc, ← Unitary.coe_symm_linearIsometryEquiv_apply]
    _ = CStarMatrix.toEuclideanCLM (φ x j) := by
        rw [Unitary.mul_star_self_of_mem uH.prop, mul_one, evalEuclideanHom_apply]

/-- **Standard block-diagonal form up to unitary conjugacy**: every `⋆`-homomorphism `φ` is
unitarily conjugate in the target to `TauCeti.cstarMatrixPiBlockHom φ.multiplicityMatrix f` for any
family of injections `f j : (Σ i, n i × Fin (φ.multiplicityMatrix j i)) ↪ m j`. -/
theorem exists_unitary_conj_cstarMatrixPiBlockHom [Fintype ι]
    [∀ i, Fintype (n i)] [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (f : ∀ j, (Σ i, n i × Fin (φ.multiplicityMatrix j i)) ↪ m j) :
    ∃ u : unitary (∀ j, CStarMatrix (m j) (m j) ℂ), ∀ x,
      (u : ∀ j, CStarMatrix (m j) (m j) ℂ) *
        TauCeti.cstarMatrixPiBlockHom φ.multiplicityMatrix f x *
        star (u : ∀ j, CStarMatrix (m j) (m j) ℂ) = φ x := by
  choose u hu using fun j ↦ φ.exists_unitary_conj_cstarMatrixBlockHom j (f j)
  refine ⟨⟨fun j ↦ u j, Pi.mem_unitary_iff.mpr fun j ↦ (u j).prop⟩, fun x ↦ funext fun j ↦ ?_⟩
  simpa only [Pi.mul_apply, Pi.star_apply, TauCeti.cstarMatrixPiBlockHom_apply] using hu j x

/-- Unitary conjugation in the target leaves `multiplicityMatrix` invariant. -/
@[simp high]
theorem multiplicityMatrix_conjStarAlgAut_comp [∀ i, Fintype (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (u : unitary (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    ((Unitary.conjStarAlgAut ℂ _ u).toNonUnitalStarAlgHom.comp φ).multiplicityMatrix =
      φ.multiplicityMatrix := by
  classical
  ext j i
  rcases isEmpty_or_nonempty (n i) with hE | hne
  · simp
  · obtain ⟨p⟩ := hne
    apply Nat.cast_injective (R := ℂ)
    rw [natCast_multiplicityMatrix_apply_eq_trace_single _ j i p,
      natCast_multiplicityMatrix_apply_eq_trace_single φ j i p]
    simpa only [comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply, Unitary.conjStarAlgAut_apply,
      Pi.mul_apply, Pi.star_apply] using
      CStarMatrix.trace_ofMatrix_symm_unitary_conj (Pi.mem_unitary_iff.mp u.prop j) _

/-- Unitary conjugation in the source leaves `multiplicityMatrix` invariant. -/
@[simp high]
theorem multiplicityMatrix_comp_conjStarAlgAut
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] [∀ j, Fintype (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (u : unitary (∀ i, CStarMatrix (n i) (n i) ℂ)) :
    (φ.comp (Unitary.conjStarAlgAut ℂ _ u).toNonUnitalStarAlgHom).multiplicityMatrix =
      φ.multiplicityMatrix := by
  classical
  ext j i
  have hunit : Unitary.conjStarAlgAut ℂ (∀ i', CStarMatrix (n i') (n i') ℂ) u
      (Pi.single i 1) = Pi.single i 1 := by
    ext i' r s
    by_cases hi : i' = i
    · subst hi; simp [Unitary.conjStarAlgAut_apply,
        Unitary.mul_star_self_of_mem (Pi.mem_unitary_iff.mp u.prop i')]
    · simp [Unitary.conjStarAlgAut_apply, Pi.single_eq_of_ne hi]
  simp [multiplicityMatrix_apply, hunit]

/-- Entrywise formula for the multiplicity matrix of a unitary inner automorphism: `1` on the
diagonal at nonempty blocks, and `0` elsewhere. -/
theorem multiplicityMatrix_conjStarAlgAut_apply [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (u : unitary (∀ i, CStarMatrix (n i) (n i) ℂ)) (i' i : ι) :
    (Unitary.conjStarAlgAut ℂ (∀ i, CStarMatrix (n i) (n i) ℂ)
        u).toNonUnitalStarAlgHom.multiplicityMatrix i' i =
      if i' = i ∧ Fintype.card (n i) ≠ 0 then 1 else 0 := by
  have hcomp : (Unitary.conjStarAlgAut ℂ (∀ i, CStarMatrix (n i) (n i) ℂ)
      u).toNonUnitalStarAlgHom =
      (Unitary.conjStarAlgAut ℂ _ u).toNonUnitalStarAlgHom.comp (.id ℂ _) := by ext; simp
  rw [hcomp, multiplicityMatrix_conjStarAlgAut_comp, multiplicityMatrix_id_apply]

/-- When every block index type `n i` is nonempty, a unitary inner automorphism has the identity
multiplicity matrix. -/
@[simp]
theorem multiplicityMatrix_conjStarAlgAut [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] [∀ i, Nonempty (n i)]
    (u : unitary (∀ i, CStarMatrix (n i) (n i) ℂ)) :
    (Unitary.conjStarAlgAut ℂ (∀ i, CStarMatrix (n i) (n i) ℂ)
        u).toNonUnitalStarAlgHom.multiplicityMatrix = 1 := by
  ext i' i; rw [multiplicityMatrix_conjStarAlgAut_apply, Matrix.one_apply]
  simp [Fintype.card_ne_zero]

private def canonicalBlockEmbedding [Fintype ι] [∀ i, Fintype (n i)] [∀ j, Fintype (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) (j : κ) :
    (Σ i, n i × Fin (φ.multiplicityMatrix j i)) ↪ m j :=
  Classical.choice <| Function.Embedding.nonempty_of_card_le <| by
    simpa [Fintype.card_sigma, Fintype.card_prod, mul_comm] using
      φ.sum_multiplicityMatrix_mul_card_le j

/-- **Classification up to unitary conjugacy**: two `⋆`-homomorphisms between finite products of
complex matrix C⋆-algebras are unitarily conjugate in the target if and only if they have the same
multiplicity matrix. -/
theorem exists_unitary_conj_iff_multiplicityMatrix_eq [Finite ι] [∀ i, Fintype (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ ψ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    (∃ u : unitary (∀ j, CStarMatrix (m j) (m j) ℂ), ∀ x,
        (u : ∀ j, CStarMatrix (m j) (m j) ℂ) * φ x *
          star (u : ∀ j, CStarMatrix (m j) (m j) ℂ) = ψ x) ↔
      φ.multiplicityMatrix = ψ.multiplicityMatrix := by
  cases nonempty_fintype ι
  classical
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun hEq ↦ ?_⟩
  · have hψ : ψ = (Unitary.conjStarAlgAut ℂ _ u).toNonUnitalStarAlgHom.comp φ :=
      NonUnitalStarAlgHom.ext fun x ↦ by
        rw [comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply, Unitary.conjStarAlgAut_apply,
          hu x]
    rw [hψ, φ.multiplicityMatrix_conjStarAlgAut_comp u]
  · let B := ∀ j, CStarMatrix (m j) (m j) ℂ
    let f := φ.canonicalBlockEmbedding
    let φ₀ := TauCeti.cstarMatrixPiBlockHom φ.multiplicityMatrix f
    obtain ⟨u₁, hu₁⟩ := φ.exists_unitary_conj_cstarMatrixPiBlockHom f
    obtain ⟨u₂, hu₂⟩ := ψ.exists_unitary_conj_cstarMatrixPiBlockHom (hEq ▸ f)
    have hcast {H₁ H₂ : Matrix κ ι ℕ} (h : H₁ = H₂)
        (g : ∀ j, (Σ i, n i × Fin (H₁ j i)) ↪ m j) :
        TauCeti.cstarMatrixPiBlockHom H₂ (h ▸ g) = TauCeti.cstarMatrixPiBlockHom H₁ g := by
      subst h; rfl
    rw [hcast hEq f] at hu₂
    refine ⟨u₂ * star u₁, fun x ↦ ?_⟩
    calc ((u₂ * star u₁ : unitary B) : B) * φ x * star ((u₂ * star u₁ : unitary B) : B)
        = ((u₂ : B) * star (u₁ : B)) * ((u₁ : B) * φ₀ x * star (u₁ : B)) *
            ((u₁ : B) * star (u₂ : B)) := by
          rw [← hu₁ x]
          simp [φ₀]
      _ = (u₂ : B) * ((star (u₁ : B) * (u₁ : B)) * φ₀ x * (star (u₁ : B) * (u₁ : B))) *
            star (u₂ : B) := by
          simp only [mul_assoc]
      _ = (u₂ : B) * φ₀ x * star (u₂ : B) := by
          rw [Unitary.coe_star_mul_self, one_mul, mul_one]
      _ = ψ x := hu₂ x

end UnitaryConjugacy

section ApproximateUnitaryEquivalence

open scoped ComplexOrder

/-- Two `⋆`-homomorphisms between finite products of complex matrix C⋆-algebras are approximately
unitarily equivalent in the target if and only if they have the same multiplicity matrix (hence, by
`exists_unitary_conj_iff_multiplicityMatrix_eq`, if and only if they are unitarily conjugate). -/
theorem approximatelyUnitarilyEquivalent_iff_multiplicityMatrix_eq
    {ι κ : Type*} {n : ι → Type*} {m : κ → Type*} [Fintype ι] [Fintype κ] [∀ i, Fintype (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ ψ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    TauCeti.ApproximatelyUnitarilyEquivalent φ ψ ↔
      φ.multiplicityMatrix = ψ.multiplicityMatrix := by
  classical
  refine ⟨fun h ↦ ?_, fun hEq ↦ ?_⟩
  · ext j i
    rcases isEmpty_or_nonempty (n i) with hE | hne
    · simp
    · obtain ⟨p⟩ := hne
      let B := ∀ j', CStarMatrix (m j') (m j') ℂ
      let e : ∀ i', CStarMatrix (n i') (n i') ℂ :=
        Pi.single i (CStarMatrix.ofMatrix (Matrix.single p p 1))
      let τ : B → ℂ := fun y ↦ Matrix.trace (CStarMatrix.ofMatrix.symm (y j))
      have hcont : Continuous τ :=
        CStarMatrix.continuous_trace_ofMatrix_symm.comp (continuous_apply j)
      obtain ⟨δ, hδ, hlt⟩ :=
        Metric.continuousAt_iff.mp (hcont.continuousAt (x := ψ e)) 1 zero_lt_one
      obtain ⟨u, hu⟩ := (TauCeti.approximatelyUnitarilyEquivalent_def φ ψ).mp h {e} δ hδ
      have hdist : dist (τ ((u : B) * φ e * star (u : B))) (τ (ψ e)) < 1 :=
        hlt <| by simpa only [dist_eq_norm] using hu e (Finset.mem_singleton_self e)
      simp only [τ, e, Pi.mul_apply, Pi.star_apply,
        CStarMatrix.trace_ofMatrix_symm_unitary_conj (Pi.mem_unitary_iff.mp u.prop j),
        ← φ.natCast_multiplicityMatrix_apply_eq_trace_single j i p,
        ← ψ.natCast_multiplicityMatrix_apply_eq_trace_single j i p] at hdist
      exact Nat.cast_injective (R := ℤ) (TauCeti.eq_of_dist_intCast_lt_one (by simpa using hdist))
  · obtain ⟨u, hu⟩ := (φ.exists_unitary_conj_iff_multiplicityMatrix_eq ψ).mpr hEq
    exact TauCeti.ApproximatelyUnitarilyEquivalent.of_unitary u hu

end ApproximateUnitaryEquivalence

section Composition

variable {ι κ μ : Type*} {n : ι → Type*} {m : κ → Type*} {l : μ → Type*}

private theorem multiplicityMatrix_comp_of_finite [Finite ι] [Fintype κ]
    [∀ i, Fintype (n i)] [∀ j, Fintype (m j)] [∀ k, Fintype (l k)]
    (ψ : (∀ j, CStarMatrix (m j) (m j) ℂ) →⋆ₙₐ[ℂ] (∀ k, CStarMatrix (l k) (l k) ℂ))
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    (ψ.comp φ).multiplicityMatrix = ψ.multiplicityMatrix * φ.multiplicityMatrix := by
  cases nonempty_fintype ι
  classical
  let f := φ.canonicalBlockEmbedding
  let φ₀ := TauCeti.cstarMatrixPiBlockHom φ.multiplicityMatrix f
  obtain ⟨u, hu⟩ := φ.exists_unitary_conj_cstarMatrixPiBlockHom f
  let ψ' := ψ.comp (Unitary.conjStarAlgAut ℂ _ u).toNonUnitalStarAlgHom
  have hcomp_eq : ψ.comp φ = ψ'.comp φ₀ :=
    NonUnitalStarAlgHom.ext fun x ↦ by
      dsimp only [ψ', φ₀]
      rw [comp_apply, comp_apply, comp_apply, StarAlgEquiv.toNonUnitalStarAlgHom_apply,
        Unitary.conjStarAlgAut_apply, hu x]
  ext k i
  rw [hcomp_eq, Matrix.mul_apply]
  rcases isEmpty_or_nonempty (n i) with hE | hne
  · simp
  · obtain ⟨p⟩ := hne
    apply Nat.cast_injective (R := ℂ)
    rw [(ψ'.comp φ₀).natCast_multiplicityMatrix_apply_eq_trace_single k i p, comp_apply]
    have hφ₀ : φ₀ (Pi.single i (CStarMatrix.ofMatrix (Matrix.single p p 1))) =
        ∑ j : κ, ∑ t : Fin (φ.multiplicityMatrix j i),
          Pi.single j (CStarMatrix.ofMatrix (Matrix.single (f j ⟨i, p, t⟩) (f j ⟨i, p, t⟩) 1)) := by
      funext j; apply CStarMatrix.ofMatrix.symm.injective
      simp only [φ₀, TauCeti.cstarMatrixPiBlockHom_apply,
        TauCeti.cstarMatrixBlockHom_piSingle_single, Finset.sum_apply, Equiv.symm_apply_apply]
      rw [Fintype.sum_eq_single j fun j' hj' ↦ by simp [Pi.single_eq_of_ne hj'.symm]]
      simp [CStarMatrix.ofMatrix_symm_sum]
    rw [hφ₀, map_sum, Finset.sum_apply, CStarMatrix.ofMatrix_symm_sum, Matrix.trace_sum,
      Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_sum, Finset.sum_apply, CStarMatrix.ofMatrix_symm_sum, Matrix.trace_sum]
    simp_rw [← ψ'.natCast_multiplicityMatrix_apply_eq_trace_single k j _]
    simp [ψ', mul_comm]

private theorem multiplicityMatrix_comp_singleFunUnique_apply [DecidableEq ι]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] [∀ j, Fintype (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (j : κ) (i : ι) :
    (φ.comp (NonUnitalStarAlgHom.singleFunUnique ℂ Unit
        (fun i' ↦ CStarMatrix (n i') (n i') ℂ) i)).multiplicityMatrix j () =
      φ.multiplicityMatrix j i := by
  rw [multiplicityMatrix_apply, multiplicityMatrix_apply, comp_apply]
  simp

/-- **Functoriality of the multiplicity matrix**: composition of `⋆`-homomorphisms between products
of complex matrix C⋆-algebras corresponds to matrix multiplication of their multiplicity matrices.
-/
@[simp]
theorem multiplicityMatrix_comp [Fintype κ]
    [∀ i, Fintype (n i)] [∀ j, Fintype (m j)] [∀ k, Fintype (l k)]
    (ψ : (∀ j, CStarMatrix (m j) (m j) ℂ) →⋆ₙₐ[ℂ] (∀ k, CStarMatrix (l k) (l k) ℂ))
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₙₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    (ψ.comp φ).multiplicityMatrix = ψ.multiplicityMatrix * φ.multiplicityMatrix := by
  classical
  ext k i
  -- Column `i` depends only on the `i`-th source block, reducing to the `Unit`-indexed finite case.
  let ιHom := NonUnitalStarAlgHom.singleFunUnique ℂ Unit (fun i' ↦ CStarMatrix (n i') (n i') ℂ) i
  have hunit := congrFun (congrFun (multiplicityMatrix_comp_of_finite ψ (φ.comp ιHom)) k) ()
  rw [← multiplicityMatrix_comp_singleFunUnique_apply (ψ.comp φ) k i, comp_assoc, hunit,
    Matrix.mul_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun j _ ↦
    congrArg (ψ.multiplicityMatrix k j * ·) (multiplicityMatrix_comp_singleFunUnique_apply φ j i)

end Composition

end NonUnitalStarAlgHom

namespace StarAlgHom

variable {ι κ μ : Type*} {n : ι → Type*} {m : κ → Type*} {l : μ → Type*}

/-- Unitary conjugation in the target leaves the multiplicity matrix of a unital `⋆`-homomorphism
invariant. -/
theorem multiplicityMatrix_conjStarAlgAut_comp [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (u : unitary (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    (((Unitary.conjStarAlgAut ℂ _ u).toStarAlgHom.comp φ).toNonUnitalStarAlgHom).multiplicityMatrix
      = φ.toNonUnitalStarAlgHom.multiplicityMatrix := by
  rw [toNonUnitalStarAlgHom_comp, StarAlgEquiv.toNonUnitalStarAlgHom_toStarAlgHom,
    NonUnitalStarAlgHom.multiplicityMatrix_conjStarAlgAut_comp]

/-- Unitary conjugation in the source leaves the multiplicity matrix of a unital `⋆`-homomorphism
invariant. -/
theorem multiplicityMatrix_comp_conjStarAlgAut [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ))
    (u : unitary (∀ i, CStarMatrix (n i) (n i) ℂ)) :
    ((φ.comp (Unitary.conjStarAlgAut ℂ _ u).toStarAlgHom).toNonUnitalStarAlgHom).multiplicityMatrix
      = φ.toNonUnitalStarAlgHom.multiplicityMatrix := by
  rw [toNonUnitalStarAlgHom_comp, StarAlgEquiv.toNonUnitalStarAlgHom_toStarAlgHom,
    NonUnitalStarAlgHom.multiplicityMatrix_comp_conjStarAlgAut]

/-- **Classification of unital `⋆`-homomorphisms up to unitary conjugacy**: two unital
`⋆`-homomorphisms between finite products of complex matrix C⋆-algebras are unitarily conjugate in
the target if and only if their multiplicity matrices coincide. -/
theorem exists_unitary_conj_iff_multiplicityMatrix_eq [Finite ι] [∀ i, Fintype (n i)]
    [∀ i, DecidableEq (n i)] [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
    (φ ψ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    (∃ u : unitary (∀ j, CStarMatrix (m j) (m j) ℂ), ∀ x,
        (u : ∀ j, CStarMatrix (m j) (m j) ℂ) * φ x *
          star (u : ∀ j, CStarMatrix (m j) (m j) ℂ) = ψ x) ↔
      φ.toNonUnitalStarAlgHom.multiplicityMatrix = ψ.toNonUnitalStarAlgHom.multiplicityMatrix := by
  simp_rw [← StarAlgHom.coe_toNonUnitalStarAlgHom]
  exact φ.toNonUnitalStarAlgHom.exists_unitary_conj_iff_multiplicityMatrix_eq
    ψ.toNonUnitalStarAlgHom

/-- Composition of unital `⋆`-homomorphisms multiplies their multiplicity matrices. -/
theorem multiplicityMatrix_comp [Fintype κ] [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)] [∀ k, Fintype (l k)] [∀ k, DecidableEq (l k)]
    (ψ : (∀ j, CStarMatrix (m j) (m j) ℂ) →⋆ₐ[ℂ] (∀ k, CStarMatrix (l k) (l k) ℂ))
    (φ : (∀ i, CStarMatrix (n i) (n i) ℂ) →⋆ₐ[ℂ] (∀ j, CStarMatrix (m j) (m j) ℂ)) :
    (ψ.comp φ).toNonUnitalStarAlgHom.multiplicityMatrix =
      ψ.toNonUnitalStarAlgHom.multiplicityMatrix * φ.toNonUnitalStarAlgHom.multiplicityMatrix := by
  rw [toNonUnitalStarAlgHom_comp, NonUnitalStarAlgHom.multiplicityMatrix_comp]

end StarAlgHom

namespace TauCeti

/-- **Divisibility criterion for unital matrix embeddings**: a unital `⋆`-homomorphism
`CStarMatrix n n ℂ →⋆ₐ[ℂ] CStarMatrix m m ℂ` exists if and only if
`Fintype.card n ∣ Fintype.card m`. -/
theorem nonempty_starAlgHom_cstarMatrix_iff {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] :
    Nonempty (CStarMatrix n n ℂ →⋆ₐ[ℂ] CStarMatrix m m ℂ) ↔ Fintype.card n ∣ Fintype.card m := by
  let e := StarAlgHom.funUniqueEquiv ℂ Unit Unit (CStarMatrix n n ℂ) (CStarMatrix m m ℂ)
  refine ⟨fun ⟨φ⟩ ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩
  · have hsum := (e.symm φ).sum_multiplicityMatrix_mul_card_eq ()
    rw [Fintype.sum_unique] at hsum
    exact ⟨(e.symm φ).toNonUnitalStarAlgHom.multiplicityMatrix () (), by rw [mul_comm, hsum]⟩
  · classical
    let entry : ℕ := if Nonempty n then k else 0
    obtain ⟨φ', _⟩ := (exists_starAlgHom_multiplicityMatrix_eq_iff
      (n := fun _ : Unit ↦ n) (m := fun _ : Unit ↦ m) (Matrix.of fun _ _ ↦ entry)).mpr
      ⟨fun _ _ hE ↦ by simp [entry, not_nonempty_iff.mpr hE], fun _ ↦ by
        rcases isEmpty_or_nonempty n with hE | hne
        · simp [Fintype.card_eq_zero, hk]
        · simp [entry, hne, hk, mul_comm]⟩
    exact ⟨e φ'⟩

end TauCeti

namespace StarAlgHom

/-- **Uniqueness of unital matrix embeddings up to unitary conjugacy**: any two unital
`⋆`-homomorphisms `CStarMatrix n n ℂ →⋆ₐ[ℂ] CStarMatrix m m ℂ` are unitarily conjugate in
`CStarMatrix m m ℂ`. -/
theorem exists_unitary_conj_cstarMatrix {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (φ ψ : CStarMatrix n n ℂ →⋆ₐ[ℂ] CStarMatrix m m ℂ) :
    ∃ u : unitary (CStarMatrix m m ℂ), ∀ x,
      (u : CStarMatrix m m ℂ) * φ x * star (u : CStarMatrix m m ℂ) = ψ x := by
  let e := StarAlgHom.funUniqueEquiv ℂ Unit Unit (CStarMatrix n n ℂ) (CStarMatrix m m ℂ)
  rw [← StarAlgHom.exists_unitary_conj_funUniqueEquiv_symm_iff (R := ℂ) (ι := Unit) (κ := Unit),
    exists_unitary_conj_iff_multiplicityMatrix_eq]
  ext ⟨⟩ ⟨⟩
  rcases isEmpty_or_nonempty n with hE | hne
  · simp
  · have h₁ := (e.symm φ).sum_multiplicityMatrix_mul_card_eq ()
    have h₂ := (e.symm ψ).sum_multiplicityMatrix_mul_card_eq ()
    rw [Fintype.sum_unique] at h₁ h₂
    exact Nat.mul_right_cancel Fintype.card_pos (h₁.trans h₂.symm)

end StarAlgHom

end
