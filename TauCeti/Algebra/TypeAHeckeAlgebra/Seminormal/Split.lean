/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Seminormal
public import TauCeti.Combinatorics.Young.Partitions
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Reindex
import TauCeti.Algebra.TypeAHeckeAlgebra.Seminormal.Irreducible
import TauCeti.Algebra.Algebra.Subalgebra.Pi
import TauCeti.Combinatorics.Young.RSK
import TauCeti.Combinatorics.Young.StandardTableau.Separation

/-!
# The split seminormal decomposition of the type-A Hecke algebra

When the quantum factorial at `Q = q²` is nonzero, the joint seminormal representation identifies
`H_n(q)` with the product of full matrix algebras indexed by partitions of `n`. The native
matrices have actual standard tableaux as row and column indices; reindexing gives matrices of
size `standardCount`.

## Main results

* `seminormalPiEquiv` gives the decomposition with tableau-indexed matrix blocks.
* `seminormalPiEquiv_apply` computes a partition block using its seminormal representation.
* `seminormalPiEquiv_additiveJucysMurphy` gives the diagonal of an additive Jucys–Murphy element.
* `nonempty_algEquiv_pi_matrix_of_prod_ne_zero` gives existence with `Fin`-indexed blocks.

## References

* H. Wenzl, *Hecke algebras of type A and subfactors*, Invent. Math. 92 (1988), 349–383,
  Theorem 2.2, DOI: 10.1007/BF01404457, for the complex split decomposition and quantum-factorial
  criterion.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

open YoungTableau Matrix

variable {K : Type*} [Field K] {q : Kˣ} {n : ℕ}

private theorem additiveContent_ne_zero_of_le_card_ofPartition
    (hn : ∀ d : ℕ, 0 < d → d ≤ n → additiveContent ((q : K) ^ 2) d ≠ 0)
    (μ : n.Partition) (d : ℕ) (hd : 0 < d) (hdμ : d ≤ (YoungDiagram.ofPartition μ).card) :
    additiveContent ((q : K) ^ 2) d ≠ 0 :=
  hn d hd (hdμ.trans_eq (YoungDiagram.card_ofPartition μ))

private noncomputable def seminormalPi
    (hn : ∀ d : ℕ, 0 < d → d ≤ n → additiveContent ((q : K) ^ 2) d ≠ 0) :
    TypeAHeckeAlgebra K q n →ₐ[K] Π μ : n.Partition,
      Matrix (StandardYoungTableau (YoungDiagram.ofPartition μ))
        (StandardYoungTableau (YoungDiagram.ofPartition μ)) K :=
  AlgHom.pi fun μ =>
    (LinearMap.toMatrixAlgEquiv' : Module.End K _ ≃ₐ[K] Matrix _ _ K).toAlgHom.comp
      ((seminormalRep q (YoungDiagram.ofPartition μ) fun d hd hdμ =>
        additiveContent_ne_zero_of_le_card_ofPartition hn μ d hd hdμ.le).comp
          (AlgEquiv.cast (YoungDiagram.card_ofPartition μ).symm).toAlgHom)

private theorem seminormalPi_apply
    (hn : ∀ d : ℕ, 0 < d → d ≤ n → additiveContent ((q : K) ^ 2) d ≠ 0)
    (x : TypeAHeckeAlgebra K q n) (μ : n.Partition) :
    seminormalPi hn x μ = LinearMap.toMatrixAlgEquiv'
      (seminormalRep q (YoungDiagram.ofPartition μ)
        (fun d hd hdμ => additiveContent_ne_zero_of_le_card_ofPartition hn μ d hd hdμ.le)
        ((AlgEquiv.cast (YoungDiagram.card_ofPartition μ).symm :
          TypeAHeckeAlgebra K q n ≃ₐ[K]
            TypeAHeckeAlgebra K q (YoungDiagram.ofPartition μ).card) x)) :=
  rfl

private noncomputable def jointDiagonal :
    ((Σ μ : n.Partition, StandardYoungTableau (YoungDiagram.ofPartition μ)) → K) →ₐ[K]
      Π μ : n.Partition, Matrix (StandardYoungTableau (YoungDiagram.ofPartition μ))
        (StandardYoungTableau (YoungDiagram.ofPartition μ)) K :=
  AlgHom.pi fun μ =>
    (diagonalAlgHom K).comp (AlgHom.pi fun U => Pi.evalAlgHom K (fun _ => K) ⟨μ, U⟩)

private theorem jointDiagonal_apply
    (f : (Σ μ : n.Partition, StandardYoungTableau (YoungDiagram.ofPartition μ)) → K)
    (μ : n.Partition) :
    jointDiagonal f μ = diagonal (fun U => f ⟨μ, U⟩) :=
  rfl

private theorem seminormalPi_additiveJucysMurphy_apply
    (hn : ∀ d : ℕ, 0 < d → d ≤ n → additiveContent ((q : K) ^ 2) d ≠ 0)
    (i : Fin n) (μ : n.Partition) :
    seminormalPi hn (additiveJucysMurphy q i) μ = diagonal (fun U =>
      additiveContent ((q : K) ^ 2) (labelContent U.toTableau
        (Fin.cast (YoungDiagram.card_ofPartition μ).symm i))) := by
  apply (toLinAlgEquiv' : Matrix _ _ K ≃ₐ[K] _).injective
  apply LinearMap.ext
  intro ψ
  funext U
  simp only [seminormalPi_apply, cast_additiveJucysMurphy, toLinAlgEquiv'_toMatrixAlgEquiv',
    seminormalRep_additiveJucysMurphy_apply, toLinAlgEquiv'_apply, mulVec_diagonal]

private theorem jointDiagonal_mem_range
    (hn : ∀ d : ℕ, 0 < d → d ≤ n → additiveContent ((q : K) ^ 2) d ≠ 0)
    (f : (Σ μ : n.Partition, StandardYoungTableau (YoungDiagram.ofPartition μ)) → K) :
    jointDiagonal f ∈ (seminormalPi hn).range := by
  -- The joint diagonal interpolation extends `single_self_mem_seminormalMatrices` in
  -- `Seminormal.Irreducible` to tableaux across all partitions.
  let S := (seminormalPi hn).range.comap jointDiagonal
  let φ (i : Fin n) (T : Σ μ : n.Partition, StandardYoungTableau (YoungDiagram.ofPartition μ)) :=
    additiveContent ((q : K) ^ 2) (labelContent T.2.toTableau
      (Fin.cast (YoungDiagram.card_ofPartition T.1).symm i))
  have hφ (i : Fin n) : φ i ∈ S :=
    ⟨additiveJucysMurphy q i, funext fun μ =>
      (seminormalPi_additiveJucysMurphy_apply hn i μ).trans (jointDiagonal_apply (φ i) μ).symm⟩
  have hinj := StandardYoungTableau.sigma_comp_labelContent_injective_of_injOn_addables
    (additiveContent ((q : K) ^ 2)) (fun μ hμ =>
      μ.injOn_additiveContent_cellContent_of_forall_ne_zero (pow_ne_zero 2 q.ne_zero)
        (fun d hd hdμ => hn d hd (hdμ.trans hμ)))
  have hsep : (S : Set ((Σ μ : n.Partition,
      StandardYoungTableau (YoungDiagram.ofPartition μ)) → K)).SeparatesPoints := by
    intro T U hTU
    by_contra! h
    exact hTU (hinj (funext fun i => h _ (hφ i)))
  have htop := Subalgebra.eq_top_of_separatesPoints hsep
  have hfS : f ∈ S := by
    rw [htop]
    trivial
  exact (Subalgebra.mem_comap _ _ f).mp hfS

private theorem seminormalPi_surjective
    (hn : ∀ d : ℕ, 0 < d → d ≤ n → additiveContent ((q : K) ^ 2) d ≠ 0) :
    Function.Surjective (seminormalPi hn) := by
  classical
  intro M
  have hsingle (μ : n.Partition) : Pi.single μ (M μ) ∈ (seminormalPi hn).range := by
    obtain ⟨x, hx⟩ := seminormalRep_surjective
      (q := q) (μ := YoungDiagram.ofPartition μ)
      (additiveContent_ne_zero_of_le_card_ofPartition hn μ)
      (toLinAlgEquiv' (M μ))
    let e : TypeAHeckeAlgebra K q n ≃ₐ[K]
        TypeAHeckeAlgebra K q (YoungDiagram.ofPartition μ).card :=
      AlgEquiv.cast (YoungDiagram.card_ofPartition μ).symm
    let y := e.symm x
    -- The cast in seminormalPi_apply is e, so it cancels the inverse cast in y.
    have hey : e y = x := e.apply_symm_apply x
    have hy : seminormalPi hn y μ = M μ := by
      rw [seminormalPi_apply, hey, hx, LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv']
    have hdiag : jointDiagonal (fun T => if T.1 = μ then (1 : K) else 0) = Pi.single μ 1 := by
      funext ν
      by_cases h : ν = μ
      · subst ν
        simp only [jointDiagonal_apply, ite_true, Pi.single_eq_same]
        exact diagonal_one
      · simp only [jointDiagonal_apply, ite_eq_right h, Pi.single_eq_of_ne h]
        exact diagonal_zero
    have hprod := (seminormalPi hn).range.mul_mem
      (jointDiagonal_mem_range hn (fun T => if T.1 = μ then 1 else 0))
      ((seminormalPi hn).mem_range_self y)
    rwa [hdiag, ← Pi.single_mul_left, one_mul, hy] at hprod
  apply (AlgHom.mem_range (seminormalPi hn)).mp
  rw [← Finset.univ_sum_single M]
  exact (seminormalPi hn).range.sum_mem fun μ _ => hsingle μ

private theorem seminormalPi_bijective
    (hn : ∀ d : ℕ, 0 < d → d ≤ n → additiveContent ((q : K) ^ 2) d ≠ 0) :
    Function.Bijective (seminormalPi hn) := by
  let : Module.Finite K (TypeAHeckeAlgebra K q n) :=
    Module.Finite.of_basis (basisTw q (permCoxeterSystem n))
  have htarget :
      Module.finrank K (Π μ : n.Partition,
        Matrix (StandardYoungTableau (YoungDiagram.ofPartition μ))
          (StandardYoungTableau (YoungDiagram.ofPartition μ)) K) = n.factorial := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_matrix, Module.finrank_self, mul_one]
    have h := Fintype.card_congr (rsk n)
    simpa only [Fintype.card_perm, Fintype.card_fin, Fintype.card_sigma,
      Fintype.card_prod] using h.symm
  have hdim : Module.finrank K (TypeAHeckeAlgebra K q n) =
      Module.finrank K (Π μ : n.Partition,
        Matrix (StandardYoungTableau (YoungDiagram.ofPartition μ))
          (StandardYoungTableau (YoungDiagram.ofPartition μ)) K) := by
    rw [finrank_eq_natCard (permCoxeterSystem n), Nat.card_eq_fintype_card,
      Fintype.card_perm, Fintype.card_fin, htarget]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (seminormalPi hn).toLinearMap) hdim).mpr (seminormalPi_surjective hn),
    seminormalPi_surjective hn⟩

/-- The joint seminormal representation is an algebra equivalence with the product of matrix
algebras indexed by the actual standard tableaux, when all quantum integers up to `n` are
nonzero. -/
noncomputable def seminormalPiEquiv
    (hn : ∀ d : ℕ, 0 < d → d ≤ n → additiveContent ((q : K) ^ 2) d ≠ 0) :
    TypeAHeckeAlgebra K q n ≃ₐ[K] Π μ : n.Partition,
      Matrix (StandardYoungTableau (YoungDiagram.ofPartition μ))
        (StandardYoungTableau (YoungDiagram.ofPartition μ)) K :=
  AlgEquiv.ofBijective (seminormalPi hn) (seminormalPi_bijective hn)

/-- The native split equivalence has the prescribed seminormal matrix in each partition block.
The cast only identifies the cardinality of the chosen partition diagram with `n`. -/
@[simp]
theorem seminormalPiEquiv_apply
    (hn : ∀ d : ℕ, 0 < d → d ≤ n → additiveContent ((q : K) ^ 2) d ≠ 0)
    (x : TypeAHeckeAlgebra K q n) (μ : n.Partition) :
    seminormalPiEquiv hn x μ = LinearMap.toMatrixAlgEquiv'
      (seminormalRep q (YoungDiagram.ofPartition μ)
        (fun d hd hdμ => hn d hd (hdμ.le.trans_eq (YoungDiagram.card_ofPartition μ)))
        ((AlgEquiv.cast (YoungDiagram.card_ofPartition μ).symm :
          TypeAHeckeAlgebra K q n ≃ₐ[K]
            TypeAHeckeAlgebra K q (YoungDiagram.ofPartition μ).card) x)) := by
  rw [seminormalPiEquiv, AlgEquiv.ofBijective_apply, seminormalPi_apply]

/-- In each split block, an additive Jucys–Murphy element is diagonal with entries given by
the additive contents of its label in the standard tableaux of that shape. -/
@[simp high] -- Prefer the diagonal formula to the general block formula.
theorem seminormalPiEquiv_additiveJucysMurphy
    (hn : ∀ d : ℕ, 0 < d → d ≤ n → additiveContent ((q : K) ^ 2) d ≠ 0)
    (i : Fin n) (μ : n.Partition) :
    seminormalPiEquiv hn (additiveJucysMurphy q i) μ = diagonal (fun U =>
      additiveContent ((q : K) ^ 2) (labelContent U.toTableau
        (Fin.cast (YoungDiagram.card_ofPartition μ).symm i))) := by
  rw [seminormalPiEquiv, AlgEquiv.ofBijective_apply, seminormalPi_additiveJucysMurphy_apply]

/-- **The split decomposition of the type-A Hecke algebra.** A nonzero quantum factorial gives
an isomorphism to the product, over partitions of `n`, of full matrix algebras whose sizes are
the numbers of standard tableaux. -/
theorem nonempty_algEquiv_pi_matrix_of_prod_ne_zero
    (q : Kˣ) (n : ℕ)
    (h : (∏ r ∈ Finset.range n, ∑ j ∈ Finset.range (r + 1), ((q : K) ^ 2) ^ j) ≠ 0) :
    Nonempty (TypeAHeckeAlgebra K q n ≃ₐ[K] Π μ : n.Partition,
      Matrix (Fin (standardCount (YoungDiagram.ofPartition μ)))
        (Fin (standardCount (YoungDiagram.ofPartition μ))) K) := by
  have hn (d : ℕ) (hd : 0 < d) (hdn : d ≤ n) :
      additiveContent ((q : K) ^ 2) d ≠ 0 := by
    have hd' : d - 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
    have hfactor := (Finset.prod_ne_zero_iff.mp h) (d - 1) hd'
    simpa only [additiveContent_natCast, Nat.sub_add_cancel hd] using hfactor
  exact ⟨(seminormalPiEquiv hn).trans (AlgEquiv.piCongrRight fun μ =>
    Matrix.reindexAlgEquiv K K ((Fintype.equivFin (StandardYoungTableau
      (YoungDiagram.ofPartition μ))).trans (finCongr (standardCount_def _).symm)))⟩

end TauCeti.TypeAHeckeAlgebra
