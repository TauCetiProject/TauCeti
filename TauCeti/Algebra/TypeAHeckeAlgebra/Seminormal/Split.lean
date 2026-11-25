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
import TauCeti.Algebra.TypeAHeckeAlgebra.Basis
import TauCeti.Combinatorics.Young.RSK
import TauCeti.Combinatorics.Young.StandardTableau.Separation
import TauCeti.GroupTheory.Perm.Coxeter

/-!
# The split seminormal decomposition of the type-A Hecke algebra

When the quantum factorial at `Q = q²` is nonzero, the joint seminormal representation identifies
`H_n(q)` with the product of full matrix algebras indexed by partitions of `n`. The native
matrices have actual standard tableaux as row and column indices; reindexing gives matrices of
size `standardCount`.

The proof uses the absolute irreducibility theorem `seminormalRep_surjective` for each shape.
Additive Jucys–Murphy eigenvalues separate tableaux across shapes as well: at the first different
cell, their contents are the contents of two addable cells of the same smaller diagram.
Interpolation then isolates every block, giving surjectivity of the joint representation.
The PBW basis and Robinson–Schensted correspondence give equal dimensions and hence injectivity.

## References

* H. Wenzl, *Hecke algebras of type A and subfactors*, Invent. Math. 92 (1988), 349–383,
  Theorem 2.2, DOI: 10.1007/BF01404457, for the complex split decomposition and quantum-factorial
  criterion. Here the nonvanishing direction is proved using the individual seminormal
  representations and their surjectivity theorem from `Seminormal.Irreducible`.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

open YoungTableau Matrix

variable {K : Type*} [Field K] {q : Kˣ} {n : ℕ}

private theorem cast_additiveJucysMurphy {m n : ℕ} (h : m = n) (i : Fin m) :
    (AlgEquiv.cast h : TypeAHeckeAlgebra K q m ≃ₐ[K] TypeAHeckeAlgebra K q n)
      (additiveJucysMurphy q i) = additiveJucysMurphy q (Fin.cast h i) := by
  subst n
  rfl

private noncomputable def seminormalPi
    (hn : ∀ d : ℕ, 0 < d → d ≤ n → additiveContent ((q : K) ^ 2) d ≠ 0) :
    TypeAHeckeAlgebra K q n →ₐ[K] Π μ : n.Partition,
      Matrix (StandardYoungTableau (YoungDiagram.ofPartition μ))
        (StandardYoungTableau (YoungDiagram.ofPartition μ)) K :=
  AlgHom.pi fun μ =>
    (LinearMap.toMatrixAlgEquiv' : Module.End K _ ≃ₐ[K] Matrix _ _ K).toAlgHom.comp
      ((seminormalRep q (YoungDiagram.ofPartition μ) fun d hd hdn =>
        hn d hd (by simpa only [YoungDiagram.card_ofPartition] using hdn.le)).comp
          (AlgEquiv.cast (YoungDiagram.card_ofPartition μ).symm).toAlgHom)

private noncomputable def jointDiagonal :
    ((Σ μ : n.Partition, StandardYoungTableau (YoungDiagram.ofPartition μ)) → K) →ₐ[K]
      Π μ : n.Partition, Matrix (StandardYoungTableau (YoungDiagram.ofPartition μ))
        (StandardYoungTableau (YoungDiagram.ofPartition μ)) K :=
  AlgHom.pi fun μ =>
    (diagonalAlgHom K).comp (AlgHom.pi fun U => Pi.evalAlgHom K (fun _ => K) ⟨μ, U⟩)

private theorem seminormalPi_additiveJucysMurphy
    (hn : ∀ d : ℕ, 0 < d → d ≤ n → additiveContent ((q : K) ^ 2) d ≠ 0)
    (i : Fin n) :
    seminormalPi hn (additiveJucysMurphy q i) = jointDiagonal (fun T =>
      additiveContent ((q : K) ^ 2) (labelContent T.2.toTableau
        (Fin.cast (YoungDiagram.card_ofPartition T.1).symm i))) := by
  funext μ
  apply (toLinAlgEquiv' : Matrix _ _ K ≃ₐ[K] _).injective
  apply LinearMap.ext
  intro ψ
  funext U
  simp only [seminormalPi, AlgHom.pi_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    cast_additiveJucysMurphy, toLinAlgEquiv'_toMatrixAlgEquiv',
    seminormalRep_additiveJucysMurphy_apply, jointDiagonal, diagonalAlgHom_apply,
    Pi.evalAlgHom_apply, toLinAlgEquiv'_apply, mulVec_diagonal]

private theorem jointDiagonal_mem_range
    (hn : ∀ d : ℕ, 0 < d → d ≤ n → additiveContent ((q : K) ^ 2) d ≠ 0)
    (f : (Σ μ : n.Partition, StandardYoungTableau (YoungDiagram.ofPartition μ)) → K) :
    jointDiagonal f ∈ (seminormalPi hn).range := by
  let S := (seminormalPi hn).range.comap jointDiagonal
  have hφ (i : Fin n) :
      (fun T : (Σ μ : n.Partition, StandardYoungTableau (YoungDiagram.ofPartition μ)) =>
        additiveContent ((q : K) ^ 2) (labelContent T.2.toTableau
          (Fin.cast (YoungDiagram.card_ofPartition T.1).symm i))) ∈ S :=
    ⟨additiveJucysMurphy q i, seminormalPi_additiveJucysMurphy hn i⟩
  have hinj := StandardYoungTableau.injective_labelContent_of_injOn_addables (n := n)
    (additiveContent ((q : K) ^ 2)) (fun μ hμ c hc d hd hcd => by
      by_cases h : c = d
      · exact h
      have habs := Finset.mem_Icc.mp (hc.natAbs_cellContent_sub_mem hd h)
      have hnat : (YoungDiagram.cellContent c - YoungDiagram.cellContent d).natAbs < n + 1 :=
        by omega
      have hlt : |YoungDiagram.cellContent c - YoungDiagram.cellContent d| < (n + 1 : ℕ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hnat
      exact YoungDiagram.injOn_cellContent μ hc hd
        ((additiveContent_inj (pow_ne_zero 2 q.ne_zero)
          (fun e he hen => hn e he (by omega)) hlt).mp hcd))
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
      (fun d hd hdn => hn d hd (by simpa only [YoungDiagram.card_ofPartition] using hdn))
      (toLinAlgEquiv' (M μ))
    let y := (AlgEquiv.cast (YoungDiagram.card_ofPartition μ) :
      TypeAHeckeAlgebra K q (YoungDiagram.ofPartition μ).card ≃ₐ[K] _) x
    have hy : seminormalPi hn y μ = M μ := by
      apply (toLinAlgEquiv' : Matrix _ _ K ≃ₐ[K] _).injective
      simpa [seminormalPi, y] using hx
    have hprod := (seminormalPi hn).range.mul_mem
      (jointDiagonal_mem_range hn (fun T => if T.1 = μ then 1 else 0))
      ((seminormalPi hn).mem_range_self y)
    convert hprod using 1
    ext ν U V
    by_cases h : ν = μ
    · subst ν
      simp [jointDiagonal, hy]
    · simp [jointDiagonal, h]
  apply (AlgHom.mem_range (seminormalPi hn)).mp
  rw [← Finset.univ_sum_single M]
  exact (seminormalPi hn).range.sum_mem fun μ _ => hsingle μ

/-- The joint seminormal representation is an algebra equivalence with the product of matrix
algebras indexed by the actual standard tableaux, when all quantum integers up to `n` are
nonzero. -/
noncomputable def seminormalPiEquiv
    (hn : ∀ d : ℕ, 0 < d → d ≤ n → additiveContent ((q : K) ^ 2) d ≠ 0) :
    TypeAHeckeAlgebra K q n ≃ₐ[K] Π μ : n.Partition,
      Matrix (StandardYoungTableau (YoungDiagram.ofPartition μ))
        (StandardYoungTableau (YoungDiagram.ofPartition μ)) K := by
  letI : Module.Finite K (TypeAHeckeAlgebra K q n) :=
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
  exact AlgEquiv.ofBijective (seminormalPi hn)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (seminormalPi hn).toLinearMap) hdim).mpr
      (seminormalPi_surjective hn), seminormalPi_surjective hn⟩

/-- The native split equivalence has the prescribed seminormal matrix in each partition block.
The cast only identifies the cardinality of the chosen partition diagram with `n`. -/
theorem seminormalPiEquiv_apply
    (hn : ∀ d : ℕ, 0 < d → d ≤ n → additiveContent ((q : K) ^ 2) d ≠ 0)
    (x : TypeAHeckeAlgebra K q n) (μ : n.Partition) :
    seminormalPiEquiv hn x μ = LinearMap.toMatrixAlgEquiv'
      (seminormalRep q (YoungDiagram.ofPartition μ)
        (fun d hd hdn => hn d hd (by simpa only [YoungDiagram.card_ofPartition] using hdn.le))
        ((AlgEquiv.cast (YoungDiagram.card_ofPartition μ).symm :
          TypeAHeckeAlgebra K q n ≃ₐ[K]
            TypeAHeckeAlgebra K q (YoungDiagram.ofPartition μ).card) x)) := (rfl)

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
