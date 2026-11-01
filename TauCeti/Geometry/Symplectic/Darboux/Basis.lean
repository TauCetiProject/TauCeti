/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.Geometry.Symplectic.SymplecticTransport

import TauCeti.LinearAlgebra.BilinearForm.Isometry
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Darboux bases of a symplectic vector space

Let `ω` be a symplectic form on a real vector space `V`. A **Darboux basis** of `(V, ω)`
(`TauCeti.SymplecticForm.IsDarbouxBasis`) is a basis `(q₁, p₁, …, qₙ, pₙ)`, indexed by
`Fin n × Fin 2` with `qᵢ = b (i, 0)` and `pᵢ = b (i, 1)`, in which

`ω(qᵢ, qⱼ) = 0`, `ω(pᵢ, pⱼ) = 0`, `ω(qᵢ, pⱼ) = δᵢⱼ`,

so that `ω = ∑ dqᵢ ∧ dpᵢ` in the dual coordinates.

The relabelling `TauCeti.SymplecticForm.darbouxIndexEquiv`, `(i, 0) ↦ inr i` and
`(i, 1) ↦ inl i`, identifies Darboux bases with the bases in which the matrix of `ω` is Mathlib's
standard symplectic matrix `Matrix.J`
(`TauCeti.SymplecticForm.isDarbouxBasis_iff_toMatrix_reindex`, and conversely
`TauCeti.SymplecticForm.isDarbouxBasis_reindex_symm_iff`). Hence Darboux bases exist on a
finite-dimensional space (`TauCeti.SymplecticForm.exists_isDarbouxBasis`), and any two of them
have relative determinant `1` (`TauCeti.SymplecticForm.IsDarbouxBasis.det_eq_one`), from the
corresponding facts `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J` and
`LinearMap.BilinForm.basis_det_eq_one_of_toMatrix_eq_J` about nondegenerate alternating forms.
Every linear symplectomorphism of `(V, ω)` has determinant `1`
(`TauCeti.SymplecticForm.IsSymplectomorphism.det_eq_one`), the specialization of
`TauCeti.BilinForm.IsIsometry.det_eq_one`.

Darboux bases are carried to Darboux bases by linear symplectomorphisms
(`TauCeti.SymplecticForm.IsDarbouxBasis.map`), and the concatenation of Darboux bases of `ω₁` and
`ω₂` is a Darboux basis of the direct sum `ω₁ ⊕ ω₂`
(`TauCeti.SymplecticForm.IsDarbouxBasis.prod`).

## Main definitions

* `TauCeti.SymplecticForm.IsDarbouxBasis ω b`: `b` is a Darboux basis of `(V, ω)`.
* `TauCeti.SymplecticForm.darbouxIndexEquiv n`: the relabelling `Fin n × Fin 2 ≃ Fin n ⊕ Fin n`
  between the Darboux and the `Matrix.J` index conventions.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 2.1 (symplectic bases).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 1.1.
-/

public section

open Module

namespace TauCeti

namespace SymplecticForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- A **Darboux basis** of a symplectic vector space `(V, ω)`: a basis `(q₁, p₁, …, qₙ, pₙ)`,
with `qᵢ = b (i, 0)` and `pᵢ = b (i, 1)`, satisfying `ω(qᵢ, qⱼ) = 0`, `ω(pᵢ, pⱼ) = 0` and
`ω(qᵢ, pⱼ) = δᵢⱼ`. -/
structure IsDarbouxBasis (ω : SymplecticForm V) {n : ℕ} (b : Basis (Fin n × Fin 2) ℝ V) :
    Prop where
  /-- The vectors `qᵢ` pair trivially with each other. -/
  apply_fst_fst : ∀ i j, ω (b (i, 0)) (b (j, 0)) = 0
  /-- The vectors `pᵢ` pair trivially with each other. -/
  apply_snd_snd : ∀ i j, ω (b (i, 1)) (b (j, 1)) = 0
  /-- `ω(qᵢ, pⱼ) = δᵢⱼ`. -/
  apply_fst_snd : ∀ i j, ω (b (i, 0)) (b (j, 1)) = if i = j then 1 else 0

variable {ω : SymplecticForm V} {n : ℕ} {b c : Basis (Fin n × Fin 2) ℝ V}

/-- In a Darboux basis, `ω(pᵢ, qⱼ) = -δᵢⱼ`. -/
theorem IsDarbouxBasis.apply_snd_fst (hb : ω.IsDarbouxBasis b) (i j : Fin n) :
    ω (b (i, 1)) (b (j, 0)) = if i = j then -1 else 0 := by
  rw [← ω.neg_eq, hb.apply_fst_snd j i]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd h₁.symm h₂
  · exact absurd h₂.symm h₁
  · exact neg_zero

/-- The relabelling `(i, 0) ↦ inr i`, `(i, 1) ↦ inl i`, under which a Darboux basis becomes a
basis in which `ω` has Mathlib's standard symplectic matrix `Matrix.J`
(`TauCeti.SymplecticForm.isDarbouxBasis_iff_toMatrix_reindex`). -/
def darbouxIndexEquiv (n : ℕ) : Fin n × Fin 2 ≃ Fin n ⊕ Fin n where
  toFun p := if p.2 = 0 then Sum.inr p.1 else Sum.inl p.1
  invFun := Sum.elim (fun i ↦ (i, 1)) (fun i ↦ (i, 0))
  left_inv := by
    rintro ⟨i, a⟩
    fin_cases a <;> simp
  right_inv := by
    rintro (i | i) <;> simp

@[simp]
theorem darbouxIndexEquiv_apply_zero (i : Fin n) : darbouxIndexEquiv n (i, 0) = Sum.inr i := by
  simp [darbouxIndexEquiv]

@[simp]
theorem darbouxIndexEquiv_apply_one (i : Fin n) : darbouxIndexEquiv n (i, 1) = Sum.inl i := by
  simp [darbouxIndexEquiv]

@[simp]
theorem darbouxIndexEquiv_symm_inl (i : Fin n) :
    (darbouxIndexEquiv n).symm (Sum.inl i) = (i, 1) :=
  (darbouxIndexEquiv n).symm_apply_eq.2 (by simp [darbouxIndexEquiv])

@[simp]
theorem darbouxIndexEquiv_symm_inr (i : Fin n) :
    (darbouxIndexEquiv n).symm (Sum.inr i) = (i, 0) :=
  (darbouxIndexEquiv n).symm_apply_eq.2 (by simp [darbouxIndexEquiv])

/-- A basis is a Darboux basis exactly when, relabelled by `darbouxIndexEquiv`, it is a basis in
which the matrix of `ω` is `Matrix.J`. -/
theorem isDarbouxBasis_iff_toMatrix_reindex :
    ω.IsDarbouxBasis b ↔
      LinearMap.BilinForm.toMatrix (b.reindex (darbouxIndexEquiv n)) ω.toBilinForm =
        Matrix.J (Fin n) ℝ := by
  constructor
  · intro hb
    ext (i | i) (j | j) <;>
      simp only [LinearMap.BilinForm.toMatrix_apply, Basis.reindex_apply,
        darbouxIndexEquiv_symm_inl, darbouxIndexEquiv_symm_inr, Matrix.J, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply]
    · exact hb.apply_snd_snd i j
    · exact (hb.apply_snd_fst i j).trans (by split_ifs <;> simp)
    · exact hb.apply_fst_snd i j
    · exact hb.apply_fst_fst i j
  · intro h
    have h' (x y) : ω (b ((darbouxIndexEquiv n).symm x)) (b ((darbouxIndexEquiv n).symm y)) =
        Matrix.J (Fin n) ℝ x y := by
      rw [← h, LinearMap.BilinForm.toMatrix_apply, Basis.reindex_apply, Basis.reindex_apply]
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩
    · simpa [Matrix.J] using h' (.inr i) (.inr j)
    · simpa [Matrix.J] using h' (.inl i) (.inl j)
    · simpa [Matrix.J, Matrix.one_apply] using h' (.inr i) (.inl j)

/-- A basis `d` indexed by `Fin n ⊕ Fin n`, relabelled by `darbouxIndexEquiv`, is a Darboux basis
exactly when the matrix of `ω` in `d` is `Matrix.J`. -/
theorem isDarbouxBasis_reindex_symm_iff {d : Basis (Fin n ⊕ Fin n) ℝ V} :
    ω.IsDarbouxBasis (d.reindex (darbouxIndexEquiv n).symm) ↔
      LinearMap.BilinForm.toMatrix d ω.toBilinForm = Matrix.J (Fin n) ℝ := by
  have hd : (d.reindex (darbouxIndexEquiv n).symm).reindex (darbouxIndexEquiv n) = d :=
    Basis.eq_of_apply_eq fun x ↦ by
      simp only [Basis.reindex_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rw [isDarbouxBasis_iff_toMatrix_reindex, hd]

/-- **Darboux bases exist**: every finite-dimensional symplectic vector space has a Darboux
basis. -/
theorem exists_isDarbouxBasis [FiniteDimensional ℝ V] (ω : SymplecticForm V) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V), ω.IsDarbouxBasis b := by
  obtain ⟨n, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  exact ⟨n, b.reindex (darbouxIndexEquiv n).symm, isDarbouxBasis_reindex_symm_iff.2 hb⟩

/-- A Darboux basis exists for any prescribed number `n` of pairs with `finrank ℝ V = n * 2`. -/
theorem exists_isDarbouxBasis_of_finrank_eq [FiniteDimensional ℝ V] (ω : SymplecticForm V)
    (hn : finrank ℝ V = n * 2) : ∃ b : Basis (Fin n × Fin 2) ℝ V, ω.IsDarbouxBasis b := by
  obtain ⟨m, b, hb⟩ := ω.exists_isDarbouxBasis
  obtain rfl : m = n := by
    have := finrank_eq_card_basis b
    simp only [Fintype.card_prod, Fintype.card_fin] at this
    omega
  exact ⟨b, hb⟩

/-- **Darboux bases have unit relative determinant**: the change of basis between two Darboux
bases of `(V, ω)` is a symplectic matrix, of determinant `1`. -/
theorem IsDarbouxBasis.det_eq_one (hb : ω.IsDarbouxBasis b) (hc : ω.IsDarbouxBasis c) :
    b.det c = 1 := by
  have h := LinearMap.BilinForm.basis_det_eq_one_of_toMatrix_eq_J
    (isDarbouxBasis_iff_toMatrix_reindex.1 hb) (isDarbouxBasis_iff_toMatrix_reindex.1 hc)
  rwa [Basis.det_reindex, Basis.coe_reindex, Function.comp_assoc, Equiv.symm_comp_self,
    Function.comp_id] at h

/-- A linear symplectomorphism carries Darboux bases to Darboux bases. -/
theorem IsDarbouxBasis.map {ω' : SymplecticForm W} {e : V ≃ₗ[ℝ] W}
    (he : IsSymplectomorphism ω ω' e) (hb : ω.IsDarbouxBasis b) : ω'.IsDarbouxBasis (b.map e) := by
  refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩ <;> simp only [Basis.map_apply, he.apply]
  exacts [hb.apply_fst_fst i j, hb.apply_snd_snd i j, hb.apply_fst_snd i j]

/-- **Linear symplectomorphisms have determinant one.** -/
theorem IsSymplectomorphism.det_eq_one [FiniteDimensional ℝ V] {e : V ≃ₗ[ℝ] V}
    (he : IsSymplectomorphism ω ω e) : LinearMap.det (e : V →ₗ[ℝ] V) = 1 :=
  BilinForm.IsIsometry.det_eq_one ω.isAlt ω.nondegenerate (BilinForm.isIsometry_iff.2 he.apply)

/-- **Darboux bases of a direct sum.** The concatenation of a Darboux basis `b` of `ω₁` and a
Darboux basis `c` of `ω₂`, listing the pairs of `b` before those of `c`, is a Darboux basis of
`ω₁ ⊕ ω₂`. -/
theorem IsDarbouxBasis.prod {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W} {m k : ℕ}
    {b : Basis (Fin m × Fin 2) ℝ V} {c : Basis (Fin k × Fin 2) ℝ W}
    (hb : ω₁.IsDarbouxBasis b) (hc : ω₂.IsDarbouxBasis c) :
    (ω₁.prod ω₂).IsDarbouxBasis ((b.prod c).reindex
      ((Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _)))) := by
  set e : (Fin m × Fin 2) ⊕ (Fin k × Fin 2) ≃ Fin (m + k) × Fin 2 :=
    (Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _))
  have hl (i : Fin m) (a : Fin 2) :
      (b.prod c).reindex e (Fin.castAdd k i, a) = (b (i, a), 0) := by
    ext <;> simp [e, Basis.reindex_apply]
  have hr (i : Fin k) (a : Fin 2) :
      (b.prod c).reindex e (Fin.natAdd m i, a) = (0, c (i, a)) := by
    ext <;> simp [e, Basis.reindex_apply]
  have hne (i : Fin m) (j : Fin k) : Fin.castAdd k i ≠ Fin.natAdd m j := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
    omega
  refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩ <;>
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp [hl, hr, hne, (hne _ _).symm, hb.apply_fst_fst, hb.apply_snd_snd, hb.apply_fst_snd,
      hc.apply_fst_fst, hc.apply_snd_snd, hc.apply_fst_snd]

end SymplecticForm

end TauCeti
