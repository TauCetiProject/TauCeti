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
import TauCeti.LinearAlgebra.BilinearForm.LinearIndependent
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
`TauCeti.BilinForm.IsIsometry.det_eq_one_of_isAlt`.

In a Darboux basis, pairing with the basis vectors reads off the coordinates of a vector:
`ω(qᵢ, v)` is its `pᵢ`-coordinate and `ω(pᵢ, v)` is minus its `qᵢ`-coordinate
(`TauCeti.SymplecticForm.IsDarbouxBasis.apply_fst`,
`TauCeti.SymplecticForm.IsDarbouxBasis.apply_snd`).
Conversely, a family satisfying the Darboux relations has Gram matrix `Matrix.J` after
relabelling (`TauCeti.SymplecticForm.apply_darbouxIndexEquiv_symm_eq_J_iff`), so it is linearly
independent (`TauCeti.SymplecticForm.linearIndependent_of_apply_fst_snd`), and `finrank V` such
vectors form a Darboux basis (`TauCeti.SymplecticForm.exists_isDarbouxBasis_coe_eq`). In
particular, pairs `(xᵢ, yᵢ)` with `ω(xᵢ, yᵢ) = 1` taken from pairwise `ω`-orthogonal subspaces
form a Darboux basis when there are `dim V / 2` of them
(`TauCeti.SymplecticForm.exists_isDarbouxBasis_of_forall_mem`), and more generally families of
pairs satisfying the Darboux relations, taken from pairwise `ω`-orthogonal subspaces, assemble to
a Darboux basis (`TauCeti.SymplecticForm.exists_isDarbouxBasis_of_blocks`).

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

/-- In a Darboux basis, pairing with `qᵢ` reads off the `pᵢ`-coordinate:
`ω(qᵢ, v) = b.repr v (i, 1)`. -/
theorem IsDarbouxBasis.apply_fst (hb : ω.IsDarbouxBasis b) (i : Fin n) (v : V) :
    ω (b (i, 0)) v = b.repr v (i, 1) := by
  have h : ω.toBilinForm (b (i, 0)) = b.coord (i, 1) := b.ext fun ⟨j, a⟩ ↦ by
    fin_cases a
    · simp [hb.apply_fst_fst]
    · simp [hb.apply_fst_snd, Finsupp.single_apply, eq_comm]
  exact LinearMap.congr_fun h v

/-- In a Darboux basis, pairing with `pᵢ` reads off minus the `qᵢ`-coordinate:
`ω(pᵢ, v) = -b.repr v (i, 0)`. -/
theorem IsDarbouxBasis.apply_snd (hb : ω.IsDarbouxBasis b) (i : Fin n) (v : V) :
    ω (b (i, 1)) v = -b.repr v (i, 0) := by
  have h : ω.toBilinForm (b (i, 1)) = -b.coord (i, 0) := b.ext fun ⟨j, a⟩ ↦ by
    fin_cases a
    · simp [hb.apply_snd_fst, Finsupp.single_apply, eq_comm, apply_ite]
    · simp [hb.apply_snd_snd]
  exact LinearMap.congr_fun h v

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

/-- **The Darboux relations as a Gram matrix.** A family with `qᵢ = v (i, 0)` and `pᵢ = v (i, 1)`
satisfies `ω(qᵢ, qⱼ) = 0`, `ω(pᵢ, pⱼ) = 0` and `ω(qᵢ, pⱼ) = δᵢⱼ` exactly when, relabelled by
`darbouxIndexEquiv`, its Gram matrix for `ω` is `Matrix.J`. -/
theorem apply_darbouxIndexEquiv_symm_eq_J_iff {v : Fin n × Fin 2 → V} :
    (∀ x y, ω.toBilinForm (v ((darbouxIndexEquiv n).symm x)) (v ((darbouxIndexEquiv n).symm y)) =
        Matrix.J (Fin n) ℝ x y) ↔
      (∀ i j, ω (v (i, 0)) (v (j, 0)) = 0) ∧ (∀ i j, ω (v (i, 1)) (v (j, 1)) = 0) ∧
        ∀ i j, ω (v (i, 0)) (v (j, 1)) = if i = j then 1 else 0 := by
  constructor
  · intro h
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩
    · simpa [Matrix.J] using h (.inr i) (.inr j)
    · simpa [Matrix.J] using h (.inl i) (.inl j)
    · simpa [Matrix.J, Matrix.one_apply] using h (.inr i) (.inl j)
  · rintro ⟨h₁, h₂, h₃⟩ (i | i) (j | j) <;>
      simp only [darbouxIndexEquiv_symm_inl, darbouxIndexEquiv_symm_inr, Matrix.J,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply]
    · exact h₂ i j
    · rw [← ω.isAlt.neg_eq, neg_inj]
      exact (h₃ j i).trans (by simp [eq_comm])
    · exact h₃ i j
    · exact h₁ i j

/-- A basis is a Darboux basis exactly when, relabelled by `darbouxIndexEquiv`, it is a basis in
which the matrix of `ω` is `Matrix.J`. -/
theorem isDarbouxBasis_iff_toMatrix_reindex :
    ω.IsDarbouxBasis b ↔
      LinearMap.BilinForm.toMatrix (b.reindex (darbouxIndexEquiv n)) ω.toBilinForm =
        Matrix.J (Fin n) ℝ := by
  simp only [← Matrix.ext_iff, LinearMap.BilinForm.toMatrix_apply, Basis.reindex_apply,
    apply_darbouxIndexEquiv_symm_eq_J_iff]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

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

/-- **Families satisfying the Darboux relations are linearly independent.** If the vectors
`qᵢ = v (i, 0)` and `pᵢ = v (i, 1)` satisfy `ω(qᵢ, qⱼ) = 0`, `ω(pᵢ, pⱼ) = 0` and
`ω(qᵢ, pⱼ) = δᵢⱼ`, then, relabelled by `darbouxIndexEquiv`, their Gram matrix is `Matrix.J`
(`TauCeti.SymplecticForm.apply_darbouxIndexEquiv_symm_eq_J_iff`), so the family is linearly
independent. -/
theorem linearIndependent_of_apply_fst_snd {v : Fin n × Fin 2 → V}
    (h₁ : ∀ i j, ω (v (i, 0)) (v (j, 0)) = 0) (h₂ : ∀ i j, ω (v (i, 1)) (v (j, 1)) = 0)
    (h₃ : ∀ i j, ω (v (i, 0)) (v (j, 1)) = if i = j then 1 else 0) : LinearIndependent ℝ v :=
  (linearIndependent_equiv (darbouxIndexEquiv n).symm).1 <|
    ω.toBilinForm.linearIndependent_of_apply_eq_J <|
      apply_darbouxIndexEquiv_symm_eq_J_iff.2 ⟨h₁, h₂, h₃⟩

/-- **Darboux bases from the Darboux relations.** A family of `finrank ℝ V = n * 2` vectors
`qᵢ = v (i, 0)`, `pᵢ = v (i, 1)` with `ω(qᵢ, qⱼ) = 0`, `ω(pᵢ, pⱼ) = 0` and `ω(qᵢ, pⱼ) = δᵢⱼ` is a
Darboux basis. -/
theorem exists_isDarbouxBasis_coe_eq [FiniteDimensional ℝ V] (hn : finrank ℝ V = n * 2)
    {v : Fin n × Fin 2 → V}
    (h₁ : ∀ i j, ω (v (i, 0)) (v (j, 0)) = 0) (h₂ : ∀ i j, ω (v (i, 1)) (v (j, 1)) = 0)
    (h₃ : ∀ i j, ω (v (i, 0)) (v (j, 1)) = if i = j then 1 else 0) :
    ∃ b : Basis (Fin n × Fin 2) ℝ V, ω.IsDarbouxBasis b ∧ ⇑b = v := by
  have hv := linearIndependent_of_apply_fst_snd h₁ h₂ h₃
  have hcard : Fintype.card (Fin n × Fin 2) = finrank ℝ V := by simp [hn]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' v hv hcard, ⟨?_, ?_, ?_⟩,
    coe_basisOfLinearIndependentOfCardEqFinrank' v hv hcard⟩ <;>
    simpa only [coe_basisOfLinearIndependentOfCardEqFinrank']

/-- **Darboux bases from orthogonal pairs.** Pairs `(xₖ, yₖ)` with `ω(xₖ, yₖ) = 1`, taken from
pairwise `ω`-orthogonal subspaces `Gₖ`, form a Darboux basis `(x₁, y₁, …, xₙ, yₙ)` when
`finrank ℝ V = n * 2`. -/
theorem exists_isDarbouxBasis_of_forall_mem [FiniteDimensional ℝ V] (hn : finrank ℝ V = n * 2)
    {G : Fin n → Submodule ℝ V} (hG : Pairwise fun k l ↦ ∀ v ∈ G k, ∀ w ∈ G l, ω v w = 0)
    {x y : Fin n → V} (hx : ∀ k, x k ∈ G k) (hy : ∀ k, y k ∈ G k)
    (hxy : ∀ k, ω (x k) (y k) = 1) :
    ∃ b : Basis (Fin n × Fin 2) ℝ V, ω.IsDarbouxBasis b ∧ (∀ k, b (k, 0) = x k) ∧
      ∀ k, b (k, 1) = y k := by
  obtain ⟨b, hb, hbf⟩ := exists_isDarbouxBasis_coe_eq (ω := ω) hn
    (v := fun i ↦ ![x i.1, y i.1] i.2)
    (fun k l ↦ by
      rcases eq_or_ne k l with rfl | hkl
      · exact ω.self_eq_zero _
      · exact hG hkl _ (hx k) _ (hx l))
    (fun k l ↦ by
      rcases eq_or_ne k l with rfl | hkl
      · exact ω.self_eq_zero _
      · exact hG hkl _ (hy k) _ (hy l))
    (fun k l ↦ by
      rcases eq_or_ne k l with rfl | hkl
      · simpa using hxy k
      · simpa [hkl] using hG hkl _ (hx k) _ (hy l))
  exact ⟨b, hb, fun k ↦ by simp [hbf], fun k ↦ by simp [hbf]⟩

/-- **Darboux bases from orthogonal blocks.** Let `G j` be pairwise `ω`-orthogonal subspaces, and
for each `j` let `v j` be `m j` pairs of vectors of `G j` satisfying the Darboux relations. If
`finrank ℝ V = n * 2` and `e` enumerates the pairs of all the blocks, these pairs form a Darboux
basis of `V`, the `i`-th pair of the `j`-th block in position `e ⟨j, i⟩`. -/
theorem exists_isDarbouxBasis_of_blocks [FiniteDimensional ℝ V] {κ : Type*} {m : κ → ℕ}
    (e : (Σ j, Fin (m j)) ≃ Fin n) (hn : finrank ℝ V = n * 2) {G : κ → Submodule ℝ V}
    (hG : Pairwise fun k l ↦ ∀ v ∈ G k, ∀ w ∈ G l, ω v w = 0) {v : ∀ j, Fin (m j) × Fin 2 → V}
    (hv : ∀ j a, v j a ∈ G j) (h₁ : ∀ j i i', ω (v j (i, 0)) (v j (i', 0)) = 0)
    (h₂ : ∀ j i i', ω (v j (i, 1)) (v j (i', 1)) = 0)
    (h₃ : ∀ j i i', ω (v j (i, 0)) (v j (i', 1)) = if i = i' then 1 else 0) :
    ∃ b : Basis (Fin n × Fin 2) ℝ V, ω.IsDarbouxBasis b ∧
      ∀ j i c, b (e ⟨j, i⟩, c) = v j (i, c) := by
  let w : Fin n × Fin 2 → V := fun p ↦ v (e.symm p.1).1 ((e.symm p.1).2, p.2)
  have hw (j : κ) (i : Fin (m j)) (c : Fin 2) : w (e ⟨j, i⟩, c) = v j (i, c) := by
    simp only [w]
    rw [Equiv.symm_apply_apply]
  -- Within a block the relations hold by assumption; across blocks `ω` vanishes.
  have hsame (c : Fin 2) (hc : ∀ j i i', ω (v j (i, c)) (v j (i', c)) = 0) (p p' : Fin n) :
      ω (w (p, c)) (w (p', c)) = 0 := by
    obtain ⟨⟨j, i⟩, rfl⟩ := e.surjective p
    obtain ⟨⟨j', i'⟩, rfl⟩ := e.surjective p'
    rw [hw, hw]
    rcases eq_or_ne j j' with rfl | hjj'
    · exact hc j i i'
    · exact hG hjj' _ (hv _ _) _ (hv _ _)
  obtain ⟨b, hb, hbw⟩ := exists_isDarbouxBasis_coe_eq hn (hsame 0 h₁) (hsame 1 h₂) fun p p' ↦ by
    obtain ⟨⟨j, i⟩, rfl⟩ := e.surjective p
    obtain ⟨⟨j', i'⟩, rfl⟩ := e.surjective p'
    rw [hw, hw]
    simp only [e.apply_eq_iff_eq]
    rcases eq_or_ne j j' with rfl | hjj'
    · simpa using h₃ j i i'
    · simpa [hjj'] using hG hjj' _ (hv _ _) _ (hv _ _)
  exact ⟨b, hb, fun j i c ↦ by rw [hbw, hw]⟩

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

/-- **Linear symplectomorphisms have determinant one.** On an infinite-dimensional space the
determinant is `1` by convention. -/
theorem IsSymplectomorphism.det_eq_one {e : V ≃ₗ[ℝ] V}
    (he : IsSymplectomorphism ω ω e) : LinearMap.det (e : V →ₗ[ℝ] V) = 1 :=
  BilinForm.IsIsometry.det_eq_one_of_isAlt ω.isAlt ω.nondegenerate
    (BilinForm.isIsometry_iff.2 he.apply)

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
