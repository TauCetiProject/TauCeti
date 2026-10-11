/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Data.Int.Interval
import TauCeti.LinearAlgebra.BilinearForm.Hermite
import TauCeti.LinearAlgebra.BilinearMap.GramCongruence
import TauCeti.LinearAlgebra.Matrix.Condensation

/-!
# Finitely many classes of positive definite integral forms

For every rank `n` and every bound `D`, there is a finite set of integral `n × n` matrices
containing a Gram matrix of every symmetric positive definite `ℤ`-valued bilinear form on a free
`ℤ`-module of rank `n` whose Gram determinant is at most `D`. In other words, positive definite
integral forms of given rank and bounded determinant fall into finitely many isometry classes.

The proof is Hermite's reduction, by induction on the rank. Let `v` be a vector of least norm
`μ = B(v, v)`. It is primitive, and Hermite's inequality bounds `μ` by the determinant. On a
complement of `ℤ v` the condensed form

```text
S(y, z) = μ · B(y, z) - B(v, y) · B(v, z)
```

is positive definite of rank `n - 1`, its determinant is bounded by Chiò's identity, and it does
not change when multiples of `v` are added to `y` and `z`. By induction, `S` has a Gram matrix
`H` in a finite set. Adding to each vector of the corresponding basis a multiple of `v` brings
`B(v, ·)` to values `r` in `[0, μ)`, and then the Gram matrix of `B` in the basis
`v, y₁, …, y_{n-1}` is determined by `μ`, `r` and `H`: its lower block is `(H + r rᵀ) / μ`.

The argument is specific to definite forms: for an indefinite form there is no vector of least
norm, and the corresponding finiteness theorem needs a different proof.

## Main results

* `LinearMap.BilinForm.exists_finset_forall_exists_toMatrix_mem`: positive definite integral forms
  of rank `n` and determinant at most `D` have Gram matrices in a fixed finite set.

## References

* C. Hermite, *Extraits de lettres de M. Ch. Hermite à M. Jacobi sur différents objets de la
  théorie des nombres*, J. Reine Angew. Math. 40 (1850), 261–315.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 9, §1.
-/

public section

open Module

namespace LinearMap.BilinForm

/-- The symmetric matrix with corner `μ`, first row and column `r`, and lower block
`(H i j + r i * r j) / μ`. A Gram matrix whose corner is `μ`, whose first row is `r` and whose
condensation at the corner is `H` is of this form. -/
private def extendGram {n : ℕ} (μ : ℤ) (r : Fin n → ℤ) (H : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of (Matrix.vecCons (Matrix.vecCons μ r) fun i ↦
    Matrix.vecCons (r i) fun j ↦ (H i j + r i * r j) / μ)

/-- The finiteness statement on the coordinate module `Fin n → ℤ`, proved by induction on `n`. -/
private def ClassBound (n : ℕ) : Prop :=
  ∀ D : ℤ, ∃ S : Finset (Matrix (Fin n) (Fin n) ℤ), ∀ B : LinearMap.BilinForm ℤ (Fin n → ℤ),
    B.IsSymm → (∀ x, x ≠ 0 → 0 < B x x) → (toMatrix (Pi.basisFun ℤ (Fin n)) B).det ≤ D →
      ∃ c : Basis (Fin n) ℤ (Fin n → ℤ), toMatrix c B ∈ S

/-- The inductive step: finiteness in rank `n` implies finiteness in rank `n + 1`. -/
private theorem classBound_succ (n : ℕ) (ih : ClassBound n) : ClassBound (n + 1) := by
  classical
  -- The finite set collects `extendGram μ r H` over `1 ≤ μ ≤ 4 ^ (n + 1 choose 2) · D`,
  -- `r ∈ [0, μ)ⁿ` and `H` in the rank-`n` set for the bound `μ ^ n · D`. Given `B`, we take a
  -- vector `v` of least norm `μ`, bound `μ` by Hermite's inequality, apply the inductive
  -- hypothesis to the condensed form `S` on a complement `φ` of `ℤ v`, and finally shift the
  -- resulting basis of the complement by multiples of `v` to normalize the first row.
  intro D
  choose T hT using ih
  refine ⟨(Finset.Icc 1 (4 ^ (n + 1).choose 2 * D)).biUnion fun μ ↦
      ((Fintype.piFinset fun _ ↦ Finset.Ico 0 μ) ×ˢ T (μ ^ n * D)).image
        fun p ↦ extendGram μ p.1 p.2, ?_⟩
  intro B hB hpos hD
  have hsymm : ∀ x y, B x y = B y x := isSymm_def.mp hB
  -- A primitive vector `v` of least norm `μ`, and a basis `c` starting with it.
  obtain ⟨v, hprim, hmin⟩ := exists_isPrimitive_forall_apply_self_le B
    (fun x hx ↦ by simpa using hpos x hx)
  set μ := B v v with hμ_def
  have hμ : 0 < μ := hpos v hprim.ne_zero
  obtain ⟨m, c₀, k, hk⟩ := hprim.exists_basis
  obtain rfl : m = n + 1 := by
    simpa using (finrank_eq_card_basis c₀).symm.trans
      (finrank_eq_card_basis (Pi.basisFun ℤ (Fin (n + 1))))
  let c := c₀.reindex (Equiv.swap k 0)
  have hc0 : c 0 = v := by
    rw [Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_right, hk]
  -- Hermite's inequality bounds `μ` and shows that the determinant is positive.
  have hdetA : (toMatrix c B).det = (toMatrix (Pi.basisFun ℤ (Fin (n + 1))) B).det := by
    rw [← toMatrixAux_eq c B, ← toMatrixAux_eq (Pi.basisFun ℤ (Fin (n + 1))) B]
    exact LinearMap.det_toMatrix₂Aux_eq_det_toMatrix₂Aux B _ _
  set A := toMatrix c B
  obtain ⟨x, hx, hxb⟩ := exists_ne_zero_three_pow_mul_pow_le_four_pow_mul_det B hB
    (fun x hx ↦ by simpa using hpos x hx) (Pi.basisFun ℤ (Fin (n + 1)))
  rw [Fintype.card_fin, ← hdetA] at hxb
  have hμx : μ ≤ B x x := hmin x hx
  have hdetA_pos : 0 < A.det := by
    have : 0 < 3 ^ (n + 1).choose 2 * B x x ^ (n + 1) :=
      mul_pos (by positivity) (pow_pos (hpos x hx) _)
    exact pos_of_mul_pos_right (this.trans_le hxb) (by positivity)
  have hμD : μ ≤ 4 ^ (n + 1).choose 2 * D :=
    calc μ ≤ μ ^ (n + 1) := le_self_pow₀ hμ (by omega)
      _ ≤ B x x ^ (n + 1) := pow_le_pow_left₀ hμ.le hμx _
      _ ≤ 3 ^ (n + 1).choose 2 * B x x ^ (n + 1) :=
          le_mul_of_one_le_left (pow_pos (hpos x hx) _).le (one_le_pow₀ (by norm_num))
      _ ≤ 4 ^ (n + 1).choose 2 * A.det := hxb
      _ ≤ 4 ^ (n + 1).choose 2 * D := by
          rw [hdetA]
          exact mul_le_mul_of_nonneg_left hD (by positivity)
  -- The coordinates `ℤ × (Fin n → ℤ) ≃ M` of `c`, and the complement `φ` of `ℤ v`.
  let E : (ℤ × (Fin n → ℤ)) ≃ₗ[ℤ] (Fin (n + 1) → ℤ) :=
    (Fin.consLinearEquiv ℤ fun _ ↦ ℤ).trans c.equivFun.symm
  have hE (a : ℤ) (y : Fin n → ℤ) : E (a, y) = a • v + E (0, y) := by
    have : ((a, y) : ℤ × (Fin n → ℤ)) = a • (1, 0) + (0, y) := by simp
    rw [this, map_add, map_smul]
    congr 2
    rw [← hc0]
    simp only [E, LinearEquiv.trans_apply, Basis.equivFun_symm_apply, Fin.sum_univ_succ]
    simp
  let φ : (Fin n → ℤ) →ₗ[ℤ] (Fin (n + 1) → ℤ) := E.toLinearMap ∘ₗ LinearMap.inr ℤ ℤ _
  have hφE (y : Fin n → ℤ) : φ y = E (0, y) := rfl
  have hφ (i : Fin n) : φ (Pi.single i 1) = c i.succ := by
    simp only [φ, E, LinearMap.comp_apply, LinearMap.inr_apply, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, Basis.equivFun_symm_apply, Fin.sum_univ_succ]
    simp [Pi.single_apply]
  -- The condensed form `S(y, z) = μ B(φ y, φ z) - B(v, φ y) B(v, φ z)`.
  let ℓ : (Fin n → ℤ) →ₗ[ℤ] ℤ := B v ∘ₗ φ
  let S : LinearMap.BilinForm ℤ (Fin n → ℤ) :=
    μ • B.compl₁₂ φ φ - (LinearMap.mul ℤ ℤ).compl₁₂ ℓ ℓ
  have hS (y z : Fin n → ℤ) : S y z = μ * B (φ y) (φ z) - B v (φ y) * B v (φ z) := by
    simp [S, ℓ]
  have hSsymm : S.IsSymm := isSymm_def.mpr fun y z ↦ by
    rw [hS, hS, hsymm (φ y)]
    ring
  have hSpos (y : Fin n → ℤ) (hy : y ≠ 0) : 0 < S y y := by
    have hEw : E (-B v (φ y), μ • y) = (-B v (φ y)) • v + μ • φ y := by
      rw [hE, hφE, ← map_smul, Prod.smul_mk, smul_zero]
    have hw : (-B v (φ y)) • v + μ • φ y ≠ 0 := by
      rw [← hEw, E.map_ne_zero_iff]
      intro h
      exact hy ((smul_eq_zero.mp (congrArg Prod.snd h)).resolve_left hμ.ne')
    have h := mul_pos hμ (hpos _ hw)
    have hexp : B ((-B v (φ y)) • v + μ • φ y) ((-B v (φ y)) • v + μ • φ y) = μ * S y y := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hS,
        hsymm (φ y) v, ← hμ_def]
      ring
    rw [hexp] at h
    exact pos_of_mul_pos_right (pos_of_mul_pos_right h hμ.le) hμ.le
  -- Chiò's identity bounds the determinant of `S`.
  have hcond : toMatrix (Pi.basisFun ℤ (Fin n)) S =
      Matrix.of fun i j : Fin n ↦ A 0 0 * A i.succ j.succ - A i.succ 0 * A 0 j.succ := by
    ext i j
    simp [A, hS, hφ, hc0, hsymm (c i.succ) v, ← hμ_def]
  have hdetS : (toMatrix (Pi.basisFun ℤ (Fin n)) S).det ≤ μ ^ n * D := by
    have hchio := Matrix.mul_det_condensation_eq_pow_mul_det A
    have hA00 : A 0 0 = μ := by simp [A, hc0, hμ_def]
    rw [← hcond, hA00] at hchio
    have hpos' : 0 < μ * (toMatrix (Pi.basisFun ℤ (Fin n)) S).det := by
      rw [hchio]
      positivity
    have hSdet := pos_of_mul_pos_right hpos' hμ.le
    calc (toMatrix (Pi.basisFun ℤ (Fin n)) S).det
        ≤ μ * (toMatrix (Pi.basisFun ℤ (Fin n)) S).det := le_mul_of_one_le_left hSdet.le hμ
      _ = μ ^ n * A.det := hchio
      _ ≤ μ ^ n * D := by
          rw [hdetA]
          exact mul_le_mul_of_nonneg_left hD (by positivity)
  obtain ⟨c', hc'⟩ := hT (μ ^ n * D) S hSsymm hSpos hdetS
  -- Shift the complement by multiples of `v` so that `B(v, ·)` takes values in `[0, μ)`.
  let τ : (Fin n → ℤ) →ₗ[ℤ] ℤ := c'.constr ℤ fun j ↦ -(ℓ (c' j) / μ)
  let ψ : (Fin n → ℤ) →ₗ[ℤ] (Fin (n + 1) → ℤ) := E.toLinearMap ∘ₗ τ.prod LinearMap.id
  have hψ (y : Fin n → ℤ) : ψ y = τ y • v + φ y := hE _ _
  have hψinj : Function.Injective ψ := fun y z h ↦ by
    simpa using congrArg Prod.snd (E.injective h)
  have hli (a : ℤ) (w : Fin (n + 1) → ℤ) (hw : w ∈ LinearMap.range ψ) (h : a • v + w = 0) :
      a = 0 := by
    obtain ⟨y, rfl⟩ := hw
    have h' : E (a + τ y, y) = 0 := by
      rw [← h, hψ, hφE, hE (a + τ y) y, add_smul, add_assoc]
    simp only [map_eq_zero_iff E E.injective, Prod.mk_eq_zero] at h'
    simpa [h'.2] using h'.1
  have hsp (w : Fin (n + 1) → ℤ) : ∃ a : ℤ, w + a • v ∈ LinearMap.range ψ := by
    obtain ⟨⟨a, y⟩, rfl⟩ := E.surjective w
    refine ⟨τ y - a, y, ?_⟩
    rw [hψ, hφE, hE a y, sub_smul]
    abel
  let e : Basis (Fin (n + 1)) ℤ (Fin (n + 1) → ℤ) :=
    Basis.mkFinCons v (c'.map (LinearEquiv.ofInjective ψ hψinj)) hli hsp
  have he0 : e 0 = v := by simp [e]
  have he (j : Fin n) : e j.succ = ψ (c' j) := by simp [e]
  -- The values `r j = B(v, ψ (c' j))` lie in `[0, μ)`.
  have hr (j : Fin n) : B v (ψ (c' j)) = ℓ (c' j) % μ := by
    rw [hψ, map_add, map_smul, Basis.constr_basis, Int.emod_def]
    simp only [smul_eq_mul, ← hμ_def]
    simp [ℓ]
    ring
  -- `S` does not change when multiples of `v` are added.
  have hψS (y z : Fin n → ℤ) :
      μ * B (ψ y) (ψ z) = S y z + B v (ψ y) * B v (ψ z) := by
    simp only [hψ, hS, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hsymm (φ y) v, ← hμ_def]
    ring
  refine ⟨e, Finset.mem_biUnion.mpr ?_⟩
  refine ⟨μ, Finset.mem_Icc.mpr ⟨hμ, hμD⟩, Finset.mem_image.mpr
    ⟨(fun j ↦ ℓ (c' j) % μ, toMatrix c' S), Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr
      fun j ↦ Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hμ.ne', Int.emod_lt_of_pos _ hμ⟩, hc'⟩, ?_⟩⟩
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp only [extendGram, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
      toMatrix_apply, he0, he, hr, ← hμ_def]
  · rw [hsymm, hr]
  · rename_i i j
    rw [← hr, ← hr, ← hψS, Int.mul_ediv_cancel_left _ hμ.ne']

/-- The finiteness statement on coordinate modules, for every rank. -/
private theorem classBound (n : ℕ) : ClassBound n := by
  induction n with
  | zero =>
    intro D
    exact ⟨{0}, fun B _ _ _ ↦ ⟨Pi.basisFun ℤ (Fin 0), Finset.mem_singleton.mpr
      (Subsingleton.elim _ _)⟩⟩
  | succ n ih => exact classBound_succ n ih

universe u

/-- **Finiteness of classes of positive definite integral forms.** For every rank `n` and bound
`D` there is a finite set `S` of integral matrices such that every symmetric positive definite
`ℤ`-valued bilinear form `B` on a free `ℤ`-module of rank `n`, with Gram determinant at most `D`,
has a Gram matrix in `S`. Hence there are only finitely many isometry classes of such forms. -/
theorem exists_finset_forall_exists_toMatrix_mem (n : ℕ) (D : ℤ) :
    ∃ S : Finset (Matrix (Fin n) (Fin n) ℤ), ∀ {M : Type u} [AddCommGroup M]
      (B : LinearMap.BilinForm ℤ M), B.IsSymm → B.toQuadraticMap.PosDef →
      ∀ b : Basis (Fin n) ℤ M, (toMatrix b B).det ≤ D →
        ∃ c : Basis (Fin n) ℤ M, toMatrix c B ∈ S := by
  obtain ⟨S, hS⟩ := classBound n D
  refine ⟨S, fun {M} _ B hB hpos b hD ↦ ?_⟩
  -- Transport `B` to the coordinates of `b`.
  let f : (Fin n → ℤ) ≃ₗ[ℤ] M := b.equivFun.symm
  let B' : LinearMap.BilinForm ℤ (Fin n → ℤ) := B.compl₁₂ f.toLinearMap f.toLinearMap
  have hf (i : Fin n) : f (Pi.basisFun ℤ (Fin n) i) = b i := by
    simp [f, Basis.equivFun_symm_apply, Pi.single_apply]
  have hB' : B'.IsSymm := isSymm_def.mpr fun x y ↦ by
    simp [B', isSymm_def.mp hB (f x)]
  have hpos' : ∀ x, x ≠ 0 → 0 < B' x x := fun x hx ↦ by
    simpa [B'] using hpos (f x) (by simpa using hx)
  have hdet : toMatrix (Pi.basisFun ℤ (Fin n)) B' = toMatrix b B := by
    ext i j
    simp only [toMatrix_apply, B', compl₁₂_apply, LinearEquiv.coe_coe, hf]
  obtain ⟨c', hc'⟩ := hS B' hB' hpos' (hdet ▸ hD)
  refine ⟨c'.map f, ?_⟩
  convert hc' using 1
  ext i j
  simp [B']

end LinearMap.BilinForm
