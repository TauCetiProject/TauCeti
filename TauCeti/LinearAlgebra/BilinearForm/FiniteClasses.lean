/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.Data.Int.Interval
import TauCeti.LinearAlgebra.Basis.Fin
import TauCeti.LinearAlgebra.BilinearForm.Condensation
import TauCeti.LinearAlgebra.BilinearForm.Hermite
import TauCeti.LinearAlgebra.BilinearMap.GramCongruence

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
S(y, z) = μ · B(y, z) - B(y, v) · B(v, z)
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

/-- Hermite's normalization of the first row of a Gram matrix. Adding to the vectors
`d 1, …, d n` of a basis suitable multiples of `v = d 0` brings the values `B(v, d j)` into
`[0, μ)`, where `μ = B(v, v) > 0`, and does not change the condensation of the Gram matrix at its
corner (`LinearMap.BilinForm.mul_apply_add_smul_add_smul`). The Gram matrix of the new basis is
then `extendGram μ r H`, with `r` the new first row and `H` the condensation. -/
private theorem exists_basis_toMatrix_eq_extendGram {M : Type*} [AddCommGroup M] {n : ℕ}
    {B : LinearMap.BilinForm ℤ M} (hB : B.IsSymm) (d : Basis (Fin (n + 1)) ℤ M)
    (hμ : 0 < B (d 0) (d 0)) :
    ∃ (e : Basis (Fin (n + 1)) ℤ M) (r : Fin n → ℤ), (∀ j, r j ∈ Finset.Ico 0 (B (d 0) (d 0))) ∧
      toMatrix e B = extendGram (B (d 0) (d 0)) r (Matrix.of fun i j ↦
        B (d 0) (d 0) * B (d i.succ) (d j.succ) - B (d i.succ) (d 0) * B (d 0) (d j.succ)) := by
  set μ := B (d 0) (d 0) with hμ_def
  set q : Fin n → ℤ := fun j ↦ B (d 0) (d j.succ) / μ
  -- The transvection `x ↦ x + g x • d 0` adds `-q j • d 0` to `d (j + 1)` and fixes `d 0`.
  let g : M →ₗ[ℤ] ℤ := ∑ j, (-q j) • d.coord j.succ
  have hg : g (d 0) = 0 := by simp [g, Fin.succ_ne_zero]
  let e := d.map (LinearEquiv.transvection hg)
  have he0 : e 0 = d 0 := by simp [e, LinearMap.transvection.apply, hg]
  have he (j : Fin n) : e j.succ = d j.succ + (-q j) • d 0 := by
    simp [e, LinearMap.transvection.apply, g, Finsupp.single_apply]
  have hr (j : Fin n) : B (d 0) (e j.succ) = B (d 0) (d j.succ) % μ := by
    rw [he, map_add, map_smul, smul_eq_mul, Int.emod_def]
    ring
  refine ⟨e, fun j ↦ B (d 0) (d j.succ) % μ, fun j ↦ Finset.mem_Ico.mpr
    ⟨Int.emod_nonneg _ hμ.ne', Int.emod_lt_of_pos _ hμ⟩, ?_⟩
  ext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp only [extendGram, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
      toMatrix_apply, he0, hr, ← hμ_def]
  · rw [hB.eq, hr]
  · rename_i i j
    have h := B.mul_apply_add_smul_add_smul (d 0) (d i.succ) (d j.succ) (-q i) (-q j)
    rw [← he, ← he, hB.eq (e i.succ) (d 0), ← hμ_def] at h
    rw [← hr, ← hr, add_comm (μ * _ - _), ← h, Int.mul_ediv_cancel_left _ hμ.ne']

/-- The condensation step of Hermite's reduction. Let `v` be a primitive vector of a symmetric
positive definite form `B` on `ℤⁿ⁺¹`, with `μ = B(v, v)`, and suppose that every symmetric positive
definite form on `ℤⁿ` of determinant at most `D'` has a Gram matrix in `T`. If
`μⁿ · det B ≤ D'`, some basis `d` starting with `v` has the condensation of its Gram matrix at the
corner in `T`. Indeed, on the kernel `K ≃ ℤⁿ` of a functional taking the value `1` on `v`, the
condensed form along `v` is symmetric and positive definite, and its determinant is at most
`μⁿ · det B` by Chiò's identity; `v` followed by a basis of `K` in which its Gram matrix lies in `T`
is the basis `d`. -/
private theorem exists_basis_condensation_mem {n : ℕ} {T : Finset (Matrix (Fin n) (Fin n) ℤ)}
    {D' : ℤ} (hT : ∀ S : LinearMap.BilinForm ℤ (Fin n → ℤ), S.IsSymm →
      (∀ y, y ≠ 0 → 0 < S y y) → (toMatrix (Pi.basisFun ℤ (Fin n)) S).det ≤ D' →
        ∃ c : Basis (Fin n) ℤ (Fin n → ℤ), toMatrix c S ∈ T)
    {B : LinearMap.BilinForm ℤ (Fin (n + 1) → ℤ)} (hB : B.IsSymm)
    (hpos : ∀ x, x ≠ 0 → 0 < B x x) {v : Fin (n + 1) → ℤ} (hv : TauCeti.IsPrimitive v)
    (hD : B v v ^ n * (toMatrix (Pi.basisFun ℤ (Fin (n + 1))) B).det ≤ D') :
    ∃ d : Basis (Fin (n + 1)) ℤ (Fin (n + 1) → ℤ), d 0 = v ∧ (Matrix.of fun i j : Fin n ↦
      B v v * B (d i.succ) (d j.succ) - B (d i.succ) v * B v (d j.succ)) ∈ T := by
  set μ := B v v with hμ_def
  have hμ : 0 < μ := hpos v hv.ne_zero
  -- Split `ℤⁿ⁺¹ = ℤ v ⊕ K` along `f`, and identify `K` with `ℤⁿ` through `φ`.
  obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp hv
  set K := LinearMap.ker f
  obtain ⟨m, ⟨bK⟩⟩ := Submodule.nonempty_basis_of_pid (Pi.basisFun ℤ (Fin (n + 1))) K
  obtain ⟨c₀, hc₀0, hc₀⟩ := bK.exists_basis_finCons_of_apply_eq_one hf
  obtain rfl : n = m := by simpa using Fintype.card_congr ((Pi.basisFun ℤ _).indexEquiv c₀)
  let φ := K.subtype ∘ₗ bK.equivFun.symm.toLinearMap
  -- The condensed form `S(y, z) = μ B(φ y, φ z) - B(φ y, v) B(v, φ z)` on `ℤⁿ`.
  obtain ⟨S, hSsymm, hS⟩ := hB.exists_isSymm_forall_apply_eq v φ
  have hSpos (y) (hy : y ≠ 0) : 0 < S y y := hS y y ▸ sub_pos.mpr
    (apply_mul_apply_lt_of_mem_ker hpos (by simp [hf]) (bK.equivFun.symm y).2
      (by simpa [φ, -Basis.equivFun_symm_apply] using hy))
  -- Chiò's identity bounds the determinant of `S`.
  have hdetS : (toMatrix (Pi.basisFun ℤ (Fin n)) S).det ≤ D' := by
    have h := mul_det_toMatrix_eq_pow_mul_det_toMatrix B c₀ (S := S) (Pi.basisFun ℤ (Fin n))
      fun i j ↦ by simp [φ, hc₀0, hc₀, hS]
    rw [hc₀0, ← toMatrixAux_eq c₀ B] at h
    rw [← toMatrixAux_eq (Pi.basisFun ℤ _) B] at hD
    simp only [toMatrixAux] at h hD
    rw [LinearMap.det_toMatrix₂Aux_eq_det_toMatrix₂Aux B (Pi.basisFun ℤ _) c₀] at h
    have hSdet := ((posDef_toQuadraticMap_iff_matrix (Pi.basisFun ℤ _) S hSsymm).mp fun y hy ↦ by
      simpa using hSpos y hy).det_pos
    exact (le_mul_of_one_le_left hSdet.le hμ).trans (h.trans_le hD)
  -- A basis `c` of `ℤⁿ` in which the Gram matrix of `S` lies in `T`, carried to `K`.
  obtain ⟨c, hc⟩ := hT S hSsymm hSpos hdetS
  obtain ⟨d, hd0, hd⟩ := (c.map bK.equivFun.symm).exists_basis_finCons_of_apply_eq_one hf
  refine ⟨d, hd0, ?_⟩
  convert hc using 1
  ext i j
  simp [hd, φ, hS, hμ_def]

/-- The inductive step: finiteness in rank `n` implies finiteness in rank `n + 1`. -/
private theorem classBound_succ (n : ℕ) (ih : ClassBound n) : ClassBound (n + 1) := by
  classical
  -- The finite set collects `extendGram μ r H` over `1 ≤ μ ≤ 4 ^ (n + 1 choose 2) · D`,
  -- `r ∈ [0, μ)ⁿ` and `H` in the rank-`n` set for the bound `μ ^ n · D`. Given `B`, we take a
  -- vector `v` of least norm `μ`, bound `μ` by Hermite's inequality, find a basis `d` starting
  -- with `v` whose condensed Gram matrix lies in the rank-`n` set, and normalize its first row.
  intro D
  choose T hT using ih
  refine ⟨(Finset.Icc 1 (4 ^ (n + 1).choose 2 * D)).biUnion fun μ ↦
      ((Fintype.piFinset fun _ ↦ Finset.Ico 0 μ) ×ˢ T (μ ^ n * D)).image
        fun p ↦ extendGram μ p.1 p.2, ?_⟩
  intro B hB hpos hD
  have hpos' : B.toQuadraticMap.PosDef := fun x hx ↦ by simpa using hpos x hx
  obtain ⟨v, hprim, hmin⟩ := exists_isPrimitive_forall_apply_self_le B hpos'
  set μ := B v v
  have hμ : 0 < μ := hpos v hprim.ne_zero
  have hμD' : μ ^ n * (toMatrix (Pi.basisFun ℤ (Fin (n + 1))) B).det ≤ μ ^ n * D :=
    mul_le_mul_of_nonneg_left hD (pow_pos hμ n).le
  -- Hermite's inequality bounds `μ`.
  obtain ⟨x, hx, hxb⟩ := exists_ne_zero_three_pow_mul_pow_le_four_pow_mul_det B hB hpos'
    (Pi.basisFun ℤ (Fin (n + 1)))
  rw [Fintype.card_fin] at hxb
  have hμD : μ ≤ 4 ^ (n + 1).choose 2 * D :=
    calc μ ≤ μ ^ (n + 1) := le_self_pow₀ hμ (by omega)
      _ ≤ B x x ^ (n + 1) := pow_le_pow_left₀ hμ.le (hmin x hx) _
      _ ≤ 3 ^ (n + 1).choose 2 * B x x ^ (n + 1) :=
          le_mul_of_one_le_left (pow_pos (hpos x hx) _).le (one_le_pow₀ (by norm_num))
      _ ≤ 4 ^ (n + 1).choose 2 * D := hxb.trans (mul_le_mul_of_nonneg_left hD (by positivity))
  -- A basis `d` starting with `v` whose condensed Gram matrix lies in the rank-`n` set, with
  -- its first row normalized.
  obtain ⟨d, rfl, hd⟩ := exists_basis_condensation_mem (hT (μ ^ n * D)) hB hpos hprim hμD'
  obtain ⟨e, r, hr, he⟩ := exists_basis_toMatrix_eq_extendGram hB d hμ
  exact ⟨e, Finset.mem_biUnion.mpr ⟨μ, Finset.mem_Icc.mpr ⟨hμ, hμD⟩, Finset.mem_image.mpr
    ⟨(r, _), Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr hr, hd⟩, he.symm⟩⟩⟩

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
