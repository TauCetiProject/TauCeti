/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Algebra.Module.Primitive
public import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.Data.Int.Round
import TauCeti.LinearAlgebra.Basis.Fin
import TauCeti.LinearAlgebra.BilinearForm.Condensation
import TauCeti.LinearAlgebra.BilinearMap.GramCongruence

/-!
# Hermite's inequality for positive definite integral forms

Let `B` be a symmetric positive definite `ℤ`-valued bilinear form on a free `ℤ`-module `M` of
rank `n ≥ 1`, and let `det B` be its Gram determinant, which does not depend on the basis. Hermite's
inequality says that some nonzero vector satisfies

```text
B(x, x) ≤ (4 / 3) ^ ((n - 1) / 2) · (det B) ^ (1 / n).
```

This file proves it with the powers cleared, as the inequality of integers

```text
3 ^ (n choose 2) · B(x, x) ^ n ≤ 4 ^ (n choose 2) · det B.
```

The proof is Hermite's induction on the rank. Let `v` be a nonzero vector of least norm
`μ = B(v, v)`. It is primitive, so `M = ℤ v ⊕ K` with `K` the kernel of a functional taking the
value `1` on `v`. On `K` the integral form

```text
S(y, z) = μ · B(y, z) - B(y, v) · B(v, z)
```

is `μ` times the form induced on the projection of `K` orthogonal to `v`; it is again positive
definite (`LinearMap.BilinForm.apply_mul_apply_lt_of_mem_ker`), and Chiò's condensation for Gram
matrices (`LinearMap.BilinForm.mul_det_toMatrix_eq_pow_mul_det_toMatrix`) gives
`μ · det S = μⁿ · det B` in a basis of `M` extending `v`. Writing a vector of `M` as `y + t v` and
choosing `t` to be a nearest integer to `-B(v, y) / μ`, the minimality of `μ` gives
`3 μ² ≤ 4 S(y, y)` for every `y` outside `ℤ v`, in particular for every nonzero `y ∈ K`. The
inductive hypothesis applied to `S` then bounds `μ`.

The forms and the determinant argument stay integral; the nearest-integer step is
`Int.exists_two_mul_abs_sub_mul_le`. The least norm exists because norms of nonzero vectors are
positive integers.

## Main results

* `LinearMap.BilinForm.exists_isPrimitive_forall_apply_self_le`: a positive definite integral form
  attains its minimum at a primitive vector.
* `LinearMap.BilinForm.three_mul_sq_le_four_mul_sub_of_forall_le`: the minimality step, which
  bounds the condensed form along a vector of least norm from below.
* `LinearMap.BilinForm.exists_ne_zero_three_pow_mul_pow_le_four_pow_mul_det`: Hermite's
  inequality `3 ^ (n choose 2) · B(x, x) ^ n ≤ 4 ^ (n choose 2) · det B` for some nonzero `x`.

## References

* C. Hermite, *Extraits de lettres de M. Ch. Hermite à M. Jacobi sur différents objets de la
  théorie des nombres*, J. Reine Angew. Math. 40 (1850), 261–315.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 1, §1.5.
-/

public section

open Module

namespace LinearMap.BilinForm

universe u

/-- **A positive definite integral form attains its minimum at a primitive vector.** On a
nontrivial free `ℤ`-module, a bilinear form whose values `B(x, x)` on nonzero vectors are positive
integers has a nonzero vector of least norm, and every such vector is primitive: a proper multiple
`d • w`, `d ≥ 2`, has norm `d² B(w, w) > B(w, w)`. -/
theorem exists_isPrimitive_forall_apply_self_le {M : Type*} [AddCommGroup M] [Module.Free ℤ M]
    [Nontrivial M] (B : LinearMap.BilinForm ℤ M) (hpos : B.toQuadraticMap.PosDef) :
    ∃ v, TauCeti.IsPrimitive v ∧ ∀ x, x ≠ 0 → B v v ≤ B x x := by
  classical
  have hpos' : ∀ x, x ≠ 0 → 0 < B x x := fun x hx ↦ by simpa using hpos x hx
  have hex : ∃ k : ℕ, ∃ x : M, x ≠ 0 ∧ B x x = k := by
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    exact ⟨(B x x).toNat, x, hx, (Int.toNat_of_nonneg (hpos' x hx).le).symm⟩
  obtain ⟨v, hv0, hvk⟩ := Nat.find_spec hex
  have hmin : ∀ x, x ≠ 0 → B v v ≤ B x x := fun x hx ↦ by
    rw [hvk, ← Int.toNat_of_nonneg (hpos' x hx).le]
    exact_mod_cast Nat.find_min' hex ⟨x, hx, (Int.toNat_of_nonneg (hpos' x hx).le).symm⟩
  refine ⟨v, ?_, hmin⟩
  obtain ⟨d, w, hd, hw, hvw⟩ := TauCeti.exists_eq_zsmul_isPrimitive hv0
  have hww := hpos' w hw.ne_zero
  have hle := hmin w hw.ne_zero
  rw [hvw] at hle
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc] at hle
  have hdd : d * d ≤ 1 := le_of_mul_le_mul_right (by rwa [one_mul]) hww
  have hd1 : d = 1 := by nlinarith
  rwa [hvw, hd1, one_smul]

/-- **The minimality step of Hermite's inequality.** Let `v` be a vector of least norm
`μ = B(v, v) > 0` among the nonzero vectors, for a symmetric integral form `B`. Every `y` outside
`ℤ v` satisfies `3 μ² ≤ 4 (μ B(y, y) - B(y, v) B(v, y))`. Indeed, adding to `y` a multiple `t v`
with `t` nearest to `-B(v, y) / μ` gives a nonzero vector with `4 B(v, y + t v)² ≤ μ²`, and
completing the square along `v` (`LinearMap.BilinForm.mul_apply_add_smul_add_smul`) compares its
norm, which is at least `μ`, with the condensed form. -/
theorem three_mul_sq_le_four_mul_sub_of_forall_le {M : Type*} [AddCommGroup M]
    {B : LinearMap.BilinForm ℤ M} (hB : B.IsSymm) {v y : M} (hμ : 0 < B v v)
    (hmin : ∀ x, x ≠ 0 → B v v ≤ B x x) (hy : y ∉ ℤ ∙ v) :
    3 * B v v ^ 2 ≤ 4 * (B v v * B y y - B y v * B v y) := by
  obtain ⟨k, hk⟩ := Int.exists_two_mul_abs_sub_mul_le (B v y) hμ
  have hk' : 0 ≤ B v v + 2 * |B v y - k * B v v| := by positivity
  have hne : y + (-k) • v ≠ 0 := fun h ↦ hy (Submodule.mem_span_singleton.mpr
    ⟨k, (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)).symm⟩)
  have hv : B v (y + (-k) • v) = B v y - k * B v v := by simp [sub_eq_add_neg]
  have h := mul_le_mul_of_nonneg_left (hmin _ hne) hμ.le
  rw [B.mul_apply_add_smul_add_smul, hB.eq (y + _) v, hv] at h
  rw [hB.eq y v] at h ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr hk) hk', sq_abs (B v y - k * B v v)]

/-- The arithmetic closing the inductive step of Hermite's inequality: if `3 μ² ≤ 4 s`, the
bound `3 ^ C · sⁿ ≤ 4 ^ C · D'` holds in rank `n`, and `μ · D' = μⁿ · D`, then
`3 ^ (C + n) · μ ^ (n + 1) ≤ 4 ^ (C + n) · D`. -/
private theorem three_pow_mul_pow_succ_le {μ s D D' : ℤ} {n C : ℕ} (hμ : 0 < μ)
    (hs : 3 * μ ^ 2 ≤ 4 * s) (hD' : 3 ^ C * s ^ n ≤ 4 ^ C * D') (hD : μ * D' = μ ^ n * D) :
    3 ^ (C + n) * μ ^ (n + 1) ≤ 4 ^ (C + n) * D := by
  have h₁ : 3 ^ C * (3 * μ ^ 2) ^ n ≤ 4 ^ n * (4 ^ C * D') :=
    calc 3 ^ C * (3 * μ ^ 2) ^ n ≤ 3 ^ C * (4 * s) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hs _) (by positivity)
      _ = 4 ^ n * (3 ^ C * s ^ n) := by ring
      _ ≤ 4 ^ n * (4 ^ C * D') := mul_le_mul_of_nonneg_left hD' (by positivity)
  refine le_of_mul_le_mul_left (a := μ ^ n) ?_ (by positivity)
  calc μ ^ n * (3 ^ (C + n) * μ ^ (n + 1)) = 3 ^ C * (3 * μ ^ 2) ^ n * μ := by ring
    _ ≤ 4 ^ n * (4 ^ C * D') * μ := mul_le_mul_of_nonneg_right h₁ hμ.le
    _ = 4 ^ n * 4 ^ C * (μ * D') := by ring
    _ = μ ^ n * (4 ^ (C + n) * D) := by rw [hD]; ring

/-- The statement of Hermite's inequality for forms on free `ℤ`-modules with a basis indexed by
`Fin n`, with the powers cleared. -/
private def HermiteBound (n : ℕ) : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Nontrivial M] (B : LinearMap.BilinForm ℤ M),
    B.IsSymm → (∀ x, x ≠ 0 → 0 < B x x) → ∀ b : Basis (Fin n) ℤ M,
      ∃ x, x ≠ 0 ∧ 3 ^ n.choose 2 * B x x ^ n ≤ 4 ^ n.choose 2 * (toMatrix b B).det

/-- The inductive step of Hermite's inequality: the bound in rank `n` implies it in rank `n + 1`.
A vector `v` of least norm `μ` is primitive, so it extends to a basis `v, bK` with `bK` a basis of
the kernel `K` of a functional taking the value `1` on `v`; the bound is applied to the condensed
form `S(y, z) = μ B(y, z) - B(y, v) B(v, z)` on `K`. -/
private theorem hermiteBound_succ (n : ℕ) (ih : HermiteBound.{u} n) :
    HermiteBound.{u} (n + 1) := by
  intro M _ _ B hB hpos b
  have : Module.Free ℤ M := .of_basis b
  -- A primitive vector `v` of least norm `μ`.
  obtain ⟨v, hprim, hmin⟩ := exists_isPrimitive_forall_apply_self_le B
    (fun x hx ↦ by simpa using hpos x hx)
  set μ := B v v
  have hμ : 0 < μ := hpos v hprim.ne_zero
  -- Split `M = ℤ v ⊕ K` along `f` and extend `v` by a basis of `K`.
  obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp hprim
  set K := LinearMap.ker f
  obtain ⟨m, ⟨bK⟩⟩ := Submodule.nonempty_basis_of_pid b K
  obtain ⟨c, hc0, hc⟩ := bK.exists_basis_finCons_of_apply_eq_one hf
  obtain rfl : n = m := by simpa using Fintype.card_congr (b.indexEquiv c)
  have hbc : (toMatrix b B).det = (toMatrix c B).det := by
    rw [← toMatrixAux_eq b B, ← toMatrixAux_eq c B]
    exact (LinearMap.det_toMatrix₂Aux_eq_det_toMatrix₂Aux B b c).symm
  -- The condensed form `S(y, z) = μ B(y, z) - B(y, v) B(v, z)` on `K`, and Chiò's identity.
  obtain ⟨S, hSsymm, hS⟩ := hB.exists_isSymm_forall_apply_eq v K.subtype
  have hdet := mul_det_toMatrix_eq_pow_mul_det_toMatrix B c bK (S := S) fun i j ↦ by
    simp [hc0, hc, hS]
  rw [hc0] at hdet
  refine ⟨v, hprim.ne_zero, hbc ▸ ?_⟩
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa using hdet.le
  have : Nontrivial K := nontrivial_of_ne _ _ (bK.ne_zero ⟨0, hn⟩)
  obtain ⟨y, hy, hyb⟩ := ih S hSsymm (fun y hy ↦ hS y y ▸ sub_pos.mpr
    (apply_mul_apply_lt_of_mem_ker hpos (by simp [hf]) y.2 (by simpa using hy))) bK
  have hyv : (y : M) ∉ ℤ ∙ v := fun h ↦ by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
    obtain rfl : a = 0 := by simpa [hf, LinearMap.mem_ker.mp y.2] using congrArg f ha
    exact hy (Subtype.ext (by simp [← ha]))
  rw [show (n + 1).choose 2 = n.choose 2 + n by simp [Nat.choose_succ_succ', add_comm]]
  exact three_pow_mul_pow_succ_le hμ
    (hS y y ▸ three_mul_sq_le_four_mul_sub_of_forall_le hB hμ hmin hyv) hyb hdet

/-- Hermite's inequality for a basis indexed by `Fin n`, by induction on `n`. -/
private theorem hermiteBound (n : ℕ) : HermiteBound.{u} n := by
  induction n with
  | zero =>
    intro M _ _ B _ _ b
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    exact absurd (b.repr.injective (Subsingleton.elim _ _)) hx
  | succ n ih => exact hermiteBound_succ n ih

/-- **Hermite's inequality.** A symmetric positive definite integral bilinear form `B` on a free
`ℤ`-module of rank `n ≥ 1` takes on some nonzero vector `x` a value with
`3 ^ (n choose 2) · B(x, x) ^ n ≤ 4 ^ (n choose 2) · det B`, where `det B` is the Gram determinant
of `B` in any basis. Equivalently `B(x, x) ≤ (4 / 3) ^ ((n - 1) / 2) · (det B) ^ (1 / n)`. -/
theorem exists_ne_zero_three_pow_mul_pow_le_four_pow_mul_det {M : Type*} [AddCommGroup M]
    [Nontrivial M] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℤ M) (hB : B.IsSymm) (hpos : B.toQuadraticMap.PosDef)
    (b : Basis ι ℤ M) :
    ∃ x, x ≠ 0 ∧ 3 ^ (Fintype.card ι).choose 2 * B x x ^ Fintype.card ι ≤
      4 ^ (Fintype.card ι).choose 2 * (toMatrix b B).det := by
  have h := hermiteBound (Fintype.card ι) B hB (fun x hx ↦ by simpa using hpos x hx)
    (b.reindex (Fintype.equivFin ι))
  rw [← toMatrixAux_eq b B]
  simp only [toMatrixAux]
  rw [← toMatrixAux_eq (b.reindex (Fintype.equivFin ι)) B] at h
  simp only [toMatrixAux] at h
  rw [LinearMap.det_toMatrix₂Aux_eq_det_toMatrix₂Aux B b (b.reindex (Fintype.equivFin ι))] at h
  exact h

end LinearMap.BilinForm
