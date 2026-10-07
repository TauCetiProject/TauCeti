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
import TauCeti.LinearAlgebra.BilinearMap.GramCongruence
import TauCeti.LinearAlgebra.Matrix.Condensation

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
S(y, z) = μ · B(y, z) - B(v, y) · B(v, z)
```

is `μ` times the form induced on the projection of `K` orthogonal to `v`; it is again positive
definite, and Chiò's condensation `Matrix.mul_det_condensation_eq_pow_mul_det` gives
`μ · det S = μⁿ · det B` in a basis of `M` extending `v`. Writing a vector of `M` as `t v + y` and
choosing `t` to be a nearest integer to `-B(v, y) / μ`, the minimality of `μ` gives
`3 μ² ≤ 4 S(y, y)` for every nonzero `y ∈ K`. The inductive hypothesis applied to `S` then
bounds `μ`.

The forms and the determinant argument stay integral; the nearest-integer step is
`Int.exists_two_mul_abs_sub_mul_le`. The least norm exists because norms of nonzero vectors are
positive integers.

## Main results

* `LinearMap.BilinForm.exists_isPrimitive_forall_apply_self_le`: a positive definite integral form
  attains its minimum at a primitive vector.
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
form `S(y, z) = μ B(y, z) - B(v, y) B(v, z)` on `K`. -/
private theorem hermiteBound_succ (n : ℕ) (ih : HermiteBound.{u} n) :
    HermiteBound.{u} (n + 1) := by
  intro M _ _ B hB hpos b
  classical
  have : Module.Free ℤ M := .of_basis b
  have : Module.Finite ℤ M := .of_basis b
  have hsymm : ∀ x y, B x y = B y x := isSymm_def.mp hB
  -- A primitive vector `v` of least norm `μ`.
  obtain ⟨v, hprim, hmin⟩ := exists_isPrimitive_forall_apply_self_le B
    (fun x hx ↦ by simpa using hpos x hx)
  have hv0 := hprim.ne_zero
  set μ := B v v with hμ_def
  have hμ : 0 < μ := hpos v hv0
  obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp hprim
  -- Split `M = ℤ v ⊕ K` along `f` and extend `v` by a basis of `K`.
  set K := LinearMap.ker f
  obtain ⟨m, ⟨bK⟩⟩ := Submodule.nonempty_basis_of_pid (Module.finBasis ℤ M) K
  have hli : ∀ (a : ℤ), ∀ x ∈ K, a • v + x = 0 → a = 0 := fun a x hx hax ↦ by
    simpa [hf, LinearMap.mem_ker.mp hx] using congrArg f hax
  have hsp : ∀ z : M, ∃ a : ℤ, z + a • v ∈ K := fun z ↦
    ⟨-f z, by simp [K, LinearMap.mem_ker, hf]⟩
  let c := Basis.mkFinCons v bK hli hsp
  have hmn : n = m := by simpa using Fintype.card_congr (b.indexEquiv c)
  subst hmn
  rw [← toMatrixAux_eq b B]
  simp only [toMatrixAux]
  rw [← LinearMap.det_toMatrix₂Aux_eq_det_toMatrix₂Aux B b c]
  -- The condensed form `S(y, z) = μ B(y, z) - B(v, y) B(v, z)` on `K`.
  let ℓ : K →ₗ[ℤ] ℤ := (B v).comp K.subtype
  let S : LinearMap.BilinForm ℤ K :=
    μ • B.compl₁₂ K.subtype K.subtype - (LinearMap.mul ℤ ℤ).compl₁₂ ℓ ℓ
  have hS : ∀ y z : K, S y z = μ * B y z - B v y * B v z := fun y z ↦ by simp [S, ℓ]
  have hSsymm : S.IsSymm := isSymm_def.mpr fun y z ↦ by
    rw [hS, hS, hsymm (y : M) z]
    ring
  have hkey : ∀ (t : ℤ) (y : M),
      μ * B (t • v + y) (t • v + y) = (t * μ + B v y) ^ 2 + (μ * B y y - B v y ^ 2) := by
    intro t y
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hsymm y v]
    ring
  -- `S` is positive definite: `B(z, z) = μ S(y, y)` for `z = -B(v, y) v + μ y`.
  have hSpos : ∀ y : K, y ≠ 0 → 0 < S y y := by
    intro y hy
    have hz : (-B v y) • v + μ • (y : M) ≠ 0 := by
      intro h
      have ht := hli _ _ (K.smul_mem μ y.2) h
      rw [ht, zero_smul, zero_add] at h
      exact hy (Subtype.ext ((smul_eq_zero.mp h).resolve_left hμ.ne'))
    have h₁ := hkey (-B v y) (μ • (y : M))
    have h₂ := mul_pos hμ (hpos _ hz)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h₁
    have h₃ : 0 < μ ^ 2 * S y y := by
      rw [hS]
      nlinarith
    exact pos_of_mul_pos_right h₃ (sq_nonneg μ)
  -- Minimality of `μ` bounds `S` from below on nonzero vectors of `K`.
  have hSlow : ∀ y : K, y ≠ 0 → 3 * μ ^ 2 ≤ 4 * S y y := by
    intro y hy
    obtain ⟨k, hk⟩ := Int.exists_two_mul_abs_sub_mul_le (B v y) hμ
    have hk' : 0 ≤ μ + 2 * |B v y - k * μ| := by positivity
    obtain ⟨t, ht⟩ : ∃ t : ℤ, 4 * (t * μ + B v y) ^ 2 ≤ μ ^ 2 :=
      ⟨-k, by nlinarith [mul_nonneg (sub_nonneg.mpr hk) hk', sq_abs (B v y - k * μ)]⟩
    have hne : t • v + (y : M) ≠ 0 := by
      intro h
      rw [hli t y y.2 h, zero_smul, zero_add] at h
      exact hy (Subtype.ext h)
    have h₁ := hkey t y
    have h₂ := mul_le_mul_of_nonneg_left (hmin _ hne) hμ.le
    rw [hS]
    nlinarith
  -- Chiò's condensation of the Gram matrix of `B` in `c` is the Gram matrix of `S` in `bK`.
  have hdet : μ * (toMatrix bK S).det = μ ^ n * (toMatrix c B).det := by
    have hc0 : toMatrix c B 0 0 = μ := by simp [c, toMatrix_apply, hμ_def]
    rw [← hc0, ← Matrix.mul_det_condensation_eq_pow_mul_det]
    congr 2
    ext i j
    simp [c, toMatrix_apply, hS, hsymm (bK i : M) v, hμ_def]
  rw [← toMatrixAux_eq c B] at hdet
  simp only [toMatrixAux] at hdet
  refine ⟨v, hv0, ?_⟩
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [pow_zero, Matrix.det_isEmpty, mul_one, one_mul] at hdet
    simpa using hdet.le
  have : Nontrivial K := nontrivial_of_ne _ _ (bK.ne_zero ⟨0, hn⟩)
  obtain ⟨y, hy, hyb⟩ := ih S hSsymm hSpos bK
  have hchoose : (n + 1).choose 2 = n.choose 2 + n := by simp [Nat.choose_succ_succ', add_comm]
  rw [hchoose]
  exact three_pow_mul_pow_succ_le hμ (hSlow y hy) hyb hdet

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
