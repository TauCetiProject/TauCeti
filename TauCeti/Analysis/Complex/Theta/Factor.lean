/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic

/-!
# The factor of automorphy of the level-`k` theta line

Fix `τ ∈ ℂ`, an integer level `k` and real characteristics `α, β`. The lattice `ℤ + τ ℤ` acts on
`ℂ × ℂ` by `(z, v) ↦ (z + m + n τ, e_(m,n)(z) v)` through the factor of automorphy
(`TauCeti.thetaFactor`)

`e_(m,n)(z) = exp (2πi(mα + nβ) - πikn²τ - 2πiknz)`,

whose generators are `e_(1,0)(z) = exp (2πiα)` and `e_(0,1)(z) = exp (2πiβ - πikτ - 2πikz)`.
The cocycle law `e_(λ + μ)(z) = e_λ(z + μ) e_μ(z)` (`TauCeti.thetaFactor_add`) makes this an action,
and the quotient is the theta line of level `k` and characteristics `(α, β)` on the torus
`ℂ / (ℤ + τℤ)`. The law uses that `k` is an integer: for an arbitrary real level `k : ℝ`, the two
ways of composing the `1`- and `τ`-translations differ by `exp (-2πik)`
(`TauCeti.exp_thetaAutomorphy_commutator`), so they commute if and only if `k` is an integer
(`TauCeti.exp_thetaAutomorphy_commutator_eq_iff_exists_intCast_eq`). Shifting `(α, β)` by integers
leaves `thetaFactor` invariant (`TauCeti.thetaFactor_add_int`), and tensor product of theta lines
adds levels and characteristics (`TauCeti.thetaFactor_mul_thetaFactor`).

## Main definitions

* `TauCeti.thetaFactor k τ α β m n z`: the factor of automorphy `e_(m,n)(z)`.

## Main results

* `TauCeti.thetaFactor_add`: the cocycle law.
* `TauCeti.thetaFactor_add_int`: shifting characteristics by integers leaves `thetaFactor`
  unchanged.
* `TauCeti.thetaFactor_mul_thetaFactor`: multiplying factors adds levels and characteristics.
* `TauCeti.exp_thetaAutomorphy_commutator` and
  `TauCeti.exp_thetaAutomorphy_commutator_eq_iff_exists_intCast_eq`: integrality obstruction at
  real level.
* `TauCeti.forall_add_eq_thetaFactor_mul_iff`: the lattice automorphy law is equivalent to the
  two generator laws.

## References

* David Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser, 1983,
  Chapter I, §§1–3 (theta functions with characteristics and their functional equations).
* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 2 (factors of
  automorphy and the canonical factor).
-/

public section

open Complex Real

namespace TauCeti

variable (k : ℤ) (τ : ℂ) (α β : ℝ)

/-- The **factor of automorphy** of the level-`k` theta line with characteristics `(α, β)` on the
torus `ℂ / (ℤ + τℤ)`: the multiplier `e_(m,n)(z) = exp (2πi(mα + nβ) - πikn²τ - 2πiknz)` by which
a section changes under translation by the lattice vector `m + nτ`. -/
noncomputable def thetaFactor (m n : ℤ) (z : ℂ) : ℂ :=
  cexp (2 * π * I * (m * α + n * β) - π * I * k * n ^ 2 * τ - 2 * π * I * k * n * z)

theorem thetaFactor_def (m n : ℤ) (z : ℂ) :
    thetaFactor k τ α β m n z =
      cexp (2 * π * I * (m * α + n * β) - π * I * k * n ^ 2 * τ - 2 * π * I * k * n * z) :=
  (rfl)

variable {k τ α β}

@[simp]
theorem thetaFactor_ne_zero (m n : ℤ) (z : ℂ) : thetaFactor k τ α β m n z ≠ 0 :=
  Complex.exp_ne_zero _

@[simp]
theorem thetaFactor_zero_zero (z : ℂ) : thetaFactor k τ α β 0 0 z = 1 := by
  simp [thetaFactor_def]

/-- The factor of the generator `1` of the lattice. -/
@[simp]
theorem thetaFactor_one_zero (z : ℂ) : thetaFactor k τ α β 1 0 z = cexp (2 * π * I * α) := by
  simp [thetaFactor_def]

/-- The factor of the generator `τ` of the lattice. -/
@[simp]
theorem thetaFactor_zero_one (z : ℂ) :
    thetaFactor k τ α β 0 1 z = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) := by
  simp [thetaFactor_def]

/-- Shifting the characteristics `(α, β)` by integers leaves `thetaFactor` unchanged. -/
theorem thetaFactor_add_int (k : ℤ) (τ : ℂ) (α β : ℝ) (a b m n : ℤ) (z : ℂ) :
    thetaFactor k τ (α + a) (β + b) m n z = thetaFactor k τ α β m n z := by
  simp only [thetaFactor_def]
  have h1 : cexp (((m * a + n * b : ℤ) : ℂ) * (2 * π * I)) = 1 :=
    Complex.exp_int_mul_two_pi_mul_I (m * a + n * b)
  conv_rhs => rw [← mul_one (cexp _), ← h1, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The cocycle law** `e_(λ + μ)(z) = e_λ(z + μ) e_μ(z)` for the lattice vectors `λ = m + nτ`
and `μ = m' + n'τ`. It holds because the level `k` is an integer. -/
theorem thetaFactor_add (m n m' n' : ℤ) (z : ℂ) :
    thetaFactor k τ α β (m + m') (n + n') z =
      thetaFactor k τ α β m n (z + m' + n' * τ) * thetaFactor k τ α β m' n' z := by
  rw [thetaFactor_def, thetaFactor_def, thetaFactor_def, ← Complex.exp_add,
    Complex.exp_eq_exp_iff_exists_int]
  exact ⟨k * n * m', by push_cast; ring⟩

/-- The tensor product of two theta lines is a theta line: factors of automorphy multiply by
adding the levels and the characteristics. -/
theorem thetaFactor_mul_thetaFactor (k' : ℤ) (α' β' : ℝ) (m n : ℤ) (z : ℂ) :
    thetaFactor k τ α β m n z * thetaFactor k' τ α' β' m n z =
      thetaFactor (k + k') τ (α + α') (β + β') m n z := by
  simp only [thetaFactor_def, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The modulus of the factor of automorphy: `|e_(m,n)(z)| = exp (πkn (n Im τ + 2 Im z))`. -/
theorem norm_thetaFactor (m n : ℤ) (z : ℂ) :
    ‖thetaFactor k τ α β m n z‖ = Real.exp (π * k * n * (n * τ.im + 2 * z.im)) := by
  rw [thetaFactor_def, Complex.norm_exp]
  congr 1
  simp only [sub_re, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im,
    intCast_re, intCast_im, re_ofNat, im_ofNat, sq]
  ring

/-- The factor of automorphy is holomorphic in `z`, with derivative `-2πikn e_(m,n)(z)`. -/
theorem hasDerivAt_thetaFactor (m n : ℤ) (z : ℂ) :
    HasDerivAt (thetaFactor k τ α β m n)
      (-(2 * π * I * k * n) * thetaFactor k τ α β m n z) z := by
  have h : HasDerivAt (fun w : ℂ ↦
      2 * π * I * (m * α + n * β) - π * I * k * n ^ 2 * τ - 2 * π * I * k * n * w)
      (-(2 * π * I * k * n)) z := by
    simpa using ((hasDerivAt_id z).const_mul (2 * π * I * k * n)).const_sub
      (2 * π * I * (m * α + n * β) - π * I * k * n ^ 2 * τ)
  rw [mul_comm]
  exact h.cexp

/-- The logarithmic derivative of the factor of automorphy is the constant `-2πikn`. -/
@[simp]
theorem logDeriv_thetaFactor (m n : ℤ) (z : ℂ) :
    logDeriv (thetaFactor k τ α β m n) z = -(2 * π * I * k * n) := by
  rw [logDeriv_apply, (hasDerivAt_thetaFactor m n z).deriv,
    mul_div_cancel_right₀ _ (thetaFactor_ne_zero m n z)]

/-- For an arbitrary real level `k : ℝ`, composing the `z ↦ z + 1` and `z ↦ z + τ` automorphy
factors in the two orders differs by the constant phase `exp (-2πik)`. -/
theorem exp_thetaAutomorphy_commutator (k : ℝ) (τ : ℂ) (α β : ℝ) (z : ℂ) :
    cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * (z + 1)) * cexp (2 * π * I * α) =
      cexp (-2 * π * I * k) *
        (cexp (2 * π * I * α) * cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z)) := by
  simp only [← Complex.exp_add]
  congr 1
  ring

/-- **Integrality obstruction for the torus automorphy factor.** The `z ↦ z + 1` and `z ↦ z + τ`
generator factors at real level `k : ℝ` satisfy the abelian compatibility relation if and only if
`k` is an integer. -/
theorem exp_thetaAutomorphy_commutator_eq_iff_exists_intCast_eq (k : ℝ) (τ : ℂ) (α β : ℝ)
    (z : ℂ) :
    cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * (z + 1)) * cexp (2 * π * I * α) =
        cexp (2 * π * I * α) * cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) ↔
      ∃ n : ℤ, (n : ℝ) = k := by
  rw [exp_thetaAutomorphy_commutator]
  have hne :
      cexp (2 * π * I * α) * cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  rw [mul_eq_right₀ hne, neg_mul, neg_mul, neg_mul, Complex.exp_neg, inv_eq_one,
    Complex.exp_two_pi_mul_I_mul_ofReal_eq_one_iff]
  exact exists_congr fun _ => eq_comm

/-- The automorphy law at one lattice vector propagates along the cocycle law: if it holds at
`λ` and `μ` it holds at `λ + μ`. -/
private theorem add_eq_thetaFactor_mul_of_add {s : ℂ → ℂ} {m n m' n' : ℤ}
    (h : ∀ z, s (z + m + n * τ) = thetaFactor k τ α β m n z * s z)
    (h' : ∀ z, s (z + m' + n' * τ) = thetaFactor k τ α β m' n' z * s z) (z : ℂ) :
    s (z + ↑(m + m') + ↑(n + n') * τ) = thetaFactor k τ α β (m + m') (n + n') z * s z := by
  have := h (z + m' + n' * τ)
  rw [show z + m' + n' * τ + m + n * τ = z + ↑(m + m') + ↑(n + n') * τ by push_cast; ring,
    h' z] at this
  rw [this, thetaFactor_add, mul_assoc]

/-- The lattice vectors at which a function satisfies the automorphy law form a subgroup. -/
private noncomputable def automorphySubgroup (s : ℂ → ℂ) : AddSubgroup (ℤ × ℤ) where
  carrier := {p | ∀ z, s (z + p.1 + p.2 * τ) = thetaFactor k τ α β p.1 p.2 z * s z}
  zero_mem' := fun z ↦ by simp
  add_mem' {p q} hp hq := add_eq_thetaFactor_mul_of_add hp hq
  neg_mem' {p} hp z := by
    have h0 := thetaFactor_add (k := k) (τ := τ) (α := α) (β := β) p.1 p.2 (-p.1) (-p.2) z
    have hs := hp (z + ↑(-p.1) + ↑(-p.2) * τ)
    simp only [add_neg_cancel, thetaFactor_zero_zero] at h0
    rw [show z + ↑(-p.1) + ↑(-p.2) * τ + p.1 + p.2 * τ = z by push_cast; ring] at hs
    have hne := thetaFactor_ne_zero (k := k) (τ := τ) (α := α) (β := β) p.1 p.2
      (z + ↑(-p.1) + ↑(-p.2) * τ)
    simp only [Prod.fst_neg, Prod.snd_neg]
    apply mul_left_cancel₀ hne
    rw [← hs, ← mul_assoc, ← h0, one_mul]

private theorem mem_automorphySubgroup {s : ℂ → ℂ} {p : ℤ × ℤ} :
    p ∈ automorphySubgroup (k := k) (τ := τ) (α := α) (β := β) s ↔
      ∀ z, s (z + p.1 + p.2 * τ) = thetaFactor k τ α β p.1 p.2 z * s z :=
  Iff.rfl

/-- **Sections of the theta line.** A function satisfies the automorphy law
`s (z + m + nτ) = e_(m,n)(z) s z` for every lattice vector exactly when it satisfies it for the
generators: `s (z + 1) = exp (2πiα) s z` and `s (z + τ) = exp (2πiβ - πikτ - 2πikz) s z`. -/
theorem forall_add_eq_thetaFactor_mul_iff {s : ℂ → ℂ} :
    (∀ (m n : ℤ) z, s (z + m + n * τ) = thetaFactor k τ α β m n z * s z) ↔
      (∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) ∧
        ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z := by
  refine ⟨fun h ↦ ⟨fun z ↦ by simpa using h 1 0 z, fun z ↦ by simpa using h 0 1 z⟩, ?_⟩
  rintro ⟨h1, hτ⟩ m n
  have h10 : ((1, 0) : ℤ × ℤ) ∈ automorphySubgroup (k := k) (τ := τ) (α := α) (β := β) s :=
    mem_automorphySubgroup.mpr fun z ↦ by simpa using h1 z
  have h01 : ((0, 1) : ℤ × ℤ) ∈ automorphySubgroup (k := k) (τ := τ) (α := α) (β := β) s :=
    mem_automorphySubgroup.mpr fun z ↦ by simpa using hτ z
  have hmn : ((m, n) : ℤ × ℤ) = m • ((1, 0) : ℤ × ℤ) + n • ((0, 1) : ℤ × ℤ) := by simp
  have h := add_mem (zsmul_mem h10 m) (zsmul_mem h01 n)
  rw [← hmn] at h
  exact mem_automorphySubgroup.mp h

end TauCeti
