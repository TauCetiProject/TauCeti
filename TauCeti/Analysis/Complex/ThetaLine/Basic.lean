/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair

/-!
# The level-`k` theta line on a complex torus

Fix `τ ∈ ℂ`, an integer level `k` and real characteristics `α, β`. The lattice `ℤ + τ ℤ` acts on
`ℂ × ℂ` by `(z, v) ↦ (z + m + n τ, e_(m,n)(z) v)` through the factor of automorphy
(`TauCeti.thetaFactor`)

`e_(m,n)(z) = exp (2πi(mα + nβ) - πikn²τ - 2πiknz)`,

whose generators are `e_(1,0)(z) = exp (2πiα)` and `e_(0,1)(z) = exp (2πiβ - πikτ - 2πikz)`.
The cocycle law `e_(λ + μ)(z) = e_λ(z + μ) e_μ(z)` (`TauCeti.thetaFactor_add`) makes this an action,
and the quotient is the theta line of level `k` and characteristics `(α, β)` on the torus
`ℂ / (ℤ + τℤ)`. The law uses that `k` is an integer: the two ways of translating by `1 + τ`
differ by `exp (-2πik)`. Its sections are the functions `s` on `ℂ` with
`s (z + m + nτ) = e_(m,n)(z) s z`, and these are exactly the functions satisfying the two generator
laws (`TauCeti.forall_add_eq_thetaFactor_mul_iff`). Tensor product of theta lines adds levels and
characteristics (`TauCeti.thetaFactor_mul_thetaFactor`).

For `Im τ ≠ 0` the function `h(z) = exp (-2πk (Im z)² / Im τ)` (`TauCeti.thetaMetric`) satisfies
`h(z + λ) |e_λ(z)|² = h(z)` (`TauCeti.thetaMetric_add_mul_norm_thetaFactor_sq`), so it is a
Hermitian metric on the theta line: for two sections `s, t` the pairing `h s conj t` is invariant
under the lattice, that is, it descends to the torus (`TauCeti.thetaMetric_add_mul_mul_conj`).
For `Im τ ≠ 0` the pointwise norm `h |s|²` of a continuous section is therefore bounded
(`TauCeti.exists_thetaMetric_mul_norm_sq_le`).

The Chern connection of `h` on holomorphic sections is `d + A dz` with
`A = ∂ log h = 2πik Im z / Im τ` (`TauCeti.thetaConnectionForm`,
`TauCeti.wirtingerDeriv_apply_one_log_thetaMetric`), computed from the Wirtinger derivatives
`∂ Im = -i/2` and `∂bar Im = i/2` (`TauCeti.wirtingerDeriv_apply_one_ofReal_im`,
`TauCeti.conjWirtingerDeriv_apply_one_ofReal_im`). It is compatible with the factor of automorphy:
`A(z + λ) + e_λ'(z) / e_λ(z) = A(z)` (`TauCeti.thetaConnectionForm_add_add_logDeriv_thetaFactor`),
which is the transformation law of a connection form under the transition function `e_λ`, so the
connection descends to the theta line. Its curvature is `∂bar A d(conj z) ∧ dz` with
`∂bar A = -πk / Im τ` (`TauCeti.conjWirtingerDeriv_apply_one_thetaConnectionForm`). In the real
coordinates `z = q + τ p`, `d(conj z) ∧ dz = 2i Im τ dq ∧ dp`, so the curvature is
`-2πik dq ∧ dp`; this is `-(i/ℏ) ω` for the symplectic form `ω = 2πℏk dq ∧ dp`, so the theta line
of level `k` is a prequantum line of `ω`.

## Main definitions

* `TauCeti.thetaFactor k τ α β m n z`: the factor of automorphy `e_(m,n)(z)`.
* `TauCeti.thetaMetric k τ z`: the Hermitian metric `exp (-2πk (Im z)² / Im τ)`.
* `TauCeti.thetaConnectionForm k τ z`: the `dz`-coefficient `2πik Im z / Im τ` of its Chern
  connection form.

## Main results

* `TauCeti.thetaFactor_add`: the cocycle law.
* `TauCeti.forall_add_eq_thetaFactor_mul_iff`: the lattice automorphy law is equivalent to the
  two generator laws.
* `TauCeti.thetaMetric_add_mul_norm_thetaFactor_sq`, `TauCeti.thetaMetric_add_mul_mul_conj`,
  `TauCeti.thetaMetric_add_mul_norm_sq`: the metric descends to the torus.
* `TauCeti.exists_thetaMetric_mul_norm_sq_le`: continuous sections have bounded pointwise norm.
* `TauCeti.wirtingerDeriv_apply_one_log_thetaMetric`,
  `TauCeti.thetaConnectionForm_add_add_logDeriv_thetaFactor`,
  `TauCeti.conjWirtingerDeriv_apply_one_thetaConnectionForm`: the Chern connection form, its
  gauge law, and its curvature.

## References

* David Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser, 1983,
  Chapter I, §§1–3 (theta functions with characteristics and their functional equations).
* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 2 (factors of
  automorphy, the canonical factor and its Hermitian metric).
-/

public section

open Complex ComplexConjugate Real

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

/-- The **Hermitian metric** `h(z) = exp (-2πk (Im z)² / Im τ)` of the level-`k` theta line on
`ℂ / (ℤ + τℤ)`, in the trivialization of its pull-back to `ℂ`. -/
noncomputable def thetaMetric (k : ℤ) (τ z : ℂ) : ℝ :=
  Real.exp (-2 * π * k * z.im ^ 2 / τ.im)

theorem thetaMetric_def (z : ℂ) :
    thetaMetric k τ z = Real.exp (-2 * π * k * z.im ^ 2 / τ.im) :=
  (rfl)

theorem thetaMetric_pos (z : ℂ) : 0 < thetaMetric k τ z :=
  Real.exp_pos _

theorem continuous_thetaMetric : Continuous (thetaMetric k τ) := by
  simp only [funext thetaMetric_def]
  fun_prop

/-- **The metric descends**: `h(z + λ) |e_λ(z)|² = h(z)` for every lattice vector
`λ = m + nτ`. -/
theorem thetaMetric_add_mul_norm_thetaFactor_sq (hτ : τ.im ≠ 0) (m n : ℤ) (z : ℂ) :
    thetaMetric k τ (z + m + n * τ) * ‖thetaFactor k τ α β m n z‖ ^ 2 = thetaMetric k τ z := by
  rw [thetaMetric_def, thetaMetric_def, norm_thetaFactor, sq (Real.exp _), ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  simp only [add_im, intCast_im, mul_im, intCast_re]
  field_simp
  ring

/-- **The Hermitian pairing of two sections descends to the torus**: if `s` and `t` satisfy the
automorphy law at the lattice vector `λ = m + nτ`, then
`h(z + λ) s(z + λ) conj (t (z + λ)) = h(z) s(z) conj (t z)`. -/
theorem thetaMetric_add_mul_mul_conj (hτ : τ.im ≠ 0) {s t : ℂ → ℂ} {m n : ℤ} {z : ℂ}
    (hs : s (z + m + n * τ) = thetaFactor k τ α β m n z * s z)
    (ht : t (z + m + n * τ) = thetaFactor k τ α β m n z * t z) :
    (thetaMetric k τ (z + m + n * τ) : ℂ) * (s (z + m + n * τ) * conj (t (z + m + n * τ))) =
      thetaMetric k τ z * (s z * conj (t z)) := by
  rw [hs, ht, map_mul, ← thetaMetric_add_mul_norm_thetaFactor_sq (α := α) (β := β) hτ m n z,
    ofReal_mul, ofReal_pow, ← Complex.mul_conj']
  ring

/-- **The pointwise norm of a section descends to the torus**: if `s` satisfies the automorphy
law at the lattice vector `λ = m + nτ`, then `h(z + λ) |s(z + λ)|² = h(z) |s(z)|²`. -/
theorem thetaMetric_add_mul_norm_sq (hτ : τ.im ≠ 0) {s : ℂ → ℂ} {m n : ℤ} {z : ℂ}
    (hs : s (z + m + n * τ) = thetaFactor k τ α β m n z * s z) :
    thetaMetric k τ (z + m + n * τ) * ‖s (z + m + n * τ)‖ ^ 2 =
      thetaMetric k τ z * ‖s z‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simpa only [Complex.mul_conj'] using thetaMetric_add_mul_mul_conj hτ hs hs

/-- **Sections have bounded pointwise norm.** For `Im τ ≠ 0`, a continuous function satisfying
the two automorphy laws of the theta line has bounded pointwise norm `h(z) |s(z)|²`, since that
norm is a continuous function on the compact torus. -/
theorem exists_thetaMetric_mul_norm_sq_le (hτ : τ.im ≠ 0) {s : ℂ → ℂ} (hc : Continuous s)
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z)
    (h2 : ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z) :
    ∃ C, ∀ z, thetaMetric k τ z * ‖s z‖ ^ 2 ≤ C := by
  have hs := forall_add_eq_thetaFactor_mul_iff.mpr ⟨h1, h2⟩
  -- The lattice `ℤ + τℤ` is that of the point `σ = ±τ` of the upper half-plane.
  obtain ⟨σ, ε, hε, rfl⟩ : ∃ (σ : UpperHalfPlane) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ τ = ε * σ := by
    rcases hτ.lt_or_gt with h | h
    · exact ⟨⟨-τ, by simpa using h⟩, -1, Or.inr rfl, by simp⟩
    · exact ⟨⟨τ, h⟩, 1, Or.inl rfl, by simp⟩
  have hper : ∀ z, ∀ w ∈ σ.periodPair.lattice, thetaMetric k (ε * σ) (z + w) * ‖s (z + w)‖ ^ 2 =
      thetaMetric k (ε * σ) z * ‖s z‖ ^ 2 := by
    intro z w hw
    obtain ⟨n, m, rfl⟩ := PeriodPair.mem_lattice.mp hw
    have hεε : (ε : ℂ) * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
    have := thetaMetric_add_mul_norm_sq hτ (hs m (ε * n) z)
    rwa [show z + m + ↑(ε * n) * (ε * σ) = z + (n * σ.periodPair.ω₁ + m * σ.periodPair.ω₂) by
      simp only [UpperHalfPlane.periodPair_ω₁, UpperHalfPlane.periodPair_ω₂]
      push_cast
      linear_combination (n * σ : ℂ) * hεε] at this
  obtain ⟨C, hC⟩ := (IsZLattice.isCompact_range_of_periodic σ.periodPair.lattice _
    (continuous_thetaMetric.mul (hc.norm.pow 2)) hper).isBounded.bddAbove
  exact ⟨C, fun z ↦ hC ⟨z, rfl⟩⟩

/-- The `dz`-coefficient `A(z) = 2πik Im z / Im τ` of the Chern connection form of the metric
`TauCeti.thetaMetric` on the theta line: on holomorphic sections the Chern connection is
`d + A dz`, with `A = ∂ log h` (`TauCeti.wirtingerDeriv_apply_one_log_thetaMetric`). -/
noncomputable def thetaConnectionForm (k : ℤ) (τ z : ℂ) : ℂ :=
  2 * π * I * k * z.im / τ.im

theorem thetaConnectionForm_def (z : ℂ) :
    thetaConnectionForm k τ z = 2 * π * I * k * z.im / τ.im :=
  (rfl)

/-- **The Chern connection form**: `∂ log h = A`, where `h` is the theta metric. -/
theorem wirtingerDeriv_apply_one_log_thetaMetric (z : ℂ) :
    wirtingerDeriv (fun w ↦ (Real.log (thetaMetric k τ w) : ℂ)) z 1 =
      thetaConnectionForm k τ z := by
  have hfun : (fun w ↦ (Real.log (thetaMetric k τ w) : ℂ)) =
      (-2 * π * k / τ.im : ℂ) • fun w : ℂ ↦ (w.im : ℂ) • (w.im : ℂ) := by
    funext w
    simp only [thetaMetric_def, Real.log_exp, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hd : DifferentiableAt ℝ (fun w : ℂ ↦ (w.im : ℂ)) z := by fun_prop
  rw [hfun, wirtingerDeriv_const_smul, smul_apply,
    wirtingerDeriv_smul_apply hd hd, wirtingerDeriv_apply_one_ofReal_im,
    thetaConnectionForm_def]
  simp only [smul_eq_mul]
  ring

/-- **The Chern connection descends to the theta line**: `A(z + λ) + e_λ'(z) / e_λ(z) = A(z)`
for every lattice vector `λ = m + nτ`, the transformation law of a connection form under the
transition function `e_λ`. -/
theorem thetaConnectionForm_add_add_logDeriv_thetaFactor (hτ : τ.im ≠ 0) (m n : ℤ) (z : ℂ) :
    thetaConnectionForm k τ (z + m + n * τ) + logDeriv (thetaFactor k τ α β m n) z =
      thetaConnectionForm k τ z := by
  rw [logDeriv_thetaFactor, thetaConnectionForm_def, thetaConnectionForm_def]
  simp only [add_im, intCast_im, mul_im, intCast_re, zero_mul, add_zero]
  have : (τ.im : ℂ) ≠ 0 := ofReal_ne_zero.mpr hτ
  field_simp
  push_cast
  ring

/-- **The curvature of the theta line**: `∂bar A = -πk / Im τ`. The curvature form is
`∂bar A d(conj z) ∧ dz`, which in the coordinates `z = q + τ p` is `-2πik dq ∧ dp`. -/
theorem conjWirtingerDeriv_apply_one_thetaConnectionForm (z : ℂ) :
    conjWirtingerDeriv (thetaConnectionForm k τ) z 1 = -(π * k / τ.im) := by
  have hfun : thetaConnectionForm k τ = (2 * π * I * k / τ.im : ℂ) • fun w : ℂ ↦ (w.im : ℂ) := by
    funext w
    simp only [thetaConnectionForm_def, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, conjWirtingerDeriv_const_smul, smul_apply,
    conjWirtingerDeriv_apply_one_ofReal_im, smul_eq_mul]
  linear_combination (π * k / τ.im : ℂ) * I_sq

end TauCeti
