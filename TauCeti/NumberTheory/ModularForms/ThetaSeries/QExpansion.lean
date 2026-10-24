/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Shell
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Cusp
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# The `q`-expansions of theta series

Let `L` be a discrete subgroup of a finite-dimensional real normed space `E` and `γ : E`. Grouping
the terms of the theta series `θ_{γ+L}(τ) = ∑_{v ∈ L} exp (π i ‖γ + v‖² τ)` by the squared norm
`‖γ + v‖²` writes it as a power series in a `q`-parameter, with the representation numbers
`r_{γ+L}(t) = #{v ∈ L | ‖γ + v‖² = t}` (`ZLattice.cosetRepresentationNumber`) as coefficients.
This needs the squared norms to lie in a discrete progression: if `h ‖γ + v‖² ∈ 2ℤ` for every
`v ∈ L`, for some `h > 0`, then with `q_h = exp (2 π i τ / h)`
`θ_{γ+L}(τ) = ∑_{m ≥ 0} r_{γ+L}(2m / h) q_h^m`,
since the term of `v` is `q_h^m` for `m = h ‖γ + v‖² / 2`, and the vectors with a given `m` form
the finite shell of squared norm `2m / h`. By uniqueness of `q`-expansion coefficients, the
coefficients of `qExpansion h (θ_{γ+L})` are these representation numbers.

The three cases of interest are the following.

* For an **even** lattice `L` (`h = 1`), in `q = exp (2 π i τ)`,
  `Θ_L(τ) = ∑_{m ≥ 0} r_L(2m) q^m`: the `m`-th coefficient counts the vectors of half-norm `m`.
  This is the expansion compared with the `q`-expansions of `E₄`, `Δ` and the other level-one
  modular forms.
* For an **integral** lattice `L` (`h = 2`), in `q^{1/2} = exp (π i τ)`,
  `Θ_L(τ) = ∑_{m ≥ 0} r_L(m) q^{m/2}`, the shape of the expansion of `jacobiTheta`.
* For an even lattice `L`, `γ ∈ L^∨` and a positive integer `N` with `N ‖γ‖² / 2 ∈ ℤ` (`h = N`;
  when `L` is a full lattice, the level of `L` is such an `N` for every `γ ∈ L^∨`), in
  `q_N = exp (2 π i τ / N)`, `θ_{γ+L}(τ) = ∑_{m ≥ 0} r_{γ+L}(2m / N) q_N^m`. The coefficient
  of `q_N^m` vanishes unless `m ≡ N ‖γ‖² / 2 (mod N)`, because `‖γ + v‖² ≡ ‖γ‖² (mod 2)` for
  `v ∈ L` (`ZLattice.IsEven.cosetShell_eq_empty`). This support condition is what boundedness
  of coset theta series at the cusps is read off from.

## Main statements

* `ZLattice.hasSum_thetaCoset_qParam`, `ZLattice.qExpansion_thetaCoset_coeff`: the expansion
  of `θ_{γ+L}` in `q_h` when `h ‖γ + v‖² ∈ 2ℤ` for all `v ∈ L`, and its coefficients.
* `ZLattice.IsEven.hasSum_thetaSeries_qParam`, `ZLattice.IsEven.qExpansion_thetaSeries_coeff`:
  `Θ_L = ∑ r_L(2m) q^m` for even `L`.
* `ZLattice.IsIntegral.hasSum_thetaSeries_qParam_two`,
  `ZLattice.IsIntegral.qExpansion_two_thetaSeries_coeff`: `Θ_L = ∑ r_L(m) q^{m/2}` for integral
  `L`.
* `ZLattice.IsEven.hasSum_thetaCoset_qParam`, `ZLattice.IsEven.qExpansion_thetaCoset_coeff`:
  `θ_{γ+L} = ∑ r_{γ+L}(2m / N) q_N^m` for even `L` and `γ ∈ L^∨`.
* `ZLattice.IsEven.qExpansion_thetaCoset_coeff_eq_zero`: that coefficient vanishes unless
  `m ≡ N ‖γ‖² / 2 (mod N)`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 3.
-/

public section

open Complex Function
open UpperHalfPlane (qExpansion ofComplex)
open scoped Real UpperHalfPlane

namespace ZLattice

section Normed

variable {E : Type*} [NormedAddCommGroup E] {L : Submodule ℤ E} {γ : E} {h : ℝ}

/-- If `h ‖γ + v‖² = 2 m` with `m ∈ ℕ`, the term `exp (π i ‖γ + v‖² τ)` of the theta series is
`q_h ^ m` with `q_h = exp (2 π i τ / h)`. -/
private theorem cexp_pi_mul_I_mul_eq_qParam_pow (hh : 0 < h) {v : E} {m : ℕ}
    (hm : h * ‖γ + v‖ ^ 2 = 2 * m) (τ : ℍ) :
    cexp (π * I * (‖γ + v‖ ^ 2 : ℝ) * τ) = Periodic.qParam h τ ^ m := by
  rw [Periodic.qParam, ← exp_nat_mul]
  congr 1
  have hv : (‖γ + v‖ ^ 2 : ℝ) = 2 * m / h := by
    rw [eq_div_iff hh.ne']
    linarith
  have hh' : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
  rw [hv]
  push_cast
  field_simp

/-- The squared norms of an even lattice satisfy the hypothesis of the expansion in
`q = exp (2 π i τ)`. -/
private theorem IsEven.one_mul_norm_zero_add_sq_eq (hL : IsEven L) {v : E} (hv : v ∈ L) :
    ∃ m : ℤ, 1 * ‖0 + v‖ ^ 2 = 2 * m := by
  obtain ⟨m, hm⟩ := isEven_iff.mp hL v hv
  exact ⟨m, by rw [zero_add, one_mul, hm]⟩

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L]

/-- **The `q`-expansion of a coset theta series.** If `h ‖γ + v‖² ∈ 2ℤ` for every `v ∈ L`, with
`h > 0`, then `θ_{γ+L}(τ) = ∑_{m ≥ 0} r_{γ+L}(2m / h) q_h^m` with `q_h = exp (2 π i τ / h)`. -/
theorem hasSum_thetaCoset_qParam (hh : 0 < h)
    (hnorm : ∀ v ∈ L, ∃ m : ℤ, h * ‖γ + v‖ ^ 2 = 2 * m) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (cosetRepresentationNumber L γ (2 * m / h) : ℂ) •
      Periodic.qParam h τ ^ m) (thetaCoset L γ τ) := by
  -- The term of index `v` is `q_h ^ g v`, where `g v = h ‖γ + v‖² / 2 ∈ ℕ`.
  let g : L → ℕ := fun v ↦ ⌊h * ‖γ + (v : E)‖ ^ 2 / 2⌋₊
  have hg (v : L) : h * ‖γ + (v : E)‖ ^ 2 = 2 * g v := by
    obtain ⟨m, hm⟩ := hnorm v v.2
    have hm0 : 0 ≤ m := by
      have : (0 : ℝ) ≤ 2 * m := hm ▸ by positivity
      exact_mod_cast (by linarith : (0 : ℝ) ≤ m)
    lift m to ℕ using hm0
    have : g v = m := by
      simp only [g, hm]
      push_cast
      rw [mul_div_cancel_left₀ _ two_ne_zero, Nat.floor_natCast]
    rw [this, hm]
    norm_cast
  -- Group the terms by the value of `g`; the fibre of `g` over `m` is the shell of `2m / h`.
  have hfib (m : ℕ) : Subtype.val '' (g ⁻¹' {m}) = cosetShell L γ (2 * m / h) := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff, mem_cosetShell]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.2, ?_⟩
      rw [eq_div_iff hh.ne', mul_comm, hg v, hv]
    · rintro ⟨hx, hxt⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      have h2 : (2 : ℝ) * g ⟨x, hx⟩ = 2 * m := by
        rw [← hg, hxt, mul_div_cancel₀ _ hh.ne']
      exact_mod_cast (mul_right_injective₀ (two_ne_zero : (2 : ℝ) ≠ 0) h2 :)
  rw [thetaCoset_apply]
  refine ((summable_thetaCoset L γ τ).hasSum.tsum_fiberwise g).congr_fun fun m ↦ ?_
  rw [tsum_congr (fun v : g ⁻¹' {m} ↦ ?_), tsum_const, cosetRepresentationNumber_def,
    ← hfib, Set.ncard_image_of_injective _ Subtype.val_injective, Nat.card_coe_set_eq,
    ← Nat.cast_smul_eq_nsmul ℂ]
  rw [cexp_pi_mul_I_mul_eq_qParam_pow hh (hg v) τ, show g v = m from v.2]

/-- The coefficients of the `q`-expansion of a coset theta series: if `h ‖γ + v‖² ∈ 2ℤ` for every
`v ∈ L`, with `h > 0`, the `m`-th coefficient of the expansion of `θ_{γ+L}` in
`q_h = exp (2 π i τ / h)` is `r_{γ+L}(2m / h)`. -/
theorem qExpansion_thetaCoset_coeff (hh : 0 < h)
    (hnorm : ∀ v ∈ L, ∃ m : ℤ, h * ‖γ + v‖ ^ 2 = 2 * m) (m : ℕ) :
    (qExpansion h (thetaCoset L γ)).coeff m = cosetRepresentationNumber L γ (2 * m / h) :=
  (TauCeti.UpperHalfPlane.qExpansion_coeff_unique hh
    (UpperHalfPlane.analyticAt_cuspFunction_zero hh
      (UpperHalfPlane.periodic_comp_ofComplex (thetaCoset_vadd_eq_self L γ hnorm))
      (mdifferentiable_thetaCoset L γ) (isBoundedAtImInfty_thetaCoset L γ))
    (hasSum_thetaCoset_qParam hh hnorm) m).symm

/-! ### Even lattices -/

namespace IsEven

/-- The `q`-expansion of the theta series of an even lattice: in `q = exp (2 π i τ)`,
`Θ_L(τ) = ∑_{m ≥ 0} r_L(2m) q^m`, where `r_L(2m)` is the number of vectors of half-norm `m`. -/
theorem hasSum_thetaSeries_qParam (hL : IsEven L) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (representationNumber L (2 * m) : ℂ) • Periodic.qParam 1 τ ^ m)
      (thetaSeries L τ) := by
  have := hasSum_thetaCoset_qParam one_pos (fun _ hv ↦ hL.one_mul_norm_zero_add_sq_eq hv) τ
  simp_rw [thetaCoset_zero, cosetRepresentationNumber_zero_left, div_one] at this
  exact this

/-- The coefficients of the `q`-expansion of the theta series of an even lattice: the `m`-th
coefficient in `q = exp (2 π i τ)` is the number `r_L(2m)` of vectors of half-norm `m`. -/
theorem qExpansion_thetaSeries_coeff (hL : IsEven L) (m : ℕ) :
    (qExpansion 1 (thetaSeries L)).coeff m = representationNumber L (2 * m) := by
  rw [← thetaCoset_zero,
    qExpansion_thetaCoset_coeff one_pos (fun _ hv ↦ hL.one_mul_norm_zero_add_sq_eq hv) m,
    cosetRepresentationNumber_zero_left, div_one]

end IsEven

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {L : Submodule ℤ E} {γ : E}

/-- The squared norms of an integral lattice are integers, which is the hypothesis of the
expansion in `q^{1/2} = exp (π i τ)`. -/
private theorem IsIntegral.two_mul_norm_zero_add_sq_eq (hL : IsIntegral L) {v : E} (hv : v ∈ L) :
    ∃ m : ℤ, 2 * ‖0 + v‖ ^ 2 = 2 * m := by
  obtain ⟨m, hm⟩ := isIntegral_iff.mp hL v hv v hv
  exact ⟨m, by rw [zero_add, ← real_inner_self_eq_norm_sq, hm]⟩

/-- For an even lattice `L`, `γ ∈ L^∨` and `N ‖γ‖² = 2 n`, the squared norms on the coset satisfy
`N ‖γ + v‖² ∈ 2n + 2Nℤ`. -/
private theorem IsEven.natCast_mul_norm_add_sq_eq (hL : IsEven L) (hγ : γ ∈ dual L) {N : ℕ}
    (hNγ : ∃ n : ℤ, N * ‖γ‖ ^ 2 = 2 * n) {v : E} (hv : v ∈ L) :
    ∃ m : ℤ, (N : ℝ) * ‖γ + v‖ ^ 2 = 2 * m := by
  obtain ⟨n, hn⟩ := hNγ
  obtain ⟨j, hj⟩ := hL.exists_norm_add_sq_sub_norm_sq_eq hγ hv
  exact ⟨n + N * j, by push_cast; linear_combination (N : ℝ) * hj + hn⟩

variable [FiniteDimensional ℝ E] [DiscreteTopology L]

/-! ### Integral lattices -/

namespace IsIntegral

/-- The `q`-expansion of the theta series of an integral lattice, with period `2`: in
`q^{1/2} = exp (π i τ)`, `Θ_L(τ) = ∑_{m ≥ 0} r_L(m) q^{m/2}`. -/
theorem hasSum_thetaSeries_qParam_two (hL : IsIntegral L) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (representationNumber L m : ℂ) • Periodic.qParam 2 τ ^ m)
      (thetaSeries L τ) := by
  have := hasSum_thetaCoset_qParam two_pos (fun _ hv ↦ hL.two_mul_norm_zero_add_sq_eq hv) τ
  simp_rw [thetaCoset_zero, cosetRepresentationNumber_zero_left,
    mul_div_cancel_left₀ _ (two_ne_zero (α := ℝ))] at this
  exact this

/-- The coefficients of the `q`-expansion with period `2` of the theta series of an integral
lattice: the `m`-th coefficient in `q^{1/2} = exp (π i τ)` is the number `r_L(m)` of vectors of
squared norm `m`. -/
theorem qExpansion_two_thetaSeries_coeff (hL : IsIntegral L) (m : ℕ) :
    (qExpansion 2 (thetaSeries L)).coeff m = representationNumber L m := by
  rw [← thetaCoset_zero,
    qExpansion_thetaCoset_coeff two_pos (fun _ hv ↦ hL.two_mul_norm_zero_add_sq_eq hv) m,
    cosetRepresentationNumber_zero_left, mul_div_cancel_left₀ _ (two_ne_zero (α := ℝ))]

end IsIntegral

/-! ### Coset theta series of even lattices -/

namespace IsEven

/-- The `q_N`-expansion of a coset theta series of an even lattice: for `γ ∈ L^∨` and a positive
integer `N` with `N ‖γ‖² / 2 ∈ ℤ`, in `q_N = exp (2 π i τ / N)`,
`θ_{γ+L}(τ) = ∑_{m ≥ 0} r_{γ+L}(2m / N) q_N^m`. -/
theorem hasSum_thetaCoset_qParam (hL : IsEven L) (hγ : γ ∈ dual L) {N : ℕ} (hN : 0 < N)
    (hNγ : ∃ n : ℤ, N * ‖γ‖ ^ 2 = 2 * n) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (cosetRepresentationNumber L γ (2 * m / N) : ℂ) •
      Periodic.qParam N τ ^ m) (thetaCoset L γ τ) :=
  ZLattice.hasSum_thetaCoset_qParam (Nat.cast_pos.mpr hN)
    (fun _ hv ↦ hL.natCast_mul_norm_add_sq_eq hγ hNγ hv) τ

/-- The coefficients of the `q_N`-expansion of a coset theta series of an even lattice: for
`γ ∈ L^∨` and a positive integer `N` with `N ‖γ‖² / 2 ∈ ℤ`, the `m`-th coefficient in
`q_N = exp (2 π i τ / N)` is `r_{γ+L}(2m / N)`. -/
theorem qExpansion_thetaCoset_coeff (hL : IsEven L) (hγ : γ ∈ dual L) {N : ℕ} (hN : 0 < N)
    (hNγ : ∃ n : ℤ, N * ‖γ‖ ^ 2 = 2 * n) (m : ℕ) :
    (qExpansion N (thetaCoset L γ)).coeff m = cosetRepresentationNumber L γ (2 * m / N) :=
  ZLattice.qExpansion_thetaCoset_coeff (Nat.cast_pos.mpr hN)
    (fun _ hv ↦ hL.natCast_mul_norm_add_sq_eq hγ hNγ hv) m

/-- **The support of the `q_N`-expansion of a coset theta series.** For an even lattice `L`,
`γ ∈ L^∨` and a positive integer `N` with `N ‖γ‖² = 2 n`, the coefficient of `q_N^m` in the
expansion of `θ_{γ+L}` vanishes unless `m ≡ n (mod N)`, that is, unless `m / N` is congruent to
`‖γ‖² / 2` modulo `ℤ`. -/
theorem qExpansion_thetaCoset_coeff_eq_zero (hL : IsEven L) (hγ : γ ∈ dual L) {N : ℕ}
    (hN : 0 < N) {n : ℤ} (hn : N * ‖γ‖ ^ 2 = 2 * n) {m : ℕ} (hm : ¬ (m : ℤ) ≡ n [ZMOD N]) :
    (qExpansion N (thetaCoset L γ)).coeff m = 0 := by
  rw [hL.qExpansion_thetaCoset_coeff hγ hN ⟨n, hn⟩, Nat.cast_eq_zero]
  refine hL.cosetRepresentationNumber_eq_zero hγ ?_
  rintro ⟨j, hj⟩
  -- `2m / N = ‖γ‖² + 2j` gives `m = n + N j`.
  rw [div_eq_iff (Nat.cast_ne_zero.mpr hN.ne')] at hj
  have h2 : ((m : ℤ) : ℝ) = ((n + N * j : ℤ) : ℝ) := by
    push_cast
    linear_combination hj / 2 + hn / 2
  exact hm (Int.modEq_iff_dvd.mpr ⟨j, by linarith [Int.cast_injective h2]⟩).symm

end IsEven

end InnerProduct

end ZLattice
