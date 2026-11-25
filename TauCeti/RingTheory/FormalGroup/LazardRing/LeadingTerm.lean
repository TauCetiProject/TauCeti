/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Order
public import TauCeti.RingTheory.FormalGroup.LazardRing.Polynomial

/-!
# Leading terms of the Lazard coordinates

By Lazard's theorem a commutative formal group law over `R` is determined by its Lazard
coordinates, the values `vₙ` of the generators `xₙ = TauCeti.LazardRing.generator n` of
`L = ℤ[x₁, x₂, …]` (`TauCeti.LazardRing.homEquiv`).

The generator `xₙ` has degree `2n`, the degree of the coefficients of the monomials of total degree
`n + 1`. This file shows that the coordinate `xₙ` first appears in total degree `n + 1`, and there
exactly through the Lazard cocycle `C_{n+1}`: if two commutative formal group laws `F` and `G`
have the same coordinates `x_m` for `m < n`, then `F - G` vanishes below degree `n + 1`, and its
part of degree `n + 1` is `(xₙ(F) - xₙ(G)) C_{n+1}`. Indeed a coefficient of total degree at most
`n` is a polynomial in the `x_m` with `2m` at most its degree, and for `0 < i ≤ n` a coefficient
`a_{i,n+1-i}` is `(n+1).choose i / d_{n+1}` times `xₙ` plus a polynomial in the `x_m`, `m < n`
(`TauCeti.LazardRing.lt_of_mem_vars_mvPolynomialEquiv_symm_sub_smul_X`). For laws agreeing below
degree `n + 1`, `FormalGroup.exists_homogeneousComponent_sub_eq_smul_lazardCocycle` gives the part
of degree `n + 1` of `F - G` as some multiple of `C_{n+1}`; here that multiple is the difference of
the Lazard coordinates.

This is what the generic Lubin–Tate deformation of a formal group law of height `h`
(`FormalGroup.lubinTateLaw`) needs: moving the coordinates `x_{pⁱ - 1}`, `0 < i < h`, by
independent parameters `tᵢ` changes the law by `tᵢ C_{pⁱ}` in degree `pⁱ` and not at all below it.

## Main results

* `TauCeti.LazardRing.succ_le_order_map_sub_map`: if `φ` and `ψ` agree on `x_m` for `m < n`, then
  the base changes of the universal law along them agree below degree `n + 1`.
* `TauCeti.LazardRing.homogeneousComponent_map_sub_map_eq_smul_lazardCocycle`: their difference in
  degree `n + 1` is `(φ xₙ - ψ xₙ) C_{n+1}`.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*, Bull. Soc. Math.
  France 94 (1966), §1.
-/

public section

noncomputable section

open MvPowerSeries

namespace TauCeti.LazardRing

variable {R : Type*} [CommRing R]

/-- Two homomorphisms agreeing on the generators occurring in `mvPolynomialEquiv.symm x` agree on
`x`. -/
private theorem apply_eq_of_vars {φ ψ : LazardRing →+* R} {x : LazardRing}
    (h : ∀ m ∈ (mvPolynomialEquiv.symm x).vars, φ (generator m) = ψ (generator m)) :
    φ x = ψ x := by
  rw [← homEquiv.symm_apply_apply φ, ← homEquiv.symm_apply_apply ψ, homEquiv_symm_apply,
    homEquiv_symm_apply]
  exact MvPolynomial.eval₂Hom_congr' rfl (fun m hm _ ↦ by simpa using h m hm) rfl

variable {φ ψ : LazardRing →+* R} {n : ℕ+}

/-- A coefficient of the universal formal group law of total degree at most `n` is a polynomial in
the generators `x_m`, `m < n`. -/
private theorem lt_of_mem_vars_coeff_formalGroup {d : Fin 2 →₀ ℕ} (hd : d.degree ≤ n) {m : ℕ+}
    (hm : m ∈ (mvPolynomialEquiv.symm (coeff d formalGroup.toPowerSeries)).vars) : m < n := by
  have hhom : (mvPolynomialEquiv.symm (coeff d formalGroup.toPowerSeries)).IsWeightedHomogeneous
      (fun j : ℕ+ ↦ 2 * (j : ℕ)) (2 * (d.degree - 1)) := by
    rw [← mvPolynomialEquiv_mem_grading_iff, AlgEquiv.apply_symm_apply]
    exact coeff_formalGroup_mem_grading d
  obtain ⟨e, he, hme⟩ := (MvPolynomial.mem_vars_iff_mem_support m).1 hm
  have hle := Finsupp.le_weight_of_ne_zero' (w := fun j : ℕ+ ↦ 2 * (j : ℕ))
    (Finsupp.mem_support_iff.1 hme)
  rw [hhom (MvPolynomial.mem_support_iff.1 he)] at hle
  have := m.pos
  exact PNat.coe_lt_coe m n |>.1 (by omega)

/-- If `φ` and `ψ` agree on the generators `x_m`, `m < n`, they agree on the coefficients of the
universal formal group law of total degree at most `n`. -/
private theorem apply_coeff_formalGroup_eq_of_degree_le
    (h : ∀ m < n, φ (generator m) = ψ (generator m)) {d : Fin 2 →₀ ℕ} (hd : d.degree ≤ n) :
    φ (coeff d formalGroup.toPowerSeries) = ψ (coeff d formalGroup.toPowerSeries) :=
  apply_eq_of_vars fun _ hm ↦ h _ (lt_of_mem_vars_coeff_formalGroup hd hm)

/-- If `φ` and `ψ` agree on the generators `x_m`, `m < n`, their values on a coefficient of total
degree `n + 1` of the universal formal group law differ by the corresponding coefficient of
`C_{n+1}` times `φ xₙ - ψ xₙ`. -/
private theorem apply_coeff_formalGroup_sub_of_degree_eq
    (h : ∀ m < n, φ (generator m) = ψ (generator m)) {d : Fin 2 →₀ ℕ}
    (hd : d.degree = n + 1) :
    φ (coeff d formalGroup.toPowerSeries) - ψ (coeff d formalGroup.toPowerSeries) =
      (lazardCocycle (n + 1) R).coeff d * (φ (generator n) - ψ (generator n)) := by
  have hdeg : d 0 + d 1 = n + 1 := by rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd
  by_cases hd0 : d 0 ≠ 0 ∧ d 1 ≠ 0
  · -- `a_{i, n+1-i} = c • xₙ + P` with `P` a polynomial in the `x_m`, `m < n`
    set c : ℕ := (n + 1 : ℕ).choose (d 0) / lazardGcd (n + 1)
    have hdi : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (n + 1 - d 0) := by
      ext j
      fin_cases j <;> simp
      -- `simp` closes `j = 0`; `j = 1` is `d 1 = n + 1 - d 0`
      omega
    have hmem := coeff_formalGroup_sub_nsmul_generator_mem_sq n (i := d 0)
      (Nat.pos_of_ne_zero hd0.1) (by omega)
    rw [← hdi] at hmem
    set y := coeff d formalGroup.toPowerSeries
    have hy : y = (c : ℤ) • generator n + (y - (c : ℤ) • generator n) := by abel
    have hyc : y - (c : ℤ) • generator n ∈ augmentationIdeal ^ 2 := by
      rwa [natCast_zsmul]
    have hrest : φ (y - (c : ℤ) • generator n) = ψ (y - (c : ℤ) • generator n) := by
      refine apply_eq_of_vars fun m hm ↦ h m ?_
      refine lt_of_mem_vars_mvPolynomialEquiv_symm_sub_smul_X ?_ hyc (k := m) ?_
      · convert coeff_formalGroup_mem_grading d using 2
        simp [hd]
      · simpa using hm
    rw [hy, map_add, map_add, hrest, hdi, coeff_single_add_single_lazardCocycle
      (Nat.pos_of_ne_zero hd0.1) (by omega)]
    simp only [zsmul_eq_mul, Int.cast_natCast, map_mul, map_natCast, c]
    ring
  · -- the monomials `X^(n+1)` and `Y^(n+1)` have coefficient zero on both sides
    have hy : coeff d formalGroup.toPowerSeries = 0 := by
      rw [formalGroup_toPowerSeries, coeff_lazardSeries_eq]
      have h1 : d 0 + d 1 ≠ 1 := by have := n.pos; omega
      rw [ite_eq_right hd0, ite_eq_right h1]
    rw [hy, map_zero, map_zero, sub_zero, coeff_lazardCocycle]
    split_ifs with h0
    exacts [absurd h0.2 hd0, (zero_mul _).symm]

/-- **The Lazard coordinate `xₙ` first appears in degree `n + 1`.** If `φ` and `ψ` agree on the
generators `x_m`, `m < n`, then the base changes of the universal formal group law along them
agree below degree `n + 1`. -/
theorem succ_le_order_map_sub_map (h : ∀ m < n, φ (generator m) = ψ (generator m)) :
    ((n + 1 : ℕ) : ℕ∞) ≤
      ((formalGroup.map φ).toPowerSeries - (formalGroup.map ψ).toPowerSeries).order := by
  refine nat_le_order fun d hd ↦ ?_
  simp only [map_sub, FormalGroup.map_toPowerSeries, coeff_map]
  rw [apply_coeff_formalGroup_eq_of_degree_le h (by omega), sub_self]

/-- **The Lazard coordinate `xₙ` enters through `C_{n+1}`.** If `φ` and `ψ` agree on the
generators `x_m`, `m < n`, then in degree `n + 1` the base changes of the universal formal group
law along them differ by `(φ xₙ - ψ xₙ) C_{n+1}`. -/
theorem homogeneousComponent_map_sub_map_eq_smul_lazardCocycle
    (h : ∀ m < n, φ (generator m) = ψ (generator m)) :
    homogeneousComponent (n + 1)
        ((formalGroup.map φ).toPowerSeries - (formalGroup.map ψ).toPowerSeries) =
      ↑((φ (generator n) - ψ (generator n)) • lazardCocycle (n + 1) R) := by
  ext d
  rw [coeff_homogeneousComponent, MvPolynomial.coe_smul, coeff_smul, MvPolynomial.coeff_coe]
  split_ifs with hd
  · simp only [map_sub, FormalGroup.map_toPowerSeries, coeff_map]
    rw [apply_coeff_formalGroup_sub_of_degree_eq h hd, mul_comm]
  · rw [coeff_lazardCocycle]
    split_ifs with hd'
    · exact absurd (by rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, hd'.1]) hd
    · rw [mul_zero]

end TauCeti.LazardRing
