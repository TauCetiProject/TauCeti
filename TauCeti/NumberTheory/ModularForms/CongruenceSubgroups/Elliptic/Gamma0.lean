/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Basic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
public import TauCeti.NumberTheory.LegendreSymbol.QuadraticCongruence

/-!
# The elliptic points of `Γ₀(N)`

The elliptic points of order two of `Γ₀(N)` correspond to the square roots of `-1` modulo `N`,
and those of order three to the roots of `x² - x + 1` modulo `N`. These are the counts `ε₂` and
`ε₃` of the dimension formulas for `Γ₀(N)`. Orbits and stabilizers are taken for the effective
image of `Γ₀(N)` in `PSL(2, ℝ)`, the group whose quotient is the analytic modular curve.

Every elliptic point lies in the `SL(2, ℤ)`-orbit of `i` or `ρ`. For `γ` with bottom row
`(c, d)`, the point `γ • i` is elliptic for `Γ₀(N)` exactly when `N ∣ c² + d²`, and `γ • ρ` exactly
when `N ∣ c² - c d + d²`. In either case `d` is invertible modulo `N`, and the residue `x = c / d`
is a root of the corresponding polynomial. Left multiplication by `Γ₀(N)` preserves `x`, and so
does right multiplication by the stabilizer of `i` or `ρ` in `SL(2, ℤ)`, because `x` is a root.
Conversely two matrices with the same residue differ on the left by an element of `Γ₀(N)`.
So `x` is a complete invariant of the elliptic orbit.

Substituting `x ↦ -x` turns `x² - x + 1` into the polynomial `x² + x + 1` of the classical count.

## Main results

* `Matrix.SpecialLinearGroup.conj_S_mem_Gamma0_iff`,
  `Matrix.SpecialLinearGroup.conj_T_inv_mul_S_mem_Gamma0_iff`: the congruence conditions for the
  conjugated elliptic generators.
* `TauCeti.gamma0OrderTwoEllipticEquiv`: the orbits of `Γ₀(N)` with stabilizer of order two
  are in bijection with the roots of `x² + 1` in `ZMod N`.
* `TauCeti.gamma0OrderThreeEllipticEquiv`: the orbits of `Γ₀(N)` with stabilizer of order three
  are in bijection with the roots of `x² - x + 1` in `ZMod N`.
* `TauCeti.card_orderTwoElliptic_Gamma0`, `TauCeti.card_orderThreeElliptic_Gamma0`: the
  resulting counts `ε₂` and `ε₃`.
* `TauCeti.card_orderTwoElliptic_Gamma0_eq_prod`, `TauCeti.card_orderThreeElliptic_Gamma0_eq_prod`:
  the closed forms `ε₂ = ∏_{p ∣ N} (1 + χ₄(p))` unless `4 ∣ N`, and
  `ε₃ = ∏_{p ∣ N} (1 + (p | 3))` unless `9 ∣ N`, in which cases the count is `0`. Here `χ₄` is
  the character of `ℤ/4ℤ`, so `χ₄(p) = (-1 | p)` for odd `p` and `χ₄(2) = 0`, and `(p | 3)` is the
  Kronecker symbol `(-3 | p)` at every prime `p`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §3.7.
* G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §1.6,
  Proposition 1.43.
-/

public section

open Matrix Matrix.SpecialLinearGroup MulAction UpperHalfPlane ModularGroup CongruenceSubgroup
open scoped MatrixGroups

namespace TauCeti

variable {N : ℕ}

/-- The conjugate `γ S γ⁻¹` lies in `Γ₀(N)` exactly when `N ∣ c² + d²`, for `(c, d)` the bottom
row of `γ`. -/
theorem _root_.Matrix.SpecialLinearGroup.conj_S_mem_Gamma0_iff (γ : SL(2, ℤ)) :
    γ * S * γ⁻¹ ∈ Gamma0 N ↔ (N : ℤ) ∣ γ 1 0 ^ 2 + γ 1 1 ^ 2 := by
  rw [mem_Gamma0_iff_dvd]
  convert Iff.rfl using 2
  simp [coe_mul, coe_inv, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The conjugate `γ (T⁻¹ S) γ⁻¹` lies in `Γ₀(N)` exactly when `N ∣ c² - c d + d²`, for `(c, d)`
the bottom row of `γ`. -/
theorem _root_.Matrix.SpecialLinearGroup.conj_T_inv_mul_S_mem_Gamma0_iff (γ : SL(2, ℤ)) :
    γ * (T⁻¹ * S) * γ⁻¹ ∈ Gamma0 N ↔ (N : ℤ) ∣ γ 1 0 ^ 2 - γ 1 0 * γ 1 1 + γ 1 1 ^ 2 := by
  rw [mem_Gamma0_iff_dvd]
  convert Iff.rfl using 2
  simp [coe_mul, coe_inv, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The bottom row of `γ` is proportional to `(x, 1)` modulo `N`: `c ≡ x d`. -/
private def IsRatio (x : ZMod N) (γ : SL(2, ℤ)) : Prop :=
  ((γ 1 0 : ℤ) : ZMod N) = x * (γ 1 1 : ℤ)

/-- The residue `x` is determined by the matrix: `d` is a unit modulo `N` once `c ≡ x d`. -/
private theorem IsRatio.eq {x y : ZMod N} {γ : SL(2, ℤ)} (hx : IsRatio x γ) (hy : IsRatio y γ) :
    x = y := by
  have hdet := intCast_fin_two_mul_sub_mul_eq_one (R := ZMod N) γ
  unfold IsRatio at hx hy
  rw [hx] at hdet
  have e : x * ((γ 1 1 : ℤ) : ZMod N) = y * (γ 1 1 : ℤ) := hx.symm.trans hy
  linear_combination ((γ 0 0 : ℤ) - (γ 0 1 : ℤ) * x : ZMod N) * e - (x - y) * hdet

/-- Left multiplication by `Γ₀(N)` preserves the residue. -/
private theorem IsRatio.mul_left {x : ZMod N} {g γ : SL(2, ℤ)} (hg : g ∈ Gamma0 N)
    (h : IsRatio x γ) : IsRatio x (g * γ) := by
  have hg0 : ((g 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp hg
  unfold IsRatio at *
  simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul, hg0, h]
  ring

/-- The lower-triangular matrix `[1, 0; x, 1]`, whose residue is `x`. -/
private def lowerRep (x : ZMod N) : SL(2, ℤ) :=
  ⟨!![1, 0; (x.cast : ℤ), 1], by simp [det_fin_two_of]⟩

private theorem isRatio_lowerRep (x : ZMod N) : IsRatio x (lowerRep x) := by
  simp [IsRatio, lowerRep]

/-- Matrices with the same residue give the same `Γ₀(N)`-orbit. -/
private theorem quotientMk_eq_of_isRatio (z₀ : ℍ) {x : ZMod N} {γ γ' : SL(2, ℤ)}
    (h : IsRatio x γ) (h' : IsRatio x γ') :
    (Quotient.mk'' (γ • z₀) : orbitRel.Quotient ((Gamma0 N).map sl2zToPSL2R) ℍ) =
      Quotient.mk'' (γ' • z₀) := by
  refine Quotient.sound' ((Subgroup.orbitRel_map_sl2zToPSL2R_iff _).mpr
    ⟨γ * γ'⁻¹, ?_, by rw [mul_smul, inv_smul_smul]⟩)
  unfold IsRatio at h h'
  rw [Gamma0_mem]
  simp only [coe_mul, coe_inv, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
    Int.cast_add, Int.cast_mul, Int.cast_neg, h, h']
  ring

/-- **The orbit classification, once the local data are known.** If the points `γ • z₀` with
stabilizer order `e` are exactly those whose residue satisfies `P`, if the residue of a root of `P`
is invariant under the stabilizer of `z₀`, and if every point of stabilizer order `e` lies in the
`SL(2, ℤ)`-orbit of `z₀`, then the residue classifies the orbits of stabilizer order `e`. -/
private noncomputable def ellipticEquivOfIsRatio (z₀ : ℍ) (e : ℕ) (P : ZMod N → Prop)
    (hcard : ∀ γ : SL(2, ℤ), Nat.card (stabilizer ((Gamma0 N).map sl2zToPSL2R) (γ • z₀)) = e ↔
      ∃ x, P x ∧ IsRatio x γ)
    (hinv : ∀ x γ s, P x → IsRatio x γ → s • z₀ = z₀ → IsRatio x (γ * s))
    (horbit : ∀ z : ℍ, Nat.card (stabilizer ((Gamma0 N).map sl2zToPSL2R) z) = e →
      ∃ γ : SL(2, ℤ), γ • z₀ = z) :
    {x : ZMod N // P x} ≃
      {q : orbitRel.Quotient ((Gamma0 N).map sl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = e} :=
  Equiv.ofBijective
    (fun x ↦ ⟨Quotient.mk'' (lowerRep x.1 • z₀), by
      rw [cardStabilizerOnOrbit_mk]
      exact (hcard _).mpr ⟨x.1, x.2, isRatio_lowerRep x.1⟩⟩)
    ⟨fun x y hxy ↦ by
      obtain ⟨g, hg, hgz⟩ := (Subgroup.orbitRel_map_sl2zToPSL2R_iff _).mp
        (Quotient.exact' (congrArg Subtype.val hxy))
      -- `s` fixes `z₀`, and transports the residue of `y` to the representative of `x`
      set s := (lowerRep x.1)⁻¹ * g * lowerRep y.1
      have hs : s⁻¹ • z₀ = z₀ := by
        rw [inv_smul_eq_iff, mul_smul, mul_smul, hgz, inv_smul_smul]
      have hrep : g * lowerRep y.1 * s⁻¹ = lowerRep x.1 := by
        simp only [s]
        group
      have h := hinv y.1 _ s⁻¹ y.2 ((isRatio_lowerRep y.1).mul_left hg) hs
      rw [hrep] at h
      exact Subtype.ext ((isRatio_lowerRep x.1).eq h),
    fun ⟨q, hq⟩ ↦ by
      induction q using Quotient.inductionOn' with
      | h z =>
        rw [cardStabilizerOnOrbit_mk] at hq
        obtain ⟨γ, rfl⟩ := horbit z hq
        obtain ⟨x, hx, hγ⟩ := (hcard γ).mp hq
        exact ⟨⟨x, hx⟩, Subtype.ext (quotientMk_eq_of_isRatio z₀ (isRatio_lowerRep x) hγ)⟩⟩

/-- Right multiplication by the stabilizer of `i` preserves a residue `x` with `x² + 1 = 0`. -/
private theorem IsRatio.mul_of_smul_I {x : ZMod N} (hx : x ^ 2 + 1 = 0) {γ s : SL(2, ℤ)}
    (h : IsRatio x γ) (hs : s • I = I) : IsRatio x (γ * s) := by
  have hmem := stabilizer_I.mp hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  unfold IsRatio at *
  rcases hmem with rfl | rfl | rfl | rfl <;>
    simp [coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> grind

/-- Right multiplication by the stabilizer of `ρ` preserves a residue `x` with
`x² - x + 1 = 0`. -/
private theorem IsRatio.mul_of_smul_ρ {x : ZMod N} (hx : x ^ 2 - x + 1 = 0) {γ s : SL(2, ℤ)}
    (h : IsRatio x γ) (hs : s • ρ = ρ) : IsRatio x (γ * s) := by
  have hmem := stabilizer_ρ.mp hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  unfold IsRatio at *
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> grind

/-- The point `γ • i` is elliptic for `Γ₀(N)` exactly when the bottom row of `γ` has a residue
that is a square root of `-1`. -/
private theorem card_stabilizer_smul_I_eq_two_iff (γ : SL(2, ℤ)) :
    Nat.card (stabilizer ((Gamma0 N).map sl2zToPSL2R) (γ • I)) = 2 ↔
      ∃ x : ZMod N, x ^ 2 + 1 = 0 ∧ IsRatio x γ := by
  have key : Nat.card (stabilizer ((Gamma0 N).map sl2zToPSL2R) (γ • I)) = 2 ↔
      γ * S * γ⁻¹ ∈ Gamma0 N := by
    rw [Subgroup.card_stabilizer_map_smul_I]
    split_ifs with h <;> simp [h]
  rw [key, conj_S_mem_Gamma0_iff, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hdet := intCast_fin_two_mul_sub_mul_eq_one (R := ZMod N) γ
  unfold IsRatio
  set a : ZMod N := ((γ 0 0 : ℤ) : ZMod N)
  set b : ZMod N := ((γ 0 1 : ℤ) : ZMod N)
  set c : ZMod N := ((γ 1 0 : ℤ) : ZMod N)
  set d : ZMod N := ((γ 1 1 : ℤ) : ZMod N)
  constructor
  · intro h
    -- `u` inverts `d`, so the residue is `c u`
    set u := a - a * b * c - b ^ 2 * d
    have hu : d * u = 1 := by linear_combination (1 - b * c) * hdet - b ^ 2 * h
    exact ⟨c * u, by linear_combination u ^ 2 * h - (d * u + 1) * hu,
      by linear_combination (-c) * hu⟩
  · rintro ⟨x, hx, hc⟩
    linear_combination (c + x * d) * hc + d ^ 2 * hx

/-- The point `γ • ρ` is elliptic for `Γ₀(N)` exactly when the bottom row of `γ` has a residue
that is a root of `x² - x + 1`. -/
private theorem card_stabilizer_smul_ρ_eq_three_iff (γ : SL(2, ℤ)) :
    Nat.card (stabilizer ((Gamma0 N).map sl2zToPSL2R) (γ • ρ)) = 3 ↔
      ∃ x : ZMod N, x ^ 2 - x + 1 = 0 ∧ IsRatio x γ := by
  have key : Nat.card (stabilizer ((Gamma0 N).map sl2zToPSL2R) (γ • ρ)) = 3 ↔
      γ * (T⁻¹ * S) * γ⁻¹ ∈ Gamma0 N := by
    rw [Subgroup.card_stabilizer_map_smul_ρ]
    split_ifs with h <;> simp [h]
  rw [key, conj_T_inv_mul_S_mem_Gamma0_iff, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  have hdet := intCast_fin_two_mul_sub_mul_eq_one (R := ZMod N) γ
  unfold IsRatio
  set a : ZMod N := ((γ 0 0 : ℤ) : ZMod N)
  set b : ZMod N := ((γ 0 1 : ℤ) : ZMod N)
  set c : ZMod N := ((γ 1 0 : ℤ) : ZMod N)
  set d : ZMod N := ((γ 1 1 : ℤ) : ZMod N)
  constructor
  · intro h
    -- `u` inverts `d`, so the residue is `c u`
    set u := a - a * b * c + b ^ 2 * c - b ^ 2 * d
    have hu : d * u = 1 := by linear_combination (1 - b * c) * hdet - b ^ 2 * h
    exact ⟨c * u, by linear_combination u ^ 2 * h + (c * u - d * u - 1) * hu,
      by linear_combination (-c) * hu⟩
  · rintro ⟨x, hx, hc⟩
    linear_combination (c + x * d - d) * hc + d ^ 2 * hx

variable (N) in
/-- **The elliptic points of order two of `Γ₀(N)`.** The orbits of the effective image of `Γ₀(N)`
on `ℍ` whose stabilizer has order `2` are in bijection with the square roots of `-1` in
`ZMod N`. The root `x` corresponds to the orbit of `γ • i` for any `γ` with bottom row `(c, d)`
satisfying `c ≡ x d` (`gamma0OrderTwoEllipticEquiv_apply`). -/
noncomputable def gamma0OrderTwoEllipticEquiv :
    {x : ZMod N // x ^ 2 + 1 = 0} ≃
      {q : orbitRel.Quotient ((Gamma0 N).map sl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 2} :=
  ellipticEquivOfIsRatio I 2 _ card_stabilizer_smul_I_eq_two_iff
    (fun _ _ _ hx h hs ↦ h.mul_of_smul_I hx hs) fun z hz ↦ by
      rcases (Gamma0 N).exists_smul_eq_of_card_stabilizer_ne_one (z := z) (by omega) with
        ⟨γ, hγ, -⟩ | ⟨γ, -, h3⟩
      exacts [⟨γ, hγ⟩, absurd (h3.symm.trans hz) (by decide)]

/-- The orbit attached to a square root `x` of `-1` modulo `N` is that of `γ • i`, for any `γ`
whose bottom row `(c, d)` satisfies `c ≡ x d` modulo `N`. -/
theorem gamma0OrderTwoEllipticEquiv_apply (x : {x : ZMod N // x ^ 2 + 1 = 0}) (γ : SL(2, ℤ))
    (hγ : ((γ 1 0 : ℤ) : ZMod N) = x.1 * (γ 1 1 : ℤ)) :
    (gamma0OrderTwoEllipticEquiv N x : orbitRel.Quotient ((Gamma0 N).map sl2zToPSL2R) ℍ) =
      Quotient.mk'' (γ • I) :=
  quotientMk_eq_of_isRatio I (isRatio_lowerRep x.1) hγ

variable (N) in
/-- **The elliptic points of order three of `Γ₀(N)`.** The orbits of the effective image of
`Γ₀(N)` on `ℍ` whose stabilizer has order `3` are in bijection with the roots of `x² - x + 1` in
`ZMod N`. The root `x` corresponds to the orbit of `γ • ρ` for any `γ` with bottom row `(c, d)`
satisfying `c ≡ x d` (`gamma0OrderThreeEllipticEquiv_apply`). -/
noncomputable def gamma0OrderThreeEllipticEquiv :
    {x : ZMod N // x ^ 2 - x + 1 = 0} ≃
      {q : orbitRel.Quotient ((Gamma0 N).map sl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 3} :=
  ellipticEquivOfIsRatio ρ 3 _ card_stabilizer_smul_ρ_eq_three_iff
    (fun _ _ _ hx h hs ↦ h.mul_of_smul_ρ hx hs) fun z hz ↦ by
      rcases (Gamma0 N).exists_smul_eq_of_card_stabilizer_ne_one (z := z) (by omega) with
        ⟨γ, -, h2⟩ | ⟨γ, hγ, -⟩
      exacts [absurd (h2.symm.trans hz) (by decide), ⟨γ, hγ⟩]

/-- The orbit attached to a root `x` of `x² - x + 1` modulo `N` is that of `γ • ρ`, for any `γ`
whose bottom row `(c, d)` satisfies `c ≡ x d` modulo `N`. -/
theorem gamma0OrderThreeEllipticEquiv_apply (x : {x : ZMod N // x ^ 2 - x + 1 = 0})
    (γ : SL(2, ℤ)) (hγ : ((γ 1 0 : ℤ) : ZMod N) = x.1 * (γ 1 1 : ℤ)) :
    (gamma0OrderThreeEllipticEquiv N x : orbitRel.Quotient ((Gamma0 N).map sl2zToPSL2R) ℍ) =
      Quotient.mk'' (γ • ρ) :=
  quotientMk_eq_of_isRatio ρ (isRatio_lowerRep x.1) hγ

variable (N) in
/-- **The count `ε₂(Γ₀(N))`**: the number of elliptic points of order two of `Γ₀(N)` is the number
of square roots of `-1` modulo `N`. -/
theorem card_orderTwoElliptic_Gamma0 :
    Nat.card {q : orbitRel.Quotient ((Gamma0 N).map sl2zToPSL2R) ℍ //
      cardStabilizerOnOrbit q = 2} = Nat.card {x : ZMod N // x ^ 2 + 1 = 0} :=
  (Nat.card_congr (gamma0OrderTwoEllipticEquiv N)).symm

variable (N) in
/-- **The count `ε₃(Γ₀(N))`**: the number of elliptic points of order three of `Γ₀(N)` is the
number of roots of `x² - x + 1` modulo `N`. -/
theorem card_orderThreeElliptic_Gamma0 :
    Nat.card {q : orbitRel.Quotient ((Gamma0 N).map sl2zToPSL2R) ℍ //
      cardStabilizerOnOrbit q = 3} = Nat.card {x : ZMod N // x ^ 2 - x + 1 = 0} :=
  (Nat.card_congr (gamma0OrderThreeEllipticEquiv N)).symm

variable (N) in
/-- **The closed form of `ε₂(Γ₀(N))`.** The number of elliptic points of order two of `Γ₀(N)` is
`0` if `4 ∣ N`, and otherwise `∏_{p ∣ N} (1 + χ₄(p))`, where `χ₄(p) = (-1 | p)` for odd `p` and
`χ₄(2) = 0`. -/
theorem card_orderTwoElliptic_Gamma0_eq_prod :
    (Nat.card {q : orbitRel.Quotient ((Gamma0 N).map sl2zToPSL2R) ℍ //
      cardStabilizerOnOrbit q = 2} : ℤ) =
      if 4 ∣ N then 0 else ∏ p ∈ N.primeFactors, (1 + ZMod.χ₄ p) := by
  rw [card_orderTwoElliptic_Gamma0, ZMod.natCard_sq_add_one_eq_zero]

variable (N) in
/-- **The closed form of `ε₃(Γ₀(N))`.** The number of elliptic points of order three of `Γ₀(N)` is
`0` if `9 ∣ N`, and otherwise `∏_{p ∣ N} (1 + (p | 3))`, where `(p | 3)` is the Kronecker symbol
`(-3 | p)` at every prime `p`, including `p = 2`. -/
theorem card_orderThreeElliptic_Gamma0_eq_prod :
    (Nat.card {q : orbitRel.Quotient ((Gamma0 N).map sl2zToPSL2R) ℍ //
      cardStabilizerOnOrbit q = 3} : ℤ) =
      if 9 ∣ N then 0 else ∏ p ∈ N.primeFactors, (1 + legendreSym 3 p) := by
  rw [card_orderThreeElliptic_Gamma0, ZMod.natCard_sq_sub_self_add_one_eq_zero]

/-! At the prime level `13 ≡ 1 (mod 12)`, both `-1` and `-3` are squares, so `Γ₀(13)` has two
elliptic points of each order. -/

example : (Nat.card {q : orbitRel.Quotient ((Gamma0 13).map sl2zToPSL2R) ℍ //
    cardStabilizerOnOrbit q = 2} : ℤ) = 2 := by
  rw [card_orderTwoElliptic_Gamma0_eq_prod, Nat.Prime.primeFactors (by decide)]
  decide

example : (Nat.card {q : orbitRel.Quotient ((Gamma0 13).map sl2zToPSL2R) ℍ //
    cardStabilizerOnOrbit q = 3} : ℤ) = 2 := by
  rw [card_orderThreeElliptic_Gamma0_eq_prod, Nat.Prime.primeFactors (by decide),
    Finset.prod_singleton, Nat.cast_ofNat, legendreSym.mod]
  norm_num

end TauCeti
