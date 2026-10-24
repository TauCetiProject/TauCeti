/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
public import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import TauCeti.Data.Int.GCD
import TauCeti.Data.ZMod.Units

/-!
# The cusps of `Γ₀(N)`

The number of cusps of `Γ₀(N)` is `ε∞ = ∑_{g ∣ N} φ(gcd(g, N / g))`, the cusp count in the
dimension formulas for `Γ₀(N)`. Cusps are counted as the cusp orbits of the effective image of
`Γ₀(N)` in `PSL(2, ℝ)`, the boundary orbits adjoined to its analytic quotient.

Every cusp is `γ • ∞` for some `γ ∈ SL(2, ℤ)`. For `γ` and `γ'` with bottom rows `(c, d)` and
`(c', d')`, the cusps `γ • ∞` and `γ' • ∞` are `Γ₀(N)`-equivalent exactly when
`N ∣ c d' - c' d + j c c'` for some integer `j`. This congruence is detected by the *label* of
`γ`: the divisor `g = gcd(c, N)` of `N`, together with the residue of `(c / g) / d` modulo
`gcd(g, N / g)`, which is a unit. Every divisor and every unit residue occur, so the cusps of
`Γ₀(N)` are in bijection with the pairs `(g, x)` with `g ∣ N` and
`x ∈ (ℤ / gcd(g, N / g))ˣ`.

## Main definitions

* `TauCeti.gamma0CuspLabel`: the label `(g, x)` of `γ ∈ SL(2, ℤ)`.
* `TauCeti.gamma0CuspOrbitEquiv`: the cusp orbits of `Γ₀(N)` are in bijection with the labels.

## Main results

* `TauCeti.cuspOrbitOfSL2Z_Gamma0_eq_iff`: the congruence criterion for equivalence of cusps.
* `TauCeti.gamma0CuspLabel_eq_iff`: two matrices have the same label exactly when they
  represent the same cusp.
* `TauCeti.card_cuspOrbit_Gamma0`: the cusp count `ε∞ = ∑_{g ∣ N} φ(gcd(g, N / g))`.
* `TauCeti.card_cuspOrbit_Gamma0_of_prime`: `Γ₀(p)` has two cusps.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §3.8.
* G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §1.6,
  Proposition 1.43.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup ModularGroup
open scoped MatrixGroups

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-! ### Equivalence of cusps -/

/-- **The criterion for equivalence of cusps of `Γ₀(N)`.** For `γ` and `γ'` with bottom rows
`(c, d)` and `(c', d')`, the cusps `γ • ∞` and `γ' • ∞` are `Γ₀(N)`-equivalent exactly when
`N ∣ c d' - c' d + j c c'` for some integer `j`. -/
theorem cuspOrbitOfSL2Z_Gamma0_eq_iff (γ γ' : SL(2, ℤ)) :
    (Gamma0 N).cuspOrbitOfSL2Z γ = (Gamma0 N).cuspOrbitOfSL2Z γ' ↔
      ∃ j : ℤ, (N : ℤ) ∣ γ 1 0 * γ' 1 1 - γ' 1 0 * γ 1 1 + j * γ 1 0 * γ' 1 0 := by
  rw [Subgroup.cuspOrbitOfSL2Z_eq_iff]
  constructor
  · rintro ⟨h, hh, hM⟩
    obtain ⟨M, hMdef⟩ : ∃ M, γ⁻¹ * h * γ' = M := ⟨_, rfl⟩
    have hh' : h = γ * M * γ'⁻¹ := by rw [← hMdef]; group
    subst hh'
    rw [hMdef] at hM
    have hdet := M.det_coe
    rw [det_fin_two, hM, mul_zero, sub_zero] at hdet
    rw [mem_Gamma0_iff_dvd] at hh
    simp only [coe_mul, coe_inv, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, of_apply,
      cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, hM] at hh
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · refine ⟨-M 0 1, ?_⟩
      rw [h0, h1] at hh
      convert hh using 1
      ring
    · refine ⟨M 0 1, ?_⟩
      rw [h0, h1] at hh
      convert dvd_neg.mpr hh using 1
      ring
  · rintro ⟨j, hj⟩
    refine ⟨γ * T ^ (-j) * γ'⁻¹, ?_, ?_⟩
    · rw [mem_Gamma0_iff_dvd]
      simp only [coe_mul, coe_inv, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
        of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, coe_T_zpow]
      convert hj using 1
      ring
    · have hT : γ⁻¹ * (γ * T ^ (-j) * γ'⁻¹) * γ' = T ^ (-j) := by group
      rw [hT, coe_T_zpow]
      rfl

/-! ### Labels of cusps -/

variable (N) in
/-- **The label of the cusp `γ • ∞` of `Γ₀(N)`.** For `γ ∈ SL(2, ℤ)` with bottom row `(c, d)`,
it is the divisor `g = gcd(c, N)` of `N` together with the unit `(c / g) / d` modulo
`gcd(g, N / g)`. Matrices representing the same cusp have the same label
(`gamma0CuspLabel_eq_iff`), and `gamma0CuspOrbitEquiv` is the resulting bijection. -/
noncomputable def gamma0CuspLabel (γ : SL(2, ℤ)) :
    Σ g : N.divisors, (ZMod (Nat.gcd g (N / g)))ˣ :=
  ⟨⟨Int.gcd (γ 1 0) N,
      Nat.mem_divisors.mpr ⟨Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right ..), NeZero.ne N⟩⟩,
    ZMod.unitOfIsCoprime (γ 1 0 / Int.gcd (γ 1 0) N) (by
        refine (Int.isCoprime_div_gcd_div_gcd (NeZero.ne N) (γ 1 0)).of_isCoprime_of_dvd_right ?_
        exact Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right ..)) /
      ZMod.unitOfIsCoprime (γ 1 1) ((bottom_row_coprime γ).symm.of_isCoprime_of_dvd_right
        ((Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left ..)).trans (Int.gcd_dvd_left ..)))⟩

/-- The divisor in the label of `γ` is `gcd(c, N)`, for `c` the lower-left entry of `γ`. -/
@[simp]
theorem coe_gamma0CuspLabel_fst (γ : SL(2, ℤ)) :
    ((gamma0CuspLabel N γ).1 : ℕ) = Int.gcd (γ 1 0) N :=
  (rfl)

/-- The residue in the label of `γ` is `(c / g) / d`, for `(c, d)` the bottom row of `γ` and
`g = gcd(c, N)`: its product with `d` is `c / g`. -/
theorem coe_gamma0CuspLabel_snd_mul (γ : SL(2, ℤ)) :
    ((gamma0CuspLabel N γ).2 : ZMod (Nat.gcd (gamma0CuspLabel N γ).1
      (N / (gamma0CuspLabel N γ).1))) * (γ 1 1 : ℤ) = (γ 1 0 / Int.gcd (γ 1 0) N : ℤ) := by
  rw [gamma0CuspLabel]
  dsimp only
  generalize_proofs _ _ hd
  rw [← ZMod.coe_unitOfIsCoprime (γ 1 1) hd, ← Units.val_mul, div_mul_cancel,
    ZMod.coe_unitOfIsCoprime]

/-- Two matrices have the same label exactly when their bottom rows `(c, d)` and `(c', d')`
satisfy `N ∣ c d' - c' d + j c c'` for some integer `j`. -/
theorem gamma0CuspLabel_eq_iff_exists_dvd (γ γ' : SL(2, ℤ)) :
    gamma0CuspLabel N γ = gamma0CuspLabel N γ' ↔
      ∃ j : ℤ, (N : ℤ) ∣ γ 1 0 * γ' 1 1 - γ' 1 0 * γ 1 1 + j * γ 1 0 * γ' 1 0 := by
  have hc (c : ℤ) : c = Int.gcd c N * (c / Int.gcd c N) :=
    (Int.mul_ediv_cancel' (Int.gcd_dvd_left ..)).symm
  have hN : (N : ℤ) = Int.gcd (γ 1 0) N * (N / Int.gcd (γ 1 0) N : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' (Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right ..))).symm
  -- The residues live in `ZMod` of moduli that agree only propositionally, so they are compared
  -- as `HEq`; once the divisors are identified this is `ZMod.unitOfIsCoprime_div_eq_iff`.
  have hx {g g' : ℕ} (hg : g = g') {a b a' b' : ℤ} (ha : IsCoprime a (Nat.gcd g (N / g) : ℤ))
      (hb : IsCoprime b (Nat.gcd g (N / g) : ℤ)) (ha' : IsCoprime a' (Nat.gcd g' (N / g') : ℤ))
      (hb' : IsCoprime b' (Nat.gcd g' (N / g') : ℤ)) :
      HEq (ZMod.unitOfIsCoprime a ha / ZMod.unitOfIsCoprime b hb)
          (ZMod.unitOfIsCoprime a' ha' / ZMod.unitOfIsCoprime b' hb') ↔
        (Nat.gcd g (N / g) : ℤ) ∣ a * b' - a' * b := by
    subst hg
    exact heq_iff_eq.trans (ZMod.unitOfIsCoprime_div_eq_iff ..)
  rw [gamma0CuspLabel, gamma0CuspLabel, Sigma.mk.inj_iff, Subtype.mk.injEq]
  constructor
  · rintro ⟨hg, hx'⟩
    rw [hx hg, ← hg] at hx'
    exact Int.exists_dvd_mul_sub_mul_add_mul_of_gcd_dvd hN (hc _) (hg ▸ hc _)
      (Int.isCoprime_div_gcd_div_gcd (NeZero.ne N) _)
      (hg ▸ Int.isCoprime_div_gcd_div_gcd (NeZero.ne N) _) hx'
  · rintro ⟨j, h⟩
    have hg := Int.gcd_eq_gcd_of_dvd_mul_sub_mul_add_mul (bottom_row_coprime γ)
      (bottom_row_coprime γ') h
    refine ⟨hg, (hx hg ..).mpr ?_⟩
    rw [← hg]
    exact Int.gcd_dvd_mul_sub_mul_of_dvd_mul_sub_mul_add_mul
      (Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast NeZero.ne N)).ne' hN (hc _) (hg ▸ hc _) h

/-- At squarefree level, two cusp labels agree exactly when their denominator gcds agree. -/
theorem gamma0CuspLabel_eq_iff_gcd_eq_of_squarefree (hN : Squarefree N) (γ γ' : SL(2, ℤ)) :
    gamma0CuspLabel N γ = gamma0CuspLabel N γ' ↔
      Int.gcd (γ 1 0) N = Int.gcd (γ' 1 0) N := by
  have hmod (g : N.divisors) : Nat.gcd g.val (N / g.val) = 1 := by
    apply Nat.coprime_iff_gcd_eq_one.mp
    apply Nat.coprime_of_squarefree_mul
    rwa [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors g.property)]
  let : ∀ g : N.divisors, Subsingleton (ZMod (Nat.gcd g.val (N / g.val)))ˣ := fun g ↦ by
    rw [hmod g]
    infer_instance
  constructor
  · intro h
    simpa only [coe_gamma0CuspLabel_fst] using congrArg (fun x ↦ (x.1 : ℕ)) h
  · intro h
    apply Sigma.fst_injective
    exact Subtype.ext (by simpa only [coe_gamma0CuspLabel_fst] using h)

/-- Every divisor `g` of `N` and every unit modulo `gcd(g, N / g)` is a label: that of a matrix
with bottom row `(g, d)`. -/
theorem gamma0CuspLabel_surjective : Function.Surjective (gamma0CuspLabel N) := by
  rintro ⟨⟨g, hg⟩, x⟩
  have hgN : g ∣ N := Nat.dvd_of_mem_divisors hg
  have : NeZero g := ⟨Nat.ne_of_gt (Nat.pos_of_mem_divisors hg)⟩
  obtain ⟨y, hy⟩ := ZMod.unitsMap_surjective (Nat.gcd_dvd_left g (N / g)) x⁻¹
  have hgd : IsCoprime (g : ℤ) ((y : ZMod g).val : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (ZMod.val_coe_unit_coprime y).symm
  have hmem : ![(g : ℤ), ((y : ZMod g).val : ℤ)] ∈
      {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} := hgd
  obtain ⟨γ, -, hγ⟩ := bottom_row_surj hmem
  have hc : γ 1 0 = g := congrFun hγ 0
  have hd : γ 1 1 = ((y : ZMod g).val : ℤ) := congrFun hγ 1
  have hgcd : Int.gcd (γ 1 0) N = g := by
    rw [hc, Int.gcd_natCast_natCast, Nat.gcd_eq_left hgN]
  have h1 : γ 1 0 / Int.gcd (γ 1 0) N = 1 := by
    rw [hgcd, hc]
    exact Int.ediv_self (by exact_mod_cast NeZero.ne g)
  refine ⟨γ, ?_⟩
  subst hgcd
  rw [gamma0CuspLabel]
  refine Sigma.ext rfl (heq_of_eq ?_)
  dsimp only
  rw [div_eq_iff_eq_mul, Units.ext_iff]
  simp only [Units.val_mul, ZMod.coe_unitOfIsCoprime, h1, Int.cast_one]
  rw [hd, Int.cast_natCast, ZMod.natCast_val, ← ZMod.unitsMap_val (Nat.gcd_dvd_left _ _), hy,
    Units.mul_inv]

/-- Two matrices have the same label exactly when they represent the same cusp of `Γ₀(N)`. -/
theorem gamma0CuspLabel_eq_iff (γ γ' : SL(2, ℤ)) :
    gamma0CuspLabel N γ = gamma0CuspLabel N γ' ↔
      (Gamma0 N).cuspOrbitOfSL2Z γ = (Gamma0 N).cuspOrbitOfSL2Z γ' := by
  rw [gamma0CuspLabel_eq_iff_exists_dvd, cuspOrbitOfSL2Z_Gamma0_eq_iff]

variable (N) in
/-- **The cusps of `Γ₀(N)`** are in bijection with the pairs `(g, x)` of a divisor `g` of `N`
and a unit `x` modulo `gcd(g, N / g)`. The cusp `γ • ∞` corresponds to the label of `γ`
(`gamma0CuspOrbitEquiv_cuspOrbitOfSL2Z`). -/
noncomputable def gamma0CuspOrbitEquiv :
    ((Gamma0 N).map sl2zToPSL2R).CuspOrbit ≃ Σ g : N.divisors, (ZMod (Nat.gcd g (N / g)))ˣ :=
  Equiv.ofBijective
    (fun C ↦ gamma0CuspLabel N (Function.surjInv (Gamma0 N).cuspOrbitOfSL2Z_surjective C))
    ⟨fun C C' h ↦ by
      rwa [gamma0CuspLabel_eq_iff, Function.surjInv_eq (Gamma0 N).cuspOrbitOfSL2Z_surjective,
        Function.surjInv_eq (Gamma0 N).cuspOrbitOfSL2Z_surjective] at h,
    fun x ↦ by
      obtain ⟨γ, rfl⟩ := gamma0CuspLabel_surjective x
      exact ⟨(Gamma0 N).cuspOrbitOfSL2Z γ,
        (gamma0CuspLabel_eq_iff _ _).mpr (Function.surjInv_eq _ _)⟩⟩

/-- The cusp `γ • ∞` of `Γ₀(N)` corresponds to the label of `γ`. -/
@[simp]
theorem gamma0CuspOrbitEquiv_cuspOrbitOfSL2Z (γ : SL(2, ℤ)) :
    gamma0CuspOrbitEquiv N ((Gamma0 N).cuspOrbitOfSL2Z γ) = gamma0CuspLabel N γ :=
  (gamma0CuspLabel_eq_iff _ _).mpr (Function.surjInv_eq _ _)

/-- The cusp with the label of `γ` is `γ • ∞`. -/
@[simp]
theorem gamma0CuspOrbitEquiv_symm_gamma0CuspLabel (γ : SL(2, ℤ)) :
    (gamma0CuspOrbitEquiv N).symm (gamma0CuspLabel N γ) = (Gamma0 N).cuspOrbitOfSL2Z γ :=
  (Equiv.symm_apply_eq _).mpr (gamma0CuspOrbitEquiv_cuspOrbitOfSL2Z γ).symm

variable (N) in
/-- **The cusp count `ε∞` of `Γ₀(N)`**: the number of cusps of `Γ₀(N)` is
`∑_{g ∣ N} φ(gcd(g, N / g))`. -/
theorem card_cuspOrbit_Gamma0 :
    Nat.card ((Gamma0 N).map sl2zToPSL2R).CuspOrbit =
      ∑ g ∈ N.divisors, Nat.totient (Nat.gcd g (N / g)) := by
  rw [Nat.card_congr (gamma0CuspOrbitEquiv N), Nat.card_sigma, ← Finset.sum_coe_sort N.divisors]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  have : NeZero (Nat.gcd g (N / g)) :=
    ⟨Nat.gcd_ne_zero_left (Nat.ne_of_gt (Nat.pos_of_mem_divisors g.2))⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- `Γ₀(p)` has two cusps for a prime `p`. -/
theorem card_cuspOrbit_Gamma0_of_prime {p : ℕ} [Fact p.Prime] :
    Nat.card ((Gamma0 p).map sl2zToPSL2R).CuspOrbit = 2 := by
  have hp := (Fact.out : p.Prime)
  rw [card_cuspOrbit_Gamma0, hp.divisors, Finset.sum_pair hp.one_lt.ne, Nat.div_self hp.pos]
  simp

end TauCeti
