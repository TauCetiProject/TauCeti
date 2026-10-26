/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
public import Mathlib.Data.ZMod.Units
import TauCeti.Data.Int.GCD
import TauCeti.Data.ZMod.Units

/-!
# The cusps of `Γ₁(N)`

Away from the levels `1`, `2` and `4`, the number `ε∞` of cusps of `Γ₁(N)` satisfies
`2 ε∞ = ∑_{g ∣ N} φ(g) φ(N / g)`. This is the cusp count in the dimension formulas for `Γ₁(N)`.
Cusps are counted as the cusp orbits of the effective image of `Γ₁(N)` in `PSL(2, ℝ)`, the
boundary orbits adjoined to its analytic quotient.

Every cusp is `γ • ∞` for some `γ ∈ SL(2, ℤ)`. Take `γ` and `γ'` with bottom rows `(c, d)` and
`(c', d')`. The cusps `γ • ∞` and `γ' • ∞` are `Γ₁(N)`-equivalent exactly when
`(c', d') ≡ ±(c, d + j c)` modulo `N` for some integer `j`. Without the sign, this congruence is
detected by the *label* of `γ`. The label is the divisor `g = gcd(c, N)` of `N`, the unit `c / g`
modulo `N / g`, and the unit `d` modulo `g`. Every label occurs. When `N ∉ {1, 2, 4}`, the
matrices `γ` and `-γ` have different labels. So each cusp then has exactly two labels.

## Main definitions

* `TauCeti.gamma1CuspLabel`: the label `(g, u, v)` of `γ ∈ SL(2, ℤ)`.

## Main results

* `TauCeti.cuspOrbitOfSL2Z_Gamma1_eq_iff`: the congruence criterion for equivalence of cusps.
* `TauCeti.cuspOrbitOfSL2Z_Gamma1_eq_iff_gamma1CuspLabel`: two matrices represent the same cusp
  exactly when one has the label of the other or of its negative.
* `TauCeti.card_cuspOrbit_Gamma1`: the cusp count `2 ε∞ = ∑_{g ∣ N} φ(g) φ(N / g)` for
  `N ∉ {1, 2, 4}`.
* `TauCeti.card_cuspOrbit_Gamma1_of_prime`: `Γ₁(p)` has `p - 1` cusps for an odd prime `p`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §3.8.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup ModularGroup
open scoped MatrixGroups

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-! ### Equivalence of cusps -/

/-- **The criterion for equivalence of cusps of `Γ₁(N)`.** For `γ` and `γ'` with bottom rows
`(c, d)` and `(c', d')`, the cusps `γ • ∞` and `γ' • ∞` are `Γ₁(N)`-equivalent exactly when
`(c', d') ≡ ±(c, d + j c)` modulo `N` for some integer `j`. -/
theorem cuspOrbitOfSL2Z_Gamma1_eq_iff (γ γ' : SL(2, ℤ)) :
    (Gamma1 N).cuspOrbitOfSL2Z γ = (Gamma1 N).cuspOrbitOfSL2Z γ' ↔
      ∃ j : ℤ, (((γ' 1 0 : ℤ) : ZMod N) = γ 1 0 ∧
          ((γ' 1 1 : ℤ) : ZMod N) = γ 1 1 + j * γ 1 0) ∨
        (((γ' 1 0 : ℤ) : ZMod N) = -γ 1 0 ∧
          ((γ' 1 1 : ℤ) : ZMod N) = -γ 1 1 - j * γ 1 0) := by
  -- Without the sign: `(c', d') ≡ (δ₁₀, δ₁₁ + j δ₁₀)` makes `δ • ∞` and `γ' • ∞` equivalent,
  -- via `δ T^j γ'⁻¹ ∈ Γ₁(N)`.
  have key (δ : SL(2, ℤ)) (j : ℤ) (hc : ((γ' 1 0 : ℤ) : ZMod N) = δ 1 0)
      (hd : ((γ' 1 1 : ℤ) : ZMod N) = δ 1 1 + j * δ 1 0) :
      (Gamma1 N).cuspOrbitOfSL2Z δ = (Gamma1 N).cuspOrbitOfSL2Z γ' := by
    have hdet := congrArg (Int.cast : ℤ → ZMod N) γ'.det_coe
    rw [det_fin_two] at hdet
    push_cast at hdet
    refine (Subgroup.cuspOrbitOfSL2Z_eq_iff _ _ _).mpr
      ⟨δ * T ^ j * γ'⁻¹, mem_Gamma1_iff.mpr ⟨Gamma0_mem.mpr ?_, ?_⟩, ?_⟩
    · simp only [coe_mul, coe_inv, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
        of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
        coe_T_zpow]
      push_cast
      linear_combination (δ 1 0 : ZMod N) * hd - (δ 1 0 * j + δ 1 1 : ZMod N) * hc
    · simp only [coe_mul, coe_inv, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
        of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
        coe_T_zpow]
      push_cast
      linear_combination (γ' 0 1 : ZMod N) * hc - (γ' 0 0 : ZMod N) * hd + hdet
    · have hT : δ⁻¹ * (δ * T ^ j * γ'⁻¹) * γ' = T ^ j := by group
      rw [hT, coe_T_zpow]
      rfl
  constructor
  · rw [Subgroup.cuspOrbitOfSL2Z_eq_iff]
    rintro ⟨h, hh, hM⟩
    -- `γ⁻¹ h γ' = ±T^m`, and comparing bottom rows of `h γ' = γ (±T^m)` modulo `N` gives the
    -- congruence, since `h` has bottom row `(0, 1)` modulo `N`.
    obtain ⟨M, hMdef⟩ : ∃ M, γ⁻¹ * h * γ' = M := ⟨_, rfl⟩
    have hhM : h * γ' = γ * M := by rw [← hMdef]; group
    rw [hMdef] at hM
    have hdet := M.det_coe
    rw [det_fin_two, hM, mul_zero, sub_zero] at hdet
    obtain ⟨h0, h1⟩ := mem_Gamma1_iff.mp hh
    rw [Gamma0_mem] at h0
    have e10 := congrArg (fun A : SL(2, ℤ) ↦ ((A 1 0 : ℤ) : ZMod N)) hhM
    have e11 := congrArg (fun A : SL(2, ℤ) ↦ ((A 1 1 : ℤ) : ZMod N)) hhM
    simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add, Int.cast_mul, h0, h1,
      hM] at e10 e11
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨hm0, hm1⟩ | ⟨hm0, hm1⟩
    · refine ⟨M 0 1, Or.inl ⟨?_, ?_⟩⟩
      · simp only [hm0] at e10
        linear_combination e10
      · simp only [hm1] at e11
        linear_combination e11
    · refine ⟨-M 0 1, Or.inr ⟨?_, ?_⟩⟩
      · simp only [hm0] at e10
        push_cast at e10
        linear_combination e10
      · simp only [hm1] at e11
        push_cast at e11 ⊢
        linear_combination e11
  · rintro ⟨j, ⟨hc, hd⟩ | ⟨hc, hd⟩⟩
    · exact key γ j hc hd
    · rw [← Subgroup.cuspOrbitOfSL2Z_neg]
      refine key (-γ) j ?_ ?_ <;> simp only [coe_neg, Matrix.neg_apply, Int.cast_neg]
      · exact hc
      · linear_combination hd

/-! ### Labels of cusps -/

omit [NeZero N] in
private theorem isCoprime_gcd (γ : SL(2, ℤ)) : IsCoprime (γ 1 1) (Int.gcd (γ 1 0) N : ℤ) :=
  (bottom_row_coprime γ).symm.of_isCoprime_of_dvd_right (Int.gcd_dvd_left ..)

variable (N) in
/-- **The label of the cusp `γ • ∞` of `Γ₁(N)`, up to sign.** For `γ ∈ SL(2, ℤ)` with bottom
row `(c, d)`, it is the divisor `g = gcd(c, N)` of `N` together with the unit `c / g` modulo
`N / g` and the unit `d` modulo `g`. Two matrices have the same label exactly when their bottom
rows are congruent modulo `N` up to adding a multiple of `c` to `d`
(`gamma1CuspLabel_eq_iff`); the cusps of `Γ₁(N)` are the labels up to the sign of `γ`
(`cuspOrbitOfSL2Z_Gamma1_eq_iff_gamma1CuspLabel`). -/
noncomputable def gamma1CuspLabel (γ : SL(2, ℤ)) :
    Σ g : N.divisors, (ZMod (N / g))ˣ × (ZMod g)ˣ :=
  ⟨⟨Int.gcd (γ 1 0) N,
      Nat.mem_divisors.mpr ⟨Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right ..), NeZero.ne N⟩⟩,
    ZMod.unitOfIsCoprime _ (Int.isCoprime_div_gcd_div_gcd (NeZero.ne N) (γ 1 0)),
    ZMod.unitOfIsCoprime _ (isCoprime_gcd γ)⟩

/-- The divisor in the label of `γ` is `gcd(c, N)`, for `c` the lower-left entry of `γ`. -/
@[simp]
theorem coe_gamma1CuspLabel_fst (γ : SL(2, ℤ)) :
    ((gamma1CuspLabel N γ).1 : ℕ) = Int.gcd (γ 1 0) N :=
  (rfl)

/-- The first unit in the label of `γ` is `c / g` modulo `N / g`, for `c` the lower-left entry
of `γ` and `g = gcd(c, N)`. -/
@[simp]
theorem coe_gamma1CuspLabel_snd_fst (γ : SL(2, ℤ)) :
    ((gamma1CuspLabel N γ).2.1 : ZMod (N / (gamma1CuspLabel N γ).1)) =
      (γ 1 0 / Int.gcd (γ 1 0) N : ℤ) :=
  ZMod.coe_unitOfIsCoprime _ (Int.isCoprime_div_gcd_div_gcd (NeZero.ne N) (γ 1 0))

/-- The second unit in the label of `γ` is `d` modulo `gcd(c, N)`, for `(c, d)` the bottom row
of `γ`. -/
@[simp]
theorem coe_gamma1CuspLabel_snd_snd (γ : SL(2, ℤ)) :
    ((gamma1CuspLabel N γ).2.2 : ZMod (gamma1CuspLabel N γ).1) = (γ 1 1 : ℤ) :=
  ZMod.coe_unitOfIsCoprime _ (isCoprime_gcd γ)

/-- The label of `γ` is `(g, u, v)` as soon as `gcd(c, N) = g`, `c / g` reduces to `u` and `d`
reduces to `v`. -/
theorem gamma1CuspLabel_eq_mk {γ : SL(2, ℤ)} {g : ℕ} (hg : g ∈ N.divisors)
    {u : (ZMod (N / g))ˣ} {v : (ZMod g)ˣ} (h₁ : Int.gcd (γ 1 0) N = g)
    (h₂ : ((γ 1 0 / g : ℤ) : ZMod (N / g)) = u) (h₃ : ((γ 1 1 : ℤ) : ZMod g) = v) :
    gamma1CuspLabel N γ = ⟨⟨g, hg⟩, u, v⟩ := by
  subst h₁
  refine Sigma.ext rfl (heq_of_eq (Prod.ext (Units.ext ?_) (Units.ext ?_)))
  · exact (coe_gamma1CuspLabel_snd_fst γ).trans h₂
  · exact (coe_gamma1CuspLabel_snd_snd γ).trans h₃

/-- **Equality of labels.** Two matrices with bottom rows `(c, d)` and `(c', d')` have the same
label exactly when `c' ≡ c` and `d' ≡ d + j c` modulo `N` for some integer `j`. -/
theorem gamma1CuspLabel_eq_iff (γ γ' : SL(2, ℤ)) :
    gamma1CuspLabel N γ = gamma1CuspLabel N γ' ↔
      ((γ' 1 0 : ℤ) : ZMod N) = γ 1 0 ∧ ∃ j : ℤ, ((γ' 1 1 : ℤ) : ZMod N) = γ 1 1 + j * γ 1 0 := by
  -- The units live in `ZMod` of moduli that agree only propositionally, so they are compared
  -- as `HEq`; once the divisors are identified they are compared as integer congruences.
  have hx {g g' : ℕ} (hg : g = g') {a b a' b' : ℤ} (ha : IsCoprime a (N / g : ℕ))
      (hb : IsCoprime b g) (ha' : IsCoprime a' (N / g' : ℕ)) (hb' : IsCoprime b' g') :
      HEq (ZMod.unitOfIsCoprime a ha, ZMod.unitOfIsCoprime b hb)
          (ZMod.unitOfIsCoprime a' ha', ZMod.unitOfIsCoprime b' hb') ↔
        ((N / g : ℕ) : ℤ) ∣ a' - a ∧ (g : ℤ) ∣ b' - b := by
    subst hg
    rw [heq_iff_eq, Prod.ext_iff, Units.ext_iff, Units.ext_iff, ZMod.coe_unitOfIsCoprime,
      ZMod.coe_unitOfIsCoprime, ZMod.coe_unitOfIsCoprime, ZMod.coe_unitOfIsCoprime,
      ZMod.intCast_eq_intCast_iff_dvd_sub, ZMod.intCast_eq_intCast_iff_dvd_sub]
  have hN : (N : ℤ) = Int.gcd (γ 1 0) N * (N / Int.gcd (γ 1 0) N : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' (Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right ..))).symm
  have hc (c : ℤ) : c = Int.gcd c N * (c / Int.gcd c N) :=
    (Int.mul_ediv_cancel' (Int.gcd_dvd_left ..)).symm
  have hg0 : (Int.gcd (γ 1 0) N : ℤ) ≠ 0 := by
    have := Int.gcd_pos_of_ne_zero_right (γ 1 0) (show (N : ℤ) ≠ 0 by exact_mod_cast NeZero.ne N)
    omega
  rw [gamma1CuspLabel, gamma1CuspLabel, Sigma.mk.inj_iff, Subtype.mk.injEq,
    ZMod.intCast_eq_intCast_iff_dvd_sub]
  simp only [← Int.cast_mul, ← Int.cast_add, ZMod.intCast_eq_intCast_iff_dvd_sub]
  constructor
  · rintro ⟨hg, hx'⟩
    obtain ⟨hu, k, hk⟩ := (hx hg ..).mp hx'
    rw [← hg] at hu
    refine ⟨?_, k * Int.gcdA (γ 1 0) N, -(k * Int.gcdB (γ 1 0) N), ?_⟩
    · have h₁ := hc (γ 1 0)
      have h₂ := hc (γ' 1 0)
      rw [← hg] at h₂
      have e : γ 1 0 - γ' 1 0 = Int.gcd (γ 1 0) N *
          (γ 1 0 / Int.gcd (γ 1 0) N - γ' 1 0 / Int.gcd (γ 1 0) N) := by
        linear_combination h₁ - h₂
      rw [e]
      exact (dvd_of_eq hN).trans (mul_dvd_mul_left _ (dvd_sub_comm.mp hu))
    · linear_combination -hk - k * Int.gcd_eq_gcd_ab (γ 1 0) N
  · rintro ⟨⟨t, ht⟩, j, s, hs⟩
    have hg : Int.gcd (γ 1 0) N = Int.gcd (γ' 1 0) N := by
      rw [show γ' 1 0 = γ 1 0 + (-t) * N by linear_combination -ht, Int.gcd_add_mul_right_left]
    refine ⟨hg, (hx hg ..).mpr ⟨⟨-t, mul_left_cancel₀ hg0 ?_⟩, ⟨j * (γ 1 0 / Int.gcd (γ 1 0) N) -
      (N / Int.gcd (γ 1 0) N : ℕ) * s, ?_⟩⟩⟩
    · have h₂ := hc (γ' 1 0)
      rw [← hg] at h₂ ⊢
      linear_combination -h₂ + hc (γ 1 0) - ht - t * hN
    · linear_combination -hs + j * hc (γ 1 0) - s * hN

/-- Every divisor `g` of `N`, unit modulo `N / g` and unit modulo `g` form a label. -/
theorem gamma1CuspLabel_surjective : Function.Surjective (gamma1CuspLabel N) := by
  rintro ⟨⟨g, hg⟩, u, v⟩
  have hgN : g ∣ N := Nat.dvd_of_mem_divisors hg
  have hg0 : g ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hg)
  have : NeZero g := ⟨hg0⟩
  have : NeZero (N / g) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hgN) (NeZero.pos g)).ne'⟩
  have hN : (N : ℤ) = g * (N / g : ℕ) := by exact_mod_cast (Nat.mul_div_cancel' hgN).symm
  -- Lift `u` and `v` to integers `u₀` and `v₀`; the residues `(g u₀, v₀)` modulo `N` lift to
  -- the bottom row of a matrix in `SL(2, ℤ)`.
  set u₀ : ℤ := ((u : ZMod (N / g)).val : ℤ) with hu₀
  set v₀ : ℤ := ((v : ZMod g).val : ℤ) with hv₀
  have hu : IsCoprime u₀ (N / g : ℕ) :=
    Nat.isCoprime_iff_coprime.mpr (ZMod.val_coe_unit_coprime u)
  have hv : IsCoprime v₀ g := Nat.isCoprime_iff_coprime.mpr (ZMod.val_coe_unit_coprime v)
  have hcop : IsCoprime ((g * u₀ : ℤ) : ZMod N) (v₀ : ZMod N) := by
    obtain ⟨x, y, hxy⟩ := hv
    obtain ⟨s, t, hst⟩ := hu
    refine ⟨((y * s : ℤ) : ZMod N), (x : ZMod N), ?_⟩
    have h : y * s * (g * u₀) + x * v₀ = 1 + N * (-(y * t)) := by
      linear_combination hxy + y * g * hst + y * t * hN
    have h' := congrArg (Int.cast : ℤ → ZMod N) h
    push_cast at h'
    rw [ZMod.natCast_self, zero_mul, add_zero] at h'
    push_cast
    exact h'
  obtain ⟨c, d, hc, hd, hcd⟩ := IsCoprime.exists_int_lifts hcop
  obtain ⟨γ, -, hγ⟩ := bottom_row_surj (show ![c, d] ∈
    {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} from hcd)
  have hγc : γ 1 0 = c := congrFun hγ 0
  have hγd : γ 1 1 = d := congrFun hγ 1
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hc.symm
  obtain ⟨l, hl⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hd
  have hck : γ 1 0 = g * (u₀ + (N / g : ℕ) * k) := by linear_combination hγc + hk + k * hN
  refine ⟨γ, gamma1CuspLabel_eq_mk hg ?_ ?_ ?_⟩
  · rw [hck, show (N : ℤ) = g * (N / g : ℕ) from hN, Int.gcd_mul_left, Int.natAbs_natCast,
      Int.gcd_add_mul_left_left, Int.isCoprime_iff_gcd_eq_one.mp hu, mul_one]
  · rw [hck, Int.mul_ediv_cancel_left _ (by exact_mod_cast hg0)]
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast (N / g), ZMod.natCast_self, zero_mul,
      add_zero, hu₀, Int.cast_natCast, ZMod.natCast_zmod_val]
  · have hdv : ((d : ℤ) : ZMod g) = ((v₀ : ℤ) : ZMod g) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr
        ⟨(N / g : ℕ) * l, by linear_combination hl + l * hN⟩
    rw [hγd, hdv, hv₀, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- **The criterion for equivalence of cusps of `Γ₁(N)` in terms of labels.** The cusps `γ • ∞`
and `γ' • ∞` of `Γ₁(N)` agree exactly when `γ'` has the label of `γ` or of `-γ`. -/
theorem cuspOrbitOfSL2Z_Gamma1_eq_iff_gamma1CuspLabel (γ γ' : SL(2, ℤ)) :
    (Gamma1 N).cuspOrbitOfSL2Z γ = (Gamma1 N).cuspOrbitOfSL2Z γ' ↔
      gamma1CuspLabel N γ = gamma1CuspLabel N γ' ∨
        gamma1CuspLabel N (-γ) = gamma1CuspLabel N γ' := by
  rw [cuspOrbitOfSL2Z_Gamma1_eq_iff, gamma1CuspLabel_eq_iff, gamma1CuspLabel_eq_iff]
  simp only [coe_neg, Matrix.neg_apply, Int.cast_neg]
  constructor
  · rintro ⟨j, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩
    · exact Or.inl ⟨h₁, j, h₂⟩
    · exact Or.inr ⟨h₁, j, by rw [h₂]; ring⟩
  · rintro (⟨h₁, j, h₂⟩ | ⟨h₁, j, h₂⟩)
    · exact ⟨j, Or.inl ⟨h₁, h₂⟩⟩
    · exact ⟨j, Or.inr ⟨h₁, by rw [h₂]; ring⟩⟩

/-- **The label of `-γ`.** It has the divisor of the label of `γ` and the negatives of its two
units. -/
theorem gamma1CuspLabel_neg (γ : SL(2, ℤ)) :
    gamma1CuspLabel N (-γ) =
      ⟨(gamma1CuspLabel N γ).1, -(gamma1CuspLabel N γ).2.1, -(gamma1CuspLabel N γ).2.2⟩ := by
  refine gamma1CuspLabel_eq_mk (gamma1CuspLabel N γ).1.2 ?_ ?_ ?_
  · simp
  · rw [Units.val_neg, coe_gamma1CuspLabel_snd_fst, coe_neg, Matrix.neg_apply,
      Int.neg_ediv_of_dvd (show ((gamma1CuspLabel N γ).1 : ℤ) ∣ γ 1 0 from Int.gcd_dvd_left ..),
      Int.cast_neg]
    rfl
  · rw [Units.val_neg, coe_gamma1CuspLabel_snd_snd, coe_neg, Matrix.neg_apply, Int.cast_neg]

/-- Away from the levels `1`, `2` and `4`, the matrices `γ` and `-γ` have different labels. -/
theorem gamma1CuspLabel_neg_ne (hN : 2 < N) (hN4 : N ≠ 4) (γ : SL(2, ℤ)) :
    gamma1CuspLabel N (-γ) ≠ gamma1CuspLabel N γ := by
  rw [Ne, gamma1CuspLabel_eq_iff]
  simp only [coe_neg, Matrix.neg_apply, Int.cast_neg]
  rintro ⟨hc, j, hd⟩
  have hc' : (N : ℤ) ∣ 2 * γ 1 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    linear_combination hc
  have hd' : (N : ℤ) ∣ 2 * γ 1 1 + j * γ 1 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    linear_combination hd
  set g := Int.gcd (γ 1 0) N
  have hgc : (g : ℤ) ∣ γ 1 0 := Int.gcd_dvd_left ..
  have hgN : (g : ℤ) ∣ N := Int.gcd_dvd_right ..
  have hg0 : (g : ℤ) ≠ 0 := by
    have := Int.gcd_pos_of_ne_zero_right (γ 1 0) (show (N : ℤ) ≠ 0 by exact_mod_cast NeZero.ne N)
    omega
  -- `g` divides `2 d`, hence `2`.
  have hg2 : (g : ℤ) ∣ 2 := by
    refine (isCoprime_gcd γ).symm.dvd_of_dvd_mul_right ?_
    have := dvd_sub (hgN.trans hd') (hgc.mul_left j)
    rwa [add_sub_cancel_right] at this
  -- `N / g` divides `2 (c / g)`, hence `2`.
  have hm2 : ((N / g : ℕ) : ℤ) ∣ 2 := by
    refine (Int.isCoprime_div_gcd_div_gcd (NeZero.ne N) (γ 1 0)).symm.dvd_of_dvd_mul_right ?_
    refine Int.dvd_of_mul_dvd_mul_left hg0 ?_
    have hN' : (N : ℤ) = g * (N / g : ℕ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Int.natCast_dvd_natCast.mp hgN)).symm
    rw [← hN', mul_left_comm, Int.mul_ediv_cancel' hgc]
    exact hc'
  have h4 : (N : ℤ) ∣ 4 := by
    have hN' : (N : ℤ) = g * (N / g : ℕ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Int.natCast_dvd_natCast.mp hgN)).symm
    rw [hN', show (4 : ℤ) = 2 * 2 by norm_num]
    exact mul_dvd_mul hg2 hm2
  have h4' : N ∣ 4 := by exact_mod_cast h4
  have := Nat.le_of_dvd (by norm_num) h4'
  interval_cases N <;> omega

/-! ### The cusp count -/

variable (N) in
/-- **The cusp count `ε∞` of `Γ₁(N)`**: away from the levels `1`, `2` and `4`, twice the number
of cusps of `Γ₁(N)` is `∑_{g ∣ N} φ(g) φ(N / g)`. -/
theorem card_cuspOrbit_Gamma1 (hN : 2 < N) (hN4 : N ≠ 4) :
    2 * Nat.card ((Gamma1 N).map sl2zToPSL2R).CuspOrbit =
      ∑ g ∈ N.divisors, Nat.totient g * Nat.totient (N / g) := by
  have hfin (g : N.divisors) : Finite ((ZMod (N / g))ˣ × (ZMod g)ˣ) := by
    have : NeZero (g : ℕ) := ⟨Nat.ne_of_gt (Nat.pos_of_mem_divisors g.2)⟩
    have : NeZero (N / g) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos N)
      (Nat.dvd_of_mem_divisors g.2)) (NeZero.pos (g : ℕ))).ne'⟩
    infer_instance
  -- Send a label to the cusp of any matrix carrying it; every fibre is `{λ(γ), λ(-γ)}`.
  let f (x : Σ g : N.divisors, (ZMod (N / g))ˣ × (ZMod g)ˣ) :
      ((Gamma1 N).map sl2zToPSL2R).CuspOrbit :=
    (Gamma1 N).cuspOrbitOfSL2Z (Function.surjInv gamma1CuspLabel_surjective x)
  have hfib (C : ((Gamma1 N).map sl2zToPSL2R).CuspOrbit) : Nat.card {x // f x = C} = 2 := by
    obtain ⟨γ, rfl⟩ := (Gamma1 N).cuspOrbitOfSL2Z_surjective C
    have h : {x | f x = (Gamma1 N).cuspOrbitOfSL2Z γ} =
        {gamma1CuspLabel N γ, gamma1CuspLabel N (-γ)} := by
      ext x
      simp only [Set.mem_ofPred_eq, f]
      rw [eq_comm, cuspOrbitOfSL2Z_Gamma1_eq_iff_gamma1CuspLabel,
        Function.surjInv_eq gamma1CuspLabel_surjective x, Set.mem_insert_iff,
        Set.mem_singleton_iff, eq_comm, eq_comm (b := x)]
    rw [← Set.coe_ofPred, Nat.card_coe_set_eq, h,
      Set.ncard_pair (gamma1CuspLabel_neg_ne hN hN4 γ).symm]
  have := Fintype.ofFinite ((Gamma1 N).map sl2zToPSL2R).CuspOrbit
  calc 2 * Nat.card ((Gamma1 N).map sl2zToPSL2R).CuspOrbit
      = ∑ C, Nat.card {x // f x = C} := by
        simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
          Nat.card_eq_fintype_card, mul_comm]
    _ = Nat.card (Σ g : N.divisors, (ZMod (N / g))ˣ × (ZMod g)ˣ) := by
        rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv f)]
    _ = ∑ g ∈ N.divisors, Nat.totient g * Nat.totient (N / g) := by
        rw [Nat.card_sigma, ← Finset.sum_coe_sort N.divisors]
        refine Finset.sum_congr rfl fun g _ ↦ ?_
        have : NeZero (g : ℕ) := ⟨Nat.ne_of_gt (Nat.pos_of_mem_divisors g.2)⟩
        have : NeZero (N / g) := ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos N)
          (Nat.dvd_of_mem_divisors g.2)) (NeZero.pos (g : ℕ))).ne'⟩
        rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
          ZMod.card_units_eq_totient, ZMod.card_units_eq_totient, mul_comm]

/-- `Γ₁(p)` has `p - 1` cusps for an odd prime `p`. -/
theorem card_cuspOrbit_Gamma1_of_prime {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    Nat.card ((Gamma1 p).map sl2zToPSL2R).CuspOrbit = p - 1 := by
  have hp' := (Fact.out : p.Prime)
  have h := card_cuspOrbit_Gamma1 p (lt_of_le_of_ne hp'.two_le (Ne.symm hp))
    (by rintro rfl; exact absurd hp' (by decide))
  rw [hp'.divisors, Finset.sum_pair hp'.one_lt.ne, Nat.div_self hp'.pos, Nat.div_one,
    Nat.totient_one, Nat.totient_prime hp'] at h
  omega

end TauCeti
