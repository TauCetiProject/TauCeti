/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.Quadratic.Pair.SmoothedSum
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Realization
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.LSeries.Quadratic.Character
import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Sign

/-!
# Siegel's theorem for quadratic Dirichlet `L`-functions

Goldfeld's fundamental inequality (`DirichletCharacter.le_LFunction_one_mul_mul_re_of_nonpos`)
bounds `Re (L(1, χ) L(1, ψ) L(1, χ.mul ψ))` from below whenever `χ` mod `M` and `ψ` mod `N` are
nonprincipal quadratic Dirichlet characters with `χ.mul ψ ≠ 1` and `3 / 4 ≤ β` satisfies
`Re (ζ(β) L(β, χ) L(β, ψ) L(β, χ.mul ψ)) ≤ 0`. Dividing by `L(1, ψ) > 0` and bounding
`L(1, χ.mul ψ) ≤ 1 + log (M N)` yields an explicit single-character lower bound for `L(1, χ)`.

To deduce **Siegel's theorem** (`DirichletCharacter.exists_pos_forall_rpow_le_LFunction_one_re`),
fix `ε > 0` and `δ = min ε 1 / 32`. Either some primitive nonprincipal quadratic character `ψ₁`
has a real zero `β ∈ [1 - δ, 1)`, in which case the four-factor product vanishes at `β` for every
primitive nonprincipal quadratic `χ` of level `M > N₁`, or no primitive nonprincipal quadratic
character vanishes on `[1 - δ, 1)`, in which case pairing with `χ_{-4}` at `β = 1 - δ` makes the
four-factor product nonpositive by `DirichletCharacter.pair_nonpos_of_forall_ne_zero` and
`DirichletCharacter.LFunction_changeLevel_eq_zero_iff`. Finitely many small conductors `M ≤ N₀`
are handled by finiteness of `DirichletCharacter ℂ M`, and imprimitive characters follow from the
primitive case via `DirichletCharacter.exists_norm_LFunction_changeLevel_le_rpow`.

## Main results

* `DirichletCharacter.le_LFunction_one_re_of_nonpos`: explicit Goldfeld lower bound for
  `Re L(1, χ)` in terms of an auxiliary nonprincipal quadratic character `ψ` and point
  `3 / 4 ≤ β` where the four-factor product has nonpositive real part.
* `DirichletCharacter.le_LFunction_one_re_of_LFunction_eq_zero`: specialization when `L(β, ψ) = 0`.
* `DirichletCharacter.exists_pos_forall_rpow_le_LFunction_one_re`: Siegel's theorem for all
  nonprincipal quadratic Dirichlet characters: for every `ε > 0` there is `c > 0` such that
  `c * M ^ (-ε) ≤ Re L(1, χ)` for every level `M ≥ 1` and nonprincipal quadratic `χ` mod `M`.
* `TauCeti.Multiquadratic.exists_pos_forall_rpow_le_LFunction_one_re`: specialization to
  fundamental-discriminant characters `χ_D` (`D ≠ 1`).

## References

* C. L. Siegel, *Über die Classenzahl quadratischer Zahlkörper*, Acta Arith. 1 (1935), 83–86.
* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, §5.9.
-/

public section

open Complex Set
open scoped ComplexOrder

namespace DirichletCharacter

private theorem one_add_log_le_mul_rpow {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ) :
    1 + Real.log x ≤ (1 + δ⁻¹) * x ^ δ := by
  have hx0 : 0 ≤ x := by linarith
  have h1 : 1 ≤ x ^ δ := Real.one_le_rpow hx hδ.le
  have hlog : Real.log x ≤ δ⁻¹ * x ^ δ := by
    simpa [div_eq_inv_mul] using Real.log_le_rpow_div hx0 hδ
  linarith

private theorem mul_ne_one_of_lt {M N : ℕ} [NeZero M] [NeZero N] {χ : DirichletCharacter ℂ M}
    {ψ : DirichletCharacter ℂ N} (hχp : χ.IsPrimitive) (hNM : N < M) :
    χ.mul ψ ≠ 1 := by
  intro h1
  have : NeZero (Nat.lcm M N) := ⟨Nat.lcm_ne_zero (NeZero.ne M) (NeZero.ne N)⟩
  have hinv : changeLevel (Nat.dvd_lcm_left M N) χ = (changeLevel (Nat.dvd_lcm_right M N) ψ)⁻¹ :=
    eq_inv_of_mul_eq_one_left h1
  have hcond := congrArg conductor hinv
  rw [conductor_changeLevel, (isPrimitive_def χ).mp hχp, conductor_inv,
    conductor_changeLevel] at hcond
  have hle : ψ.conductor ≤ N :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) ψ.conductor_dvd_level
  omega

/-- **Single-character Goldfeld lower bound.** If `χ` mod `M` and `ψ` mod `N` are nonprincipal
quadratic Dirichlet characters with `χ.mul ψ ≠ 1` and `3 / 4 ≤ β` satisfies
`Re (ζ(β) L(β, χ) L(β, ψ) L(β, χ.mul ψ)) ≤ 0`, then `Re L(1, χ)` is bounded below explicitly in
terms of `1 - β`, `M * N`, and `Re L(1, ψ)`. -/
theorem le_LFunction_one_re_of_nonpos {M N : ℕ} [NeZero M] [NeZero N]
    {χ : DirichletCharacter ℂ M} {ψ : DirichletCharacter ℂ N}
    (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) (hχ₁ : χ ≠ 1) (hψ₁ : ψ ≠ 1)
    (hχψ : χ.mul ψ ≠ 1) {β : ℝ} (hβ : 3 / 4 ≤ β)
    (hsign : (riemannZeta β * χ.LFunction β * ψ.LFunction β * (χ.mul ψ).LFunction β).re ≤ 0) :
    (1 / 3360000000 : ℝ) * (1 - β) * ((M : ℝ) * N) ^ (-8 * (1 - β)) /
        ((ψ.LFunction 1).re * (1 + Real.log ((M : ℝ) * N))) ≤
      (χ.LFunction 1).re := by
  have : NeZero (Nat.lcm M N) := ⟨Nat.lcm_ne_zero (NeZero.ne M) (NeZero.ne N)⟩
  have hgold := le_LFunction_one_mul_mul_re_of_nonpos hχ hψ hχ₁ hψ₁ hχψ hβ hsign
  have hχ_pos := Complex.pos_iff.mp (LFunction_apply_one_pos hχ hχ₁)
  have hψ_pos := Complex.pos_iff.mp (LFunction_apply_one_pos hψ hψ₁)
  have hχψ_pos := Complex.pos_iff.mp (LFunction_apply_one_pos (isQuadratic_mul hχ hψ) hχψ)
  have hre_prod : (χ.LFunction 1 * ψ.LFunction 1 * (χ.mul ψ).LFunction 1).re =
      (χ.LFunction 1).re * ((ψ.LFunction 1).re * ((χ.mul ψ).LFunction 1).re) := by
    have h1 : χ.LFunction 1 = ((χ.LFunction 1).re : ℂ) := Complex.ext rfl hχ_pos.2.symm
    have h2 : ψ.LFunction 1 = ((ψ.LFunction 1).re : ℂ) := Complex.ext rfl hψ_pos.2.symm
    have h3 : (χ.mul ψ).LFunction 1 = (((χ.mul ψ).LFunction 1).re : ℂ) :=
      Complex.ext rfl hχψ_pos.2.symm
    conv_lhs => rw [h1, h2, h3, ← ofReal_mul, ← ofReal_mul, ofReal_re]
    ring
  have hlcm_le : ((Nat.lcm M N : ℕ) : ℝ) ≤ (M : ℝ) * N := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne M))
      (Nat.pos_of_ne_zero (NeZero.ne N))) (Nat.lcm_dvd_mul M N)
  have hlcm_pos : (0 : ℝ) < (Nat.lcm M N : ℕ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne _))
  have hMN1 : 1 ≤ (M : ℝ) * N := by
    have : (1 : ℝ) ≤ M := Nat.one_le_cast.mpr NeZero.one_le
    have : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr NeZero.one_le
    nlinarith
  have hlog_pos : 0 < 1 + Real.log ((M : ℝ) * N) :=
    add_pos_of_pos_of_nonneg one_pos (Real.log_nonneg hMN1)
  have hχψ_ub : ((χ.mul ψ).LFunction 1).re ≤ 1 + Real.log ((M : ℝ) * N) :=
    (re_le_norm _).trans <| (norm_LFunction_one_le_one_add_log _ hχψ).trans <|
      add_le_add_right (Real.log_le_log hlcm_pos hlcm_le) 1
  rw [div_le_iff₀ (mul_pos hψ_pos.1 hlog_pos)]
  refine hgold.trans ?_
  rw [hre_prod]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hχψ_ub hψ_pos.1.le) hχ_pos.1.le

/-- **Goldfeld lower bound from an exceptional real zero.** If a nonprincipal quadratic character
`ψ` mod `N` vanishes at `3 / 4 ≤ β`, then every nonprincipal quadratic `χ` mod `M` with
`χ.mul ψ ≠ 1` satisfies the corresponding algebraic lower bound at `s = 1`. -/
theorem le_LFunction_one_re_of_LFunction_eq_zero {M N : ℕ} [NeZero M] [NeZero N]
    {χ : DirichletCharacter ℂ M} {ψ : DirichletCharacter ℂ N}
    (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) (hχ₁ : χ ≠ 1) (hψ₁ : ψ ≠ 1)
    (hχψ : χ.mul ψ ≠ 1) {β : ℝ} (hβ : 3 / 4 ≤ β) (hzero : ψ.LFunction β = 0) :
    (1 / 3360000000 : ℝ) * (1 - β) * ((M : ℝ) * N) ^ (-8 * (1 - β)) /
        ((ψ.LFunction 1).re * (1 + Real.log ((M : ℝ) * N))) ≤
      (χ.LFunction 1).re :=
  le_LFunction_one_re_of_nonpos hχ hψ hχ₁ hψ₁ hχψ hβ (by simp [hzero])

private theorem LFunction_ne_zero_of_no_primitive_zero {δ : ℝ} (hδ : δ < 1)
    (hno : ¬ ∃ (N₁ : ℕ) (_ : NeZero N₁) (ψ₁ : DirichletCharacter ℂ N₁) (β₁ : ℝ),
      ψ₁.IsPrimitive ∧ ψ₁.IsQuadratic ∧ ψ₁ ≠ 1 ∧ β₁ ∈ Ico (1 - δ) 1 ∧ ψ₁.LFunction β₁ = 0)
    {K : ℕ} [NeZero K] {η : DirichletCharacter ℂ K} (hηq : η.IsQuadratic) (hη1 : η ≠ 1)
    {σ : ℝ} (hσ : σ ∈ Ioo (1 - δ) 1) : η.LFunction σ ≠ 0 := by
  intro hzero
  have : NeZero η.conductor := ⟨η.conductor_ne_zero⟩
  have hη₀q : η.primitiveCharacter.IsQuadratic := by
    rw [← isQuadratic_changeLevel_iff η.conductor_dvd_level, η.changeLevel_primitiveCharacter]
    exact hηq
  have hη₀1 : η.primitiveCharacter ≠ 1 := fun h1 ↦ hη1 (by
    rw [← η.changeLevel_primitiveCharacter, h1, map_one])
  have hσ_pos : 0 < (σ : ℂ).re := by simp only [ofReal_re]; linarith [hσ.1]
  have hzero₀ : η.primitiveCharacter.LFunction σ = 0 := by
    rw [← LFunction_changeLevel_eq_zero_iff η.primitiveCharacter η.conductor_dvd_level
      hσ_pos (.inl hη₀1), η.changeLevel_primitiveCharacter]
    exact hzero
  exact hno ⟨η.conductor, inferInstance, η.primitiveCharacter, σ,
    η.primitiveCharacter_isPrimitive, hη₀q, hη₀1, ⟨hσ.1.le, hσ.2⟩, hzero₀⟩

private theorem exists_aux_character {δ : ℝ} (hδ : δ ∈ Ioo 0 (1 / 4)) :
    ∃ (N₀ : ℕ) (_ : NeZero N₀) (ψ₀ : DirichletCharacter ℂ N₀) (β : ℝ),
      ψ₀.IsQuadratic ∧ ψ₀ ≠ 1 ∧ β ∈ Ico (1 - δ) 1 ∧
      ∀ (M : ℕ) [NeZero M], N₀ < M → ∀ (χ : DirichletCharacter ℂ M),
        χ.IsPrimitive → χ.IsQuadratic →
        (riemannZeta β * χ.LFunction β * ψ₀.LFunction β * (χ.mul ψ₀).LFunction β).re ≤ 0 := by
  classical
  by_cases hex : ∃ (N₁ : ℕ) (_ : NeZero N₁) (ψ₁ : DirichletCharacter ℂ N₁) (β₁ : ℝ),
      ψ₁.IsPrimitive ∧ ψ₁.IsQuadratic ∧ ψ₁ ≠ 1 ∧ β₁ ∈ Ico (1 - δ) 1 ∧ ψ₁.LFunction β₁ = 0
  · obtain ⟨N₁, hN₁, ψ₁, β₁, _, hψq, hψ1, hβ₁, hzero⟩ := hex
    exact ⟨N₁, hN₁, ψ₁, β₁, hψq, hψ1, hβ₁, fun _ _ _ _ _ _ ↦ by simp [hzero]⟩
  · have hD₀ : Int.IsFundamentalDiscr (-4) :=
      TauCeti.Multiquadratic.isPrimeDiscriminant_neg_four.isFundamentalDiscr
    have : NeZero (-4 : ℤ).natAbs := hD₀.neZero_natAbs
    set ψ₀ := TauCeti.Multiquadratic.fundamentalDiscriminantCharCast ℂ (-4) hD₀
    have hψq : ψ₀.IsQuadratic :=
      TauCeti.Multiquadratic.fundamentalDiscriminantCharCast_isQuadratic hD₀
    have hψ1 : ψ₀ ≠ 1 :=
      mt (TauCeti.Multiquadratic.fundamentalDiscriminantCharCast_eq_one_iff hD₀).mp (by decide)
    refine ⟨(-4 : ℤ).natAbs, inferInstance, ψ₀, 1 - δ, hψq, hψ1, ⟨le_rfl, by linarith [hδ.1]⟩,
      fun M _ hNM χ hχp hχq ↦ ?_⟩
    have hχ1 : χ ≠ 1 := mt hχp.eq_one_iff.mp (by omega)
    have hχψ1 : χ.mul ψ₀ ≠ 1 := mul_ne_one_of_lt hχp hNM
    have : NeZero (Nat.lcm M (-4 : ℤ).natAbs) :=
      ⟨Nat.lcm_ne_zero (NeZero.ne M) (NeZero.ne _)⟩
    have hδ1 : δ < 1 := by linarith [hδ.2]
    have hnonpos := pair_nonpos_of_forall_ne_zero hχq hψq hχ1 hψ1 hχψ1
      (by linarith [hδ.2]) (by linarith [hδ.1]) fun σ hσ ↦
      ⟨LFunction_ne_zero_of_no_primitive_zero hδ1 hex hχq hχ1 hσ,
        LFunction_ne_zero_of_no_primitive_zero hδ1 hex hψq hψ1 hσ,
        LFunction_ne_zero_of_no_primitive_zero hδ1 hex (isQuadratic_mul hχq hψq) hχψ1 hσ⟩
    exact (Complex.le_def.mp hnonpos).1

private theorem exists_pos_forall_le_LFunction_one_re_of_le (Q : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], M ≤ Q → ∀ (χ : DirichletCharacter ℂ M),
      χ.IsQuadratic → χ ≠ 1 → c ≤ (χ.LFunction 1).re := by
  classical
  induction Q with
  | zero =>
    exact ⟨1, one_pos, fun M _ hM _ _ _ ↦ absurd (Nat.eq_zero_of_le_zero hM) (NeZero.ne M)⟩
  | succ Q ih =>
    obtain ⟨c₀, hc₀, hih⟩ := ih
    set S : Finset (DirichletCharacter ℂ (Q + 1)) :=
      Finset.univ.filter fun χ ↦ χ.IsQuadratic ∧ χ ≠ 1
    by_cases hS : S.Nonempty
    · set c₁ : ℝ := S.inf' hS fun χ ↦ (χ.LFunction 1).re
      have hc₁ : 0 < c₁ := (Finset.lt_inf'_iff hS).mpr fun χ hχ ↦ by
        obtain ⟨hχq, hχ1⟩ := (Finset.mem_filter.mp hχ).2
        exact (Complex.pos_iff.mp (LFunction_apply_one_pos hχq hχ1)).1
      refine ⟨min c₀ c₁, lt_min hc₀ hc₁, fun M _ hM χ hχq hχ1 ↦ ?_⟩
      rcases Nat.of_le_succ hM with hle | rfl
      · exact (min_le_left _ _).trans (hih M hle χ hχq hχ1)
      · exact (min_le_right _ _).trans
          (Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hχq, hχ1⟩))
    · refine ⟨c₀, hc₀, fun M _ hM χ hχq hχ1 ↦ ?_⟩
      rcases Nat.of_le_succ hM with hle | rfl
      · exact hih M hle χ hχq hχ1
      · exact absurd ⟨χ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hχq, hχ1⟩⟩ hS

private theorem exists_pos_forall_rpow_le_LFunction_one_re_of_lt {ε : ℝ} (hε : 0 < ε)
    {N₀ : ℕ} [NeZero N₀] {ψ₀ : DirichletCharacter ℂ N₀} {β : ℝ}
    (hψq : ψ₀.IsQuadratic) (hψ1 : ψ₀ ≠ 1) (hβ34 : β ∈ Ico (3 / 4) 1) (h8β : 8 * (1 - β) ≤ ε / 2)
    (hsign : ∀ (M : ℕ) [NeZero M], N₀ < M → ∀ (χ : DirichletCharacter ℂ M),
      χ.IsPrimitive → χ.IsQuadratic →
      (riemannZeta β * χ.LFunction β * ψ₀.LFunction β * (χ.mul ψ₀).LFunction β).re ≤ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], N₀ < M → ∀ (χ : DirichletCharacter ℂ M),
      χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 → c * (M : ℝ) ^ (-ε) ≤ (χ.LFunction 1).re := by
  have h1β : 0 < 1 - β := sub_pos.mpr hβ34.2
  have hψ_re : 0 < (ψ₀.LFunction 1).re := (Complex.pos_iff.mp (LFunction_apply_one_pos hψq hψ1)).1
  have hN₀1 : (1 : ℝ) ≤ N₀ := Nat.one_le_cast.mpr NeZero.one_le
  have hε2 : 0 < ε / 2 := half_pos hε
  set K : ℝ := (ψ₀.LFunction 1).re * (1 + (ε / 2)⁻¹)
  set c : ℝ := (1 / 3360000000 : ℝ) * (1 - β) / K * (N₀ : ℝ) ^ (-ε)
  refine ⟨c, by positivity, fun M _ hNM χ hχp hχq hχ1 ↦ ?_⟩
  have hM1 : (1 : ℝ) ≤ M := Nat.one_le_cast.mpr NeZero.one_le
  have hMN1 : 1 ≤ (M : ℝ) * N₀ := by nlinarith
  have hMN_pos : 0 < (M : ℝ) * N₀ := by positivity
  have hgold := le_LFunction_one_re_of_nonpos hχq hψq hχ1 hψ1 (mul_ne_one_of_lt hχp hNM)
    hβ34.1 (hsign M hNM χ hχp hχq)
  have hrpow : ((M : ℝ) * N₀) ^ (-(ε / 2)) ≤ ((M : ℝ) * N₀) ^ (-8 * (1 - β)) :=
    Real.rpow_le_rpow_of_exponent_le hMN1 (by linarith)
  have hlog : 1 + Real.log ((M : ℝ) * N₀) ≤ (1 + (ε / 2)⁻¹) * ((M : ℝ) * N₀) ^ (ε / 2) :=
    one_add_log_le_mul_rpow hMN1 hε2
  have hlog_pos : 0 < 1 + Real.log ((M : ℝ) * N₀) :=
    add_pos_of_pos_of_nonneg one_pos (Real.log_nonneg hMN1)
  have hden : (ψ₀.LFunction 1).re * (1 + Real.log ((M : ℝ) * N₀)) ≤
      K * ((M : ℝ) * N₀) ^ (ε / 2) := by
    dsimp only [K]; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hlog hψ_re.le
  refine le_trans ?_ hgold
  have hdiv : (1 / 3360000000 : ℝ) * (1 - β) * ((M : ℝ) * N₀) ^ (-(ε / 2)) /
        (K * ((M : ℝ) * N₀) ^ (ε / 2)) ≤
      (1 / 3360000000 : ℝ) * (1 - β) * ((M : ℝ) * N₀) ^ (-8 * (1 - β)) /
        ((ψ₀.LFunction 1).re * (1 + Real.log ((M : ℝ) * N₀))) :=
    div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left hrpow (by positivity))
      (mul_pos hψ_re hlog_pos) hden
  refine le_trans ?_ hdiv
  rw [mul_comm K, ← div_div, mul_div_assoc, ← Real.rpow_sub hMN_pos,
    show -(ε / 2) - ε / 2 = -ε by ring, Real.mul_rpow (by positivity) (by positivity)]
  exact le_of_eq (by dsimp only [c]; ring)

private theorem exists_pos_forall_rpow_le_LFunction_one_re_of_isPrimitive {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M),
      χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 → c * (M : ℝ) ^ (-ε) ≤ (χ.LFunction 1).re := by
  set δ : ℝ := min ε 1 / 32
  have hδ0 : 0 < δ := by positivity
  have hδ_le1 : δ ≤ 1 / 32 := by
    dsimp only [δ]; linarith [min_le_right ε 1]
  have hδ_leε : δ ≤ ε / 32 := by
    dsimp only [δ]; linarith [min_le_left ε 1]
  obtain ⟨N₀, _, ψ₀, β, hψq, hψ1, hβ, hsign⟩ :=
    exists_aux_character (δ := δ) ⟨hδ0, by linarith⟩
  obtain ⟨c_large, hc_large, hlarge⟩ := exists_pos_forall_rpow_le_LFunction_one_re_of_lt hε
    hψq hψ1 ⟨by linarith [hβ.1], hβ.2⟩ (by linarith [hβ.1]) hsign
  obtain ⟨c_small, hc_small, hsmall⟩ := exists_pos_forall_le_LFunction_one_re_of_le N₀
  refine ⟨min c_large c_small, lt_min hc_large hc_small, fun M _ χ hχp hχq hχ1 ↦ ?_⟩
  rcases lt_or_ge N₀ M with hNM | hMN
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans
      (hlarge M hNM χ hχp hχq hχ1)
  · have hM1 : (1 : ℝ) ≤ M := Nat.one_le_cast.mpr NeZero.one_le
    have hrpow : (M : ℝ) ^ (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hM1 (by linarith)
    calc min c_large c_small * (M : ℝ) ^ (-ε)
        ≤ c_small * 1 := mul_le_mul (min_le_right _ _) hrpow (by positivity) hc_small.le
      _ = c_small := mul_one _
      _ ≤ (χ.LFunction 1).re := hsmall M hMN χ hχq hχ1

/-- **Siegel's theorem for quadratic Dirichlet `L`-functions.** For every `ε > 0` there exists
`c > 0` (ineffective) such that every nonprincipal quadratic Dirichlet character `χ` modulo `M ≥ 1`
satisfies `c * M ^ (-ε) ≤ Re L(1, χ)`. -/
theorem exists_pos_forall_rpow_le_LFunction_one_re {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M),
      χ.IsQuadratic → χ ≠ 1 → c * (M : ℝ) ^ (-ε) ≤ (χ.LFunction 1).re := by
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨c₀, hc₀, hprim⟩ := exists_pos_forall_rpow_le_LFunction_one_re_of_isPrimitive hε2
  obtain ⟨A, hA, hchg⟩ := exists_norm_LFunction_changeLevel_le_rpow one_pos hε2
  refine ⟨c₀ / A, div_pos hc₀ hA, fun M _ χ hχq hχ1 ↦ ?_⟩
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hχ₀q : χ.primitiveCharacter.IsQuadratic := by
    rw [← isQuadratic_changeLevel_iff χ.conductor_dvd_level, χ.changeLevel_primitiveCharacter]
    exact hχq
  have hχ₀1 : χ.primitiveCharacter ≠ 1 := fun h1 ↦ hχ1 (by
    rw [← χ.changeLevel_primitiveCharacter, h1, map_one])
  have hlo₀ := hprim χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hχ₀q hχ₀1
  have hcond_le : (χ.conductor : ℝ) ≤ M := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) χ.conductor_dvd_level
  have hcond_pos : (0 : ℝ) < χ.conductor :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.conductor_ne_zero)
  have hrpow : (M : ℝ) ^ (-(ε / 2)) ≤ (χ.conductor : ℝ) ^ (-(ε / 2)) :=
    Real.rpow_le_rpow_of_nonpos hcond_pos hcond_le (by linarith)
  have hχ₀_pos := Complex.pos_iff.mp (LFunction_apply_one_pos hχ₀q hχ₀1)
  have hχ_pos := Complex.pos_iff.mp (LFunction_apply_one_pos hχq hχ1)
  have hnorm₀ : ‖χ.primitiveCharacter.LFunction 1‖ = (χ.primitiveCharacter.LFunction 1).re := by
    rw [← Complex.abs_re_eq_norm.mpr hχ₀_pos.2.symm, abs_of_nonneg hχ₀_pos.1.le]
  have hnorm : ‖χ.LFunction 1‖ = (χ.LFunction 1).re := by
    rw [← Complex.abs_re_eq_norm.mpr hχ_pos.2.symm, abs_of_nonneg hχ_pos.1.le]
  have hcmp := (hchg χ.conductor M χ.primitiveCharacter χ.conductor_dvd_level 1
    (by simp) (.inl hχ₀1)).2
  rw [χ.changeLevel_primitiveCharacter, hnorm₀, hnorm] at hcmp
  have hM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  rw [← div_le_iff₀' (mul_pos hA (Real.rpow_pos_of_pos hM_pos (ε / 2)))] at hcmp
  refine le_trans ?_ hcmp
  have hstep : c₀ * (M : ℝ) ^ (-(ε / 2)) / (A * (M : ℝ) ^ (ε / 2)) ≤
      (χ.primitiveCharacter.LFunction 1).re / (A * (M : ℝ) ^ (ε / 2)) :=
    div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_left hrpow hc₀.le).trans hlo₀) (by positivity)
  refine le_trans ?_ hstep
  rw [mul_comm A, ← div_div, mul_div_assoc, ← Real.rpow_sub hM_pos,
    show -(ε / 2) - ε / 2 = -ε by ring]
  exact le_of_eq (by ring)

end DirichletCharacter

namespace TauCeti.Multiquadratic

/-- **Siegel's theorem for fundamental-discriminant characters.** For every `ε > 0` there exists
`c > 0` such that for every fundamental discriminant `D ≠ 1`, the associated complex quadratic
Dirichlet character `χ_D` of conductor `|D|` satisfies `c * |D| ^ (-ε) ≤ Re L(1, χ_D)`. -/
theorem exists_pos_forall_rpow_le_LFunction_one_re {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (D : ℤ) [NeZero D.natAbs] (hD : Int.IsFundamentalDiscr D), D ≠ 1 →
      c * |(D : ℝ)| ^ (-ε) ≤
        ((fundamentalDiscriminantCharCast ℂ D hD).LFunction 1).re := by
  obtain ⟨c, hc, hS⟩ := DirichletCharacter.exists_pos_forall_rpow_le_LFunction_one_re hε
  refine ⟨c, hc, fun D _ hD hD1 ↦ ?_⟩
  have h := hS D.natAbs (fundamentalDiscriminantCharCast ℂ D hD)
    (fundamentalDiscriminantCharCast_isQuadratic hD)
    (mt (fundamentalDiscriminantCharCast_eq_one_iff hD).mp hD1)
  rwa [Nat.cast_natAbs, Int.cast_abs] at h

end TauCeti.Multiquadratic
