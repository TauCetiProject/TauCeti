/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.MulChar.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.Primitive
import TauCeti.NumberTheory.LSeries.Quadratic.Character
import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Estermann
import TauCeti.NumberTheory.LSeries.Quadratic.Pair.Sign

/-!
# Siegel's theorem for quadratic Dirichlet `L`-functions

For every `ε > 0`, there exists a positive constant `c` such that `Re L(1, χ) ≥ c q ^ (-ε)` for
every nonprincipal quadratic Dirichlet character `χ` modulo `q`
(`TauCeti.quadratic_LFunction_siegel`). Since `L(1, χ)` is a positive real number
(`DirichletCharacter.LFunction_apply_one_pos`), this bounds `L(1, χ)` itself away from zero
uniformly up to an arbitrarily small negative power of `q`.

Following Goldfeld's streamlining of Estermann's proof (Davenport, Chapter 21), the argument for
primitive characters splits by excluded middle according to whether any primitive nonprincipal
quadratic character has a real zero close to `1`:

1. **Zero-free alternative**
   (`DirichletCharacter.exists_pos_LFunction_one_re_ge_of_forall_LFunction_ne_zero`):
   if no primitive nonprincipal quadratic `L`-function vanishes on `(β₀, 1)`, pairing an arbitrary
   primitive quadratic character `ψ` with the Legendre character modulo `3` makes the four-factor
   product nonpositive at a fixed `β ∈ (β₀, 1)` close to `1`, and Estermann's comparison gives
   `Re L(1, ψ) ≫_ε N ^ (-ε)`.
2. **Exceptional-zero alternative**
   (`DirichletCharacter.exists_pos_LFunction_one_re_ge_of_LFunction_eq_zero`):
   for `δ(ε) ∈ (0, 1 / 2)` supplied by Estermann's theorem, if some primitive nonprincipal
   quadratic character `χ` has a zero `β ∈ [1 - δ, 1)`, pairing `ψ` with `χ` makes the four-factor
   product vanish at `β` whenever `χ.mul ψ ≠ 1`, while the equal-character case `χ.mul ψ = 1`
   reduces to the single positive value `L(1, χ)`.

Because the choice of `χ` and `β` in the second branch is nonconstructive, the resulting constant
`c(ε)` is ineffective. Finally, `DirichletCharacter.exists_norm_LFunction_changeLevel_le_rpow`
transfers the lower bound from primitive characters at `ε / 2` to arbitrary nonprincipal quadratic
characters of any positive level `q` at `ε`.

## Main results

* `DirichletCharacter.exists_pos_LFunction_one_re_ge_of_forall_LFunction_ne_zero`: uniform lower
  bound for `Re L(1, ψ)` assuming no primitive nonprincipal quadratic `L`-function vanishes on
  `(β₀, 1)`.
* `DirichletCharacter.exists_pos_LFunction_one_re_ge_of_LFunction_eq_zero`: uniform lower bound
  for `Re L(1, ψ)` obtained from a hypothetical real zero `β ∈ [1 - δ, 1)` of a primitive
  nonprincipal quadratic character.
* `TauCeti.quadratic_LFunction_siegel`: Siegel's theorem `Re L(1, χ) ≥ c q ^ (-ε)` for all
  nonprincipal quadratic characters `χ` of level `q`.

## References

* C. L. Siegel, *Über die Classenzahl quadratischer Zahlkörper*, Acta Arith. 1 (1935), 83–86.
* T. Estermann, *On Dirichlet's L functions*, J. London Math. Soc. 23 (1948), 275–279.
* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
* H. Davenport, *Multiplicative Number Theory*, Chapter 21.
-/

public section

open Complex
open scoped ComplexOrder

namespace DirichletCharacter

private theorem LFunction_ne_zero_of_forall_isPrimitive {N : ℕ} [NeZero N]
    {ρ : DirichletCharacter ℂ N} (hρq : ρ.IsQuadratic) (hρ1 : ρ ≠ 1)
    {σ : ℝ} (hσ0 : 0 < σ)
    (hzero : ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M),
      χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 → χ.LFunction σ ≠ 0) :
    ρ.LFunction σ ≠ 0 := by
  have : NeZero ρ.conductor := ⟨ρ.conductor_ne_zero⟩
  have hprim_q : ρ.primitiveCharacter.IsQuadratic :=
    (isQuadratic_changeLevel_iff ρ.conductor_dvd_level).mp
      (by rwa [ρ.changeLevel_primitiveCharacter])
  have hprim_1 : ρ.primitiveCharacter ≠ 1 := mt ρ.primitiveCharacter_eq_one_iff.mp hρ1
  have hne := hzero ρ.conductor ρ.primitiveCharacter ρ.primitiveCharacter_isPrimitive
    hprim_q hprim_1
  rw [← ρ.changeLevel_primitiveCharacter]
  exact mt (LFunction_changeLevel_eq_zero_iff ρ.primitiveCharacter ρ.conductor_dvd_level
    (by simpa using hσ0) (Or.inl hprim_1)).mp hne

/-- **Zero-free branch of Siegel's theorem.** If no primitive nonprincipal quadratic `L`-function
vanishes on `(β₀, 1)` for some `β₀ < 1`, then for every `ε > 0` there is a constant `c > 0` such
that `Re L(1, ψ) ≥ c N ^ (-ε)` for every primitive nonprincipal quadratic character `ψ` of
conductor `N`. -/
theorem exists_pos_LFunction_one_re_ge_of_forall_LFunction_ne_zero {β₀ : ℝ} (hβ₀ : β₀ < 1)
    (hzero : ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M),
      χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 → ∀ σ ∈ Set.Ioo β₀ 1, χ.LFunction σ ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N),
      ψ.IsPrimitive → ψ.IsQuadratic → ψ ≠ 1 → c * (N : ℝ) ^ (-ε) ≤ (ψ.LFunction 1).re := by
  obtain ⟨δ, ⟨hδ0, hδ12⟩, c₀, hc₀, hest⟩ := exists_pos_LFunction_one_re_ge_of_pair_re_nonpos hε
  let β : ℝ := max (1 - δ) ((max 0 β₀ + 1) / 2)
  have hβ_lt : β < 1 := max_lt (by linarith) (by linarith [max_lt zero_lt_one hβ₀])
  have hβ_pos : 0 < β := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hβ₀_lt : β₀ < β := lt_of_lt_of_le
    (by linarith [le_max_right 0 β₀] : β₀ < (max 0 β₀ + 1) / 2) (le_max_right _ _)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let χ₃ : DirichletCharacter ℂ 3 := (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)
  have hχ₃q : χ₃.IsQuadratic := (quadraticChar_isQuadratic (ZMod 3)).comp _
  have hχ₃1 : χ₃ ≠ 1 :=
    quadraticChar_ringHomComp_ne_one (by simp : ringChar ℂ ≠ 2) (by decide : 3 ≠ 2)
  have hχ₃p : χ₃.IsPrimitive := (isPrimitive_def χ₃).mpr <| by
    simpa [changeLevel_self] using conductor_changeLevel_quadraticChar
      (R := ℂ) (by simp : ringChar ℂ ≠ 2) (by decide : 3 ≠ 2) (dvd_refl 3)
  have hχ₃_pos : 0 < (χ₃.LFunction 1).re :=
    (Complex.pos_iff.mp (LFunction_apply_one_pos hχ₃q hχ₃1)).1
  have : 0 < 1 - β := sub_pos.mpr hβ_lt
  let c : ℝ := min (c₀ * (1 - β) * (3 : ℝ) ^ (-ε)) ((χ₃.LFunction 1).re * (3 : ℝ) ^ ε)
  refine ⟨c, lt_min (by positivity) (by positivity), fun N _ ψ hψp hψq hψ1 ↦ ?_⟩
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  by_cases hmul : χ₃.mul ψ = 1
  · obtain ⟨rfl, rfl⟩ := (hχ₃p.mul_eq_one_iff hψp hψq).mp hmul
    calc
      c * (3 : ℝ) ^ (-ε) ≤ ((χ₃.LFunction 1).re * (3 : ℝ) ^ ε) * (3 : ℝ) ^ (-ε) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = (χ₃.LFunction 1).re := by
        rw [mul_assoc, ← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero, mul_one]
  · have hpair : (riemannZeta β * χ₃.LFunction β * ψ.LFunction β *
        (χ₃.mul ψ).LFunction β).re ≤ 0 := by
      have hle := pair_nonpos_of_forall_ne_zero hχ₃q hψq hχ₃1 hψ1 hmul hβ_pos hβ_lt
        fun σ hσ ↦ ⟨hzero 3 χ₃ hχ₃p hχ₃q hχ₃1 σ ⟨hβ₀_lt.trans hσ.1, hσ.2⟩,
          hzero N ψ hψp hψq hψ1 σ ⟨hβ₀_lt.trans hσ.1, hσ.2⟩,
          LFunction_ne_zero_of_forall_isPrimitive (isQuadratic_mul hχ₃q hψq) hmul
            (hβ_pos.trans hσ.1) fun M _ ρ hρp hρq hρ1 ↦
              hzero M ρ hρp hρq hρ1 σ ⟨hβ₀_lt.trans hσ.1, hσ.2⟩⟩
      simpa using (Complex.le_def.mp hle).1
    calc
      c * (N : ℝ) ^ (-ε) ≤ (c₀ * (1 - β) * (3 : ℝ) ^ (-ε)) * (N : ℝ) ^ (-ε) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = c₀ * (1 - β) * ((3 : ℝ) * N) ^ (-ε) := by
        rw [Real.mul_rpow (by norm_num) hNpos.le]; ring
      _ ≤ (ψ.LFunction 1).re := hest χ₃ ψ hχ₃q hψq hχ₃1 hψ1 hmul ⟨le_max_left _ _, hβ_lt⟩ hpair

/-- **Exceptional-zero branch of Siegel's theorem.** For every `ε > 0`, there is `δ ∈ (0, 1 / 2)`
such that if a primitive nonprincipal quadratic character `χ` has a real zero `β ∈ [1 - δ, 1)`,
then there exists `c > 0` with `Re L(1, ψ) ≥ c N ^ (-ε)` for every primitive nonprincipal
quadratic character `ψ` of conductor `N`. -/
theorem exists_pos_LFunction_one_re_ge_of_LFunction_eq_zero {ε : ℝ} (hε : 0 < ε) :
    ∃ δ ∈ Set.Ioo (0 : ℝ) (1 / 2),
      ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M),
        χ.IsPrimitive → χ.IsQuadratic → χ ≠ 1 →
        ∀ {β : ℝ}, β ∈ Set.Ico (1 - δ) 1 → χ.LFunction β = 0 →
        ∃ c > 0, ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N),
          ψ.IsPrimitive → ψ.IsQuadratic → ψ ≠ 1 →
          c * (N : ℝ) ^ (-ε) ≤ (ψ.LFunction 1).re := by
  obtain ⟨δ, hδ, c₀, hc₀, hest⟩ := exists_pos_LFunction_one_re_ge_of_pair_re_nonpos hε
  refine ⟨δ, hδ, fun M _ χ hχp hχq hχ1 {β} hβ hz ↦ ?_⟩
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr (NeZero.pos M)
  have hχ_pos : 0 < (χ.LFunction 1).re := (Complex.pos_iff.mp (LFunction_apply_one_pos hχq hχ1)).1
  have : 0 < 1 - β := sub_pos.mpr hβ.2
  let c : ℝ := min (c₀ * (1 - β) * (M : ℝ) ^ (-ε)) ((χ.LFunction 1).re * (M : ℝ) ^ ε)
  refine ⟨c, lt_min (by positivity) (by positivity), fun N _ ψ hψp hψq hψ1 ↦ ?_⟩
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  by_cases hmul : χ.mul ψ = 1
  · obtain ⟨rfl, rfl⟩ := (hχp.mul_eq_one_iff hψp hψq).mp hmul
    calc
      c * (M : ℝ) ^ (-ε) ≤ ((χ.LFunction 1).re * (M : ℝ) ^ ε) * (M : ℝ) ^ (-ε) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = (χ.LFunction 1).re := by
        rw [mul_assoc, ← Real.rpow_add hMpos, add_neg_cancel, Real.rpow_zero, mul_one]
  · calc
      c * (N : ℝ) ^ (-ε) ≤ (c₀ * (1 - β) * (M : ℝ) ^ (-ε)) * (N : ℝ) ^ (-ε) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = c₀ * (1 - β) * ((M : ℝ) * N) ^ (-ε) := by
        rw [Real.mul_rpow hMpos.le hNpos.le]; ring
      _ ≤ (ψ.LFunction 1).re :=
        hest χ ψ hχq hψq hχ1 hψ1 hmul hβ (by simp [hz])

private theorem exists_pos_LFunction_one_re_ge_isPrimitive {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N),
      ψ.IsPrimitive → ψ.IsQuadratic → ψ ≠ 1 → c * (N : ℝ) ^ (-ε) ≤ (ψ.LFunction 1).re := by
  obtain ⟨δ, hδ, halt2⟩ := exists_pos_LFunction_one_re_ge_of_LFunction_eq_zero hε
  by_cases hex : ∃ (M : ℕ) (_ : NeZero M) (χ : DirichletCharacter ℂ M),
      χ.IsPrimitive ∧ χ.IsQuadratic ∧ χ ≠ 1 ∧ ∃ β ∈ Set.Ioo (1 - δ) 1, χ.LFunction β = 0
  · obtain ⟨M, _, χ, hχp, hχq, hχ1, β, hβ, hz⟩ := hex
    exact halt2 M χ hχp hχq hχ1 ⟨hβ.1.le, hβ.2⟩ hz
  · refine exists_pos_LFunction_one_re_ge_of_forall_LFunction_ne_zero
      (by linarith [hδ.1] : 1 - δ < 1) (fun M _ χ hχp hχq hχ1 σ hσ hz ↦ hex ?_) hε
    exact ⟨M, inferInstance, χ, hχp, hχq, hχ1, σ, hσ, hz⟩

end DirichletCharacter

namespace TauCeti

/-- **Siegel's theorem for quadratic Dirichlet `L`-functions.** For every `ε > 0`, there exists a
constant `c > 0` such that `Re L(1, χ) ≥ c q ^ (-ε)` for every nonprincipal quadratic Dirichlet
character `χ` of positive level `q`. Primitivity is not assumed; for a primitive character `χ`,
`q` is its conductor. -/
theorem quadratic_LFunction_siegel {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsQuadratic → χ ≠ 1 → c * (q : ℝ) ^ (-ε) ≤ (χ.LFunction 1).re := by
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨c₁, hc₁, hprim⟩ := DirichletCharacter.exists_pos_LFunction_one_re_ge_isPrimitive hε2
  obtain ⟨A, hA, hchg⟩ :=
    DirichletCharacter.exists_norm_LFunction_changeLevel_le_rpow one_pos hε2
  refine ⟨c₁ / A, div_pos hc₁ hA, fun q _ χ hχq hχ1 ↦ ?_⟩
  let M := χ.conductor
  have : NeZero M := ⟨χ.conductor_ne_zero⟩
  let χ₀ := χ.primitiveCharacter
  have hχ₀q : χ₀.IsQuadratic :=
    (DirichletCharacter.isQuadratic_changeLevel_iff χ.conductor_dvd_level).mp
      (by rwa [χ.changeLevel_primitiveCharacter])
  have hχ₀1 : χ₀ ≠ 1 := mt χ.primitiveCharacter_eq_one_iff.mp hχ1
  have hMq : (M : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr (NeZero.pos M)
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hχ₀_pos := Complex.pos_iff.mp (DirichletCharacter.LFunction_apply_one_pos hχ₀q hχ₀1)
  have hχ_pos := Complex.pos_iff.mp (DirichletCharacter.LFunction_apply_one_pos hχq hχ1)
  have hnorm_χ₀ : ‖χ₀.LFunction 1‖ = (χ₀.LFunction 1).re := by
    rw [← Complex.abs_re_eq_norm.mpr hχ₀_pos.2.symm, abs_of_pos hχ₀_pos.1]
  have hnorm_χ : ‖χ.LFunction 1‖ = (χ.LFunction 1).re := by
    rw [← Complex.abs_re_eq_norm.mpr hχ_pos.2.symm, abs_of_pos hχ_pos.1]
  have hstep1 : c₁ * (q : ℝ) ^ (-(ε / 2)) ≤ (χ₀.LFunction 1).re :=
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hMpos hMq (by linarith)) hc₁.le).trans
      (hprim M χ₀ χ.primitiveCharacter_isPrimitive hχ₀q hχ₀1)
  have hstep2 : (χ₀.LFunction 1).re ≤ A * (q : ℝ) ^ (ε / 2) * (χ.LFunction 1).re := by
    have hb := (hchg M q χ₀ χ.conductor_dvd_level 1 (by simp) (Or.inl hχ₀1)).2
    rwa [χ.changeLevel_primitiveCharacter, hnorm_χ₀, hnorm_χ] at hb
  have hcomb := hstep1.trans hstep2
  rw [div_mul_eq_mul_div, div_le_iff₀ hA]
  calc
    c₁ * (q : ℝ) ^ (-ε) = c₁ * (q : ℝ) ^ (-(ε / 2)) * (q : ℝ) ^ (-(ε / 2)) := by
      have hexp : -ε = -(ε / 2) + -(ε / 2) := by ring
      rw [hexp, Real.rpow_add hqpos, mul_assoc]
    _ ≤ (A * (q : ℝ) ^ (ε / 2) * (χ.LFunction 1).re) * (q : ℝ) ^ (-(ε / 2)) :=
      mul_le_mul_of_nonneg_right hcomb (by positivity)
    _ = (χ.LFunction 1).re * A * ((q : ℝ) ^ (ε / 2) * (q : ℝ) ^ (-(ε / 2))) := by ring
    _ = (χ.LFunction 1).re * A := by
      rw [← Real.rpow_add hqpos, add_neg_cancel, Real.rpow_zero, mul_one]

end TauCeti
