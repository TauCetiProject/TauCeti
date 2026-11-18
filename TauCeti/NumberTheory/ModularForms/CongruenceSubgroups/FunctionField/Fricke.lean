/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Basic
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Weighted
import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Extension
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Degree
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Separation
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion

/-!
# The Fricke functions generate the function field of `X(N)`

For a residue vector `a ∈ (ℤ/Nℤ)²` the **Fricke function** is

`f_a(τ) = (2πi)⁻² · E₄(τ) E₆(τ) / Δ(τ) · N⁻² ℘((a₀ τ + a₁) / N; ℤ τ + ℤ)`

(`TauCeti.frickeFunction`), the weight-two division value
`TauCeti.EisensteinSeries.weightedG2 (Pi.single a 1)` multiplied by the weight `-2` level-one
factor `E₄ E₆ / Δ`, so that it has weight zero. This is the function of Shimura, §6.1, up to a
rational factor: there `f_a = g₂ g₃ / Δ · ℘(a)` with the unnormalized `g₂`, `g₃` and `Δ`, and
`g₂ g₃ / Δ` is a rational multiple of `π⁻² E₄ E₆ / Δ`; the factor `(2πi)⁻²` removes the
transcendental factor `(2πi)²` of the `q`-expansion of `℘`.

Since `℘` only sees the division point modulo the lattice, `f_a(γ τ) = f_{a γ}(τ)` for every
`γ ∈ SL(2, ℤ)` (`TauCeti.frickeFunction_smul`). In particular `f_a` is invariant under `Γ(N)`.
It is holomorphic on the upper half-plane, since `Δ` has no zeros, and grows at most like
`|q|⁻¹ = exp (2π Im τ)` at `i∞`, since `Δ / q → 1` while the other factors are bounded. The cusps
of `Γ(N)` are the orbits of the points `γ • ∞`, and at such a cusp `f_a` is read through
`f_a ∘ γ = f_{aγ}`, which has the same growth. Hence `f_a` descends to a meromorphic function on
the compactified modular curve `X(N)` (`TauCeti.frickeMeromorphicFunction`).

The action of `SL(2, ℤ/Nℤ)` on the function field of `X(N)` permutes the Fricke functions:
`g` sends `f_a` to `f_{a g}` (`TauCeti.unop_modularFunctionActionZMod_frickeMeromorphicFunction`).
At a point where `E₄ E₆` does not vanish the values of the `f_a` are proportional to the division
values, which separate the nonzero residues up to sign
(`TauCeti.EisensteinSeries.weightedG2_single_apply_eq_iff`). Consequently `f_a = f_b` for nonzero
`a`, `b` exactly when `a = ± b`, and `g` fixes every `f_a`, `a ≠ 0`, exactly when `g = ± 1`.
For `N = 2` the two signs coincide.

The function field of `X(N)` is a Galois extension of the fixed field `ℂ(j)` of the action, with
group the image of `SL(2, ℤ/Nℤ)` (Artin's theorem). The subgroup fixing all the `f_a`, `a ≠ 0`, is
trivial, so by the Galois correspondence

`ℂ(X(N)) = ℂ(j, f_a : a ≠ 0)`

(`TauCeti.adjoin_insert_image_frickeMeromorphicFunction_eq_top`). This exhibits explicit
generators of the function field, on which the action of `SL(2, ℤ/Nℤ)` is the permutation of the
residues.

## Main declarations

* `TauCeti.frickeFunction`: the Fricke function `f_a` on the upper half-plane, with its
  transformation law `TauCeti.frickeFunction_smul`, holomorphy
  `TauCeti.mdifferentiable_frickeFunction` and growth at `i∞`
  `TauCeti.isBigO_frickeFunction_atImInfty`.
* `TauCeti.frickeMeromorphicFunction`: `f_a` as a meromorphic function on `X(N)`, with its values
  `TauCeti.frickeMeromorphicFunction_ofQuotient_mk`.
* `TauCeti.unop_modularFunctionAction_frickeMeromorphicFunction` and
  `TauCeti.unop_modularFunctionActionZMod_frickeMeromorphicFunction`: `γ` sends `f_a` to `f_{aγ}`.
* `TauCeti.frickeMeromorphicFunction_eq_iff`: `f_a = f_b` exactly when `a = ± b`, for nonzero
  `a`, `b`.
* `TauCeti.forall_unop_modularFunctionActionZMod_frickeMeromorphicFunction_eq_iff`: `g` fixes
  every `f_a`, `a ≠ 0`, exactly when `g = ± 1`, with the level-two form
  `TauCeti.forall_unop_modularFunctionActionZMod_frickeMeromorphicFunction_eq_iff_level_two`.
* `TauCeti.adjoin_insert_image_frickeMeromorphicFunction_eq_top`: `j` and the `f_a`, `a ≠ 0`,
  generate the function field of `X(N)` over `ℂ`.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §6.1.
* Serge Lang, *Elliptic Functions*, 2nd ed., Graduate Texts in Mathematics 112, Springer, 1987,
  Chapter 6, §§2–3.
-/

public noncomputable section

open Asymptotics CongruenceSubgroup Filter MulOpposite UpperHalfPlane
open Subgroup.CompactifiedQuotient TauCeti.RiemannSurface
open scoped Manifold Matrix MatrixGroups Real

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-- **The Fricke function** `f_a` of a residue vector `a ∈ (ℤ/Nℤ)²`: the weight-two division
value `N⁻² ℘((a₀ τ + a₁) / N; ℤ τ + ℤ)` multiplied by the weight `-2` factor `E₄ E₆ / Δ` and
by `(2πi)⁻²`. It is a modular function of weight zero for `Γ(N)`. -/
def frickeFunction (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  ModularForm.E₄ τ * ModularForm.E₆ τ / _root_.ModularForm.discriminant τ *
    EisensteinSeries.weightedG2 (Pi.single a 1) τ / (2 * π * Complex.I) ^ 2

/-- The defining formula of the Fricke function. -/
theorem frickeFunction_def (a : Fin 2 → ZMod N) (τ : ℍ) :
    frickeFunction a τ =
      ModularForm.E₄ τ * ModularForm.E₆ τ / _root_.ModularForm.discriminant τ *
        EisensteinSeries.weightedG2 (Pi.single a 1) τ / (2 * π * Complex.I) ^ 2 :=
  (rfl)

/-- **The transformation law of the Fricke functions**: `f_a(γ τ) = f_{a γ}(τ)` for
`γ ∈ SL(2, ℤ)`, with `γ` acting on the residue row vector `a` through its reduction modulo
`N`. -/
theorem frickeFunction_smul (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ) :
    frickeFunction a (γ • τ) =
      frickeFunction (a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) τ := by
  have hd := denom_ne_zero γ τ
  have hΔ := _root_.ModularForm.discriminant_ne_zero τ
  have hγ : Matrix.SpecialLinearGroup.mapGL ℝ γ ∈ 𝒮ℒ := MonoidHom.mem_range.2 ⟨γ, rfl⟩
  have hG := congrFun (EisensteinSeries.weightedG2_single_slash a γ) τ
  rw [ModularForm.SL_slash_apply] at hG
  -- the level-one forms `E₄`, `E₆` and `Δ` transform with the automorphy factor `denom γ τ`
  have h₄ : ModularForm.E₄ (γ • τ) = denom γ τ ^ (4 : ℤ) * ModularForm.E₄ τ :=
    SlashInvariantForm.slash_action_eqn'' _ hγ τ
  have h₆ : ModularForm.E₆ (γ • τ) = denom γ τ ^ (6 : ℤ) * ModularForm.E₆ τ :=
    SlashInvariantForm.slash_action_eqn'' _ hγ τ
  have h₁₂ : _root_.ModularForm.discriminant (γ • τ) =
      denom γ τ ^ (12 : ℤ) * _root_.ModularForm.discriminant τ :=
    SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  rw [frickeFunction_def, frickeFunction_def, ← hG, h₄, h₆, h₁₂]
  field_simp

/-- The Fricke functions are holomorphic on the upper half-plane. -/
theorem mdifferentiable_frickeFunction (a : Fin 2 → ZMod N) : MDiff (frickeFunction a) := by
  have h := ((((ModularForm.holo' ModularForm.E₄).mul (ModularForm.holo' ModularForm.E₆)).div
    CuspForm.discriminant.holo' _root_.ModularForm.discriminant_ne_zero).mul
    (EisensteinSeries.weightedG2_mdifferentiable (Pi.single a 1))).mul
    (mdifferentiable_const (c := ((2 * π * Complex.I) ^ 2)⁻¹))
  convert h using 1
  ext τ
  simp [frickeFunction_def, div_eq_mul_inv]

/-- **Growth at `i∞`.** The Fricke functions are `O(|q|⁻¹) = O(exp (2π Im τ))` at `i∞`: the
factor `Δ⁻¹` is asymptotic to `q⁻¹`, and the other factors are bounded. -/
theorem isBigO_frickeFunction_atImInfty (a : Fin 2 → ZMod N) :
    frickeFunction a =O[atImInfty] fun τ ↦ Real.exp (2 * π * τ.im) := by
  have hE₄ := (EisensteinSeries.tendsto_E_atImInfty (k := 4)).isBigO_one ℝ
  have hE₆ := (EisensteinSeries.tendsto_E_atImInfty (k := 6)).isBigO_one ℝ
  have hG := EisensteinSeries.isBoundedAtImInfty_weightedG2 (Pi.single a (1 : ℂ))
  have hΔ := (ModularForm.tendsto_discriminant_div_qParam_atImInfty.inv₀ one_ne_zero).isBigO_one ℝ
  have hq : (fun τ : ℍ ↦ (Function.Periodic.qParam 1 (τ : ℂ))⁻¹) =O[atImInfty]
      fun τ ↦ Real.exp (2 * π * τ.im) :=
    isBigO_of_le _ fun τ ↦ by
      rw [norm_inv, Function.Periodic.norm_qParam, Real.norm_of_nonneg (Real.exp_pos _).le,
        ← Real.exp_neg]
      simp
  have h := ((((hE₄.mul hE₆).mul hG).mul hΔ).mul hq).const_mul_left ((2 * π * Complex.I) ^ 2)⁻¹
  refine h.congr' (.of_forall fun τ ↦ ?_) (.of_forall fun τ ↦ by simp)
  have hq₀ := Function.Periodic.qParam_ne_zero (h := 1) (τ : ℂ)
  have hΔ₀ := _root_.ModularForm.discriminant_ne_zero τ
  simp only [frickeFunction_def]
  field_simp

/-! ### The Fricke functions on `X(N)` -/

/-- The Fricke functions are invariant under the effective image of `Γ(N)`. -/
private theorem frickeFunction_smul_of_mem (a : Fin 2 → ZMod N) {g : PSL(2, ℝ)}
    (hg : g ∈ (Gamma N).map sl2zToPSL2R) (τ : ℍ) :
    frickeFunction a (g • τ) = frickeFunction a τ := by
  obtain ⟨γ, hγ, rfl⟩ := hg
  rw [UpperHalfPlane.sl2zToPSL2R_smul, frickeFunction_smul]
  simp [Gamma_mem'.mp hγ]

/-- `f_a` as a function on `X(N)`. Its value at the cusps is `0`; it only matters through its
germs there, which do not see it. -/
private def frickeCompactified (a : Fin 2 → ZMod N) :
    ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient → ℂ
  | .ofQuotient p => Quotient.lift (frickeFunction a) (fun _ _ h ↦ by
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
      exact frickeFunction_smul_of_mem a g.2 _) p
  | .ofCusp _ => 0

private theorem frickeCompactified_ofQuotient_mk (a : Fin 2 → ZMod N) (τ : ℍ) :
    frickeCompactified a (ofQuotient (Quotient.mk _ τ)) = frickeFunction a τ :=
  (rfl)

private theorem continuousAt_frickeCompactified_ofQuotient (a : Fin 2 → ZMod N)
    (p : MulAction.orbitRel.Quotient ((Gamma N).map sl2zToPSL2R) ℍ) :
    ContinuousAt (frickeCompactified a) (ofQuotient p) :=
  isOpenEmbedding_ofQuotient.continuousAt_iff.mp <| Continuous.continuousAt <|
    isQuotientMap_quotient_mk'.continuous_iff (g := frickeCompactified a ∘ ofQuotient) |>.mpr <|
      (mdifferentiable_frickeFunction a).continuous.congr fun τ ↦
        (frickeCompactified_ofQuotient_mk a τ).symm

/-- `f_a` is meromorphic on `X(N)`. At the cusp of `γ • ∞` it is read in the cusp datum of `∞`
transported by `γ`, where it is `f_{aγ}` and has at most a pole of order `N` in `q_N`. -/
private theorem meromorphicAt_frickeCompactified (a : Fin 2 → ZMod N)
    (x : ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) :
    RiemannSurface.MeromorphicAt (frickeCompactified a) x := by
  refine Fuchsian.meromorphicAt_of_forall_isBigO (frickeCompactified_ofQuotient_mk a)
    (fun τ ↦ meromorphicAt_of_eventually_mdifferentiableAt
      (.of_forall (mdifferentiable_frickeFunction a))) (fun C ↦ ?_) x
  obtain ⟨γ, rfl⟩ := (Gamma N).cuspOrbitOfSL2Z_surjective C
  refine ⟨(cuspDatumInftyGamma N).conj (conjAct_sl2zToPSL2R_smul_map_Gamma γ), N,
    Subtype.ext ?_, .of_forall fun τ ↦ mdifferentiable_frickeFunction a _, ?_⟩
  · rw [Subgroup.CuspDatum.cuspOrbit_val, Subgroup.cuspOrbitOfSL2Z_val,
      Subgroup.CuspDatum.conj_cusp, cuspDatumInftyGamma_cusp]
  · simp only [Subgroup.CuspDatum.conj_scaling, cuspDatumInftyGamma_scaling, one_mul, inv_inv,
      UpperHalfPlane.sl2zToPSL2R_smul, frickeFunction_smul, Subgroup.CuspDatum.conj_width,
      cuspDatumInftyGamma_width]
    refine (isBigO_frickeFunction_atImInfty _).congr_right fun τ ↦ ?_
    have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    rw [Int.cast_natCast]
    field_simp

/-- **The Fricke function `f_a` as a meromorphic function on `X(N)`**: the function whose value at
the orbit of `τ` is `f_a(τ)` (`TauCeti.frickeMeromorphicFunction_ofQuotient_mk`). -/
def frickeMeromorphicFunction (a : Fin 2 → ZMod N) :
    MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient :=
  MeromorphicFunction.ofMeromorphic (meromorphicAt_frickeCompactified a)

/-- The value of `f_a` at the orbit of `τ` is `f_a(τ)`. -/
@[simp]
theorem frickeMeromorphicFunction_ofQuotient_mk (a : Fin 2 → ZMod N) (τ : ℍ) :
    frickeMeromorphicFunction a (ofQuotient (Quotient.mk _ τ)) = frickeFunction a τ :=
  MeromorphicFunction.ofMeromorphic_apply_of_continuousAt _
    (continuousAt_frickeCompactified_ofQuotient a _)

/-- The finite part of `f_a` at the orbit of `τ` is `f_a(τ)`. -/
@[simp]
theorem finitePart_frickeMeromorphicFunction_ofQuotient_mk (a : Fin 2 → ZMod N) (τ : ℍ) :
    (frickeMeromorphicFunction a).finitePart (ofQuotient (Quotient.mk _ τ)) =
      frickeFunction a τ :=
  MeromorphicFunction.finitePart_of_eq_coe (frickeMeromorphicFunction_ofQuotient_mk a τ)

/-- **`SL(2, ℤ)` permutes the Fricke functions**: `γ` sends `f_a` to `f_{a γ}`. -/
theorem unop_modularFunctionAction_frickeMeromorphicFunction (γ : SL(2, ℤ))
    (a : Fin 2 → ZMod N) :
    unop (modularFunctionAction N γ) (frickeMeromorphicFunction a) =
      frickeMeromorphicFunction
        (a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) :=
  meromorphicFunction_ext fun τ ↦ by
    rw [modularFunctionAction_apply_ofQuotient, frickeMeromorphicFunction_ofQuotient_mk,
      frickeMeromorphicFunction_ofQuotient_mk, frickeFunction_smul]

/-- **`SL(2, ℤ/Nℤ)` permutes the Fricke functions**: `g` sends `f_a` to `f_{a g}`. -/
theorem unop_modularFunctionActionZMod_frickeMeromorphicFunction (g : SL(2, ZMod N))
    (a : Fin 2 → ZMod N) :
    unop (modularFunctionActionZMod N g) (frickeMeromorphicFunction a) =
      frickeMeromorphicFunction (a ᵥ* (g : Matrix (Fin 2) (Fin 2) (ZMod N))) := by
  obtain ⟨γ, rfl⟩ := Matrix.SpecialLinearGroup.map_intCast_zmod_surjective (d := N) g
  rw [modularFunctionActionZMod_map, unop_modularFunctionAction_frickeMeromorphicFunction]

/-! ### Separation and generation -/

/-- At some point of the upper half-plane the factor `E₄ E₆ / Δ` does not vanish, so the values
of the Fricke functions there are proportional to the division values. -/
private theorem exists_frickeFunction_eq_iff :
    ∃ τ : ℍ, ∀ a b : Fin 2 → ZMod N, frickeFunction a τ = frickeFunction b τ ↔
      EisensteinSeries.weightedG2 (Pi.single a 1) τ =
        EisensteinSeries.weightedG2 (Pi.single b 1) τ := by
  obtain ⟨τ, h₄, h₆⟩ := (((EisensteinSeries.tendsto_E_atImInfty (k := 4)).eventually_ne
    one_ne_zero).and ((EisensteinSeries.tendsto_E_atImInfty (k := 6)).eventually_ne
    one_ne_zero)).exists
  refine ⟨τ, fun a b ↦ ?_⟩
  have hc : ModularForm.E₄ τ * ModularForm.E₆ τ / _root_.ModularForm.discriminant τ ≠ 0 :=
    div_ne_zero (mul_ne_zero h₄ h₆) (_root_.ModularForm.discriminant_ne_zero τ)
  have hπ : ((2 * π * Complex.I) ^ 2 : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [frickeFunction_def, frickeFunction_def, div_left_inj₀ hπ, mul_right_inj' hc]

/-- Opposite residues give the same Fricke function. -/
@[simp]
theorem frickeFunction_neg (a : Fin 2 → ZMod N) : frickeFunction (-a) = frickeFunction a := by
  ext τ
  rw [frickeFunction_def, frickeFunction_def, EisensteinSeries.weightedG2_single_neg]

/-- Opposite residues give the same Fricke function on `X(N)`. -/
@[simp]
theorem frickeMeromorphicFunction_neg (a : Fin 2 → ZMod N) :
    frickeMeromorphicFunction (-a) = frickeMeromorphicFunction a :=
  meromorphicFunction_ext fun τ ↦ by simp

/-- **Separation of the Fricke functions.** For nonzero residues `a`, `b`, the Fricke functions
`f_a` and `f_b` agree exactly when `a = ± b`. -/
theorem frickeMeromorphicFunction_eq_iff {a b : Fin 2 → ZMod N} (ha : a ≠ 0) (hb : b ≠ 0) :
    frickeMeromorphicFunction a = frickeMeromorphicFunction b ↔ a = b ∨ a = -b := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨τ, hτ⟩ := exists_frickeFunction_eq_iff (N := N)
    have h' := congrArg (· (ofQuotient (Quotient.mk _ τ))) h
    simp only [frickeMeromorphicFunction_ofQuotient_mk, OnePoint.coe_eq_coe] at h'
    exact (EisensteinSeries.weightedG2_single_apply_eq_iff ha hb τ).mp ((hτ a b).mp h')
  · rintro (rfl | rfl) <;> simp

/-- **The common stabilizer of the Fricke functions is `±1`.** An element `g ∈ SL(2, ℤ/Nℤ)` fixes
every Fricke function `f_a`, `a ≠ 0`, exactly when `g = ± 1`. -/
theorem forall_unop_modularFunctionActionZMod_frickeMeromorphicFunction_eq_iff
    (g : SL(2, ZMod N)) :
    (∀ a : Fin 2 → ZMod N, a ≠ 0 →
      unop (modularFunctionActionZMod N g) (frickeMeromorphicFunction a) =
        frickeMeromorphicFunction a) ↔ g = 1 ∨ g = -1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨τ, hτ⟩ := exists_frickeFunction_eq_iff (N := N)
    have hGL : Matrix.SpecialLinearGroup.toGL (-1 : SL(2, ZMod N)) = -1 := Units.ext (by simp)
    rw [← Matrix.SpecialLinearGroup.toGL_inj, ← Matrix.SpecialLinearGroup.toGL_inj, map_one, hGL,
      ← Matrix.GeneralLinearGroup.forall_weightedG2_single_vecMul_apply_eq_iff _ τ]
    intro a ha
    have h' := congrArg (· (ofQuotient (Quotient.mk _ τ))) (h a ha)
    simp only [unop_modularFunctionActionZMod_frickeMeromorphicFunction,
      frickeMeromorphicFunction_ofQuotient_mk, OnePoint.coe_eq_coe] at h'
    simpa using (hτ _ _).mp h'
  · rintro (rfl | rfl) a _ <;> simp

/-- At level two, where `-1 = 1`, only the identity of `SL(2, ℤ/2ℤ)` fixes every Fricke function
`f_a`, `a ≠ 0`. -/
theorem forall_unop_modularFunctionActionZMod_frickeMeromorphicFunction_eq_iff_level_two
    (g : SL(2, ZMod 2)) :
    (∀ a : Fin 2 → ZMod 2, a ≠ 0 →
      unop (modularFunctionActionZMod 2 g) (frickeMeromorphicFunction a) =
        frickeMeromorphicFunction a) ↔ g = 1 := by
  have hneg : (-1 : SL(2, ZMod 2)) = 1 := by ext i j; simp [ZMod.neg_eq_self_mod_two]
  rw [forall_unop_modularFunctionActionZMod_frickeMeromorphicFunction_eq_iff, hneg, or_self]

/-- An automorphism of the function field of `X(N)` in the image of `SL(2, ℤ/Nℤ)` fixing every
Fricke function `f_a`, `a ≠ 0`, is the identity. -/
private theorem eq_one_of_mem_range_of_forall_frickeMeromorphicFunction
    {σ : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient ≃ₐ[ℂ]
      MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient}
    (hσ : σ ∈ (modularFunctionActionZMod N).range.unop)
    (h : ∀ a : Fin 2 → ZMod N, a ≠ 0 →
      σ (frickeMeromorphicFunction a) = frickeMeromorphicFunction a) : σ = 1 := by
  obtain ⟨g, hg⟩ := Subgroup.mem_unop.mp hσ
  rw [← unop_op σ, ← hg] at h ⊢
  rcases (forall_unop_modularFunctionActionZMod_frickeMeromorphicFunction_eq_iff g).mp h with
    rfl | rfl <;> simp

/-- **The Fricke functions generate the function field of `X(N)`**: the field of meromorphic
functions on `X(N)` is `ℂ(j, f_a : a ≠ 0)`, generated over `ℂ` by the modular invariant `j`,
pulled back from `X(1)`, and the Fricke functions of the nonzero residues. -/
theorem adjoin_insert_image_frickeMeromorphicFunction_eq_top :
    IntermediateField.adjoin ℂ (insert (Subgroup.compactifiedQuotientComap
        (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R ModularGroup.jMeromorphicFunction)
      (frickeMeromorphicFunction '' {a : Fin 2 → ZMod N | a ≠ 0})) = ⊤ := by
  set H := (modularFunctionActionZMod N).range.unop
  set M := MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient
  set S := frickeMeromorphicFunction '' {a : Fin 2 → ZMod N | a ≠ 0}
  -- `H` is finite, being the image of `SL(2, ℤ/Nℤ)`, so by Artin's theorem the function field is
  -- a finite Galois extension of the fixed field `ℂ(j)` (the instances
  -- `IntermediateField.finiteDimensional_fixedField` and `IntermediateField.isGalois_fixedField`).
  -- Every automorphism over `ℂ(j)` comes from `H`, so only the identity fixes all the `f_a`.
  have hfix :
      (IntermediateField.adjoin (IntermediateField.fixedField H) S).fixingSubgroup = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun σ hσ ↦ ?_
    obtain ⟨τ, rfl⟩ := FixedPoints.toAlgAut_surjective H M σ
    have hτ : (τ : M ≃ₐ[ℂ] M) = 1 := eq_one_of_mem_range_of_forall_frickeMeromorphicFunction τ.2
      fun a ha ↦ (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _
        (IntermediateField.subset_adjoin _ _ ⟨a, ha, rfl⟩)
    have hτ' : τ = 1 := Subtype.ext hτ
    rw [hτ']
    exact map_one _
  -- By the Galois correspondence `ℂ(j)(f_a : a ≠ 0)` is everything.
  have htop := IntermediateField.restrictScalars_adjoin ℂ (IntermediateField.fixedField H) S
  rw [← IsGalois.fixedField_fixingSubgroup
      (IntermediateField.adjoin (IntermediateField.fixedField H) S), hfix,
    IntermediateField.fixedField_bot, IntermediateField.restrictScalars_top,
    ← adjoin_coe_modularFunctionJ_eq_fixedField N ⊥, coe_modularFunctionJ] at htop
  refine eq_top_iff.mpr (htop.le.trans (IntermediateField.adjoin_le_iff.mpr ?_))
  rintro _ (hx | hx)
  · exact IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr
      (Set.mem_insert _ _)) hx
  · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ hx)

end TauCeti
