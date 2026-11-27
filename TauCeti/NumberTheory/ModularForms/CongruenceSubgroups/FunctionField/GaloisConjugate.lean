/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.QExpansion.Laurent
public import TauCeti.NumberTheory.ModularForms.WeakForm
import TauCeti.Analysis.SpecialFunctions.Complex.CircleAddChar
import TauCeti.LinearAlgebra.Matrix.Diagonal
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Holomorphic
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Invariant
import TauCeti.NumberTheory.ModularForms.DedekindEta.Basic
import TauCeti.NumberTheory.ModularForms.DedekindEta.Galois
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion

/-!
# Galois conjugates of modular forms of level `N`

Let `σ` be an automorphism of `ℂ`; it need not be continuous. For a modular form
`f = ∑ aₙ qⁿ` of weight `k` on `Γ(N)`, expanded at `∞` in `q = exp (2 π i τ / N)`, there is a
modular form of weight `k` on `Γ(N)` with expansion `∑ σ(aₙ) qⁿ`
(`ModularForm.exists_qExpansion_eq_map`); if `f` is a cusp form, so is this conjugate
(`CuspForm.exists_qExpansion_eq_map`), and the same holds for weak forms, which may have poles at
the cusps (`TauCeti.IsWeakForm.exists_laurentQExpansion_eq_mapRingHom`). As `σ` is not continuous,
the conjugate is not computed from the values of `f`. It is obtained from the action of `σ` on
the field `ℂ(X(M))` of modular functions of level `M` through their Fourier coefficients
(`TauCeti.modularFunctionCoeffAction`), which preserves the functions without poles on `ℍ`
(`TauCeti.forall_ne_infty_modularFunctionCoeffAction_iff`).

**Construction.** Put `M = 12 N`. The quotient `u = f / η^{2k}` has weight zero and is invariant
under `Γ(M)`, on which `η^{2k}` is invariant in weight `k`; since `η` has no zeros on `ℍ`, `u` is
an element of `ℂ(X(M))` without poles on `ℍ`, and so is its conjugate `u^σ`. The conjugate of
`f` is `c η^{2k} u^σ`, holomorphic on `ℍ`. The constant `c` corrects the expansion of `η^{2k}`,
which `σ` multiplies by a twelfth root of unity: its twelfth power is the expansion of `Δ^k`,
whose coefficients are integers.

**Modularity.** Let `σ (ζ_M) = ζ_M ^ d` and, for `γ ∈ SL(2, ℤ)`, let
`γ' ≡ diag(1, d) γ diag(1, d)⁻¹` modulo `M`. The coefficient action is twisted by `diag(1, d)`
under fractional linear maps (`TauCeti.modularFunctionCoeffAction_unop_modularFunctionActionZMod`),
so the translate by `γ` of the conjugate of `f` is the conjugate of `f ∣[k] γ'`: the multiplier
`σ(ε(γ')^{2k})` that `σ` puts on `u` is the multiplier `ε(γ)^{2k}` of `η^{2k}`
(`TauCeti.ModularForm.etaMultiplier_sq_eq_of_mul_diagonal_eq`). For `γ ∈ Γ(N)` also `γ' ∈ Γ(N)`,
so the conjugate is invariant under `Γ(N)`; and its expansion at every cusp is the conjugate of an
expansion of `f` at another cusp, so it is bounded, or vanishes, at every cusp when `f` is.

## Main results

* `TauCeti.IsWeakForm.exists_laurentQExpansion_eq_mapRingHom`: the conjugate of a weak form on
  `Γ(N)`.
* `ModularForm.exists_qExpansion_eq_map`: the conjugate of a modular form on `Γ(N)`.
* `CuspForm.exists_qExpansion_eq_map`: the conjugate of a cusp form on `Γ(N)`.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §§6.1–6.2, for the action of `Aut(ℂ)` on modular functions of level
  `N` through their Fourier coefficients, which this file extends to forms of weight `k`.
-/

public noncomputable section

open CongruenceSubgroup MulOpposite Subgroup.CompactifiedQuotient UpperHalfPlane Filter
open TauCeti.RiemannSurface Asymptotics OnePoint
open scoped MatrixGroups ModularForm Real Manifold Topology

namespace TauCeti

variable {N : ℕ} {k : ℤ} {f : ℍ → ℂ}

/-- The transformation of `f / η ^ (2 k)` under `γ ∈ SL(2, ℤ)`: it is `ε(γ) ^ (-2 k)` times
`(f ∣[k] γ) / η ^ (2 k)`. -/
private theorem div_eta_zpow_smul (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    f (γ • τ) / η (γ • τ : ℍ) ^ (2 * k) =
      (ModularForm.etaMultiplier γ ^ (2 * k))⁻¹ * ((f ∣[k] γ) τ / η τ ^ (2 * k)) := by
  have hden : ((γ 1 0 : ℂ) * τ + γ 1 1) ≠ 0 := UpperHalfPlane.denom_ne_zero γ τ
  have hη : η (τ : ℂ) ^ (2 * k) ≠ 0 := zpow_ne_zero _ (_root_.ModularForm.eta_ne_zero τ.im_pos)
  have hε := zpow_ne_zero (2 * k) (ModularForm.etaMultiplier_ne_zero γ)
  rw [ModularForm.eta_smul_zpow_two_mul, _root_.ModularForm.SL_slash_apply,
    ModularGroup.denom_apply, zpow_neg]
  field_simp

/-- `f / η ^ (2 k)` is holomorphic when `f` is. -/
private theorem mdifferentiable_div_eta_zpow (hf : MDiff f) :
    MDiff fun τ : ℍ ↦ f τ / η τ ^ (2 * k) := by
  have h := hf.mul (ModularForm.mdifferentiable_eta_zpow (-(2 * k)))
  convert h using 1
  funext τ
  rw [Pi.mul_apply, zpow_neg, div_eq_mul_inv]

/-- For a weak form `f` of weight `k` on `Γ(N)`, the translates of `f / η ^ (2 k)` grow at most
exponentially at `i∞`. -/
private theorem exists_isBigO_div_eta_zpow_smul (hf : IsWeakForm (Gamma N) k f) (γ : SL(2, ℤ)) :
    ∃ c : ℝ, (fun τ : ℍ ↦ f (γ • τ) / η (γ • τ : ℍ) ^ (2 * k)) =O[atImInfty]
      fun τ ↦ Real.exp (c * τ.im) := by
  obtain ⟨C, hC⟩ := hf.exists_isBigO_exp γ
  have h := (hC.mul (ModularForm.isBigO_eta_zpow_atImInfty (-(2 * k)))).const_mul_left
    (ModularForm.etaMultiplier γ ^ (2 * k))⁻¹
  refine ⟨C + -(π * ((-(2 * k) : ℤ) : ℝ) / 12), h.congr (fun τ ↦ ?_) fun τ ↦ ?_⟩
  · rw [div_eta_zpow_smul, zpow_neg, div_eq_mul_inv]
  · rw [← Real.exp_add]
    ring_nf

variable [NeZero N]

variable (k) in
/-- **The modular function `f / η ^ (2 k)` of level `12 N`.** For a weak form `f` of weight `k`
on `Γ(N)`, the quotient `f / η ^ (2 k)` has weight zero and is invariant under `Γ(12 N)`, since
`η ^ (2 k)` is invariant there in weight `k`; it is holomorphic on the upper half-plane and of
exponential growth at every cusp. -/
private def divEtaZPow (hf : IsWeakForm (Gamma N) k f) :
    MeromorphicFunction ((Gamma (12 * N)).map sl2zToPSL2R).CompactifiedQuotient :=
  meromorphicFunctionOfGammaInvariant (fun τ ↦ f τ / η τ ^ (2 * k))
    (mdifferentiable_div_eta_zpow hf.mdifferentiable)
    (fun γ hγ τ ↦ by
      rw [div_eta_zpow_smul, hf.slash_eq γ (Gamma_le_Gamma_of_dvd (dvd_mul_left N 12) hγ),
        ModularForm.etaMultiplier_zpow_eq_one_of_mem_Gamma (even_two_mul k)
          ⟨k * N, by push_cast; ring⟩ hγ, inv_one, one_mul])
    (exists_isBigO_div_eta_zpow_smul hf)

private theorem divEtaZPow_ofQuotient_mk (hf : IsWeakForm (Gamma N) k f) (τ : ℍ) :
    divEtaZPow k hf (ofQuotient (Quotient.mk _ τ)) = ((f τ / η τ ^ (2 * k) : ℂ) : OnePoint ℂ) :=
  meromorphicFunctionOfGammaInvariant_ofQuotient_mk _ _ _ τ

/-- **Fractional linear maps on `f / η ^ (2 k)`.** Composing `f / η ^ (2 k)` with `γ ∈ SL(2, ℤ)`
gives `ε(γ) ^ (-2 k)` times the quotient `(f ∣[k] γ) / η ^ (2 k)`. -/
private theorem unop_modularFunctionAction_divEtaZPow (hf : IsWeakForm (Gamma N) k f)
    (γ : SL(2, ℤ)) :
    unop (modularFunctionAction (12 * N) γ) (divEtaZPow k hf) =
      algebraMap ℂ _ (ModularForm.etaMultiplier γ ^ (2 * k))⁻¹ *
        divEtaZPow k (hf.slash_of_normal γ) :=
  meromorphicFunction_ext fun τ ↦ by
    rw [modularFunctionAction_apply_ofQuotient, divEtaZPow_ofQuotient_mk,
      MeromorphicFunction.mul_apply_of_eq_coe (by rw [MeromorphicFunction.coe_algebraMap])
        (divEtaZPow_ofQuotient_mk _ τ), div_eta_zpow_smul]

/-- The conjugate `(f / η ^ (2 k))^σ` has no pole on the upper half-plane. -/
private theorem coeffAction_divEtaZPow_ne_infty (σ : ℂ ≃+* ℂ) (hf : IsWeakForm (Gamma N) k f)
    (τ : ℍ) :
    modularFunctionCoeffAction (12 * N) σ (divEtaZPow k hf) (ofQuotient (Quotient.mk _ τ)) ≠ ∞ :=
  (forall_ne_infty_modularFunctionCoeffAction_iff σ _).2
    (fun τ ↦ by rw [divEtaZPow_ofQuotient_mk]; exact OnePoint.coe_ne_infty _) τ

variable (k) in
/-- The function `η ^ (2 k) (f / η ^ (2 k))^σ` on the upper half-plane, which is the conjugate of
`f` up to a twelfth root of unity. -/
private def conjAux (σ : ℂ ≃+* ℂ) (hf : IsWeakForm (Gamma N) k f) (τ : ℍ) : ℂ :=
  η τ ^ (2 * k) * (modularFunctionCoeffAction (12 * N) σ (divEtaZPow k hf)).finitePart
    (ofQuotient (Quotient.mk _ τ))

private theorem conjAux_def (σ : ℂ ≃+* ℂ) (hf : IsWeakForm (Gamma N) k f) :
    conjAux k σ hf = (fun τ : ℍ ↦ η τ ^ (2 * k)) * fun τ ↦
      (modularFunctionCoeffAction (12 * N) σ (divEtaZPow k hf)).finitePart
        (ofQuotient (Quotient.mk _ τ)) :=
  rfl

private theorem mdifferentiable_conjAux (σ : ℂ ≃+* ℂ) (hf : IsWeakForm (Gamma N) k f) :
    MDiff (conjAux k σ hf) :=
  conjAux_def σ hf ▸ (ModularForm.mdifferentiable_eta_zpow (2 * k)).mul fun τ ↦
    (MeromorphicFunction.mdifferentiableAt_finitePart
      (coeffAction_divEtaZPow_ne_infty σ hf τ)).comp τ
        ((mdifferentiable_ofQuotient _).comp τ (Subgroup.mdifferentiable_quotientMk _ τ))

/-- **The translates of the conjugate.** Let `σ (ζ_{12N}) = ζ_{12N} ^ d` and let
`γ' diag(1, d) = diag(1, d) γ` modulo `12 N`. Then the translate by `γ` of the conjugate of `f` is
the conjugate of the translate `f ∣[k] γ'`: the twist `σ (ε(γ') ^ (2 k))` that `σ` puts on the
transformation of `f / η ^ (2 k)` is the factor `ε(γ) ^ (2 k)` of `η ^ (2 k)`. -/
private theorem conjAux_slash {σ : ℂ ≃+* ℂ} {d : (ZMod (12 * N))ˣ}
    (hσ : σ (ZMod.stdAddChar (1 : ZMod (12 * N))) = ZMod.stdAddChar (d : ZMod (12 * N)))
    (hf : IsWeakForm (Gamma N) k f) {γ γ' : SL(2, ℤ)}
    (h : ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (12 * N))) γ' :
        SL(2, ZMod (12 * N))) : Matrix (Fin 2) (Fin 2) (ZMod (12 * N))) *
          Matrix.diagonal ![1, (d : ZMod (12 * N))] =
        Matrix.diagonal ![1, (d : ZMod (12 * N))] *
          (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (12 * N))) γ)) :
    conjAux k σ hf ∣[k] γ = conjAux k σ (hf.slash_of_normal γ') := by
  have hw (τ : ℍ) :
      (modularFunctionCoeffAction (12 * N) σ (divEtaZPow k hf)).finitePart
          (ofQuotient (Quotient.mk _ (γ • τ))) =
        (σ (ModularForm.etaMultiplier γ' ^ (2 * k)))⁻¹ *
          (modularFunctionCoeffAction (12 * N) σ (divEtaZPow k (hf.slash_of_normal γ'))).finitePart
            (ofQuotient (Quotient.mk _ τ)) := by
    refine MeromorphicFunction.finitePart_of_eq_coe ?_
    rw [← modularFunctionAction_apply_ofQuotient γ, ← modularFunctionActionZMod_map,
      ← modularFunctionCoeffAction_unop_modularFunctionActionZMod hσ h,
      modularFunctionActionZMod_map, unop_modularFunctionAction_divEtaZPow, map_mul,
      modularFunctionCoeffAction_algebraMap, map_inv₀]
    exact MeromorphicFunction.mul_apply_of_eq_coe (by rw [MeromorphicFunction.coe_algebraMap])
      (MeromorphicFunction.coe_finitePart (coeffAction_divEtaZPow_ne_infty σ _ τ)).symm
  have hε : ModularForm.etaMultiplier γ ^ (2 * k) =
      σ (ModularForm.etaMultiplier γ' ^ (2 * k)) := by
    rw [zpow_mul, zpow_mul, zpow_ofNat, zpow_ofNat, map_zpow₀,
      ModularForm.etaMultiplier_sq_eq_of_mul_diagonal_eq (dvd_mul_right 12 N)
        (σ := (σ : ℂ →+* ℂ)) hσ h, RingHom.coe_coe]
  ext τ
  have hden : ((γ 1 0 : ℂ) * τ + γ 1 1) ≠ 0 := UpperHalfPlane.denom_ne_zero γ τ
  have hε₀ : σ (ModularForm.etaMultiplier γ' ^ (2 * k)) ≠ 0 :=
    (map_ne_zero σ).2 (zpow_ne_zero _ (ModularForm.etaMultiplier_ne_zero γ'))
  rw [_root_.ModularForm.SL_slash_apply, conjAux, conjAux, hw, ModularForm.eta_smul_zpow_two_mul,
    hε, ModularGroup.denom_apply, zpow_neg]
  field_simp

/-! ### Laurent expansions at `∞` -/

omit [NeZero N] in
/-- `η ^ (2 k)` has period `12 N`: `η(τ + 1) = e^{π i / 12} η(τ)`. -/
private theorem periodic_eta_zpow :
    Function.Periodic ((fun τ : ℍ ↦ η τ ^ (2 * k)) ∘ ofComplex) ((12 * N : ℕ) : ℝ) :=
  UpperHalfPlane.periodic_comp_ofComplex fun τ ↦ by
    have h := ModularForm.eta_add_intCast (τ : ℂ) (12 * N)
    rw [UpperHalfPlane.coe_vadd]
    push_cast at h ⊢
    rw [add_comm, h, mul_zpow, ← Complex.exp_intCast_mul]
    convert one_mul _ using 2
    convert Complex.exp_int_mul_two_pi_mul_I (N * k) using 2
    push_cast
    ring

private theorem twelve_mul_pos : (0 : ℝ) < ((12 * N : ℕ) : ℝ) := by
  have := NeZero.pos N
  positivity

/-- The cusp function of `η ^ (2 k)` at period `12 N` is meromorphic at `0`, since `η ^ (2 k)`
grows at most exponentially. -/
private theorem meromorphicAt_cuspFunction_eta_zpow :
    _root_.MeromorphicAt (cuspFunction ((12 * N : ℕ) : ℝ) fun τ : ℍ ↦ η τ ^ (2 * k)) 0 :=
  UpperHalfPlane.meromorphicAt_cuspFunction_of_isBigO_exp twelve_mul_pos periodic_eta_zpow
    (.of_forall (ModularForm.mdifferentiable_eta_zpow _))
    (ModularForm.isBigO_eta_zpow_atImInfty (2 * k))

/-- The pullback to the upper half-plane of a meromorphic function on `X(12 N)`. -/
private theorem laurentQExpansion_cuspDatumInftyGamma
    (F : MeromorphicFunction ((Gamma (12 * N)).map sl2zToPSL2R).CompactifiedQuotient) :
    Subgroup.CompactifiedQuotient.laurentQExpansion (cuspDatumInftyGamma (12 * N)) F =
      TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ)
        fun τ ↦ F.finitePart (ofQuotient (Quotient.mk _ τ)) := by
  simpa using Subgroup.CompactifiedQuotient.laurentQExpansion_apply (cuspDatumInftyGamma (12 * N)) F

private theorem meromorphicAt_cuspFunction_finitePart_ofQuotient
    (F : MeromorphicFunction ((Gamma (12 * N)).map sl2zToPSL2R).CompactifiedQuotient) :
    _root_.MeromorphicAt (cuspFunction ((12 * N : ℕ) : ℝ)
      fun τ ↦ F.finitePart (ofQuotient (Quotient.mk _ τ))) 0 := by
  simpa using Subgroup.CompactifiedQuotient.meromorphicAt_cuspFunction_finitePart
    (cuspDatumInftyGamma (12 * N)) F

private theorem periodic_finitePart_ofQuotient
    (F : MeromorphicFunction ((Gamma (12 * N)).map sl2zToPSL2R).CompactifiedQuotient) :
    Function.Periodic ((fun τ ↦ F.finitePart (ofQuotient (Quotient.mk _ τ))) ∘ ofComplex)
      ((12 * N : ℕ) : ℝ) := by
  simpa using Subgroup.CompactifiedQuotient.periodic_finitePart (cuspDatumInftyGamma (12 * N)) F

private theorem finitePart_divEtaZPow (hf : IsWeakForm (Gamma N) k f) (τ : ℍ) :
    (divEtaZPow k hf).finitePart (ofQuotient (Quotient.mk _ τ)) = f τ / η τ ^ (2 * k) :=
  MeromorphicFunction.finitePart_of_eq_coe (divEtaZPow_ofQuotient_mk hf τ)

/-- A weak form on `Γ(N)` is the product of `η ^ (2 k)` and the pullback of `f / η ^ (2 k)`. -/
private theorem eq_eta_zpow_mul_finitePart (hf : IsWeakForm (Gamma N) k f) :
    f = (fun τ : ℍ ↦ η τ ^ (2 * k)) *
      fun τ ↦ (divEtaZPow k hf).finitePart (ofQuotient (Quotient.mk _ τ)) := by
  funext τ
  rw [Pi.mul_apply, finitePart_divEtaZPow,
    mul_div_cancel₀ _ (zpow_ne_zero _ (_root_.ModularForm.eta_ne_zero τ.im_pos))]

/-- The Laurent expansion at period `12 N` of a weak form on `Γ(N)` factors through
`f = η ^ (2 k) (f / η ^ (2 k))`. -/
private theorem laurentQExpansion_eq_mul (hf : IsWeakForm (Gamma N) k f) :
    TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ) f =
      TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ) (fun τ : ℍ ↦ η τ ^ (2 * k)) *
        Subgroup.CompactifiedQuotient.laurentQExpansion (cuspDatumInftyGamma (12 * N))
          (divEtaZPow k hf) := by
  conv_lhs => rw [eq_eta_zpow_mul_finitePart hf]
  rw [TauCeti.UpperHalfPlane.laurentQExpansion_mul meromorphicAt_cuspFunction_eta_zpow
    (meromorphicAt_cuspFunction_finitePart_ofQuotient _), laurentQExpansion_cuspDatumInftyGamma]

private theorem laurentQExpansion_conjAux (σ : ℂ ≃+* ℂ) (hf : IsWeakForm (Gamma N) k f) :
    TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ) (conjAux k σ hf) =
      TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ) (fun τ : ℍ ↦ η τ ^ (2 * k)) *
        HahnSeries.mapRingHom (σ : ℂ →+* ℂ)
          (Subgroup.CompactifiedQuotient.laurentQExpansion (cuspDatumInftyGamma (12 * N))
            (divEtaZPow k hf)) := by
  rw [← laurentQExpansion_modularFunctionCoeffAction, laurentQExpansion_cuspDatumInftyGamma,
    ← TauCeti.UpperHalfPlane.laurentQExpansion_mul meromorphicAt_cuspFunction_eta_zpow
      (meromorphicAt_cuspFunction_finitePart_ofQuotient _), conjAux_def]

private theorem meromorphicAt_cuspFunction_conjAux (σ : ℂ ≃+* ℂ) (hf : IsWeakForm (Gamma N) k f) :
    _root_.MeromorphicAt (cuspFunction ((12 * N : ℕ) : ℝ) (conjAux k σ hf)) 0 :=
  conjAux_def σ hf ▸ UpperHalfPlane.meromorphicAt_cuspFunction_mul
    meromorphicAt_cuspFunction_eta_zpow (meromorphicAt_cuspFunction_finitePart_ofQuotient _)

private theorem periodic_conjAux (σ : ℂ ≃+* ℂ) (hf : IsWeakForm (Gamma N) k f) :
    Function.Periodic (conjAux k σ hf ∘ ofComplex) ((12 * N : ℕ) : ℝ) :=
  conjAux_def σ hf ▸ periodic_eta_zpow.mul (periodic_finitePart_ofQuotient _)

omit [NeZero N] in
/-- The coefficient map `σ` fixes the expansion at period `12 N` of a power of the discriminant,
whose `q`-expansion has integer coefficients. -/
private theorem mapRingHom_expand_discriminant_zpow (σ : ℂ →+* ℂ) (d : ℕ+) :
    HahnSeries.mapRingHom σ (LaurentSeries.expand ℂ d
        ((qExpansion 1 CuspForm.discriminant : LaurentSeries ℂ) ^ k)) =
      LaurentSeries.expand ℂ d ((qExpansion 1 CuspForm.discriminant : LaurentSeries ℂ) ^ k) := by
  have hq : PowerSeries.map σ (qExpansion 1 CuspForm.discriminant) =
      qExpansion 1 CuspForm.discriminant := by
    ext n
    obtain ⟨m, hm⟩ := ModularForm.exists_discriminant_qExpansion_coeff_eq_intCast n
    rw [PowerSeries.coeff_map, CuspForm.coe_discriminant] at *
    rw [hm, map_intCast]
  rw [LaurentSeries.mapRingHom_expand, map_zpow₀, HahnSeries.mapRingHom_apply,
    HahnSeries.map_ofPowerSeries, hq]

/-- **The conjugate of the expansion of `η ^ (2 k)`.** Applying `σ` to the coefficients of the
expansion of `η ^ (2 k)` at period `12 N` multiplies it by a constant: the twelfth power
of that expansion is the expansion of `Δ ^ k`, which has integer coefficients, so the ratio is a
twelfth root of unity. -/
private theorem exists_mapRingHom_laurentQExpansion_eta_zpow (σ : ℂ →+* ℂ) :
    ∃ c : ℂ, HahnSeries.mapRingHom σ
        (TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ) fun τ : ℍ ↦ η τ ^ (2 * k)) =
      HahnSeries.C c *
        TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ) fun τ : ℍ ↦ η τ ^ (2 * k) := by
  set A := TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ) fun τ : ℍ ↦ η τ ^ (2 * k)
  set Δ : ℍ → ℂ := ⇑CuspForm.discriminant
  set d : ℕ+ := ⟨12 * N, Nat.mul_pos (by norm_num) (NeZero.pos N)⟩
  have hΔan : AnalyticAt ℂ (cuspFunction 1 Δ) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero (f := CuspForm.discriminant) one_pos
      one_mem_strictPeriods_SL
  have hΔper : Function.Periodic ((Δ ^ k) ∘ ofComplex) 1 :=
    (SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
      one_mem_strictPeriods_SL).comp (· ^ k)
  have hpow : (fun τ : ℍ ↦ η τ ^ (2 * k)) ^ 12 = Δ ^ k := by
    funext τ
    simp only [Pi.pow_apply, Δ, CuspForm.coe_discriminant, ModularForm.discriminant]
    rw [← zpow_natCast, ← zpow_natCast _ 24, ← zpow_mul, ← zpow_mul]
    ring_nf
  -- `A ^ 12` is the expansion of `Δ ^ k`, which `σ` fixes
  have hA12 : A ^ 12 = LaurentSeries.expand ℂ d ((qExpansion 1 Δ : LaurentSeries ℂ) ^ k) := by
    -- `laurentQExpansion_pnat_mul` expands from period `1` to period `d * 1`, so the period
    -- `12 N` is first written in that form
    rw [← TauCeti.UpperHalfPlane.laurentQExpansion_pow meromorphicAt_cuspFunction_eta_zpow, hpow,
      show ((12 * N : ℕ) : ℝ) = ((d : ℕ) : ℝ) * 1 by simp [d],
      TauCeti.UpperHalfPlane.laurentQExpansion_pnat_mul hΔper
        (UpperHalfPlane.meromorphicAt_cuspFunction_zpow hΔan.meromorphicAt k),
      TauCeti.UpperHalfPlane.laurentQExpansion_zpow hΔan.meromorphicAt,
      TauCeti.UpperHalfPlane.laurentQExpansion_of_analyticAt hΔan]
  have hq0 : (qExpansion 1 Δ : LaurentSeries ℂ) ≠ 0 := by
    intro h
    have h1 := congrArg (fun x : LaurentSeries ℂ ↦ x.coeff ((1 : ℕ) : ℤ)) h
    simp only [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.coeff_zero] at h1
    exact one_ne_zero (ModularForm.discriminant_qExpansion_coeff_one.symm.trans h1)
  have hA0 : A ≠ 0 := by
    intro h
    have := hA12
    rw [h, zero_pow (by norm_num), eq_comm, map_eq_zero_iff _ (LaurentSeries.expand_injective d)]
      at this
    exact zpow_ne_zero k hq0 this
  -- so `σ(A) / A` is a twelfth root of unity in the field of Laurent series
  have hroot : (HahnSeries.mapRingHom σ A / A) ^ 12 = 1 := by
    rw [div_pow, ← map_pow, hA12, mapRingHom_expand_discriminant_zpow, ← hA12,
      div_self (pow_ne_zero _ hA0)]
  have hprim : IsPrimitiveRoot (HahnSeries.C (Complex.exp (2 * π * Complex.I / (12 : ℕ))) :
      LaurentSeries ℂ) 12 :=
    (Complex.isPrimitiveRoot_exp 12 (by norm_num)).map_of_injective HahnSeries.C_injective
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hroot
  refine ⟨Complex.exp (2 * π * Complex.I / (12 : ℕ)) ^ i, ?_⟩
  rw [map_pow, hi, div_mul_cancel₀ _ hA0]

private theorem conjAux_congr (σ : ℂ ≃+* ℂ) {f₁ f₂ : ℍ → ℂ} (hf₁ : IsWeakForm (Gamma N) k f₁)
    (hf₂ : IsWeakForm (Gamma N) k f₂) (h : f₁ = f₂) : conjAux k σ hf₁ = conjAux k σ hf₂ := by
  subst h
  rfl

omit [NeZero N] in
/-- Every `γ ∈ SL(2, ℤ)` has a partner `γ'` with `γ' diag(1, d) = diag(1, d) γ` modulo `12 N`,
which lies in `Γ(N)` when `γ` does. -/
private theorem exists_map_mul_diagonal_eq (d : (ZMod (12 * N))ˣ) (γ : SL(2, ℤ)) :
    ∃ γ' : SL(2, ℤ), (γ ∈ Gamma N → γ' ∈ Gamma N) ∧
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (12 * N))) γ' :
        SL(2, ZMod (12 * N))) : Matrix (Fin 2) (Fin 2) (ZMod (12 * N))) *
          Matrix.diagonal ![1, (d : ZMod (12 * N))] =
        Matrix.diagonal ![1, (d : ZMod (12 * N))] *
          (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (12 * N))) γ) := by
  set red : SL(2, ℤ) →* SL(2, ZMod (12 * N)) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (12 * N)))
  set D := Matrix.diagonal ![1, (d : ZMod (12 * N))]
  set D' := Matrix.diagonal ![1, ((d⁻¹ : (ZMod (12 * N))ˣ) : ZMod (12 * N))]
  obtain ⟨γ', hγ'⟩ := Matrix.SpecialLinearGroup.map_intCast_zmod_surjective (d := 12 * N)
    ⟨D * red γ * D', by simp [D, D', Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two]⟩
  have hγ'm : (red γ' : Matrix (Fin 2) (Fin 2) (ZMod (12 * N))) = D * red γ * D' :=
    congrArg Subtype.val hγ'
  refine ⟨γ', fun hγ ↦ ?_, ?_⟩
  · -- reducing modulo `N`, the conjugate of `γ ≡ 1` by `D` is `1`
    let ρ := ZMod.castHom (dvd_mul_left N 12) (ZMod N)
    have hred (δ : SL(2, ℤ)) :
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) δ : SL(2, ZMod N)) :
          Matrix (Fin 2) (Fin 2) (ZMod N)) = ρ.mapMatrix (red δ) := by
      ext i j
      simp [red, ρ]
    refine Gamma_mem'.2 (Subtype.ext ?_)
    rw [hred, hγ'm, map_mul, map_mul, ← hred, congrArg Subtype.val (Gamma_mem'.1 hγ)]
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, ← map_mul, D, D',
      TauCeti.diagonal_vec2_one_mul_eq_one d.mul_inv, map_one]
  · rw [hγ'm, Matrix.mul_assoc, TauCeti.diagonal_vec2_one_mul_eq_one d.inv_mul, Matrix.mul_one]

omit [NeZero N] in
/-- A weak form on `Γ(N)` has period `12 N`. -/
private theorem IsWeakForm.periodic_twelve_mul (hf : IsWeakForm (Gamma N) k f) :
    Function.Periodic (f ∘ ofComplex) ((12 * N : ℕ) : ℝ) := by
  have h := periodic_slash_comp_ofComplex hf.slash_eq 1
  rw [SlashAction.slash_one, strictLevel_Gamma] at h
  simpa [mul_comm] using h.nat_mul 12

/-- The cusp function of a weak form on `Γ(N)` at period `12 N` is meromorphic at `0`. -/
private theorem IsWeakForm.meromorphicAt_twelve_mul (hf : IsWeakForm (Gamma N) k f) :
    _root_.MeromorphicAt (cuspFunction ((12 * N : ℕ) : ℝ) f) 0 := by
  rw [eq_eta_zpow_mul_finitePart hf]
  exact UpperHalfPlane.meromorphicAt_cuspFunction_mul meromorphicAt_cuspFunction_eta_zpow
    (meromorphicAt_cuspFunction_finitePart_ofQuotient _)

/-- The Laurent expansion at period `12 N` of a weak form on `Γ(N)` is its expansion at period
`N` in the variable `q ^ 12`. -/
private theorem IsWeakForm.laurentQExpansion_twelve_mul (hf : IsWeakForm (Gamma N) k f) :
    TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ) f =
      LaurentSeries.expand ℂ 12 (TauCeti.UpperHalfPlane.laurentQExpansion N f) := by
  have h := periodic_slash_comp_ofComplex hf.slash_eq 1
  rw [SlashAction.slash_one, strictLevel_Gamma] at h
  have hm := hf.meromorphicAt_cuspFunction_slash 1
  rw [SlashAction.slash_one, strictLevel_Gamma] at hm
  simpa using TauCeti.UpperHalfPlane.laurentQExpansion_pnat_mul h hm 12

/-- **Conjugates of weak forms, with their translates.** For a weak form `f` of weight `k` on
`Γ(N)` and an automorphism `σ` of `ℂ`, some weak form `g` of weight `k` on `Γ(N)` has, at every
cusp `γ • ∞`, the `σ`-conjugate of the expansion of `f` at a cusp `γ' • ∞`, with `γ' ∈ Γ(N)` when
`γ ∈ Γ(N)`. -/
private theorem IsWeakForm.exists_conj (σ : ℂ ≃+* ℂ) (hf : IsWeakForm (Gamma N) k f) :
    ∃ g : ℍ → ℂ, IsWeakForm (Gamma N) k g ∧ ∀ γ : SL(2, ℤ), ∃ γ' : SL(2, ℤ),
      (γ ∈ Gamma N → γ' ∈ Gamma N) ∧
        TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ) (g ∣[k] γ) =
          HahnSeries.mapRingHom (σ : ℂ →+* ℂ)
            (TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ) (f ∣[k] γ')) := by
  obtain ⟨d, hd⟩ := ZMod.exists_map_stdAddChar_one_eq (N := 12 * N) σ
  obtain ⟨c, hc⟩ :=
    exists_mapRingHom_laurentQExpansion_eta_zpow (N := N) (k := k) (σ : ℂ →+* ℂ)
  -- the conjugate of a weak form, normalized by `c`
  have hL {F : ℍ → ℂ} (hF : IsWeakForm (Gamma N) k F) :
      TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ) (c • conjAux k σ hF) =
        HahnSeries.mapRingHom (σ : ℂ →+* ℂ)
          (TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ) F) := by
    rw [TauCeti.UpperHalfPlane.laurentQExpansion_smul (meromorphicAt_cuspFunction_conjAux σ hF),
      laurentQExpansion_conjAux, laurentQExpansion_eq_mul hF, map_mul, hc,
      ← HahnSeries.C_mul_eq_smul, mul_assoc]
  have hslash {F : ℍ → ℂ} (hF : IsWeakForm (Gamma N) k F) (γ : SL(2, ℤ)) :
      ∃ γ' : SL(2, ℤ), (γ ∈ Gamma N → γ' ∈ Gamma N) ∧
        (c • conjAux k σ hF) ∣[k] γ = c • conjAux k σ (hF.slash_of_normal γ') := by
    obtain ⟨γ', hmem, hγ'⟩ := exists_map_mul_diagonal_eq d γ
    exact ⟨γ', hmem, by rw [_root_.ModularForm.SL_smul_slash, conjAux_slash hd hF hγ']⟩
  refine ⟨c • conjAux k σ hf, ⟨(mdifferentiable_conjAux σ hf).const_smul c, fun γ hγ ↦ ?_,
    fun γ ↦ ?_⟩, fun γ ↦ ?_⟩
  · obtain ⟨γ', hmem, h⟩ := hslash hf γ
    rw [h, conjAux_congr σ _ hf (hf.slash_eq γ' (hmem hγ))]
  · obtain ⟨γ', -, h⟩ := hslash hf γ
    rw [h]
    exact UpperHalfPlane.exists_isBigO_exp_of_meromorphicAt_cuspFunction twelve_mul_pos
      ((periodic_conjAux σ _).smul c)
      (((meromorphicAt_cuspFunction_conjAux σ _).const_smul c).congr
        (UpperHalfPlane.cuspFunction_map_eventuallyEq (c • ·) _).symm)
  · obtain ⟨γ', hmem, h⟩ := hslash hf γ
    exact ⟨γ', hmem, by rw [h, hL]⟩

/-! ### Conjugates of weak forms, modular forms and cusp forms -/

variable {F : Type*} [FunLike F ℍ ℂ]

/-- The Laurent expansions at every cusp, at period `12 N`, of a modular form on `Γ(N)` have no
negative powers. -/
private theorem orderTop_laurentQExpansion_slash_nonneg [ModularFormClass F (Gamma N) k] (f : F)
    (γ : SL(2, ℤ)) :
    0 ≤ (TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ) (⇑f ∣[k] γ)).orderTop := by
  have hf := (ModularFormClass.isWeakForm f).slash_of_normal γ
  rw [TauCeti.UpperHalfPlane.orderTop_laurentQExpansion hf.meromorphicAt_twelve_mul]
  exact (UpperHalfPlane.analyticAt_cuspFunction_zero twelve_mul_pos hf.periodic_twelve_mul
    hf.mdifferentiable (ModularFormClass.bdd_at_infty_slash f γ)).meromorphicOrderAt_nonneg

/-- The expansion at period `12 N` of a modular form on `Γ(N)` is its `q`-expansion at period `N`
in the variable `q ^ 12`. -/
private theorem laurentQExpansion_twelve_mul_eq_expand [ModularFormClass F (Gamma N) k] (f : F) :
    TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ) f =
      LaurentSeries.expand ℂ 12 (qExpansion N f : LaurentSeries ℂ) := by
  have hf := ModularFormClass.isWeakForm f
  have h := periodic_slash_comp_ofComplex hf.slash_eq 1
  rw [SlashAction.slash_one, strictLevel_Gamma] at h
  rw [hf.laurentQExpansion_twelve_mul, TauCeti.UpperHalfPlane.laurentQExpansion_of_analyticAt
    (UpperHalfPlane.analyticAt_cuspFunction_zero (Nat.cast_pos.2 (NeZero.pos N)) h
      hf.mdifferentiable (ModularFormClass.bdd_at_infty f))]

/-- **Conjugates of modular forms, with their translates.** The conjugate of a modular form of
level `N` is a modular form, with the conjugate `q`-expansion at `∞`; at every other cusp its
expansion is the conjugate of an expansion of the original form. -/
private theorem exists_conj_modularForm [ModularFormClass F (Gamma N) k] (f : F) (σ : ℂ ≃+* ℂ) :
    ∃ g : ModularForm (Gamma N) k,
      qExpansion N g = PowerSeries.map (σ : ℂ →+* ℂ) (qExpansion N f) ∧
        ∀ γ : SL(2, ℤ), ∃ γ' : SL(2, ℤ),
          TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ) (⇑g ∣[k] γ) =
            HahnSeries.mapRingHom (σ : ℂ →+* ℂ)
              (TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ) (⇑f ∣[k] γ')) := by
  have hf := ModularFormClass.isWeakForm f
  obtain ⟨g, hg, hγ⟩ := hf.exists_conj σ
  have hbdd (γ : SL(2, ℤ)) : IsBoundedAtImInfty (g ∣[k] γ) := by
    obtain ⟨γ', -, h⟩ := hγ γ
    have hg' := hg.slash_of_normal γ
    refine (TauCeti.UpperHalfPlane.tendsto_laurentQExpansion_coeff_zero twelve_mul_pos
      hg'.periodic_twelve_mul hg'.meromorphicAt_twelve_mul ?_).isBigO_one ℝ
    rw [h, HahnSeries.orderTop_mapRingHom_of_injective _ σ.injective]
    exact orderTop_laurentQExpansion_slash_nonneg f γ'
  obtain ⟨G, rfl⟩ := (exists_modularForm_coe_eq_iff).2 ⟨hg, hbdd⟩
  refine ⟨G, ?_, fun γ ↦ (hγ γ).imp fun _ ↦ And.right⟩
  obtain ⟨γ', hmem, h⟩ := hγ 1
  rw [SlashAction.slash_one, hf.slash_eq γ' (hmem (one_mem _)),
    laurentQExpansion_twelve_mul_eq_expand, laurentQExpansion_twelve_mul_eq_expand,
    LaurentSeries.mapRingHom_expand] at h
  have hc := HahnSeries.mapRingHom_ofPowerSeries_eq_ofPowerSeries_iff.1
    (LaurentSeries.expand_injective 12 h).symm
  exact PowerSeries.ext fun n ↦ by rw [PowerSeries.coeff_map, hc n]

/-- **Galois conjugates of weak forms.** For a weak form `f` of weight `k` on `Γ(N)` and an
automorphism `σ` of `ℂ`, which need not be continuous, there is a weak form of weight `k` on
`Γ(N)` whose Laurent expansion at `∞`, in `q = exp (2 π i τ / N)`, is obtained by applying `σ` to
every coefficient of that of `f`. -/
theorem IsWeakForm.exists_laurentQExpansion_eq_mapRingHom (hf : IsWeakForm (Gamma N) k f)
    (σ : ℂ ≃+* ℂ) :
    ∃ g : ℍ → ℂ, IsWeakForm (Gamma N) k g ∧
      TauCeti.UpperHalfPlane.laurentQExpansion N g =
        HahnSeries.mapRingHom (σ : ℂ →+* ℂ) (TauCeti.UpperHalfPlane.laurentQExpansion N f) := by
  obtain ⟨g, hg, hγ⟩ := hf.exists_conj σ
  obtain ⟨γ', hmem, h⟩ := hγ 1
  rw [SlashAction.slash_one, hf.slash_eq γ' (hmem (one_mem _))] at h
  refine ⟨g, hg, LaurentSeries.expand_injective (R := ℂ) 12 ?_⟩
  rw [← hg.laurentQExpansion_twelve_mul, h, hf.laurentQExpansion_twelve_mul,
    LaurentSeries.mapRingHom_expand]

end TauCeti

namespace ModularForm

open TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **Galois conjugates of modular forms of level `N`.** For a modular form `f` of weight `k` on
`Γ(N)` and an automorphism `σ` of `ℂ`, which need not be continuous, there is a modular form of
weight `k` on `Γ(N)` whose `q`-expansion at `∞`, in `q = exp (2 π i τ / N)`, is obtained by
applying `σ` to every coefficient of that of `f`. -/
theorem exists_qExpansion_eq_map (f : ModularForm (Gamma N) k) (σ : ℂ ≃+* ℂ) :
    ∃ g : ModularForm (Gamma N) k,
      qExpansion N g = PowerSeries.map (σ : ℂ →+* ℂ) (qExpansion N f) :=
  (exists_conj_modularForm f σ).imp fun _ ↦ And.left

end ModularForm

namespace CuspForm

open TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **Galois conjugates of cusp forms of level `N`.** For a cusp form `f` of weight `k` on `Γ(N)`
and an automorphism `σ` of `ℂ`, which need not be continuous, there is a cusp form of weight `k`
on `Γ(N)` whose `q`-expansion at `∞`, in `q = exp (2 π i τ / N)`, is obtained by applying `σ` to
every coefficient of that of `f`. -/
theorem exists_qExpansion_eq_map (f : CuspForm (Gamma N) k) (σ : ℂ ≃+* ℂ) :
    ∃ g : CuspForm (Gamma N) k,
      qExpansion N g = PowerSeries.map (σ : ℂ →+* ℂ) (qExpansion N f) := by
  obtain ⟨G, hG, hγ⟩ := exists_conj_modularForm f σ
  -- the constant term of the conjugate at every cusp is the conjugate of a constant term of `f`
  have hzero (γ : SL(2, ℤ)) : IsZeroAtImInfty (⇑G ∣[k] γ) := by
    obtain ⟨γ', h⟩ := hγ γ
    have hG' := (ModularFormClass.isWeakForm G).slash_of_normal γ
    have hf' := (ModularFormClass.isWeakForm f).slash_of_normal γ'
    have h₀ : (TauCeti.UpperHalfPlane.laurentQExpansion ((12 * N : ℕ) : ℝ) (⇑f ∣[k] γ')).coeff 0 =
        0 :=
      tendsto_nhds_unique (TauCeti.UpperHalfPlane.tendsto_laurentQExpansion_coeff_zero
        twelve_mul_pos hf'.periodic_twelve_mul hf'.meromorphicAt_twelve_mul
        (orderTop_laurentQExpansion_slash_nonneg f γ')) (CuspFormClass.zero_at_infty_slash f γ')
    have ht := TauCeti.UpperHalfPlane.tendsto_laurentQExpansion_coeff_zero twelve_mul_pos
      hG'.periodic_twelve_mul hG'.meromorphicAt_twelve_mul
      (orderTop_laurentQExpansion_slash_nonneg G γ)
    rwa [h, HahnSeries.coeff_mapRingHom, h₀, map_zero] at ht
  refine ⟨{ toSlashInvariantForm := G.toSlashInvariantForm
            holo' := G.holo'
            zero_at_cusps' := fun {c} hc ↦ ?_ }, hG⟩
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  exact (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr fun γ _ ↦ hzero γ

end CuspForm
