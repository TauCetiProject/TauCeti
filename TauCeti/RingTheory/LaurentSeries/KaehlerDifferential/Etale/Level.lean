/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Etale.Trace
public import TauCeti.RingTheory.LaurentSeries.Level.Adjoin
public import TauCeti.RingTheory.LaurentSeries.Level.ModuleTopology
public import TauCeti.RingTheory.LaurentSeries.Level.Residue
public import TauCeti.RingTheory.LaurentSeries.Puiseux.KaehlerDifferential.Basic

/-!
# Comparison of étale continuous one-forms with ramified Laurent levels

Let `F = K⸨X⸩` and let `d` be a positive integer with `((d : ℕ) : K) ≠ 0`, so that the ramified
level `Level K d` (`t = u ^ d`) is separable and formally étale over `F`
(`TauCeti.LaurentSeries.Level.isSeparable_iff`, `formallyEtale_iff`). This file compares the
intrinsic continuous Kähler quotient `Extension.ContinuousKaehlerDifferential K (Level K d)` with
the explicit coordinate one-forms `Level.ContinuousKaehlerDifferential K d` (`g du`):

* In the level variable `u`, the extended formal derivative `d/dt` on `Level K d` is
  `(d u ^ (d - 1))⁻¹ · d/du` (`ringEquivLaurentSeries_derivation`).
* Composing the two scalar-extension equivalences with `Level K d ⊗_F Ω¹_cont(F/K)` yields a
  continuous `Level K d`-linear equivalence
  `Level.ContinuousKaehlerDifferential.equivExtension K d` intertwining pullback from `F`,
  universal derivations (`D x ↦ d(x(u))`), differential traces (`trace_equivExtension`), and
  residues (`residue_eq_coeff_equivExtension`).
* Along any `F`-algebra chart `e : L ≃ₐ[F] Level K d` from a formally étale `F`-algebra `L`,
  `AlgEquiv.laurentExtensionDifferentialEquiv e` (and its topological upgrade when `L` carries the
  `F`-module topology) identifies `Ω¹_cont(L/K)` with `Level.ContinuousKaehlerDifferential K d`,
  intertwines differential traces, and proves `Res_F(Tr_{L/F} ω) = Res_L(ω)` directly on the
  continuous Kähler quotient (`residue_eq_coeff_laurentExtensionDifferentialEquiv`).
* On the `d`-th Puiseux level `L_d = puiseuxField.level K d`, tracing continuous one-forms down to
  `F` multiplies the rational-exponent Puiseux residue by `d`:
  `Res_F(Tr_{L_d/F} ω) = d • Res_t^ℚ(ω)` (`residue_puiseuxLevel_eq_nsmul_puiseuxResidue` in any
  characteristic coprime to `d`, and
  `coeff_neg_one_equivLaurentSeries_trace_eq_nsmul_residue_levelMap` via `levelMap` in
  characteristic zero).

## Main definitions

* `Level.ContinuousKaehlerDifferential.equivExtension K d`: continuous `Level K d`-linear
  equivalence `Ω¹_cont(Level K d / K) ≃L[Level K d] Level.ContinuousKaehlerDifferential K d`.
* `AlgEquiv.laurentExtensionDifferentialEquiv` and
  `AlgEquiv.laurentExtensionContinuousDifferentialEquiv`: transport of `Ω¹_cont(L/K)` along any
  separable level chart `e : L ≃ₐ[K⸨X⸩] Level K d`.

## Main results

* `TauCeti.LaurentSeries.Level.ringEquivLaurentSeries_derivation`: chain rule for `d/dt` in the
  level parameter `u`.
* `Level.ContinuousKaehlerDifferential.equivExtension_D`, `trace_equivExtension`, and
  `residue_eq_coeff_equivExtension`: `equivExtension` intertwines `d`, differential traces, and
  residues (`Res_F(Tr_{L/F} ω) = Res_L(ω)`).
* `AlgEquiv.residue_eq_coeff_laurentExtensionDifferentialEquiv`: `Res_F(Tr_{L/F} ω) = Res_L(ω)` in
  any separable level chart.
* `Extension.ContinuousKaehlerDifferential.residue_puiseuxLevel_eq_nsmul_puiseuxResidue` and
  `coeff_neg_one_equivLaurentSeries_trace_eq_nsmul_residue_levelMap`:
  `Res_F(Tr_{L_d/F} ω) = d • Res_t^ℚ(ω)`.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968).
-/

public section

open HahnSeries TensorProduct
open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Level

section SeparableLevel

variable (K : Type*) [Field K] (d : ℕ+) [NeZero ((d : ℕ) : K)]

private theorem derivative_single_ne_zero' :
    _root_.LaurentSeries.derivative K (single (d : ℤ) (1 : K)) ≠ 0 := by
  simp [NeZero.ne ((d : ℕ) : K)]

variable {K d} in
/-- **Chain rule for `d/dt` on a separable ramified level.** In the level variable `u`
(`t = u ^ d`), the extended formal derivative `Extension.derivation K (Level K d)` acts as
`(d u ^ (d - 1))⁻¹ · d/du`. -/
theorem ringEquivLaurentSeries_derivation (x : Level K d) :
    ringEquivLaurentSeries K d (Extension.derivation K (Level K d) x) =
      _root_.LaurentSeries.derivative K (ringEquivLaurentSeries K d x) /
        _root_.LaurentSeries.derivative K (single (d : ℤ) 1) := by
  set J : K⸨X⸩ := _root_.LaurentSeries.derivative K (single (d : ℤ) 1)
  have hJ : J ≠ 0 := derivative_single_ne_zero' K d
  let du : Derivation K (Level K d) (Level K d) :=
    { toFun y := (algEquivLaurentSeries K d).symm
        (_root_.LaurentSeries.derivative K (algEquivLaurentSeries K d y))
      map_add' y z := by simp
      map_smul' c y := by
        apply (algEquivLaurentSeries K d).injective
        simp [Algebra.smul_def, laurentSeries_algebraMap_mul_eq_smul]
      map_one_eq_zero' := by
        apply (ringEquivLaurentSeries K d).injective
        simp only [LinearMap.coe_mk, AddHom.coe_mk, algEquivLaurentSeries_apply,
          algEquivLaurentSeries_symm_apply, map_one, map_zero, ← laurentSeriesDerivation_apply,
          Derivation.map_one_eq_zero]
      leibniz' y z := by
        apply (ringEquivLaurentSeries K d).injective
        simp only [LinearMap.coe_mk, AddHom.coe_mk, algEquivLaurentSeries_apply,
          algEquivLaurentSeries_symm_apply, smul_eq_mul, map_add,
          (ringEquivLaurentSeries K d).map_mul, RingEquiv.apply_symm_apply,
          _root_.LaurentSeries.derivative_mul]
        ring }
  let δ : Derivation K (Level K d) (Level K d) := ((ringEquivLaurentSeries K d).symm J)⁻¹ • du
  have hdu (y : Level K d) :
      ringEquivLaurentSeries K d (du y) =
        _root_.LaurentSeries.derivative K (ringEquivLaurentSeries K d y) := by
    simp [du]
  have hδ : δ = Extension.derivation K (Level K d) := by
    refine Extension.eq_derivation fun f ↦ ?_
    apply (ringEquivLaurentSeries K d).injective
    have hexp (g : K⸨X⸩) : _root_.LaurentSeries.expand K d g =
        TauCeti.LaurentSeries.substAlgHom (K := K) (φ := PowerSeries.X ^ (d : ℕ))
          (by simp) (pow_ne_zero _ PowerSeries.X_ne_zero) g := by
      rw [TauCeti.LaurentSeries.substAlgHom_X_pow_eq_expand]
    have hXd : ((PowerSeries.X ^ (d : ℕ) : PowerSeries K) : K⸨X⸩) = single (d : ℤ) 1 := by
      simp [single_pow]
    rw [show δ _ = _ from _root_.smul_apply _ _ _, smul_eq_mul, map_mul, map_inv₀,
      RingEquiv.apply_symm_apply, hdu, algebraMap_apply, algebraMap_apply,
      laurentSeriesDerivation_apply, hexp f, TauCeti.LaurentSeries.derivative_substAlgHom,
      ← hexp, hXd, mul_comm _ J, ← mul_assoc, inv_mul_cancel₀ hJ, one_mul]
  rw [← hδ, show δ x = _ from _root_.smul_apply _ _ _, smul_eq_mul, map_mul, map_inv₀,
    RingEquiv.apply_symm_apply, hdu, div_eq_mul_inv, mul_comm]

variable {K d} in
/-- On level `d`, `d u / d t = (d u ^ (d - 1))⁻¹`. -/
theorem ringEquivLaurentSeries_derivation_parameter :
    ringEquivLaurentSeries K d (Extension.derivation K (Level K d) (parameter K d)) =
      (_root_.LaurentSeries.derivative K (single (d : ℤ) 1))⁻¹ := by
  have h1 : _root_.LaurentSeries.derivative K (single 1 (1 : K)) = 1 := by simp
  rw [ringEquivLaurentSeries_derivation, ringEquiv_parameter, h1, one_div]

namespace ContinuousKaehlerDifferential

/-- **Equivalence of intrinsic and level continuous one-forms.** For `((d : ℕ) : K) ≠ 0`, the
scalar-extension equivalences `Extension.ContinuousKaehlerDifferential.tensorEquiv` and
`Level.ContinuousKaehlerDifferential.tensorEquiv` compose to a continuous `Level K d`-linear
equivalence between the continuous Kähler quotient `Ω¹_cont(Level K d / K)` and the coordinate
module `Level.ContinuousKaehlerDifferential K d` (`g du`). -/
noncomputable def equivExtension :
    Extension.ContinuousKaehlerDifferential K (Level K d) ≃L[Level K d]
      Level.ContinuousKaehlerDifferential K d :=
  ((Extension.ContinuousKaehlerDifferential.tensorEquiv K (Level K d)).symm.trans
    (Level.ContinuousKaehlerDifferential.tensorEquiv K d)).toContinuousLinearEquivOfIsModuleTopology

variable {K d}

@[simp]
theorem equivExtension_tensorEquiv
    (η : Level K d ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    equivExtension K d
        (Extension.ContinuousKaehlerDifferential.tensorEquiv K (Level K d) η) =
      Level.ContinuousKaehlerDifferential.tensorEquiv K d η := by
  simp [equivExtension]

@[simp]
theorem equivExtension_symm_tensorEquiv
    (η : Level K d ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    (equivExtension K d).symm (Level.ContinuousKaehlerDifferential.tensorEquiv K d η) =
      Extension.ContinuousKaehlerDifferential.tensorEquiv K (Level K d) η := by
  simp [equivExtension]

/-- `equivExtension` intertwines the two pullbacks from `Ω¹_cont(K⸨X⸩/K)`. -/
@[simp]
theorem equivExtension_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    equivExtension K d (Extension.ContinuousKaehlerDifferential.map K (Level K d) ω) =
      Level.ContinuousKaehlerDifferential.map K d ω := by
  rw [← one_smul (Level K d) (Extension.ContinuousKaehlerDifferential.map K (Level K d) ω),
    ← Extension.ContinuousKaehlerDifferential.tensorEquiv_tmul, equivExtension_tensorEquiv,
    Level.ContinuousKaehlerDifferential.tensorEquiv_tmul, one_smul]

/-- In coordinates, `equivExtension` sends `x dt` to `(x · d u ^ (d - 1)) du`. -/
theorem equivLevel_equivExtension
    (ω : Extension.ContinuousKaehlerDifferential K (Level K d)) :
    equivLevel K d (equivExtension K d ω) =
      Extension.ContinuousKaehlerDifferential.equivSelf K (Level K d) ω *
        (ringEquivLaurentSeries K d).symm
          (_root_.LaurentSeries.derivative K (single (d : ℤ) 1)) := by
  conv_lhs =>
    rw [← Extension.ContinuousKaehlerDifferential.equivSelf_smul_D_algebraMap_single_one ω,
      ← Extension.ContinuousKaehlerDifferential.map_D]
  rw [ContinuousLinearEquiv.map_smul, equivExtension_map, LinearEquiv.map_smul, equivLevel_map,
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D_single_one, map_one, one_mul,
    smul_eq_mul]

/-- **`equivExtension` commutes with universal continuous derivations**: it sends `d x` on
`Level K d` to `d(x(u))` in the level variable `u`. -/
@[simp]
theorem equivExtension_D (x : Level K d) :
    equivExtension K d (Extension.ContinuousKaehlerDifferential.D K (Level K d) x) =
      ofForm (TauCeti.ContinuousKaehlerDifferential.D K (ringEquivLaurentSeries K d x)) := by
  apply (equivLevel K d).injective
  apply (ringEquivLaurentSeries K d).injective
  rw [equivLevel_equivExtension, Extension.ContinuousKaehlerDifferential.equivSelf_D, map_mul,
    RingEquiv.apply_symm_apply, ringEquivLaurentSeries_derivation,
    div_mul_cancel₀ _ (derivative_single_ne_zero' K d), ringEquivLaurentSeries_equivLevel,
    addEquivContinuousKaehlerDifferential_ofForm,
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D]

/-- The differential of the level parameter `u` corresponds to `du`. -/
theorem equivLevel_equivExtension_D_parameter :
    equivLevel K d
      (equivExtension K d
        (Extension.ContinuousKaehlerDifferential.D K (Level K d) (parameter K d))) = 1 := by
  apply (ringEquivLaurentSeries K d).injective
  rw [equivExtension_D, ringEquivLaurentSeries_equivLevel,
    addEquivContinuousKaehlerDifferential_ofForm, ringEquiv_parameter,
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D_single_one, map_one]

/-- `equivExtension` intertwines the intrinsic differential trace with the level differential
trace. -/
@[simp]
theorem trace_equivExtension (ω : Extension.ContinuousKaehlerDifferential K (Level K d)) :
    Level.ContinuousKaehlerDifferential.trace K d (equivExtension K d ω) =
      Extension.ContinuousKaehlerDifferential.trace K (Level K d) ω := by
  conv_lhs =>
    rw [← Extension.ContinuousKaehlerDifferential.equivSelf_smul_D_algebraMap_single_one ω,
      ← Extension.ContinuousKaehlerDifferential.map_D]
  conv_rhs =>
    rw [← Extension.ContinuousKaehlerDifferential.equivSelf_smul_D_algebraMap_single_one ω,
      ← Extension.ContinuousKaehlerDifferential.map_D]
  rw [ContinuousLinearEquiv.map_smul, equivExtension_map,
    Level.ContinuousKaehlerDifferential.trace_smul_map,
    Extension.ContinuousKaehlerDifferential.trace_smul_map]

/-- **`Res_F(Tr_{L/F} ω) = Res_L(ω)` on `Level K d`.** The intrinsic trace-defined residue of a
continuous one-form on `Level K d` equals its `u⁻¹`-coefficient in the coordinate `du`. -/
theorem residue_eq_coeff_equivExtension
    (ω : Extension.ContinuousKaehlerDifferential K (Level K d)) :
    Extension.ContinuousKaehlerDifferential.residue K (Level K d) ω =
      (ringEquivLaurentSeries K d (equivLevel K d (equivExtension K d ω))).coeff (-1) := by
  rw [Extension.ContinuousKaehlerDifferential.residue_apply, ← trace_equivExtension,
    coeff_neg_one_equivLaurentSeries_trace]

/-- On `x dt`, the intrinsic residue on `Level K d` recovers `Level.residue K d x`. -/
theorem residue_equivSelf_symm_eq_levelResidue (x : Level K d) :
    Extension.ContinuousKaehlerDifferential.residue K (Level K d)
        ((Extension.ContinuousKaehlerDifferential.equivSelf K (Level K d)).symm x) =
      Level.residue K d x := by
  rw [residue_eq_coeff_equivExtension, equivLevel_equivExtension, LinearEquiv.apply_symm_apply,
    map_mul, RingEquiv.apply_symm_apply, Level.residue_apply]

end ContinuousKaehlerDifferential

end SeparableLevel

end TauCeti.LaurentSeries.Level

/-! ### Level charts on general étale Laurent extensions -/

namespace AlgEquiv

open TauCeti.LaurentSeries
open TauCeti.LaurentSeries.Level
open TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential

section LevelChart

variable {K : Type*} [Field K] {L : Type*} [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]
  {d : ℕ+} [NeZero ((d : ℕ) : K)]

/-- A `K⸨X⸩`-algebra chart `e : L ≃ₐ[K⸨X⸩] Level K d` identifies the intrinsic continuous one-forms
`Ω¹_cont(L/K)` with the coordinate one-forms of level `d`. -/
noncomputable def laurentExtensionDifferentialEquiv (e : L ≃ₐ[K⸨X⸩] Level K d) :
    Extension.ContinuousKaehlerDifferential K L ≃ₗ[K⸨X⸩]
      Level.ContinuousKaehlerDifferential K d :=
  (Extension.ContinuousKaehlerDifferential.linearEquivAlgEquiv e).trans
    ((equivExtension K d).toLinearEquiv.restrictScalars K⸨X⸩)

theorem laurentExtensionDifferentialEquiv_apply (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    e.laurentExtensionDifferentialEquiv ω =
      equivExtension K d (Extension.ContinuousKaehlerDifferential.mapAlgHom e.toAlgHom ω) := by
  simp [laurentExtensionDifferentialEquiv]

theorem laurentExtensionDifferentialEquiv_smul (e : L ≃ₐ[K⸨X⸩] Level K d) (x : L)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    e.laurentExtensionDifferentialEquiv (x • ω) =
      e x • e.laurentExtensionDifferentialEquiv ω := by
  rw [laurentExtensionDifferentialEquiv_apply,
    Extension.ContinuousKaehlerDifferential.mapAlgHom_smul, AlgEquiv.coe_toAlgHom,
    ContinuousLinearEquiv.map_smul, ← laurentExtensionDifferentialEquiv_apply]

@[simp]
theorem laurentExtensionDifferentialEquiv_map (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : TauCeti.ContinuousKaehlerDifferential K) :
    e.laurentExtensionDifferentialEquiv (Extension.ContinuousKaehlerDifferential.map K L ω) =
      Level.ContinuousKaehlerDifferential.map K d ω := by
  rw [laurentExtensionDifferentialEquiv_apply,
    Extension.ContinuousKaehlerDifferential.mapAlgHom_map, equivExtension_map]

@[simp]
theorem laurentExtensionDifferentialEquiv_D (e : L ≃ₐ[K⸨X⸩] Level K d) (x : L) :
    e.laurentExtensionDifferentialEquiv (Extension.ContinuousKaehlerDifferential.D K L x) =
      ofForm (TauCeti.ContinuousKaehlerDifferential.D K (ringEquivLaurentSeries K d (e x))) := by
  rw [laurentExtensionDifferentialEquiv_apply,
    Extension.ContinuousKaehlerDifferential.mapAlgHom_D, AlgEquiv.coe_toAlgHom, equivExtension_D]

/-- On a finite separable field extension, `laurentExtensionDifferentialEquiv` agrees with
`laurentDifferentialTensorEquiv` through `Extension.ContinuousKaehlerDifferential.tensorEquiv`. -/
@[simp]
theorem laurentExtensionDifferentialEquiv_tensorEquiv {E : Type*} [Field E] [Algebra K⸨X⸩ E]
    [Algebra K E] [IsScalarTower K K⸨X⸩ E] [Algebra.FormallyEtale K⸨X⸩ E]
    (e : E ≃ₐ[K⸨X⸩] Level K d) (η : E ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    e.laurentExtensionDifferentialEquiv
        (Extension.ContinuousKaehlerDifferential.tensorEquiv K E η) =
      e.laurentDifferentialTensorEquiv η := by
  induction η using TensorProduct.inductionOn with
  | tmul x ω =>
    rw [Extension.ContinuousKaehlerDifferential.tensorEquiv_tmul,
      laurentExtensionDifferentialEquiv_smul, laurentExtensionDifferentialEquiv_map,
      laurentDifferentialTensorEquiv_tmul]
  | add a b ha hb => simp [ha, hb]

/-- Differential trace on `Ω¹_cont(L/K)` commutes with every separable level chart. -/
@[simp]
theorem trace_laurentExtensionDifferentialEquiv (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    Level.ContinuousKaehlerDifferential.trace K d (e.laurentExtensionDifferentialEquiv ω) =
      Extension.ContinuousKaehlerDifferential.trace K L ω := by
  rw [laurentExtensionDifferentialEquiv_apply, trace_equivExtension,
    Extension.ContinuousKaehlerDifferential.trace_mapAlgHom_algEquiv]

/-- **`Res_F(Tr_{L/F} ω) = Res_L(ω)` in any separable level chart.** For any `K⸨X⸩`-algebra
isomorphism `e : L ≃ₐ[K⸨X⸩] Level K d`, the residue of `Tr_{L/F} ω` at `X` equals the coefficient
of `u⁻¹` of `ω` read in the level parameter `u` via `e`. -/
theorem residue_eq_coeff_laurentExtensionDifferentialEquiv (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    Extension.ContinuousKaehlerDifferential.residue K L ω =
      (ringEquivLaurentSeries K d (equivLevel K d (e.laurentExtensionDifferentialEquiv ω))).coeff
        (-1) := by
  rw [← Extension.ContinuousKaehlerDifferential.residue_mapAlgHom_algEquiv e ω,
    residue_eq_coeff_equivExtension, laurentExtensionDifferentialEquiv_apply]

/-- **Chart independence on `Ω¹_cont(L/K)`.** Two isomorphisms of `L` with separable ramified
levels yield the same `u⁻¹`-coefficient residue on every continuous one-form of `L`. -/
theorem coeff_laurentExtensionDifferentialEquiv_eq {n : ℕ+} [NeZero ((n : ℕ) : K)]
    (e : L ≃ₐ[K⸨X⸩] Level K d) (e' : L ≃ₐ[K⸨X⸩] Level K n)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    (ringEquivLaurentSeries K d (equivLevel K d (e.laurentExtensionDifferentialEquiv ω))).coeff
      (-1) =
    (ringEquivLaurentSeries K n (equivLevel K n (e'.laurentExtensionDifferentialEquiv ω))).coeff
      (-1) := by
  rw [← residue_eq_coeff_laurentExtensionDifferentialEquiv e,
    ← residue_eq_coeff_laurentExtensionDifferentialEquiv e']

/-- When `L` carries the `K⸨X⸩`-module topology and is module-finite over `K⸨X⸩`, any separable
level chart induces a continuous `K⸨X⸩`-linear equivalence of continuous one-forms. -/
noncomputable def laurentExtensionContinuousDifferentialEquiv
    [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L] [Module.Finite K⸨X⸩ L]
    (e : L ≃ₐ[K⸨X⸩] Level K d) :
    Extension.ContinuousKaehlerDifferential K L ≃L[K⸨X⸩]
      Level.ContinuousKaehlerDifferential K d :=
  e.laurentExtensionDifferentialEquiv.toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem laurentExtensionContinuousDifferentialEquiv_apply
    [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L] [Module.Finite K⸨X⸩ L]
    (e : L ≃ₐ[K⸨X⸩] Level K d) (ω : Extension.ContinuousKaehlerDifferential K L) :
    e.laurentExtensionContinuousDifferentialEquiv ω = e.laurentExtensionDifferentialEquiv ω := by
  simp [laurentExtensionContinuousDifferentialEquiv]

end LevelChart

end AlgEquiv

/-! ### Compatibility with `Level.residueOfFinrankEq` and Puiseux level corollaries -/

namespace TauCeti.LaurentSeries

section PuiseuxCorollaries

/-- Over an algebraically closed field of characteristic zero, the intrinsic residue on
`Ω¹_cont(L/K)` agrees with `Level.residueOfFinrankEq` applied to the `dt`-coordinate. -/
theorem Extension.ContinuousKaehlerDifferential.residue_eq_residueOfFinrankEq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {L : Type*} [Field L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
    [Algebra.FormallyEtale K⸨X⸩ L] {e : ℕ+} (h : Module.finrank K⸨X⸩ L = e)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    Extension.ContinuousKaehlerDifferential.residue K L ω =
      Level.residueOfFinrankEq h (Extension.ContinuousKaehlerDifferential.equivSelf K L ω) := by
  rw [Level.residueOfFinrankEq_eq_coeff_neg_one_trace h,
    Extension.ContinuousKaehlerDifferential.residue_eq_coeff_neg_one_trace]

/-- **`Res_F(Tr_{L_d/F} ω) = d • Res_t^ℚ(ω)` on `puiseuxField.level K d`**, valid over any field
`K` in which `d` is nonzero. Here `ω` is an intrinsic continuous one-form on `L_d = K⸨t^(1/d)⸩`,
and its image in `puiseuxField K` has `dt`-coordinate
`(equivSelf K (level K d) ω : puiseuxField K)`. -/
theorem Extension.ContinuousKaehlerDifferential.residue_puiseuxLevel_eq_nsmul_puiseuxResidue
    {K : Type*} [Field K] (d : ℕ+) [NeZero ((d : ℕ) : K)]
    (ω : Extension.ContinuousKaehlerDifferential K (puiseuxField.level K d)) :
    Extension.ContinuousKaehlerDifferential.residue K (puiseuxField.level K d) ω =
      (d : ℕ) • puiseuxField.residue K
        (Extension.ContinuousKaehlerDifferential.equivSelf K (puiseuxField.level K d) ω :
          puiseuxField K) := by
  set y : Level K d :=
    (puiseuxField.levelEquiv K d).symm
      (Extension.ContinuousKaehlerDifferential.equivSelf K (puiseuxField.level K d) ω)
  have hy : ((puiseuxField.levelEquiv K d y : puiseuxField.level K d) : puiseuxField K) =
      (Extension.ContinuousKaehlerDifferential.equivSelf K (puiseuxField.level K d) ω :
        puiseuxField K) := by
    simp [y]
  have hω : Extension.ContinuousKaehlerDifferential.mapAlgHom
        (puiseuxField.levelEquiv K d).symm.toAlgHom ω =
      (Extension.ContinuousKaehlerDifferential.equivSelf K (Level K d)).symm y := by
    apply (Extension.ContinuousKaehlerDifferential.equivSelf K (Level K d)).injective
    rw [Extension.ContinuousKaehlerDifferential.equivSelf_mapAlgHom,
      LinearEquiv.apply_symm_apply, AlgEquiv.coe_toAlgHom]
  rw [← Extension.ContinuousKaehlerDifferential.residue_mapAlgHom_algEquiv
      (puiseuxField.levelEquiv K d).symm ω,
    hω, Level.ContinuousKaehlerDifferential.residue_equivSelf_symm_eq_levelResidue,
    Level.residue_eq_nsmul_residue_toPuiseux, ← puiseuxField.coe_levelEquiv_apply, hy]

namespace Level.ContinuousKaehlerDifferential

/-- **`Res_F(Tr_{L_d/F} ω) = d • Res_t^ℚ(levelMap K d ω)` in characteristic zero.** For any level
continuous one-form `ω : Level.ContinuousKaehlerDifferential K d`, the residue at `X` of its
differential trace down to `K⸨X⸩` is `d` times the rational-exponent Puiseux residue of its image
under `puiseuxField.ContinuousKaehlerDifferential.levelMap K d`. -/
theorem coeff_neg_one_equivLaurentSeries_trace_eq_nsmul_residue_levelMap
    {K : Type*} [Field K] [CharZero K] (d : ℕ+)
    (ω : Level.ContinuousKaehlerDifferential K d) :
    (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K
        (trace K d ω)).coeff (-1) =
      (d : ℕ) • puiseuxField.residue K
        (puiseuxField.ContinuousKaehlerDifferential.equivPuiseuxField K
          (puiseuxField.ContinuousKaehlerDifferential.levelMap K d
            (addEquivContinuousKaehlerDifferential K d ω))) := by
  set f : K⸨X⸩ := TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K
    (addEquivContinuousKaehlerDifferential K d ω)
  have h1 : _root_.LaurentSeries.derivative K (single 1 (1 : K)) = 1 := by simp
  rw [coeff_neg_one_equivLaurentSeries_trace, ringEquivLaurentSeries_equivLevel,
    show f.coeff (-1) = (f * _root_.LaurentSeries.derivative K (single 1 (1 : K))).coeff (-1) by
      rw [h1, mul_one],
    puiseuxField.coeff_neg_one_mul_derivative_eq_nsmul_residue d f (single 1 1),
    puiseuxField.ContinuousKaehlerDifferential.equivPuiseuxField_levelMap]

end Level.ContinuousKaehlerDifferential

end PuiseuxCorollaries

end TauCeti.LaurentSeries
