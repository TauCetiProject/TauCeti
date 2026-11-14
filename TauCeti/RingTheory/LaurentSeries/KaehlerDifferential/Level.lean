/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Field
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.FiniteExtension
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Trace
public import TauCeti.RingTheory.LaurentSeries.Level.Adjoin
public import TauCeti.RingTheory.LaurentSeries.Level.ModuleTopology
public import TauCeti.RingTheory.LaurentSeries.Level.Residue

/-!
# Continuous one-forms, traces, and residues on ramified levels and level charts

For a field `K` and a positive integer `d` with `(d : K) ≠ 0`, the ramified level `Level K d`
(`K⸨u⸩` with `u ^ d = t`) is finite separable, hence formally étale, over `F = K⸨t⸩`. It therefore
carries two constructions of continuous one-forms:

1. the intrinsic quotient `Extension.ContinuousKaehlerDifferential K (Level K d)` of
   `Ω[Level K d⁄K]` by the kernel of `D_{Level K d} = d/dt` (`Etale.lean`), equipped with its
   `Level K d`-module topology and intrinsic `trace` and `residue` (`Trace.lean`); and
2. the concrete coordinate module `Level.ContinuousKaehlerDifferential K d` (`g du` in the level
   variable `u`, from `Level/KaehlerDifferential.lean`), equipped with its valuation topology.

This file identifies these two objects in the category of topological `Level K d`-modules via
`Extension.ContinuousKaehlerDifferential.equivLevel`, proves that `D_{Level K d}` is
`(dx/du) / (d u ^ (d - 1))` so that `equivLevel` sends the universal derivation `D K (Level K d) x`
to `d_u x`, and shows that `equivLevel` intertwines base-change pullbacks, tensor-product
comparisons, differential traces, and residues. In particular:

* `Res_F(Tr_{Level K d / F} ω) = Res_{Level K d}(ω)` (`residue_level_eq_coeff_neg_one`),
* on the Puiseux embedding, `Res_{Level K d}(ω) = d • Res_t^ℚ(ω)`
  (`residue_level_eq_nsmul_puiseuxResidue`), and
* exact continuous one-forms `d x` have residue zero in every characteristic with `(d : K) ≠ 0`
  (`residue_level_D`).

Transporting along any `F`-algebra chart `e : L ≃ₐ[F] Level K d` produces the semilinear comparison
`AlgEquiv.laurentDifferentialEquiv` (upgraded to a continuous `F`-linear equivalence
`AlgEquiv.continuousLaurentDifferentialEquiv` whenever `L` carries the `F`-module topology, without
assuming continuity of `e`), proves chart-independence of the level-parameter residue directly on
`Ω¹_cont(L/K)`, and identifies `Extension.ContinuousKaehlerDifferential.residue` with
`Level.residueOfFinrankEq` when `K` is algebraically closed of characteristic zero.

## Main definitions

* `TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.equivLevel K d`: the continuous
  `Level K d`-linear equivalence
  `Extension.ContinuousKaehlerDifferential K (Level K d) ≃L[Level K d]
    Level.ContinuousKaehlerDifferential K d`.
* `AlgEquiv.laurentDifferentialEquiv`: the `e`-semilinear equivalence
  `Extension.ContinuousKaehlerDifferential K L ≃ₛₗ[e] Level.ContinuousKaehlerDifferential K d` for a
  separable level chart `e : L ≃ₐ[K⸨X⸩] Level K d`.
* `AlgEquiv.continuousLaurentDifferentialEquiv`: the upgrade of `e.laurentDifferentialEquiv` to a
  continuous `K⸨X⸩`-linear equivalence when `L` carries the `K⸨X⸩`-module topology.

## Main results

* `TauCeti.LaurentSeries.Level.formallyEtale_iff`: `Level K d` is formally étale over `K⸨X⸩` if and
  only if `(d : K) ≠ 0`.
* `TauCeti.LaurentSeries.Extension.ringEquivLaurentSeries_derivation`: on `Level K d`, `d/dt` is
  `(dx/du) / (d u ^ (d - 1))`, hence continuous (`continuous_derivation_level`,
  `continuous_D_level`).
* `Extension.ContinuousKaehlerDifferential.addEquivContinuousKaehlerDifferential_equivLevel_D`:
  `equivLevel` sends `D K (Level K d) x` to `d_u x`.
* `Extension.ContinuousKaehlerDifferential.trace_equivLevel`, `residue_level_eq_coeff_neg_one`,
  `residue_level_eq_levelResidue`, `residue_level_eq_nsmul_puiseuxResidue`, and `residue_level_D`:
  trace and residue comparisons on `Level K d`.
* `AlgEquiv.residue_eq_coeff_laurentDifferentialEquiv`,
  `AlgEquiv.coeff_laurentDifferentialEquiv_eq`, and `AlgEquiv.residue_D_of_algEquiv`: chart formula,
  chart-independence, and vanishing on exact forms for any extension admitting a separable level
  chart.
* `Extension.ContinuousKaehlerDifferential.residue_eq_residueOfFinrankEq` and `residue_D`:
  agreement with `Level.residueOfFinrankEq` and vanishing on exact forms over algebraically closed
  fields of characteristic zero.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968).
-/

public section

open HahnSeries TensorProduct
open scoped LaurentSeries

/-! ### Compatibility with scalar-extended trace and residue -/

namespace TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential

section BaseChangeCompatibility

variable {K L : Type*} [Field K] [Field L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]

/-- Under `L ⊗_{K⸨X⸩} Ω¹_cont(K⸨X⸩/K) ≃ Ω¹_cont(L/K)`, the intrinsic differential trace agrees with
`TauCeti.ContinuousKaehlerDifferential.traceBaseChange`. -/
@[simp]
theorem trace_tensorEquiv (η : L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (tensorEquiv K L η) = TauCeti.ContinuousKaehlerDifferential.traceBaseChange L η := by
  induction η using TensorProduct.inductionOn with
  | tmul x ω => simp
  | add η θ hη hθ => simp [hη, hθ]

/-- Under `L ⊗_{K⸨X⸩} Ω¹_cont(K⸨X⸩/K) ≃ Ω¹_cont(L/K)`, the intrinsic residue agrees with
`TauCeti.ContinuousKaehlerDifferential.residueBaseChange`. -/
@[simp]
theorem residue_tensorEquiv (η : L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    residue K L (tensorEquiv K L η) =
      TauCeti.ContinuousKaehlerDifferential.residueBaseChange L η := by
  rw [residue_apply, TauCeti.ContinuousKaehlerDifferential.residueBaseChange_apply,
    trace_tensorEquiv]

end BaseChangeCompatibility

end TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential

/-! ### Formal étaleness and `d/dt` on ramified levels -/

namespace TauCeti.LaurentSeries.Level

/-- The ramified level `Level K d` is formally étale over `K⸨X⸩` if and only if `(d : K) ≠ 0`. -/
theorem formallyEtale_iff {K : Type*} [Field K] {d : ℕ+} :
    Algebra.FormallyEtale K⸨X⸩ (Level K d) ↔ ((d : ℕ) : K) ≠ 0 := by
  rw [Algebra.FormallyEtale.iff_isSeparable, isSeparable_iff]

/-- When `(d : K) ≠ 0`, the ramified level `Level K d` is formally étale over `K⸨X⸩`. -/
instance {K : Type*} [Field K] {d : ℕ+} [NeZero ((d : ℕ) : K)] :
    Algebra.FormallyEtale K⸨X⸩ (Level K d) :=
  .of_isSeparable _ _

end TauCeti.LaurentSeries.Level

namespace TauCeti.LaurentSeries.Extension

section LevelDerivation

variable {K : Type*} [Field K] {d : ℕ+} [NeZero ((d : ℕ) : K)]

private theorem derivative_single_level_ne_zero :
    _root_.LaurentSeries.derivative K (single (d : ℤ) (1 : K)) ≠ 0 := by
  simp [NeZero.ne ((d : ℕ) : K)]

/-- **Explicit formula for `d/dt` on `Level K d`.** In the level parameter `u` (`u ^ d = t`),
`D_{Level K d} x = (dx/du) / (d u ^ (d - 1))`. -/
theorem ringEquivLaurentSeries_derivation (x : Level K d) :
    Level.ringEquivLaurentSeries K d (derivation K (Level K d) x) =
      _root_.LaurentSeries.derivative K (Level.ringEquivLaurentSeries K d x) /
        _root_.LaurentSeries.derivative K (single (d : ℤ) 1) := by
  let e := Level.algEquivLaurentSeries K d
  let c : Level K d := e.symm (_root_.LaurentSeries.derivative K (single (d : ℤ) 1))
  let δ₀ : Derivation K (Level K d) (Level K d) :=
    { toFun y := e.symm (_root_.LaurentSeries.derivative K (e y))
      map_add' y z := by simp
      map_smul' r y := by
        simp only [Algebra.smul_def, map_mul, AlgEquiv.commutes, RingHom.id_apply]
        rw [_root_.LaurentSeries.algebraMap_apply, C_mul_eq_smul, LinearMap.map_smul,
          ← C_mul_eq_smul, ← _root_.LaurentSeries.algebraMap_apply, ← e.commutes, map_mul,
          e.symm_apply_apply]
      map_one_eq_zero' := by
        change e.symm (_root_.LaurentSeries.derivative K (e 1)) = 0
        rw [map_one, ← laurentSeriesDerivation_apply, Derivation.map_one_eq_zero, map_zero]
      leibniz' y z := by
        change e.symm (_root_.LaurentSeries.derivative K (e (y * z))) =
          y * e.symm (_root_.LaurentSeries.derivative K (e z)) +
            z * e.symm (_root_.LaurentSeries.derivative K (e y))
        rw [map_mul, _root_.LaurentSeries.derivative_mul, map_add, map_mul, map_mul,
          e.symm_apply_apply, e.symm_apply_apply]
        ring }
  have hδ₀ (y : Level K d) :
      Level.ringEquivLaurentSeries K d (δ₀ y) =
        _root_.LaurentSeries.derivative K (Level.ringEquivLaurentSeries K d y) := by
    change Level.ringEquivLaurentSeries K d
      (e.symm (_root_.LaurentSeries.derivative K (e y))) = _
    rw [Level.algEquivLaurentSeries_symm_apply, RingEquiv.apply_symm_apply,
      Level.algEquivLaurentSeries_apply]
  have hc : Level.ringEquivLaurentSeries K d c =
      _root_.LaurentSeries.derivative K (single (d : ℤ) 1) := by
    change Level.ringEquivLaurentSeries K d (e.symm _) = _
    rw [Level.algEquivLaurentSeries_symm_apply, RingEquiv.apply_symm_apply]
  have hδ : c⁻¹ • δ₀ = derivation K (Level K d) := by
    refine eq_derivation fun f ↦ (Level.ringEquivLaurentSeries K d).injective ?_
    have hexp : _root_.LaurentSeries.derivative K (_root_.LaurentSeries.expand K d f) =
        _root_.LaurentSeries.expand K d (_root_.LaurentSeries.derivative K f) *
          _root_.LaurentSeries.derivative K (single (d : ℤ) 1) := by
      simpa only [TauCeti.LaurentSeries.substAlgHom_X_pow_eq_expand, PowerSeries.coe_pow,
        PowerSeries.coe_X, single_pow, one_pow, nsmul_one] using
        TauCeti.LaurentSeries.derivative_substAlgHom (K := K) (φ := PowerSeries.X ^ (d : ℕ))
          (by simp) (pow_ne_zero _ PowerSeries.X_ne_zero) f
    rw [smul_apply, smul_eq_mul, map_mul, map_inv₀, hc, hδ₀, Level.algebraMap_apply,
      hexp, mul_comm _ (_root_.LaurentSeries.derivative K (single (d : ℤ) 1)),
      inv_mul_cancel_left₀ derivative_single_level_ne_zero, Level.algebraMap_apply,
      laurentSeriesDerivation_apply]
  rw [← hδ, smul_apply, smul_eq_mul, map_mul, map_inv₀, hc, hδ₀, div_eq_mul_inv, mul_comm]

/-- On `Level K d`, `d/dt` sends the level parameter `u` to `(d u ^ (d - 1))⁻¹`. -/
theorem derivation_parameter :
    derivation K (Level K d) (Level.parameter K d) =
      (Level.ringEquivLaurentSeries K d).symm
        (_root_.LaurentSeries.derivative K (single (d : ℤ) 1))⁻¹ := by
  apply (Level.ringEquivLaurentSeries K d).injective
  rw [ringEquivLaurentSeries_derivation, RingEquiv.apply_symm_apply, Level.ringEquiv_parameter]
  simp [div_eq_inv_mul]

/-- The canonical derivation `d/dt` on a separable ramified level is continuous for the valuation
topology. -/
@[fun_prop]
theorem continuous_derivation_level : Continuous (derivation K (Level K d)) := by
  rw [← (Level.homeomorphLaurentSeries K d).comp_continuous_iff]
  have h : (Level.homeomorphLaurentSeries K d ∘ derivation K (Level K d)) =
      fun x ↦ _root_.LaurentSeries.derivative K (Level.homeomorphLaurentSeries K d x) *
        (_root_.LaurentSeries.derivative K (single (d : ℤ) 1))⁻¹ := by
    ext x
    simp [ringEquivLaurentSeries_derivation, div_eq_mul_inv]
  rw [h]
  exact (_root_.LaurentSeries.continuous_derivative.comp
    (Level.homeomorphLaurentSeries K d).continuous).mul continuous_const

/-- The universal continuous derivation `d : Level K d → Ω¹_cont(Level K d / K)` is continuous. -/
@[fun_prop]
theorem continuous_D_level :
    Continuous (ContinuousKaehlerDifferential.D K (Level K d)) :=
  ContinuousKaehlerDifferential.continuous_D_iff.mpr continuous_derivation_level

end LevelDerivation

/-! ### Comparison of `Extension.ContinuousKaehlerDifferential` with `Level` -/

namespace ContinuousKaehlerDifferential

section LevelComparison

variable (K : Type*) [Field K] (d : ℕ+) [NeZero ((d : ℕ) : K)]

/-- **Continuous `Level K d`-linear comparison of one-forms.** When `(d : K) ≠ 0`, the intrinsic
continuous one-forms `Extension.ContinuousKaehlerDifferential K (Level K d)` identify as a
topological `Level K d`-module with the concrete level one-forms
`Level.ContinuousKaehlerDifferential K d`, intertwining the base-change equivalences with
`Level K d ⊗_{K⸨X⸩} Ω¹_cont(K⸨X⸩/K)`. -/
noncomputable def equivLevel :
    ContinuousKaehlerDifferential K (Level K d) ≃L[Level K d]
      Level.ContinuousKaehlerDifferential K d :=
  ((tensorEquiv K (Level K d)).symm.trans
    (Level.ContinuousKaehlerDifferential.tensorEquiv K d)).toContinuousLinearEquivOfIsModuleTopology

variable {K d}

/-- `equivLevel` intertwines the two scalar-extension equivalences from
`Level K d ⊗_{K⸨X⸩} Ω¹_cont(K⸨X⸩/K)`. -/
@[simp]
theorem equivLevel_tensorEquiv
    (η : Level K d ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    equivLevel K d (tensorEquiv K (Level K d) η) =
      Level.ContinuousKaehlerDifferential.tensorEquiv K d η := by
  simp [equivLevel]

/-- The inverse of `equivLevel` intertwines the scalar-extension equivalences in the reverse
direction. -/
@[simp]
theorem equivLevel_symm_tensorEquiv
    (η : Level K d ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    (equivLevel K d).symm (Level.ContinuousKaehlerDifferential.tensorEquiv K d η) =
      tensorEquiv K (Level K d) η :=
  (equivLevel K d).symm_apply_eq.mpr (equivLevel_tensorEquiv η).symm

/-- `equivLevel` intertwines the pullbacks of continuous one-forms from `K⸨X⸩`. -/
@[simp]
theorem equivLevel_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    equivLevel K d (map K (Level K d) ω) = Level.ContinuousKaehlerDifferential.map K d ω := by
  rw [← one_smul (Level K d) (map K (Level K d) ω), ← tensorEquiv_tmul, equivLevel_tensorEquiv,
    Level.ContinuousKaehlerDifferential.tensorEquiv_tmul, one_smul]

/-- The inverse of `equivLevel` sends `Level.ContinuousKaehlerDifferential.map K d ω` back to
`map K (Level K d) ω`. -/
@[simp]
theorem equivLevel_symm_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    (equivLevel K d).symm (Level.ContinuousKaehlerDifferential.map K d ω) =
      map K (Level K d) ω :=
  (equivLevel K d).symm_apply_eq.mpr (equivLevel_map ω).symm

/-- In coordinates, `equivLevel` rewrites `g dt` as `g · d(u ^ d)/du · du`. -/
theorem equivLevel_apply_equivLevel (ω : ContinuousKaehlerDifferential K (Level K d)) :
    Level.ContinuousKaehlerDifferential.equivLevel K d (equivLevel K d ω) =
      equivSelf K (Level K d) ω *
        (Level.ringEquivLaurentSeries K d).symm
          (_root_.LaurentSeries.derivative K (single (d : ℤ) 1)) := by
  conv_lhs =>
    rw [← equivSelf_smul_D_algebraMap_single_one ω, ← map_D (L := Level K d) (single 1 1),
      map_smul, equivLevel_map]
  simp [smul_eq_mul]

/-- Under `equivLevel`, the intrinsic universal derivation `D K (Level K d) x` corresponds to the
formal differential `d_u x` in the level parameter `u`. -/
@[simp]
theorem addEquivContinuousKaehlerDifferential_equivLevel_D (x : Level K d) :
    Level.ContinuousKaehlerDifferential.addEquivContinuousKaehlerDifferential K d
        (equivLevel K d (D K (Level K d) x)) =
      TauCeti.ContinuousKaehlerDifferential.D K (Level.ringEquivLaurentSeries K d x) := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [← Level.ContinuousKaehlerDifferential.ringEquivLaurentSeries_equivLevel,
    equivLevel_apply_equivLevel, equivSelf_D, map_mul, ringEquivLaurentSeries_derivation,
    RingEquiv.apply_symm_apply, div_mul_cancel₀ _ derivative_single_level_ne_zero,
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D]

/-- `equivLevel` intertwines the intrinsic differential trace with the concrete level trace. -/
@[simp]
theorem trace_equivLevel (ω : ContinuousKaehlerDifferential K (Level K d)) :
    Level.ContinuousKaehlerDifferential.trace K d (equivLevel K d ω) =
      trace K (Level K d) ω := by
  conv_lhs =>
    rw [← equivSelf_smul_D_algebraMap_single_one ω, ← map_D (L := Level K d) (single 1 1),
      map_smul, equivLevel_map, Level.ContinuousKaehlerDifferential.trace_smul_map]
  conv_rhs =>
    rw [← equivSelf_smul_D_algebraMap_single_one ω, ← map_D (L := Level K d) (single 1 1),
      trace_smul_map]

/-- **Trace-residue formula on `Level K d`.** For every continuous one-form `ω` on a separable
ramified level, `Res_F(Tr_{Level K d / F} ω)` equals the `u⁻¹`-coefficient of `ω` in the level
parameter `u`. -/
theorem residue_level_eq_coeff_neg_one (ω : ContinuousKaehlerDifferential K (Level K d)) :
    residue K (Level K d) ω =
      (Level.ringEquivLaurentSeries K d
        (Level.ContinuousKaehlerDifferential.equivLevel K d (equivLevel K d ω))).coeff (-1) := by
  rw [residue_apply, ← trace_equivLevel,
    Level.ContinuousKaehlerDifferential.coeff_neg_one_equivLaurentSeries_trace]

/-- On `Level K d`, the intrinsic residue of `ω` agrees with `Level.residue K d` applied to its
`dt`-coefficient. -/
theorem residue_level_eq_levelResidue (ω : ContinuousKaehlerDifferential K (Level K d)) :
    residue K (Level K d) ω = Level.residue K d (equivSelf K (Level K d) ω) := by
  rw [residue_level_eq_coeff_neg_one, equivLevel_apply_equivLevel, map_mul,
    RingEquiv.apply_symm_apply, ← Level.residue_apply]

/-- **Puiseux residue comparison (`Res_F(Tr_{L_d/F} ω) = d • Res_t^ℚ(ω)`).** Embedded into the
Puiseux field via `Level.toPuiseux`, the intrinsic residue of a continuous one-form on `Level K d`
is `d` times the rational-exponent Puiseux residue of its `dt`-coefficient. -/
theorem residue_level_eq_nsmul_puiseuxResidue
    (ω : ContinuousKaehlerDifferential K (Level K d)) :
    residue K (Level K d) ω =
      (d : ℕ) • puiseuxField.residue K (Level.toPuiseux K d (equivSelf K (Level K d) ω)) := by
  rw [residue_level_eq_levelResidue, Level.residue_eq_nsmul_residue_toPuiseux]

/-- Exact continuous one-forms on a separable ramified level have residue zero, in every
characteristic with `(d : K) ≠ 0`. -/
@[simp]
theorem residue_level_D (x : Level K d) : residue K (Level K d) (D K (Level K d) x) = 0 := by
  rw [residue_level_eq_coeff_neg_one,
    Level.ContinuousKaehlerDifferential.ringEquivLaurentSeries_equivLevel,
    addEquivContinuousKaehlerDifferential_equivLevel_D,
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D,
    _root_.LaurentSeries.coeff_neg_one_derivative]

end LevelComparison

end ContinuousKaehlerDifferential

end TauCeti.LaurentSeries.Extension

/-! ### Separable level charts for extensions of `K⸨X⸩` -/

namespace AlgEquiv

open TauCeti TauCeti.LaurentSeries
open TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential

section LevelChart

variable {K L : Type*} [Field K] [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]
  {d : ℕ+} [NeZero ((d : ℕ) : K)]

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- **Level chart on intrinsic continuous one-forms.** A separable level chart
`e : L ≃ₐ[K⸨X⸩] Level K d` induces an `e`-semilinear equivalence between `Ω¹_cont(L/K)` and the
concrete level one-forms `Level.ContinuousKaehlerDifferential K d`. -/
noncomputable def laurentDifferentialEquiv (e : L ≃ₐ[K⸨X⸩] Level K d) :
    Extension.ContinuousKaehlerDifferential K L
      ≃ₛₗ[(e.toRingEquiv : L →+* Level K d)] Level.ContinuousKaehlerDifferential K d :=
  (mapAlgEquiv e).trans (equivLevel K d).toLinearEquiv

@[simp]
theorem laurentDifferentialEquiv_apply (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    e.laurentDifferentialEquiv ω = equivLevel K d (mapAlgEquiv e ω) :=
  (rfl)

@[simp]
theorem laurentDifferentialEquiv_symm_apply (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Level.ContinuousKaehlerDifferential K d) :
    e.laurentDifferentialEquiv.symm ω = (mapAlgEquiv e).symm ((equivLevel K d).symm ω) :=
  (rfl)

/-- A separable level chart sends `x • map K L ω` to `e x • Level...map K d ω`. -/
@[simp]
theorem laurentDifferentialEquiv_smul_map (e : L ≃ₐ[K⸨X⸩] Level K d) (x : L)
    (ω : TauCeti.ContinuousKaehlerDifferential K) :
    e.laurentDifferentialEquiv (x • map K L ω) =
      e x • Level.ContinuousKaehlerDifferential.map K d ω := by
  rw [laurentDifferentialEquiv_apply, mapAlgEquiv_apply, mapAlgHom_smul, mapAlgHom_map, map_smul,
    equivLevel_map, AlgEquiv.toAlgHom_apply]

/-- A separable level chart sends `D K L x` to `d_u (e x)` in the level parameter `u`. -/
@[simp]
theorem addEquivContinuousKaehlerDifferential_laurentDifferentialEquiv_D
    (e : L ≃ₐ[K⸨X⸩] Level K d) (x : L) :
    Level.ContinuousKaehlerDifferential.addEquivContinuousKaehlerDifferential K d
        (e.laurentDifferentialEquiv (D K L x)) =
      TauCeti.ContinuousKaehlerDifferential.D K (Level.ringEquivLaurentSeries K d (e x)) := by
  rw [laurentDifferentialEquiv_apply, mapAlgEquiv_apply, mapAlgHom_D, AlgEquiv.toAlgHom_apply,
    addEquivContinuousKaehlerDifferential_equivLevel_D]

/-- Over a field extension `E`, `e.laurentDifferentialEquiv` agrees with
`e.laurentDifferentialTensorEquiv` through `tensorEquiv K E`. -/
@[simp]
theorem laurentDifferentialEquiv_tensorEquiv {E : Type*} [Field E] [Algebra K⸨X⸩ E] [Algebra K E]
    [IsScalarTower K K⸨X⸩ E] [Algebra.FormallyEtale K⸨X⸩ E] (e : E ≃ₐ[K⸨X⸩] Level K d)
    (η : E ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    e.laurentDifferentialEquiv (tensorEquiv K E η) = e.laurentDifferentialTensorEquiv η := by
  induction η using TensorProduct.inductionOn with
  | tmul x ω =>
    rw [tensorEquiv_tmul, laurentDifferentialEquiv_smul_map, laurentDifferentialTensorEquiv_tmul]
  | add η θ hη hθ =>
    rw [map_add, LinearEquiv.map_add, map_add, hη, hθ]

/-- Every separable level chart intertwines the concrete level trace with the intrinsic
differential trace on `Ω¹_cont(L/K)`. -/
@[simp]
theorem trace_laurentDifferentialEquiv (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    Level.ContinuousKaehlerDifferential.trace K d (e.laurentDifferentialEquiv ω) =
      trace K L ω := by
  rw [laurentDifferentialEquiv_apply, trace_equivLevel, trace_mapAlgEquiv]

/-- **Trace-residue compatibility in any level chart.** On `Ω¹_cont(L/K)`, the intrinsic residue
equals the `u⁻¹`-coefficient in the level parameter of any separable level chart. -/
theorem residue_eq_coeff_laurentDifferentialEquiv (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    residue K L ω =
      (Level.ringEquivLaurentSeries K d
        (Level.ContinuousKaehlerDifferential.equivLevel K d
          (e.laurentDifferentialEquiv ω))).coeff (-1) := by
  rw [← residue_mapAlgEquiv e ω, residue_level_eq_coeff_neg_one, laurentDifferentialEquiv_apply]

/-- **Chart-independence of the level residue on `Ω¹_cont(L/K)`.** Any two separable level charts
compute the same coefficient residue on continuous one-forms, even for different level indices. -/
theorem coeff_laurentDifferentialEquiv_eq {n : ℕ+} [NeZero ((n : ℕ) : K)]
    (e : L ≃ₐ[K⸨X⸩] Level K d) (e' : L ≃ₐ[K⸨X⸩] Level K n)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    (Level.ringEquivLaurentSeries K d
      (Level.ContinuousKaehlerDifferential.equivLevel K d
        (e.laurentDifferentialEquiv ω))).coeff (-1) =
    (Level.ringEquivLaurentSeries K n
      (Level.ContinuousKaehlerDifferential.equivLevel K n
        (e'.laurentDifferentialEquiv ω))).coeff (-1) := by
  rw [← residue_eq_coeff_laurentDifferentialEquiv e, ← residue_eq_coeff_laurentDifferentialEquiv e']

/-- If `L` admits a separable level chart, every exact continuous one-form `D K L x` has residue
zero, in every characteristic with `(d : K) ≠ 0`. -/
theorem residue_D_of_algEquiv (e : L ≃ₐ[K⸨X⸩] Level K d) (x : L) :
    residue K L (D K L x) = 0 := by
  rw [← residue_mapAlgEquiv e, mapAlgEquiv_apply, mapAlgHom_D, residue_level_D]

/-- When `L` carries the `K⸨X⸩`-module topology, any algebraic separable level chart upgrades
automatically to a continuous `K⸨X⸩`-linear equivalence of continuous one-forms, without assuming
continuity of `e` in advance. -/
noncomputable def continuousLaurentDifferentialEquiv [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L]
    (e : L ≃ₐ[K⸨X⸩] Level K d) :
    Extension.ContinuousKaehlerDifferential K L ≃L[K⸨X⸩]
      Level.ContinuousKaehlerDifferential K d :=
  have : Module.Finite K⸨X⸩ L := Module.Finite.equiv e.symm.toLinearEquiv
  let eₗ : Extension.ContinuousKaehlerDifferential K L ≃ₗ[K⸨X⸩]
      Level.ContinuousKaehlerDifferential K d :=
    { toFun := e.laurentDifferentialEquiv
      invFun := e.laurentDifferentialEquiv.symm
      left_inv := e.laurentDifferentialEquiv.left_inv
      right_inv := e.laurentDifferentialEquiv.right_inv
      map_add' := LinearEquiv.map_add _
      map_smul' f ω := by
        rw [← IsScalarTower.algebraMap_smul L f ω, e.laurentDifferentialEquiv.map_smulₛₗ,
          RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv, e.commutes,
          IsScalarTower.algebraMap_smul, RingHom.id_apply] }
  eₗ.toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem continuousLaurentDifferentialEquiv_apply [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L]
    (e : L ≃ₐ[K⸨X⸩] Level K d) (ω : Extension.ContinuousKaehlerDifferential K L) :
    e.continuousLaurentDifferentialEquiv ω = e.laurentDifferentialEquiv ω := by
  simp [continuousLaurentDifferentialEquiv]

@[simp]
theorem continuousLaurentDifferentialEquiv_symm_apply [TopologicalSpace L]
    [IsModuleTopology K⸨X⸩ L] (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Level.ContinuousKaehlerDifferential K d) :
    e.continuousLaurentDifferentialEquiv.symm ω = e.laurentDifferentialEquiv.symm ω := by
  simp [continuousLaurentDifferentialEquiv]

end LevelChart

end AlgEquiv

/-! ### Algebraically closed residue fields of characteristic zero -/

namespace TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential

section AlgClosedCharZero

variable {K L : Type*} [Field K] [IsAlgClosed K] [CharZero K]
  [Field L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
  [Algebra.FormallyEtale K⸨X⸩ L]

/-- Over an algebraically closed residue field of characteristic zero, the intrinsic residue on
`Ω¹_cont(L/K)` agrees with `Level.residueOfFinrankEq` applied to the `dt`-coefficient. -/
theorem residue_eq_residueOfFinrankEq {e : ℕ+} (h : Module.finrank K⸨X⸩ L = e)
    (ω : ContinuousKaehlerDifferential K L) :
    residue K L ω = Level.residueOfFinrankEq h (equivSelf K L ω) := by
  rw [residue_eq_coeff_neg_one_trace, Level.residueOfFinrankEq_eq_coeff_neg_one_trace]

/-- Over an algebraically closed residue field of characteristic zero, every exact continuous
one-form `D K L x` on a finite extension `L` of `K⸨X⸩` has residue zero. -/
@[simp]
theorem residue_D [FiniteDimensional K⸨X⸩ L] (x : L) :
    residue K L (D K L x) = 0 := by
  let e : ℕ+ := ⟨Module.finrank K⸨X⸩ L, Module.finrank_pos⟩
  have : NeZero ((e : ℕ) : K) := ⟨Nat.cast_ne_zero.mpr e.ne_zero⟩
  exact (Level.algEquivOfFinrankEq (e := e) rfl).residue_D_of_algEquiv x

end AlgClosedCharZero

end TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential
