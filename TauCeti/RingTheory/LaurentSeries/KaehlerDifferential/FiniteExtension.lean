/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Trace
public import TauCeti.RingTheory.LaurentSeries.Level.ModuleTopology
public import TauCeti.RingTheory.LaurentSeries.Level.Residue

/-!
# Level and level-chart comparisons for continuous one-forms on Laurent extensions

Write `F = K⸨X⸩` and `Ω = TauCeti.ContinuousKaehlerDifferential K`.

For the finite separable ramified level `Level K d` (`t = u ^ d`, `[NeZero ((d : ℕ) : K)]`), the
canonical formally étale derivation `Extension.derivation K (Level K d)` acts in the level variable
`u` as `(d x / d u) / (d(u ^ d) / d u)` (`ringEquivLaurentSeries_derivation_level`), and the general
formally étale module `Extension.ContinuousKaehlerDifferential K (Level K d)` is identified with the
explicit level module `Level.ContinuousKaehlerDifferential K d` by a continuous `Level K d`-linear
equivalence `Extension.ContinuousKaehlerDifferential.equivLevelContinuousKaehlerDifferential K d`.
Under this equivalence, `D K (Level K d) x` corresponds to
`Level.ContinuousKaehlerDifferential.D K d x` in the level uniformizer `u`, the intrinsic and
explicit differential traces agree (`trace_equivLevelContinuousKaehlerDifferential`), and
`Res_F(Tr_{L/F} ω) = Res_L(ω)` holds on `Ω¹_cont(L/K)`
(`residue_eq_coeff_equivLevelContinuousKaehlerDifferential`).

More generally, any level chart `e : L ≃ₐ[F] Level K d` identifies scalar-extended forms `L ⊗[F] Ω`
(`AlgEquiv.laurentDifferentialTensorEquiv`) and, when `L` is formally étale over `F`, intrinsic
continuous forms `Ω¹_cont(L/K)` (`AlgEquiv.laurentDifferentialEquiv`, upgraded to
`AlgEquiv.laurentDifferentialContinuousEquiv` under `[IsModuleTopology F L]`) with
`Level.ContinuousKaehlerDifferential K d`, sending `d x` to `d_u (e x)`, intertwining differential
traces, and computing `Extension.ContinuousKaehlerDifferential.residue K L ω` as the
`u⁻¹`-coefficient in the chart parameter `u` independently of the choice of chart.

## Main definitions

* `Extension.ContinuousKaehlerDifferential.equivLevelContinuousKaehlerDifferential K d`: the
  continuous `Level K d`-linear equivalence
  `Extension.ContinuousKaehlerDifferential K (Level K d) ≃L[Level K d]
  Level.ContinuousKaehlerDifferential K d`.
* `AlgEquiv.laurentDifferentialTensorEquiv`: the `F`-linear equivalence
  `L ⊗[F] Ω ≃ₗ[F] Level.ContinuousKaehlerDifferential K d` induced by `e : L ≃ₐ[F] Level K d`.
* `AlgEquiv.laurentDifferentialEquiv` and `AlgEquiv.laurentDifferentialContinuousEquiv`: the
  `F`-linear and continuous `F`-linear equivalences
  `Extension.ContinuousKaehlerDifferential K L ≃ Level.ContinuousKaehlerDifferential K d` induced by
  a level chart `e : L ≃ₐ[F] Level K d`.

## Main results

* `TauCeti.LaurentSeries.Extension.ringEquivLaurentSeries_derivation_level`: `d/dt` on `Level K d`
  in the level parameter `u`.
* `Extension.ContinuousKaehlerDifferential.equivLevelContinuousKaehlerDifferential_D`:
  `equivLevelContinuousKaehlerDifferential K d` sends `D K (Level K d) x` to
  `Level.ContinuousKaehlerDifferential.D K d x`.
* `Extension.ContinuousKaehlerDifferential.trace_equivLevelContinuousKaehlerDifferential` and
  `residue_eq_coeff_equivLevelContinuousKaehlerDifferential`: compatibility of
  `equivLevelContinuousKaehlerDifferential K d` with traces and `u⁻¹`-residues.
* `Extension.ContinuousKaehlerDifferential.residue_eq_levelResidue` and
  `Extension.ContinuousKaehlerDifferential.residue_eq_residueOfFinrankEq`: agreement of the
  intrinsic differential residue on `Ω¹_cont(L/K)` with `Level.residue` and
  `Level.residueOfFinrankEq`.
* `AlgEquiv.trace_laurentDifferentialTensorEquiv`, `AlgEquiv.residueBaseChange_eq_coeff`, and
  `AlgEquiv.coeff_laurentDifferentialTensorEquiv_eq`: chart compatibility and chart independence on
  `L ⊗[F] Ω`.
* `AlgEquiv.laurentDifferentialEquiv_D`, `AlgEquiv.trace_laurentDifferentialEquiv`,
  `AlgEquiv.residue_eq_coeff_laurentDifferentialEquiv`, and
  `AlgEquiv.coeff_laurentDifferentialEquiv_eq`: chart transport of `d`, trace-residue compatibility,
  and chart independence on `Ω¹_cont(L/K)`.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968), Theorem 1, for the
  compatibility of trace-defined residues with local uniformizer coordinates.
-/

public section

open HahnSeries TensorProduct
open scoped PowerSeries LaurentSeries

namespace TauCeti.LaurentSeries.Extension

/-! ### Derivative on a finite separable ramified level -/

section LevelDerivation

/-- On a finite separable ramified level `Level K d` (`t = u ^ d`), the canonical derivation
`d/dt` acts in the level variable `u` as `(d x / d u) / (d(u ^ d) / d u)`. -/
theorem ringEquivLaurentSeries_derivation_level {K : Type*} [Field K] {d : ℕ+}
    [NeZero ((d : ℕ) : K)] (x : Level K d) :
    Level.ringEquivLaurentSeries K d (derivation K (Level K d) x) =
      _root_.LaurentSeries.derivative K (Level.ringEquivLaurentSeries K d x) /
        _root_.LaurentSeries.derivative K (single (d : ℤ) 1) := by
  set c : Level K d :=
    (Level.ringEquivLaurentSeries K d).symm (_root_.LaurentSeries.derivative K (single (d : ℤ) 1))
  have hδ : c⁻¹ • Level.derivation K d = derivation K (Level K d) := by
    refine eq_derivation fun f ↦ (Level.ringEquivLaurentSeries K d).injective ?_
    have hpow : ((PowerSeries.X ^ (d : ℕ) : K⟦X⟧) : K⸨X⸩) = single (d : ℤ) 1 := by
      simp [PowerSeries.coe_pow, single_pow]
    rw [_root_.smul_apply, smul_eq_mul, map_mul, map_inv₀, RingEquiv.apply_symm_apply,
      Level.ringEquivLaurentSeries_derivation, Level.algebraMap_apply, Level.algebraMap_apply,
      ← TauCeti.LaurentSeries.substAlgHom_X_pow_eq_expand,
      TauCeti.LaurentSeries.derivative_substAlgHom, hpow, laurentSeriesDerivation_apply,
      inv_mul_eq_div,
      mul_div_cancel_right₀ _ _root_.LaurentSeries.derivative_single_natCast_one_ne_zero]
  rw [← hδ, _root_.smul_apply, smul_eq_mul, map_mul, map_inv₀, RingEquiv.apply_symm_apply,
    Level.ringEquivLaurentSeries_derivation, inv_mul_eq_div]

end LevelDerivation

namespace ContinuousKaehlerDifferential

/-! ### Identification for a finite separable ramified level -/

section Level

variable (K : Type*) [Field K] (d : ℕ+) [NeZero ((d : ℕ) : K)]

/-- **Equivalence with explicit ramified-level one-forms.** For `d` nonzero in `K`, `Level K d` is
formally étale over `K⸨X⸩`, and the continuous `Level K d`-linear equivalence
`equivLevelContinuousKaehlerDifferential K d` identifies
`Extension.ContinuousKaehlerDifferential K (Level K d)` with
`Level.ContinuousKaehlerDifferential K d` by matching their base-change decompositions over
`Ω¹_cont(K⸨X⸩/K)`. -/
noncomputable def equivLevelContinuousKaehlerDifferential :
    ContinuousKaehlerDifferential K (Level K d) ≃L[Level K d]
      Level.ContinuousKaehlerDifferential K d :=
  ((tensorEquiv K (Level K d)).symm.trans
    (Level.ContinuousKaehlerDifferential.tensorEquiv K d)).toContinuousLinearEquivOfIsModuleTopology

variable {K d}

@[simp]
theorem equivLevelContinuousKaehlerDifferential_tensorEquiv
    (η : Level K d ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    equivLevelContinuousKaehlerDifferential K d (tensorEquiv K (Level K d) η) =
      Level.ContinuousKaehlerDifferential.tensorEquiv K d η := by
  simp [equivLevelContinuousKaehlerDifferential]

@[simp]
theorem equivLevelContinuousKaehlerDifferential_symm_tensorEquiv
    (η : Level K d ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    (equivLevelContinuousKaehlerDifferential K d).symm
        (Level.ContinuousKaehlerDifferential.tensorEquiv K d η) =
      tensorEquiv K (Level K d) η := by
  simp [equivLevelContinuousKaehlerDifferential]

@[simp]
theorem equivLevelContinuousKaehlerDifferential_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    equivLevelContinuousKaehlerDifferential K d (map K (Level K d) ω) =
      Level.ContinuousKaehlerDifferential.map K d ω := by
  simpa using equivLevelContinuousKaehlerDifferential_tensorEquiv (K := K) (d := d) (1 ⊗ₜ[K⸨X⸩] ω)

@[simp]
theorem equivLevelContinuousKaehlerDifferential_symm_map
    (ω : TauCeti.ContinuousKaehlerDifferential K) :
    (equivLevelContinuousKaehlerDifferential K d).symm
        (Level.ContinuousKaehlerDifferential.map K d ω) =
      map K (Level K d) ω := by
  simpa using
    equivLevelContinuousKaehlerDifferential_symm_tensorEquiv (K := K) (d := d) (1 ⊗ₜ[K⸨X⸩] ω)

/-- In coordinates, `equivLevelContinuousKaehlerDifferential K d` converts `x dt` into
`(x * d u ^ (d - 1)) du`. -/
theorem equivLevel_equivLevelContinuousKaehlerDifferential
    (ω : ContinuousKaehlerDifferential K (Level K d)) :
    Level.ContinuousKaehlerDifferential.equivLevel K d
        (equivLevelContinuousKaehlerDifferential K d ω) =
      equivSelf K (Level K d) ω *
        (Level.ringEquivLaurentSeries K d).symm
          (_root_.LaurentSeries.derivative K (single (d : ℤ) 1)) := by
  conv_lhs => rw [← equivSelf_smul_D_algebraMap_single_one ω, ← map_D]
  rw [ContinuousLinearEquiv.map_smul, equivLevelContinuousKaehlerDifferential_map,
    LinearEquiv.map_smul, Level.ContinuousKaehlerDifferential.equivLevel_map,
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D_single_one]
  simp [smul_eq_mul]

/-- Under `equivLevelContinuousKaehlerDifferential K d`, the formally étale differential
`D K (Level K d) x` is the level differential `Level.ContinuousKaehlerDifferential.D K d x`. -/
@[simp]
theorem equivLevelContinuousKaehlerDifferential_D (x : Level K d) :
    equivLevelContinuousKaehlerDifferential K d (D K (Level K d) x) =
      Level.ContinuousKaehlerDifferential.D K d x := by
  apply (Level.ContinuousKaehlerDifferential.equivLevel K d).injective
  apply (Level.ringEquivLaurentSeries K d).injective
  rw [equivLevel_equivLevelContinuousKaehlerDifferential, equivSelf_D,
    Level.ContinuousKaehlerDifferential.equivLevel_D, map_mul, RingEquiv.apply_symm_apply,
    RingEquiv.apply_symm_apply, ringEquivLaurentSeries_derivation_level,
    div_mul_cancel₀ _ _root_.LaurentSeries.derivative_single_natCast_one_ne_zero]

@[simp]
theorem equivLevelContinuousKaehlerDifferential_symm_D (x : Level K d) :
    (equivLevelContinuousKaehlerDifferential K d).symm
        (Level.ContinuousKaehlerDifferential.D K d x) =
      D K (Level K d) x :=
  (equivLevelContinuousKaehlerDifferential K d).symm_apply_eq.mpr
    (equivLevelContinuousKaehlerDifferential_D x).symm

/-- `equivLevelContinuousKaehlerDifferential K d` intertwines the intrinsic formally étale
differential trace with the explicit level differential trace. -/
@[simp]
theorem trace_equivLevelContinuousKaehlerDifferential
    (ω : ContinuousKaehlerDifferential K (Level K d)) :
    Level.ContinuousKaehlerDifferential.trace K d
        (equivLevelContinuousKaehlerDifferential K d ω) =
      trace K (Level K d) ω := by
  obtain ⟨η, rfl⟩ := (tensorEquiv K (Level K d)).surjective ω
  rw [equivLevelContinuousKaehlerDifferential_tensorEquiv, trace_tensorEquiv]
  induction η using TensorProduct.inductionOn with
  | tmul g ω => simp
  | add x y hx hy => simp [hx, hy]

/-- **`Res_F(Tr_{L/F} ω) = Res_L(ω)` on a finite separable ramified level.** For `L = Level K d`
with `d` nonzero in `K`, the trace-defined residue `residue K (Level K d) ω` equals the coefficient
of `u⁻¹` of `ω` read in the level uniformizer `u`. -/
theorem residue_eq_coeff_equivLevelContinuousKaehlerDifferential
    (ω : ContinuousKaehlerDifferential K (Level K d)) :
    residue K (Level K d) ω =
      (Level.ringEquivLaurentSeries K d
        (Level.ContinuousKaehlerDifferential.equivLevel K d
          (equivLevelContinuousKaehlerDifferential K d ω))).coeff (-1) := by
  rw [residue_apply, ← trace_equivLevelContinuousKaehlerDifferential,
    Level.ContinuousKaehlerDifferential.residue_trace]

/-- On a finite separable ramified level `Level K d` (`[NeZero ((d : ℕ) : K)]`), the intrinsic
differential residue `residue K (Level K d)` agrees with `Level.residue K d` on the `dt`-coordinate
`equivSelf K (Level K d) ω`. -/
theorem residue_eq_levelResidue (ω : ContinuousKaehlerDifferential K (Level K d)) :
    residue K (Level K d) ω = Level.residue K d (equivSelf K (Level K d) ω) := by
  rw [residue_eq_coeff_neg_one_trace, Level.coeff_neg_one_trace, ← Level.residue_apply]

end Level

section FiniteExtension

/-- Over an algebraically closed coefficient field `K` of characteristic zero, the intrinsic
residue `residue K L` on `Ω¹_cont(L/K)` agrees with `Level.residueOfFinrankEq` applied to the
`dt`-coordinate `equivSelf K L ω`. -/
theorem residue_eq_residueOfFinrankEq {K L : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    [Field L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
    [Algebra.FormallyEtale K⸨X⸩ L] {d : ℕ+} (h : Module.finrank K⸨X⸩ L = d)
    (ω : ContinuousKaehlerDifferential K L) :
    residue K L ω = Level.residueOfFinrankEq h (equivSelf K L ω) := by
  rw [residue_eq_coeff_neg_one_trace, Level.residueOfFinrankEq_eq_coeff_neg_one_trace]

end FiniteExtension

end ContinuousKaehlerDifferential

end TauCeti.LaurentSeries.Extension

namespace AlgEquiv

open TauCeti TauCeti.ContinuousKaehlerDifferential
open TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential

section BaseChange

variable {K : Type*} [Field K] {L : Type*} [CommRing L] [Algebra K⸨X⸩ L]
  {d : ℕ+} [NeZero ((d : ℕ) : K)]

/-- A level chart identifies scalar-extended forms with the continuous forms of that
level. This is an equivalence over the base Laurent field; scalar multiplication by
`x : L` corresponds to multiplication by `e x` on the target. -/
noncomputable def laurentDifferentialTensorEquiv (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d) :
    L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K ≃ₗ[K⸨X⸩]
      TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential K d :=
  (TensorProduct.congr e.toLinearEquiv (.refl K⸨X⸩ _)).trans
    ((TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.tensorEquiv K d).restrictScalars
      K⸨X⸩)

@[simp]
theorem laurentDifferentialTensorEquiv_tmul (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (x : L) (ω : ContinuousKaehlerDifferential K) :
    e.laurentDifferentialTensorEquiv (x ⊗ₜ ω) =
      e x • TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.map K d ω := by
  simp [laurentDifferentialTensorEquiv]

/-- The inverse chart comparison sends a scalar multiple of a pulled-back form to
its corresponding pure tensor. -/
@[simp]
theorem laurentDifferentialTensorEquiv_symm_smul_map
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (x : TauCeti.LaurentSeries.Level K d) (ω : ContinuousKaehlerDifferential K) :
    e.laurentDifferentialTensorEquiv.symm
        (x • TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.map K d ω) =
      e.symm x ⊗ₜ ω := by
  apply e.laurentDifferentialTensorEquiv.symm_apply_eq.mpr
  simp

/-- The chart comparison respects the extension's scalar action through the chart. -/
@[simp]
theorem laurentDifferentialTensorEquiv_smul
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (x : L) (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    e.laurentDifferentialTensorEquiv (x • η) = e x • e.laurentDifferentialTensorEquiv η := by
  induction η using TensorProduct.inductionOn with
  | tmul y ω => simp [smul_tmul', smul_eq_mul, mul_smul]
  | add η θ hη hθ => simp [smul_add, hη, hθ]

/-- Differential trace commutes with every level chart. In particular the trace
transported from the explicit level is the trace on the first tensor factor. -/
@[simp]
theorem trace_laurentDifferentialTensorEquiv
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.trace K d
        (e.laurentDifferentialTensorEquiv η) = traceBaseChange L η := by
  induction η using TensorProduct.inductionOn with
  | tmul x ω =>
    simp only [laurentDifferentialTensorEquiv_tmul,
      TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.trace_smul_map,
      traceBaseChange_tmul]
    rw [Algebra.trace_eq_of_algEquiv e]
  | add η θ hη hθ => simp [hη, hθ]

/-- **Trace-residue compatibility in any level chart.** The residue of the trace
of a scalar-extended form is the coefficient residue in the level parameter. -/
theorem residueBaseChange_eq_coeff (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    residueBaseChange L η =
      (TauCeti.LaurentSeries.Level.ringEquivLaurentSeries K d
        (TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.equivLevel K d
          (e.laurentDifferentialTensorEquiv η))).coeff (-1) := by
  rw [residueBaseChange_apply, ← trace_laurentDifferentialTensorEquiv e]
  exact residue_trace _

/-- **Independence of the level chart.** Two isomorphisms with ramified levels give
the same coefficient residue on scalar-extended forms. The levels need not be
identified in advance. -/
theorem coeff_laurentDifferentialTensorEquiv_eq {n : ℕ+} [NeZero ((n : ℕ) : K)]
    (e : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K d)
    (e' : L ≃ₐ[K⸨X⸩] TauCeti.LaurentSeries.Level K n)
    (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    (TauCeti.LaurentSeries.Level.ringEquivLaurentSeries K d
      (TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.equivLevel K d
        (e.laurentDifferentialTensorEquiv η))).coeff (-1) =
    (TauCeti.LaurentSeries.Level.ringEquivLaurentSeries K n
      (TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential.equivLevel K n
        (e'.laurentDifferentialTensorEquiv η))).coeff (-1) := by
  rw [← residueBaseChange_eq_coeff e, ← residueBaseChange_eq_coeff e']

end BaseChange

section EtaleChart

open TauCeti.LaurentSeries

variable {K : Type*} [Field K] {L : Type*} [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L] {d : ℕ+} [NeZero ((d : ℕ) : K)]

/-- A level chart `e : L ≃ₐ[K⸨X⸩] Level K d` on a formally étale `K⸨X⸩`-algebra `L` identifies
`Extension.ContinuousKaehlerDifferential K L` with `Level.ContinuousKaehlerDifferential K d` over
`K⸨X⸩`, semilinearly with respect to `e`. -/
noncomputable def laurentDifferentialEquiv (e : L ≃ₐ[K⸨X⸩] Level K d) :
    Extension.ContinuousKaehlerDifferential K L ≃ₗ[K⸨X⸩]
      Level.ContinuousKaehlerDifferential K d :=
  (Extension.ContinuousKaehlerDifferential.congrLinearEquiv (K := K) e).trans
    ((Extension.ContinuousKaehlerDifferential.equivLevelContinuousKaehlerDifferential
      K d).toLinearEquiv.restrictScalars K⸨X⸩)

/-- `e.laurentDifferentialEquiv` transports along `e` via `mapSemilinear` and then identifies with
explicit level one-forms via `equivLevelContinuousKaehlerDifferential K d`. -/
theorem laurentDifferentialEquiv_apply (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    e.laurentDifferentialEquiv ω =
      Extension.ContinuousKaehlerDifferential.equivLevelContinuousKaehlerDifferential K d
        (Extension.ContinuousKaehlerDifferential.mapSemilinear
          (e : L →ₐ[K⸨X⸩] Level K d) ω) := by
  rw [laurentDifferentialEquiv, LinearEquiv.trans_apply,
    Extension.ContinuousKaehlerDifferential.congrLinearEquiv_apply,
    LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv]

/-- The inverse of `e.laurentDifferentialEquiv` applies
`(equivLevelContinuousKaehlerDifferential K d).symm` followed by
`mapSemilinear (e.symm : Level K d →ₐ[K⸨X⸩] L)`. -/
theorem laurentDifferentialEquiv_symm_apply (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Level.ContinuousKaehlerDifferential K d) :
    e.laurentDifferentialEquiv.symm ω =
      Extension.ContinuousKaehlerDifferential.mapSemilinear
        (e.symm : Level K d →ₐ[K⸨X⸩] L)
        ((Extension.ContinuousKaehlerDifferential.equivLevelContinuousKaehlerDifferential
          K d).symm ω) := by
  rw [laurentDifferentialEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.restrictScalars_symm_apply, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
    Extension.ContinuousKaehlerDifferential.congrLinearEquiv_symm,
    Extension.ContinuousKaehlerDifferential.congrLinearEquiv_apply]

@[simp]
theorem laurentDifferentialEquiv_map (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : TauCeti.ContinuousKaehlerDifferential K) :
    e.laurentDifferentialEquiv (Extension.ContinuousKaehlerDifferential.map K L ω) =
      Level.ContinuousKaehlerDifferential.map K d ω := by
  rw [laurentDifferentialEquiv_apply, Extension.ContinuousKaehlerDifferential.mapSemilinear_map,
    Extension.ContinuousKaehlerDifferential.equivLevelContinuousKaehlerDifferential_map]

@[simp]
theorem laurentDifferentialEquiv_symm_map (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : TauCeti.ContinuousKaehlerDifferential K) :
    e.laurentDifferentialEquiv.symm (Level.ContinuousKaehlerDifferential.map K d ω) =
      Extension.ContinuousKaehlerDifferential.map K L ω := by
  apply e.laurentDifferentialEquiv.symm_apply_eq.mpr
  simp

@[simp]
theorem laurentDifferentialEquiv_tensorEquiv (e : L ≃ₐ[K⸨X⸩] Level K d)
    (η : L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    e.laurentDifferentialEquiv (Extension.ContinuousKaehlerDifferential.tensorEquiv K L η) =
      e.laurentDifferentialTensorEquiv η := by
  induction η using TensorProduct.inductionOn with
  | tmul x ω =>
    rw [Extension.ContinuousKaehlerDifferential.tensorEquiv_tmul, laurentDifferentialEquiv_apply,
      Extension.ContinuousKaehlerDifferential.mapSemilinear_smul,
      Extension.ContinuousKaehlerDifferential.mapSemilinear_map, AlgEquiv.coe_toAlgHom,
      ContinuousLinearEquiv.map_smul,
      Extension.ContinuousKaehlerDifferential.equivLevelContinuousKaehlerDifferential_map,
      laurentDifferentialTensorEquiv_tmul]
  | add x y hx hy => simp [hx, hy]

@[simp]
theorem laurentDifferentialEquiv_symm_laurentDifferentialTensorEquiv
    (e : L ≃ₐ[K⸨X⸩] Level K d) (η : L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    e.laurentDifferentialEquiv.symm (e.laurentDifferentialTensorEquiv η) =
      Extension.ContinuousKaehlerDifferential.tensorEquiv K L η := by
  apply e.laurentDifferentialEquiv.symm_apply_eq.mpr
  simp

@[simp]
theorem laurentDifferentialEquiv_smul (e : L ≃ₐ[K⸨X⸩] Level K d) (x : L)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    e.laurentDifferentialEquiv (x • ω) = e x • e.laurentDifferentialEquiv ω := by
  obtain ⟨η, rfl⟩ := (Extension.ContinuousKaehlerDifferential.tensorEquiv K L).surjective ω
  rw [← LinearEquiv.map_smul, laurentDifferentialEquiv_tensorEquiv,
    laurentDifferentialEquiv_tensorEquiv, laurentDifferentialTensorEquiv_smul]

@[simp]
theorem laurentDifferentialEquiv_symm_smul (e : L ≃ₐ[K⸨X⸩] Level K d) (x : Level K d)
    (ω : Level.ContinuousKaehlerDifferential K d) :
    e.laurentDifferentialEquiv.symm (x • ω) = e.symm x • e.laurentDifferentialEquiv.symm ω := by
  apply e.laurentDifferentialEquiv.symm_apply_eq.mpr
  simp

/-- A level chart sends the étale differential `d x` on `L` to the level differential `d_u (e x)`
in the level parameter `u`. -/
@[simp]
theorem laurentDifferentialEquiv_D (e : L ≃ₐ[K⸨X⸩] Level K d) (x : L) :
    e.laurentDifferentialEquiv (Extension.ContinuousKaehlerDifferential.D K L x) =
      Level.ContinuousKaehlerDifferential.D K d (e x) := by
  rw [laurentDifferentialEquiv_apply, Extension.ContinuousKaehlerDifferential.mapSemilinear_D,
    AlgEquiv.coe_toAlgHom,
    Extension.ContinuousKaehlerDifferential.equivLevelContinuousKaehlerDifferential_D]

@[simp]
theorem laurentDifferentialEquiv_symm_D (e : L ≃ₐ[K⸨X⸩] Level K d) (x : Level K d) :
    e.laurentDifferentialEquiv.symm (Level.ContinuousKaehlerDifferential.D K d x) =
      Extension.ContinuousKaehlerDifferential.D K L (e.symm x) := by
  apply e.laurentDifferentialEquiv.symm_apply_eq.mpr
  simp

/-- A level chart intertwines the intrinsic differential trace on `Ω¹_cont(L/K)` with the explicit
level differential trace. -/
@[simp]
theorem trace_laurentDifferentialEquiv (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    Level.ContinuousKaehlerDifferential.trace K d (e.laurentDifferentialEquiv ω) =
      Extension.ContinuousKaehlerDifferential.trace K L ω := by
  obtain ⟨η, rfl⟩ := (Extension.ContinuousKaehlerDifferential.tensorEquiv K L).surjective ω
  rw [laurentDifferentialEquiv_tensorEquiv, trace_laurentDifferentialTensorEquiv,
    Extension.ContinuousKaehlerDifferential.trace_tensorEquiv]

@[simp]
theorem trace_laurentDifferentialEquiv_symm (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Level.ContinuousKaehlerDifferential K d) :
    Extension.ContinuousKaehlerDifferential.trace K L (e.laurentDifferentialEquiv.symm ω) =
      Level.ContinuousKaehlerDifferential.trace K d ω := by
  rw [← trace_laurentDifferentialEquiv e, LinearEquiv.apply_symm_apply]

/-- **Trace-residue compatibility on `Ω¹_cont(L/K)` in any level chart.** For `e : L ≃ₐ[K⸨X⸩]
Level K d` with `d` nonzero in `K`, the intrinsic trace-defined residue `residue K L ω` equals the
`u⁻¹`-coefficient of `e.laurentDifferentialEquiv ω` in the level parameter `u`. -/
theorem residue_eq_coeff_laurentDifferentialEquiv (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    Extension.ContinuousKaehlerDifferential.residue K L ω =
      (Level.ringEquivLaurentSeries K d
        (Level.ContinuousKaehlerDifferential.equivLevel K d
          (e.laurentDifferentialEquiv ω))).coeff (-1) := by
  rw [Extension.ContinuousKaehlerDifferential.residue_apply, ← trace_laurentDifferentialEquiv e,
    residue_trace]

/-- **Chart-independence of residues on intrinsic continuous one-forms.** Any two separable level
charts yield the same coefficient residue on `Ω¹_cont(L/K)`. -/
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

/-- When `L` carries the `K⸨X⸩`-module topology, `e.laurentDifferentialEquiv` upgrades to a
continuous `K⸨X⸩`-linear equivalence with the valuation-topologized level one-forms. -/
noncomputable def laurentDifferentialContinuousEquiv [TopologicalSpace L]
    [IsModuleTopology K⸨X⸩ L] (e : L ≃ₐ[K⸨X⸩] Level K d) :
    Extension.ContinuousKaehlerDifferential K L ≃L[K⸨X⸩]
      Level.ContinuousKaehlerDifferential K d :=
  have : Module.Finite K⸨X⸩ L := Module.Finite.equiv e.symm.toLinearEquiv
  e.laurentDifferentialEquiv.toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem laurentDifferentialContinuousEquiv_apply [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L]
    (e : L ≃ₐ[K⸨X⸩] Level K d) (ω : Extension.ContinuousKaehlerDifferential K L) :
    e.laurentDifferentialContinuousEquiv ω = e.laurentDifferentialEquiv ω := by
  simp [laurentDifferentialContinuousEquiv]

@[simp]
theorem laurentDifferentialContinuousEquiv_symm_apply [TopologicalSpace L]
    [IsModuleTopology K⸨X⸩ L] (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Level.ContinuousKaehlerDifferential K d) :
    e.laurentDifferentialContinuousEquiv.symm ω = e.laurentDifferentialEquiv.symm ω := by
  simp [laurentDifferentialContinuousEquiv]

end EtaleChart

end AlgEquiv
