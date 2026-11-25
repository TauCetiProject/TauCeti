/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import TauCeti.RingTheory.Kaehler.Trace.Extension
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Etale
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Residue

import TauCeti.LinearAlgebra.Trace.RestrictScalars
import TauCeti.RingTheory.Derivation.Determinant

/-!
# Differential traces and residues on formally étale Laurent extensions

Write `F = K⸨X⸩` and `Ω = TauCeti.ContinuousKaehlerDifferential K`.

For any `F`-algebra `L`, the scalar-extension trace `traceBaseChange L : L ⊗[F] Ω →ₗ[F] Ω` applies
`Algebra.trace F L` to the first tensor factor, sending `x ⊗ ω` to `Tr_{L/F}(x) ω`, and
`residueBaseChange L` takes the residue of that trace.

When `L` is a formally étale `F`-algebra (for instance a finite separable field extension of `F`),
`Extension.ContinuousKaehlerDifferential K L` (`Ω¹_cont(L/K)`) is canonically isomorphic to
`L ⊗[F] Ω` via `Extension.ContinuousKaehlerDifferential.tensorEquiv`. Transporting `traceBaseChange`
and `residueBaseChange` along this equivalence defines the intrinsic `F`-linear differential trace
`Extension.ContinuousKaehlerDifferential.trace K L : Ω¹_cont(L/K) →ₗ[F] Ω` and the `K`-linear
residue `Extension.ContinuousKaehlerDifferential.residue K L : Ω¹_cont(L/K) →ₗ[K] K`. In a tower
`F → M → L` of formally étale `F`-algebras, `traceTower K M L : Ω¹_cont(L/K) →ₗ[M] Ω¹_cont(M/K)`
defines the relative `M`-linear differential trace.

This intrinsic trace and residue satisfy Tate's identities in every characteristic:

* `trace_mk`: when `L` is finite over `F`, `trace K L` is induced on algebraic Kähler differentials
  `Ω[L⁄K]` by the Kunz-Lipman trace `Derivation.traceLin (KaehlerDifferential.D K F)`.
* `trace_D` and `traceTower_D`: `Tr_{L/F}(d x) = d(Tr_{L/F} x)` and
  `Tr_{L/M}(d x) = d(Tr_{L/M} x)`.
* `trace_traceTower` and `residue_traceTower`: transitivity in towers `F → M → L` of formally étale
  extensions with `L` free over `M`.
* `residue_D` and `residue_smul_D`: exact forms `d x` have residue zero, and `Res_L(x d y) =
  -Res_L(y d x)`.
* `residue_units_inv_smul_D` and `residue_inv_smul_D`: logarithmic differentials satisfy
  `Res_L(u⁻¹ d u) = ord_F(N_{L/F}(u))`.
* `continuous_trace`: when `L` carries the `F`-module topology, `trace K L` is continuous.

## Main definitions

* `TauCeti.ContinuousKaehlerDifferential.traceBaseChange L`: the differential trace
  `L ⊗[F] Ω →ₗ[F] Ω` on scalar-extended forms.
* `TauCeti.ContinuousKaehlerDifferential.residueBaseChange L`: the residue on scalar-extended forms.
* `Extension.ContinuousKaehlerDifferential.trace K L`: the intrinsic differential trace
  `Ω¹_cont(L/K) →ₗ[F] Ω`.
* `Extension.ContinuousKaehlerDifferential.residue K L`: the intrinsic `K`-linear residue
  `Ω¹_cont(L/K) →ₗ[K] K`.
* `Extension.ContinuousKaehlerDifferential.traceTower K M L`: the `M`-linear relative differential
  trace `Ω¹_cont(L/K) →ₗ[M] Ω¹_cont(M/K)` in a tower `F → M → L`.

## Main results

* `TauCeti.LaurentSeries.Extension.derivative_trace` and `derivative_norm_units`: compatibility of
  `d/dt` with `Algebra.trace` and `Algebra.norm`.
* `Extension.ContinuousKaehlerDifferential.trace_mk`: compatibility with the Kunz-Lipman trace.
* `Extension.ContinuousKaehlerDifferential.trace_D` and `traceTower_D`: differential traces commute
  with `d`.
* `Extension.ContinuousKaehlerDifferential.trace_traceTower` and `residue_traceTower`: tower
  transitivity of traces and residues.
* `Extension.ContinuousKaehlerDifferential.residue_D` and `residue_units_inv_smul_D`: Tate's `(R3)`
  and `(R4)` identities.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968), Theorem 1, for the
  construction of residues via differential traces and properties `(R1)`, `(R3)`, and `(R4)`.
* E. Kunz, *Kähler Differentials*, Vieweg, 1986, §16, for the algebraic differential trace on
  finite locally free extensions.
* J. Lipman, *Dualizing sheaves, differentials and residues on algebraic varieties*, Astérisque 117,
  1984, §I.4, for the Kunz-Lipman trace of Kähler differentials.
-/

public section

open HahnSeries TensorProduct
open scoped LaurentSeries

namespace TauCeti.ContinuousKaehlerDifferential

variable {K : Type*} [Field K] (L : Type*) [CommRing L] [Algebra K⸨X⸩ L]

/-- The differential trace on scalar-extended continuous forms: apply the algebra trace
on the first tensor factor, so that `x ⊗ ω` maps to `Tr(x) ω`. As with `Algebra.trace`,
this is zero for infinite-dimensional extensions. -/
noncomputable def traceBaseChange :
    L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K →ₗ[K⸨X⸩] ContinuousKaehlerDifferential K :=
  (TensorProduct.lid K⸨X⸩ _).toLinearMap ∘ₗ (Algebra.trace K⸨X⸩ L).rTensor _

@[simp]
theorem traceBaseChange_tmul (x : L) (ω : ContinuousKaehlerDifferential K) :
    traceBaseChange L (x ⊗ₜ ω) = Algebra.trace K⸨X⸩ L x • ω := by
  simp [traceBaseChange]

/-- Tracing a pulled-back form multiplies it by the degree of the extension. -/
theorem traceBaseChange_one_tmul (ω : ContinuousKaehlerDifferential K) :
    traceBaseChange L (1 ⊗ₜ ω) = Module.finrank K⸨X⸩ L • ω := by
  rw [traceBaseChange_tmul, TauCeti.Algebra.trace_one_smul]

/-- The residue on scalar-extended continuous forms, computed as the residue of
their differential trace. For every separable level chart this is exactly the
coefficient residue in its level parameter. -/
noncomputable def residueBaseChange :
    L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K →+ K where
  toFun η := residue K (traceBaseChange L η)
  map_zero' := by simp
  map_add' η θ := by simp

/-- The residue on scalar-extended forms is the residue of the differential trace. -/
theorem residueBaseChange_apply (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    residueBaseChange L η = residue K (traceBaseChange L η) :=
  (rfl)

/-- On a pure tensor `x ⊗ f dt`, the residue is the coefficient of `t⁻¹` in
`Tr(x) f`, equivalently in `Tr(x f)`. -/
@[simp]
theorem residueBaseChange_tmul (x : L) (ω : ContinuousKaehlerDifferential K) :
    residueBaseChange L (x ⊗ₜ ω) =
      (Algebra.trace K⸨X⸩ L x * equivLaurentSeries K ω).coeff (-1) := by
  simp [residueBaseChange_apply, residue_apply]

/-- The residue of a form pulled back from the base is multiplied by the degree. -/
theorem residueBaseChange_one_tmul (ω : ContinuousKaehlerDifferential K) :
    residueBaseChange L (1 ⊗ₜ ω) =
      Module.finrank K⸨X⸩ L • residue K ω := by
  rw [residueBaseChange_apply, traceBaseChange_one_tmul, map_nsmul]

end TauCeti.ContinuousKaehlerDifferential

namespace TauCeti.LaurentSeries.Extension

section TraceAndNorm

variable {K L : Type*} [Field K] [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]

/-- The formal derivative of `K⸨X⸩` commutes with `Algebra.trace K⸨X⸩ L` via `derivation K L`. -/
theorem derivative_trace (x : L) :
    _root_.LaurentSeries.derivative K (Algebra.trace K⸨X⸩ L x) =
      Algebra.trace K⸨X⸩ L (derivation K L x) := by
  simpa using (laurentSeriesAlgebraDerivation K).map_trace (derivation K L) (by simp) x

/-- Logarithmic derivative of `Algebra.norm K⸨X⸩` on units of a formally étale `K⸨X⸩`-algebra. -/
theorem derivative_norm_units (u : Lˣ) :
    _root_.LaurentSeries.derivative K (Algebra.norm K⸨X⸩ (u : L)) =
      Algebra.norm K⸨X⸩ (u : L) * Algebra.trace K⸨X⸩ L (↑u⁻¹ * derivation K L u) := by
  simpa using (laurentSeriesAlgebraDerivation K).leibniz_norm (derivation K L) (by simp) u

end TraceAndNorm

namespace ContinuousKaehlerDifferential

/-! ### Intrinsic differential trace and residue -/

section TraceAndResidue

variable (K L : Type*) [Field K] [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]

/-- **The differential trace** `Tr_{L/F} : Ω¹_cont(L/K) → Ω¹_cont(F/K)` of a formally étale
`K⸨X⸩`-algebra `L`: it transports `traceBaseChange L` along `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)`,
sending `x dt` to `Tr_{L/F}(x) dt`. -/
noncomputable def trace :
    ContinuousKaehlerDifferential K L →ₗ[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K :=
  TauCeti.ContinuousKaehlerDifferential.traceBaseChange L ∘ₗ
    ((tensorEquiv K L).symm.restrictScalars K⸨X⸩).toLinearMap

variable {K L}

@[simp]
theorem trace_tensorEquiv (η : L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (tensorEquiv K L η) =
      TauCeti.ContinuousKaehlerDifferential.traceBaseChange L η := by
  simp [trace]

@[simp]
theorem trace_smul_map (x : L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (x • map K L ω) = Algebra.trace K⸨X⸩ L x • ω := by
  rw [← tensorEquiv_tmul, trace_tensorEquiv,
    TauCeti.ContinuousKaehlerDifferential.traceBaseChange_tmul]

/-- Tracing a pulled-back continuous one-form multiplies it by `finrank K⸨X⸩ L`. -/
@[simp]
theorem trace_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (map K L ω) = Module.finrank K⸨X⸩ L • ω := by
  rw [← one_smul L (map K L ω), ← tensorEquiv_tmul, trace_tensorEquiv,
    TauCeti.ContinuousKaehlerDifferential.traceBaseChange_one_tmul]

/-- In coordinates in `dt`, the differential trace applies `Algebra.trace K⸨X⸩ L` to the
coefficient `equivSelf K L ω`. -/
@[simp]
theorem equivLaurentSeries_trace (ω : ContinuousKaehlerDifferential K L) :
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K (trace K L ω) =
      Algebra.trace K⸨X⸩ L (equivSelf K L ω) := by
  conv_lhs => rw [← equivSelf_smul_D_algebraMap_single_one ω, ← map_D, trace_smul_map]
  simp

/-- Isomorphisms of formally étale `K⸨X⸩`-algebras preserve the differential trace. -/
@[simp]
theorem trace_mapSemilinear_algEquiv {L' : Type*} [CommRing L'] [Algebra K⸨X⸩ L'] [Algebra K L']
    [IsScalarTower K K⸨X⸩ L'] [Algebra.FormallyEtale K⸨X⸩ L'] (e : L ≃ₐ[K⸨X⸩] L')
    (ω : ContinuousKaehlerDifferential K L) :
    trace K L' (mapSemilinear (e : L →ₐ[K⸨X⸩] L') ω) = trace K L ω := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [equivLaurentSeries_trace, equivLaurentSeries_trace, equivSelf_mapSemilinear,
    AlgEquiv.coe_toAlgHom, Algebra.trace_eq_of_algEquiv]

/-- **Compatibility with the Kunz-Lipman algebraic trace.** On a finite formally étale
`K⸨X⸩`-algebra `L`, the continuous differential trace of `mk K L ω` is the projection of
`Derivation.traceLin (KaehlerDifferential.D K K⸨X⸩) ω`. -/
theorem trace_mk [Module.Finite K⸨X⸩ L] (ω : Ω[L⁄K]) :
    trace K L (mk K L ω) =
      TauCeti.ContinuousKaehlerDifferential.mk K
        (Derivation.traceLin (KaehlerDifferential.D K K⸨X⸩) ω) := by
  obtain ⟨θ, rfl⟩ := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K⸨X⸩ L).surjective ω
  induction θ using TensorProduct.inductionOn with
  | tmul b η =>
    rw [Derivation.traceLin_D_tensorKaehlerEquivOfFormallyEtale_tmul,
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul, LinearMap.map_smul, ← map_mk, trace_smul_map,
      LinearMap.map_smul]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, map_add, map_add, hx, hy]

/-- **`Tr_{L/F}(d x) = d(Tr_{L/F} x)`.** On a formally étale `K⸨X⸩`-algebra, the differential trace
commutes with the universal continuous derivation. -/
@[simp]
theorem trace_D (x : L) :
    trace K L (D K L x) =
      TauCeti.ContinuousKaehlerDifferential.D K (Algebra.trace K⸨X⸩ L x) := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [equivLaurentSeries_trace, equivSelf_D,
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D, derivative_trace]

variable (K L) in
/-- When `L` carries the `K⸨X⸩`-module topology, the differential trace is continuous. -/
@[fun_prop]
theorem continuous_trace [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L] :
    Continuous (trace K L) := by
  by_cases h : Module.Finite K⸨X⸩ L
  · exact IsModuleTopology.continuous_of_linearMap (trace K L)
  · refine (continuous_const (y := (0 : TauCeti.ContinuousKaehlerDifferential K))).congr fun ω ↦ ?_
    apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
    simp [TauCeti.Algebra.trace_eq_zero_of_not_finite h]

variable (K L) in
/-- **The residue** `Res_L : Ω¹_cont(L/K) →ₗ[K] K` on continuous one-forms of a formally étale
`K⸨X⸩`-algebra `L`, defined as the residue `Res_F(Tr_{L/F} ω)` of the differential trace. -/
noncomputable def residue : ContinuousKaehlerDifferential K L →ₗ[K] K :=
  (TauCeti.ContinuousKaehlerDifferential.residue K).comp ((trace K L).restrictScalars K)

/-- **`Res_L(ω) = Res_F(Tr_{L/F} ω)`.** -/
theorem residue_apply (ω : ContinuousKaehlerDifferential K L) :
    residue K L ω = TauCeti.ContinuousKaehlerDifferential.residue K (trace K L ω) :=
  (rfl)

/-- In coordinates in `dt`, `Res_L(x dt)` is the `t⁻¹`-coefficient of `Tr_{L/F}(x)`. -/
theorem residue_eq_coeff_neg_one_trace (ω : ContinuousKaehlerDifferential K L) :
    residue K L ω = (Algebra.trace K⸨X⸩ L (equivSelf K L ω)).coeff (-1) := by
  rw [residue_apply, TauCeti.ContinuousKaehlerDifferential.residue_apply, equivLaurentSeries_trace]

@[simp]
theorem residue_tensorEquiv (η : L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    residue K L (tensorEquiv K L η) =
      TauCeti.ContinuousKaehlerDifferential.residueBaseChange L η := by
  rw [residue_apply, trace_tensorEquiv,
    TauCeti.ContinuousKaehlerDifferential.residueBaseChange_apply]

@[simp]
theorem residue_smul_map (x : L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    residue K L (x • map K L ω) =
      (Algebra.trace K⸨X⸩ L x *
        TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K ω).coeff (-1) := by
  rw [← tensorEquiv_tmul, residue_tensorEquiv,
    TauCeti.ContinuousKaehlerDifferential.residueBaseChange_tmul]

@[simp]
theorem residue_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    residue K L (map K L ω) =
      Module.finrank K⸨X⸩ L • TauCeti.ContinuousKaehlerDifferential.residue K ω := by
  rw [residue_apply, trace_map, map_nsmul]

/-- Isomorphisms of formally étale `K⸨X⸩`-algebras preserve the residue. -/
@[simp]
theorem residue_mapSemilinear_algEquiv {L' : Type*} [CommRing L'] [Algebra K⸨X⸩ L'] [Algebra K L']
    [IsScalarTower K K⸨X⸩ L'] [Algebra.FormallyEtale K⸨X⸩ L'] (e : L ≃ₐ[K⸨X⸩] L')
    (ω : ContinuousKaehlerDifferential K L) :
    residue K L' (mapSemilinear (e : L →ₐ[K⸨X⸩] L') ω) = residue K L ω := by
  rw [residue_apply, residue_apply, trace_mapSemilinear_algEquiv]

/-- **Exact differentials have residue zero** (Tate `(R3)`), in every characteristic. -/
@[simp]
theorem residue_D (x : L) :
    residue K L (D K L x) = 0 := by
  rw [residue_apply, trace_D, TauCeti.ContinuousKaehlerDifferential.residue_D]

/-- **Integration by parts for residues**: `Res_L(x d y) = -Res_L(y d x)`. -/
theorem residue_smul_D (x y : L) :
    residue K L (x • D K L y) = -residue K L (y • D K L x) := by
  have h := residue_D (K := K) (L := L) (x * y)
  rw [(D K L).leibniz, map_add] at h
  exact eq_neg_of_add_eq_zero_left h

/-- **Residue of a logarithmic differential** (Tate `(R4)`): for any unit `u` of a formally étale
`K⸨X⸩`-algebra `L`, `Res_L(u⁻¹ d u)` is the `X`-adic order of `N_{L/K⸨X⸩}(u)` in `K`. -/
theorem residue_units_inv_smul_D (u : Lˣ) :
    residue K L ((↑u⁻¹ : L) • D K L u) = ((Algebra.norm K⸨X⸩ (u : L)).order : K) := by
  have hnu : Algebra.norm K⸨X⸩ (u : L) ≠ 0 := (Units.map (Algebra.norm K⸨X⸩) u).ne_zero
  have hlog : Algebra.trace K⸨X⸩ L (↑u⁻¹ * derivation K L u) =
      _root_.LaurentSeries.derivative K (Algebra.norm K⸨X⸩ (u : L)) *
        (Algebra.norm K⸨X⸩ (u : L))⁻¹ := by
    rw [derivative_norm_units, mul_comm (Algebra.norm K⸨X⸩ (u : L)), mul_inv_cancel_right₀ hnu]
  rw [residue_eq_coeff_neg_one_trace, LinearEquiv.map_smul, equivSelf_D, smul_eq_mul, hlog,
    _root_.LaurentSeries.coeff_neg_one_derivative_mul_inv]

/-- On a formally étale field extension `F'/K⸨X⸩`, `Res_{F'}(x⁻¹ d x) = ord(N_{F'/K⸨X⸩}(x))` for
every `x : F'` (including `x = 0`, where both sides vanish). -/
theorem residue_inv_smul_D {F' : Type*} [Field F'] [Algebra K⸨X⸩ F'] [Algebra K F']
    [IsScalarTower K K⸨X⸩ F'] [Algebra.FormallyEtale K⸨X⸩ F'] (x : F') :
    residue K F' (x⁻¹ • D K F' x) = ((Algebra.norm K⸨X⸩ x).order : K) := by
  rcases eq_or_ne x 0 with rfl | hx
  · by_cases hF : Module.Finite K⸨X⸩ F'
    · simp [Algebra.norm_zero]
    · simp [Algebra.norm_eq_one_of_not_module_finite hF]
  · simpa [Units.val_inv_eq_inv_val] using residue_units_inv_smul_D (K := K) (Units.mk0 x hx)

end TraceAndResidue

/-! ### Transitivity in towers -/

section Tower

variable (K M L : Type*) [Field K] [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
  [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M]
  [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
  [Algebra M L] [Algebra.FormallyEtale K⸨X⸩ L]

/-- Relative differential trace `Tr_{L/M} : Ω¹_cont(L/K) →ₗ[M] Ω¹_cont(M/K)` in a tower
`K⸨X⸩ → M → L` of formally étale `K⸨X⸩`-algebras. -/
noncomputable def traceTower :
    ContinuousKaehlerDifferential K L →ₗ[M] ContinuousKaehlerDifferential K M :=
  (equivSelf K M).symm.toLinearMap ∘ₗ
    Algebra.trace M L ∘ₗ
      (equivSelf K L).toLinearMap.restrictScalars M

variable {K M L}

@[simp]
theorem equivSelf_traceTower (ω : ContinuousKaehlerDifferential K L) :
    equivSelf K M (traceTower K M L ω) = Algebra.trace M L (equivSelf K L ω) :=
  (equivSelf K M).apply_symm_apply _

variable [IsScalarTower K⸨X⸩ M L]

/-- On a form `x • ω` pulled back from `M` along `M → L`, the relative differential trace applies
`Algebra.trace M L` to `x`. -/
@[simp]
theorem traceTower_smul_mapSemilinear (x : L) (ω : ContinuousKaehlerDifferential K M) :
    traceTower K M L (x • mapSemilinear (IsScalarTower.toAlgHom K⸨X⸩ M L) ω) =
      Algebra.trace M L x • ω :=
  (equivSelf K M).injective <| by
    rw [equivSelf_traceTower, LinearEquiv.map_smul, LinearEquiv.map_smul, equivSelf_mapSemilinear,
      IsScalarTower.coe_toAlgHom', smul_eq_mul, mul_comm, ← Algebra.smul_def, LinearMap.map_smul,
      smul_eq_mul, smul_eq_mul, mul_comm]

/-- Tracing a form pulled back along a free step `M → L` multiplies it by `finrank M L`. -/
@[simp]
theorem traceTower_mapSemilinear [Module.Free M L] (ω : ContinuousKaehlerDifferential K M) :
    traceTower K M L (mapSemilinear (IsScalarTower.toAlgHom K⸨X⸩ M L) ω) =
      Module.finrank M L • ω := by
  rw [← one_smul L (mapSemilinear _ ω), traceTower_smul_mapSemilinear,
    TauCeti.Algebra.trace_one_smul]

/-- **`Tr_{L/M}(d x) = d(Tr_{L/M} x)`.** In a tower `K⸨X⸩ → M → L` of formally étale
`K⸨X⸩`-algebras, the relative differential trace commutes with `d`. -/
@[simp]
theorem traceTower_D (x : L) :
    traceTower K M L (D K L x) = D K M (Algebra.trace M L x) :=
  (equivSelf K M).injective <| by
    rw [equivSelf_traceTower, equivSelf_D, equivSelf_D,
      (derivation K M).map_trace (derivation K L) derivation_algebraMap_tower]

/-- **Transitivity of the differential trace** in a tower `K⸨X⸩ → M → L` with `L` free over `M`. -/
@[simp]
theorem trace_traceTower [Module.Free M L] (ω : ContinuousKaehlerDifferential K L) :
    trace K M (traceTower K M L ω) = trace K L ω := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [equivLaurentSeries_trace, equivSelf_traceTower, equivLaurentSeries_trace,
    TauCeti.Algebra.trace_trace_of_free]

/-- **Trace invariance of the residue in towers**: `Res_M(Tr_{L/M} ω) = Res_L(ω)`. -/
@[simp]
theorem residue_traceTower [Module.Free M L] (ω : ContinuousKaehlerDifferential K L) :
    residue K M (traceTower K M L ω) = residue K L ω := by
  rw [residue_apply, residue_apply, trace_traceTower]

end Tower

end ContinuousKaehlerDifferential

end TauCeti.LaurentSeries.Extension
