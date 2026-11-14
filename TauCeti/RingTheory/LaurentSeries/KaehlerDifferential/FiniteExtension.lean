/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import TauCeti.RingTheory.Kaehler.Trace.Extension
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Etale
public import TauCeti.RingTheory.LaurentSeries.Level.ModuleTopology
public import TauCeti.RingTheory.LaurentSeries.Level.Residue

/-!
# Differential traces and residues on formally étale Laurent extensions

Write `F = K⸨X⸩` and `Ω = TauCeti.ContinuousKaehlerDifferential K`.

For any `F`-algebra `L`, the scalar-extension trace `traceBaseChange L : L ⊗[F] Ω →ₗ[F] Ω` applies
`Algebra.trace F L` to the first tensor factor, sending `x ⊗ ω` to `Tr_{L/F}(x) ω`, and
`residueBaseChange L` takes the `t⁻¹`-coefficient of that trace.

When `L` is a formally étale `F`-algebra (for instance a finite separable field extension of `F`),
`Extension.ContinuousKaehlerDifferential K L` (`Ω¹_cont(L/K)`) is canonically isomorphic to
`L ⊗[F] Ω` via `Extension.ContinuousKaehlerDifferential.tensorEquiv`. Transporting `traceBaseChange`
and `residueBaseChange` along this equivalence defines the intrinsic `F`-linear differential trace
`Extension.ContinuousKaehlerDifferential.trace K L : Ω¹_cont(L/K) →ₗ[F] Ω` and the `K`-linear
residue `Extension.ContinuousKaehlerDifferential.residue K L : Ω¹_cont(L/K) →ₗ[K] K`.

This intrinsic trace and residue satisfy Tate's identities in every characteristic:

* `trace_mk`: when `L` is finite over `F`, `trace K L` is induced on algebraic Kähler differentials
  `Ω[L⁄K]` by the Kunz-Lipman trace `Derivation.traceLin (KaehlerDifferential.D K F)`.
* `trace_D`: `Tr_{L/F}(d x) = d(Tr_{L/F} x)`.
* `trace_traceTower` and `residue_traceTower`: transitivity in towers `F → M → L` of formally étale
  extensions with `L` free over `M`.
* `residue_D` and `residue_smul_D`: exact forms `d x` have residue zero, and `Res_L(x d y) =
  -Res_L(y d x)`.
* `residue_units_inv_smul_D` and `residue_inv_smul_D`: logarithmic differentials satisfy
  `Res_L(u⁻¹ d u) = ord_F(N_{L/F}(u))`.
* `continuous_trace`: when `L` carries the `F`-module topology, `trace K L` is continuous.

For the finite separable ramified level `Level K d` (`[NeZero ((d : ℕ) : K)]`), the general
formally étale module `Extension.ContinuousKaehlerDifferential K (Level K d)` is identified with the
explicit level module `Level.ContinuousKaehlerDifferential K d` by a continuous `Level K d`-linear
equivalence `Extension.ContinuousKaehlerDifferential.equivLevel K d`. Under this equivalence,
`D K (Level K d) x` corresponds to `d(x(u))` in the level uniformizer `u`, the two differential
traces agree (`trace_equivLevel`), and `Res_F(Tr_{L/F} ω) = Res_L(ω)` holds on `Ω¹_cont(L/K)`
(`residue_eq_coeff_equivLevel`, `AlgEquiv.residue_eq_coeff_laurentDifferentialEquiv`).

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968), Theorem 1, for the
  construction of residues via differential traces and properties `(R1)`, `(R3)`, and `(R4)`.
-/

public section

open HahnSeries TensorProduct
open scoped PowerSeries LaurentSeries

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
  rw [traceBaseChange_tmul, ← map_one (algebraMap K⸨X⸩ L), Algebra.trace_algebraMap,
    smul_assoc, one_smul]

/-- The residue on scalar-extended continuous forms, computed as the residue of
their differential trace. For every separable level chart this is exactly the
coefficient residue in its level parameter. -/
noncomputable def residueBaseChange :
    L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K →+ K where
  toFun η := (equivLaurentSeries K (traceBaseChange L η)).coeff (-1)
  map_zero' := by simp
  map_add' η θ := by simp

/-- The residue is the coefficient of `t⁻¹` in the differential trace. -/
theorem residueBaseChange_apply (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    residueBaseChange L η = (equivLaurentSeries K (traceBaseChange L η)).coeff (-1) :=
  (rfl)

/-- On a pure tensor `x ⊗ f dt`, the residue is the coefficient of `t⁻¹` in
`Tr(x) f`, equivalently in `Tr(x f)`. -/
@[simp]
theorem residueBaseChange_tmul (x : L) (ω : ContinuousKaehlerDifferential K) :
    residueBaseChange L (x ⊗ₜ ω) =
      (Algebra.trace K⸨X⸩ L x * equivLaurentSeries K ω).coeff (-1) := by
  simp [residueBaseChange_apply]

/-- The residue of a form pulled back from the base is multiplied by the degree. -/
theorem residueBaseChange_one_tmul (ω : ContinuousKaehlerDifferential K) :
    residueBaseChange L (1 ⊗ₜ ω) =
      Module.finrank K⸨X⸩ L • (equivLaurentSeries K ω).coeff (-1) := by
  rw [residueBaseChange_apply, traceBaseChange_one_tmul]
  simp only [map_nsmul, HahnSeries.coeff_nsmul, Pi.smul_apply]

end TauCeti.ContinuousKaehlerDifferential

namespace TauCeti.LaurentSeries.Extension

section TraceAndNorm

variable {K L : Type*} [Field K] [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]

private noncomputable def laurentAlgebraDerivation (K : Type*) [Field K] :
    @Derivation K K⸨X⸩ K⸨X⸩ _ _ _ _ _ Algebra.toModule :=
  have h1 : _root_.LaurentSeries.derivative K 1 = 0 := by
    rw [← laurentSeriesDerivation_apply, Derivation.map_one_eq_zero]
  letI : Module K K⸨X⸩ := Algebra.toModule
  { toFun := _root_.LaurentSeries.derivative K
    map_add' := map_add _
    map_smul' c f := by
      change _root_.LaurentSeries.derivative K (algebraMap K K⸨X⸩ c * f) =
        algebraMap K K⸨X⸩ c * _root_.LaurentSeries.derivative K f
      rw [laurentSeries_algebraMap_mul_eq_smul, laurentSeries_algebraMap_mul_eq_smul]
      exact map_smul (_root_.LaurentSeries.derivative K) c f
    map_one_eq_zero' := h1
    leibniz' f g := by
      change _root_.LaurentSeries.derivative K (f * g) =
        f * _root_.LaurentSeries.derivative K g + g * _root_.LaurentSeries.derivative K f
      rw [_root_.LaurentSeries.derivative_mul]
      ring }

/-- The formal derivative of `K⸨X⸩` commutes with `Algebra.trace K⸨X⸩ L` via `derivation K L`. -/
theorem derivative_trace (x : L) :
    _root_.LaurentSeries.derivative K (Algebra.trace K⸨X⸩ L x) =
      Algebra.trace K⸨X⸩ L (derivation K L x) :=
  (laurentAlgebraDerivation K).map_trace (derivation K L)
    (fun f ↦ (derivation_algebraMap f).trans (by rw [laurentSeriesDerivation_apply]; rfl)) x

/-- Logarithmic derivative of `Algebra.norm K⸨X⸩` on units of a formally étale `K⸨X⸩`-algebra. -/
theorem derivative_norm_units (u : Lˣ) :
    _root_.LaurentSeries.derivative K (Algebra.norm K⸨X⸩ (u : L)) =
      Algebra.norm K⸨X⸩ (u : L) * Algebra.trace K⸨X⸩ L (↑u⁻¹ * derivation K L u) := by
  by_cases h : Module.Finite K⸨X⸩ L
  · exact (laurentAlgebraDerivation K).leibniz_norm (derivation K L)
      (fun f ↦ (derivation_algebraMap f).trans (by rw [laurentSeriesDerivation_apply]; rfl)) u
  · have htr : Algebra.trace K⸨X⸩ L = 0 :=
      Algebra.trace_eq_zero_of_not_exists_basis K⸨X⸩ fun ⟨_, ⟨b⟩⟩ ↦ h (.of_basis b)
    rw [Algebra.norm_eq_one_of_not_module_finite h, htr, LinearMap.zero_apply, mul_zero,
      ← laurentSeriesDerivation_apply, Derivation.map_one_eq_zero]

end TraceAndNorm

/-! ### Derivative on a finite separable ramified level -/

section LevelDerivation

private noncomputable def levelUniformizerDerivation (K : Type*) [Field K] (d : ℕ+) :
    Derivation K (Level K d) (Level K d) where
  toFun x := (Level.ringEquivLaurentSeries K d).symm
    (_root_.LaurentSeries.derivative K (Level.ringEquivLaurentSeries K d x))
  map_add' x y := by simp
  map_smul' c x := by
    apply (Level.ringEquivLaurentSeries K d).injective
    simp only [RingHom.id_apply, Algebra.smul_def, RingEquiv.map_mul, RingEquiv.apply_symm_apply,
      Level.ringEquivLaurentSeries_algebraMap_const, laurentSeries_algebraMap_mul_eq_smul, map_smul]
  map_one_eq_zero' := by
    dsimp
    rw [map_one, ← laurentSeriesDerivation_apply, Derivation.map_one_eq_zero, map_zero]
  leibniz' x y := by
    apply (Level.ringEquivLaurentSeries K d).injective
    simp only [LinearMap.coe_mk, AddHom.coe_mk, RingEquiv.apply_symm_apply, map_mul, smul_eq_mul,
      map_add, _root_.LaurentSeries.derivative_mul]
    ring

private theorem ringEquivLaurentSeries_levelUniformizerDerivation {K : Type*} [Field K] {d : ℕ+}
    (x : Level K d) :
    Level.ringEquivLaurentSeries K d (levelUniformizerDerivation K d x) =
      _root_.LaurentSeries.derivative K (Level.ringEquivLaurentSeries K d x) :=
  (Level.ringEquivLaurentSeries K d).apply_symm_apply _

/-- On a finite separable ramified level `Level K d` (`t = u ^ d`), the canonical derivation
`d/dt` acts in the level variable `u` as `(d x / d u) / (d(u ^ d) / d u)`. -/
theorem ringEquivLaurentSeries_derivation_level {K : Type*} [Field K] {d : ℕ+}
    [NeZero ((d : ℕ) : K)] (x : Level K d) :
    Level.ringEquivLaurentSeries K d (derivation K (Level K d) x) =
      _root_.LaurentSeries.derivative K (Level.ringEquivLaurentSeries K d x) /
        _root_.LaurentSeries.derivative K (single (d : ℤ) 1) := by
  have hd : _root_.LaurentSeries.derivative K (single (d : ℤ) (1 : K)) ≠ 0 := by
    simpa using NeZero.ne ((d : ℕ) : K)
  set c : Level K d :=
    (Level.ringEquivLaurentSeries K d).symm (_root_.LaurentSeries.derivative K (single (d : ℤ) 1))
  have hδ : c⁻¹ • levelUniformizerDerivation K d = derivation K (Level K d) := by
    refine eq_derivation fun f ↦ (Level.ringEquivLaurentSeries K d).injective ?_
    have hpow : ((PowerSeries.X ^ (d : ℕ) : K⟦X⟧) : K⸨X⸩) = single (d : ℤ) 1 := by
      simp [PowerSeries.coe_pow, single_pow]
    rw [_root_.smul_apply, smul_eq_mul, map_mul, map_inv₀, RingEquiv.apply_symm_apply,
      ringEquivLaurentSeries_levelUniformizerDerivation, Level.algebraMap_apply,
      Level.algebraMap_apply, ← TauCeti.LaurentSeries.substAlgHom_X_pow_eq_expand,
      TauCeti.LaurentSeries.derivative_substAlgHom, hpow, laurentSeriesDerivation_apply,
      inv_mul_eq_div, mul_div_cancel_right₀ _ hd]
  rw [← hδ, _root_.smul_apply, smul_eq_mul, map_mul, map_inv₀, RingEquiv.apply_symm_apply,
    ringEquivLaurentSeries_levelUniformizerDerivation, inv_mul_eq_div]

end LevelDerivation

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
theorem trace_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (map K L ω) = Module.finrank K⸨X⸩ L • ω := by
  rw [← one_smul L (map K L ω), trace_smul_map, ← map_one (algebraMap K⸨X⸩ L),
    Algebra.trace_algebraMap, smul_assoc, one_smul]

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
    trace K L' (mapSemilinear e.toAlgHom ω) = trace K L ω := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [equivLaurentSeries_trace, equivLaurentSeries_trace, equivSelf_mapSemilinear,
    AlgEquiv.toAlgHom_apply, Algebra.trace_eq_of_algEquiv]

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
theorem continuous_trace [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L] :
    Continuous (trace K L) := by
  by_cases h : Module.Finite K⸨X⸩ L
  · exact IsModuleTopology.continuous_of_linearMap (trace K L)
  · refine (continuous_const (y := (0 : TauCeti.ContinuousKaehlerDifferential K))).congr fun ω ↦ ?_
    apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
    have htr : Algebra.trace K⸨X⸩ L = 0 :=
      Algebra.trace_eq_zero_of_not_exists_basis K⸨X⸩ fun ⟨_, ⟨b⟩⟩ ↦ h (.of_basis b)
    simp [htr]

variable (K L) in
/-- **The residue** `Res_L : Ω¹_cont(L/K) →ₗ[K] K` on continuous one-forms of a formally étale
`K⸨X⸩`-algebra `L`, defined as the `t⁻¹`-coefficient of `Tr_{L/F} ω`. -/
noncomputable def residue : ContinuousKaehlerDifferential K L →ₗ[K] K where
  toFun ω := (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K (trace K L ω)).coeff (-1)
  map_add' ω η := by simp
  map_smul' c ω := by
    have hc : trace K L (c • ω) = c • trace K L ω :=
      ((trace K L).restrictScalars K).map_smul c ω
    rw [hc]
    change (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K
        (algebraMap K K⸨X⸩ c • trace K L ω)).coeff (-1) = _
    rw [ContinuousLinearEquiv.map_smul, smul_eq_mul, laurentSeries_algebraMap_mul_eq_smul,
      coeff_smul, RingHom.id_apply]

/-- **`Res_L(ω) = Res_F(Tr_{L/F} ω)`.** -/
theorem residue_apply (ω : ContinuousKaehlerDifferential K L) :
    residue K L ω =
      (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K (trace K L ω)).coeff (-1) :=
  (rfl)

/-- In coordinates in `dt`, `Res_L(x dt)` is the `t⁻¹`-coefficient of `Tr_{L/F}(x)`. -/
theorem residue_eq_coeff_neg_one_trace (ω : ContinuousKaehlerDifferential K L) :
    residue K L ω = (Algebra.trace K⸨X⸩ L (equivSelf K L ω)).coeff (-1) := by
  rw [residue_apply, equivLaurentSeries_trace]

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

theorem residue_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    residue K L (map K L ω) =
      Module.finrank K⸨X⸩ L •
        (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K ω).coeff (-1) := by
  rw [residue_apply, trace_map, map_nsmul, coeff_nsmul, Pi.smul_apply]

/-- Isomorphisms of formally étale `K⸨X⸩`-algebras preserve the residue. -/
@[simp]
theorem residue_mapSemilinear_algEquiv {L' : Type*} [CommRing L'] [Algebra K⸨X⸩ L'] [Algebra K L']
    [IsScalarTower K K⸨X⸩ L'] [Algebra.FormallyEtale K⸨X⸩ L'] (e : L ≃ₐ[K⸨X⸩] L')
    (ω : ContinuousKaehlerDifferential K L) :
    residue K L' (mapSemilinear e.toAlgHom ω) = residue K L ω := by
  rw [residue_apply, residue_apply, trace_mapSemilinear_algEquiv]

/-- **Exact differentials have residue zero** (Tate `(R3)`), in every characteristic. -/
@[simp]
theorem residue_D (x : L) :
    residue K L (D K L x) = 0 := by
  rw [residue_apply, trace_D, TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D,
    _root_.LaurentSeries.coeff_neg_one_derivative]

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
  [Algebra M L] [IsScalarTower K⸨X⸩ M L] [Algebra.FormallyEtale K⸨X⸩ L]

/-- Relative differential trace `Tr_{L/M} : Ω¹_cont(L/K) →ₗ[K⸨X⸩] Ω¹_cont(M/K)` in a tower
`K⸨X⸩ → M → L` of formally étale `K⸨X⸩`-algebras. -/
noncomputable def traceTower :
    ContinuousKaehlerDifferential K L →ₗ[K⸨X⸩] ContinuousKaehlerDifferential K M :=
  (equivSelf K M).symm.toLinearMap.restrictScalars K⸨X⸩ ∘ₗ
    (Algebra.trace M L).restrictScalars K⸨X⸩ ∘ₗ
      (equivSelf K L).toLinearMap.restrictScalars K⸨X⸩

variable {K M L}

@[simp]
theorem equivSelf_traceTower (ω : ContinuousKaehlerDifferential K L) :
    equivSelf K M (traceTower K M L ω) = Algebra.trace M L (equivSelf K L ω) :=
  (equivSelf K M).apply_symm_apply _

theorem traceTower_algebraMap_smul (m : M) (ω : ContinuousKaehlerDifferential K L) :
    traceTower K M L (algebraMap M L m • ω) = m • traceTower K M L ω :=
  (equivSelf K M).injective <| by
    rw [equivSelf_traceTower, LinearEquiv.map_smul, LinearEquiv.map_smul, equivSelf_traceTower,
      IsScalarTower.algebraMap_smul, LinearMap.map_smul]

/-- **Transitivity of the differential trace** in a tower `K⸨X⸩ → M → L` with `L` free over `M`. -/
@[simp]
theorem trace_traceTower [Module.Free M L] (ω : ContinuousKaehlerDifferential K L) :
    trace K M (traceTower K M L ω) = trace K L ω := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [equivLaurentSeries_trace, equivSelf_traceTower, equivLaurentSeries_trace]
  rcases subsingleton_or_nontrivial L with hL | hL
  · rw [Subsingleton.elim (equivSelf K L ω) 0, map_zero, map_zero, map_zero]
  by_cases hML : Module.Finite M L
  · by_cases hKM : Module.Finite K⸨X⸩ M
    · exact Algebra.trace_trace (equivSelf K L ω)
    · have hKL : ¬Module.Finite K⸨X⸩ L := fun h ↦ by
        let b := Module.Free.chooseBasis M L
        obtain ⟨i⟩ := b.index_nonempty
        exact hKM (Module.Finite.of_surjective ((b.coord i).restrictScalars K⸨X⸩)
          fun m ↦ ⟨m • b i, by simp⟩)
      have htrM : Algebra.trace K⸨X⸩ M = 0 :=
        Algebra.trace_eq_zero_of_not_exists_basis K⸨X⸩ fun ⟨_, ⟨b⟩⟩ ↦ hKM (.of_basis b)
      have htrL : Algebra.trace K⸨X⸩ L = 0 :=
        Algebra.trace_eq_zero_of_not_exists_basis K⸨X⸩ fun ⟨_, ⟨b⟩⟩ ↦ hKL (.of_basis b)
      simp [htrM, htrL]
  · have hKL : ¬Module.Finite K⸨X⸩ L := fun h ↦ hML (.of_restrictScalars_finite K⸨X⸩ M L)
    have htrML : Algebra.trace M L = 0 :=
      Algebra.trace_eq_zero_of_not_exists_basis M fun ⟨_, ⟨b⟩⟩ ↦ hML (.of_basis b)
    have htrL : Algebra.trace K⸨X⸩ L = 0 :=
      Algebra.trace_eq_zero_of_not_exists_basis K⸨X⸩ fun ⟨_, ⟨b⟩⟩ ↦ hKL (.of_basis b)
    simp [htrML, htrL]

/-- **Trace invariance of the residue in towers**: `Res_M(Tr_{L/M} ω) = Res_L(ω)`. -/
@[simp]
theorem residue_traceTower [Module.Free M L] (ω : ContinuousKaehlerDifferential K L) :
    residue K M (traceTower K M L ω) = residue K L ω := by
  rw [residue_apply, residue_apply, trace_traceTower]

end Tower

/-! ### Identification for a finite separable ramified level -/

section Level

variable (K : Type*) [Field K] (d : ℕ+) [NeZero ((d : ℕ) : K)]

/-- **Equivalence with explicit ramified-level one-forms.** For `d` nonzero in `K`, `Level K d` is
formally étale over `K⸨X⸩`, and the continuous `Level K d`-linear equivalence `equivLevel K d`
identifies `Extension.ContinuousKaehlerDifferential K (Level K d)` with
`Level.ContinuousKaehlerDifferential K d` by matching their base-change decompositions over
`Ω¹_cont(K⸨X⸩/K)`. -/
noncomputable def equivLevel :
    ContinuousKaehlerDifferential K (Level K d) ≃L[Level K d]
      Level.ContinuousKaehlerDifferential K d :=
  ((tensorEquiv K (Level K d)).symm.trans
    (Level.ContinuousKaehlerDifferential.tensorEquiv K d)).toContinuousLinearEquivOfIsModuleTopology

variable {K d}

@[simp]
theorem equivLevel_tensorEquiv
    (η : Level K d ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    equivLevel K d (tensorEquiv K (Level K d) η) =
      Level.ContinuousKaehlerDifferential.tensorEquiv K d η := by
  simp [equivLevel]

@[simp]
theorem equivLevel_symm_tensorEquiv
    (η : Level K d ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    (equivLevel K d).symm (Level.ContinuousKaehlerDifferential.tensorEquiv K d η) =
      tensorEquiv K (Level K d) η := by
  simp [equivLevel]

@[simp]
theorem equivLevel_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    equivLevel K d (map K (Level K d) ω) = Level.ContinuousKaehlerDifferential.map K d ω := by
  simpa using equivLevel_tensorEquiv (K := K) (d := d) (1 ⊗ₜ[K⸨X⸩] ω)

/-- In coordinates, `equivLevel K d` converts `x dt` into `(x * d u ^ (d - 1)) du`. -/
theorem levelEquivLevel_equivLevel (ω : ContinuousKaehlerDifferential K (Level K d)) :
    Level.ContinuousKaehlerDifferential.equivLevel K d (equivLevel K d ω) =
      equivSelf K (Level K d) ω *
        (Level.ringEquivLaurentSeries K d).symm
          (_root_.LaurentSeries.derivative K (single (d : ℤ) 1)) := by
  conv_lhs => rw [← equivSelf_smul_D_algebraMap_single_one ω, ← map_D]
  rw [ContinuousLinearEquiv.map_smul, equivLevel_map, LinearEquiv.map_smul,
    Level.ContinuousKaehlerDifferential.equivLevel_map,
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D_single_one]
  simp [smul_eq_mul]

/-- Under `equivLevel K d`, the formally étale differential `D K (Level K d) x` is the explicit
Laurent differential `d(x(u))` in the level variable `u`. -/
@[simp]
theorem addEquivContinuousKaehlerDifferential_equivLevel_D (x : Level K d) :
    Level.ContinuousKaehlerDifferential.addEquivContinuousKaehlerDifferential K d
        (equivLevel K d (D K (Level K d) x)) =
      TauCeti.ContinuousKaehlerDifferential.D K (Level.ringEquivLaurentSeries K d x) := by
  have hd : _root_.LaurentSeries.derivative K (single (d : ℤ) (1 : K)) ≠ 0 := by
    simpa using NeZero.ne ((d : ℕ) : K)
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [← Level.ContinuousKaehlerDifferential.ringEquivLaurentSeries_equivLevel,
    levelEquivLevel_equivLevel, equivSelf_D, map_mul, RingEquiv.apply_symm_apply,
    ringEquivLaurentSeries_derivation_level, div_mul_cancel₀ _ hd,
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D]

/-- `equivLevel K d` intertwines the intrinsic formally étale differential trace with the explicit
level differential trace. -/
@[simp]
theorem trace_equivLevel (ω : ContinuousKaehlerDifferential K (Level K d)) :
    Level.ContinuousKaehlerDifferential.trace K d (equivLevel K d ω) =
      trace K (Level K d) ω := by
  obtain ⟨η, rfl⟩ := (tensorEquiv K (Level K d)).surjective ω
  rw [equivLevel_tensorEquiv, trace_tensorEquiv]
  induction η using TensorProduct.inductionOn with
  | tmul g ω => simp
  | add x y hx hy => simp [hx, hy]

/-- **`Res_F(Tr_{L/F} ω) = Res_L(ω)` on a finite separable ramified level.** For `L = Level K d`
with `d` nonzero in `K`, the trace-defined residue `residue K (Level K d) ω` equals the coefficient
of `u⁻¹` of `ω` read in the level uniformizer `u`. -/
theorem residue_eq_coeff_equivLevel (ω : ContinuousKaehlerDifferential K (Level K d)) :
    residue K (Level K d) ω =
      (Level.ringEquivLaurentSeries K d
        (Level.ContinuousKaehlerDifferential.equivLevel K d (equivLevel K d ω))).coeff (-1) := by
  rw [residue_apply, ← trace_equivLevel,
    Level.ContinuousKaehlerDifferential.coeff_neg_one_equivLaurentSeries_trace]

/-- On `Level K d`, `residue K (Level K d)` agrees with `Level.residue K d` on the `dt`-coordinate
`equivSelf K (Level K d) ω`. -/
theorem residue_eq_level_residue (ω : ContinuousKaehlerDifferential K (Level K d)) :
    residue K (Level K d) ω = Level.residue K d (equivSelf K (Level K d) ω) := by
  rw [residue_eq_coeff_equivLevel, levelEquivLevel_equivLevel, map_mul, RingEquiv.apply_symm_apply,
    ← Level.residue_apply]

end Level

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
  exact coeff_neg_one_equivLaurentSeries_trace _

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
    ((Extension.ContinuousKaehlerDifferential.equivLevel K d).toLinearEquiv.restrictScalars K⸨X⸩)

@[simp]
theorem laurentDifferentialEquiv_tensorEquiv (e : L ≃ₐ[K⸨X⸩] Level K d)
    (η : L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    e.laurentDifferentialEquiv (Extension.ContinuousKaehlerDifferential.tensorEquiv K L η) =
      e.laurentDifferentialTensorEquiv η := by
  induction η using TensorProduct.inductionOn with
  | tmul x ω =>
    rw [laurentDifferentialEquiv, LinearEquiv.trans_apply,
      Extension.ContinuousKaehlerDifferential.tensorEquiv_tmul,
      Extension.ContinuousKaehlerDifferential.congrLinearEquiv_apply,
      Extension.ContinuousKaehlerDifferential.mapSemilinear_smul,
      Extension.ContinuousKaehlerDifferential.mapSemilinear_map, AlgEquiv.toAlgHom_apply,
      LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.map_smul, Extension.ContinuousKaehlerDifferential.equivLevel_map,
      laurentDifferentialTensorEquiv_tmul]
  | add x y hx hy => simp [hx, hy]

@[simp]
theorem laurentDifferentialEquiv_smul (e : L ≃ₐ[K⸨X⸩] Level K d) (x : L)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    e.laurentDifferentialEquiv (x • ω) = e x • e.laurentDifferentialEquiv ω := by
  rw [laurentDifferentialEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    Extension.ContinuousKaehlerDifferential.congrLinearEquiv_apply,
    Extension.ContinuousKaehlerDifferential.congrLinearEquiv_apply,
    Extension.ContinuousKaehlerDifferential.mapSemilinear_smul, AlgEquiv.toAlgHom_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.restrictScalars_apply,
    ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.map_smul]

/-- Under a level chart `e`, `D K L x` becomes `d((e x)(u))` in the level variable `u`. -/
@[simp]
theorem addEquivContinuousKaehlerDifferential_laurentDifferentialEquiv_D
    (e : L ≃ₐ[K⸨X⸩] Level K d) (x : L) :
    addEquivContinuousKaehlerDifferential K d
        (e.laurentDifferentialEquiv (Extension.ContinuousKaehlerDifferential.D K L x)) =
      TauCeti.ContinuousKaehlerDifferential.D K (Level.ringEquivLaurentSeries K d (e x)) := by
  rw [laurentDifferentialEquiv, LinearEquiv.trans_apply,
    Extension.ContinuousKaehlerDifferential.congrLinearEquiv_apply,
    Extension.ContinuousKaehlerDifferential.mapSemilinear_D, AlgEquiv.toAlgHom_apply,
    LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
    Extension.ContinuousKaehlerDifferential.addEquivContinuousKaehlerDifferential_equivLevel_D]

/-- A level chart intertwines the intrinsic differential trace on `Ω¹_cont(L/K)` with the explicit
level differential trace. -/
@[simp]
theorem trace_laurentDifferentialEquiv (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    Level.ContinuousKaehlerDifferential.trace K d (e.laurentDifferentialEquiv ω) =
      Extension.ContinuousKaehlerDifferential.trace K L ω := by
  rw [laurentDifferentialEquiv, LinearEquiv.trans_apply,
    Extension.ContinuousKaehlerDifferential.congrLinearEquiv_apply,
    LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
    Extension.ContinuousKaehlerDifferential.trace_equivLevel,
    Extension.ContinuousKaehlerDifferential.trace_mapSemilinear_algEquiv]

/-- **Trace-residue compatibility on `Ω¹_cont(L/K)` in any level chart.** For `e : L ≃ₐ[K⸨X⸩]
Level K d` with `d` nonzero in `K`, the intrinsic trace-defined residue `residue K L ω` equals the
`u⁻¹`-coefficient of `e.laurentDifferentialEquiv ω` in the level parameter `u`. -/
theorem residue_eq_coeff_laurentDifferentialEquiv (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    Extension.ContinuousKaehlerDifferential.residue K L ω =
      (Level.ringEquivLaurentSeries K d
        (Level.ContinuousKaehlerDifferential.equivLevel K d
          (e.laurentDifferentialEquiv ω))).coeff (-1) := by
  rw [laurentDifferentialEquiv, LinearEquiv.trans_apply,
    Extension.ContinuousKaehlerDifferential.congrLinearEquiv_apply,
    LinearEquiv.restrictScalars_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
    ← Extension.ContinuousKaehlerDifferential.residue_eq_coeff_equivLevel,
    Extension.ContinuousKaehlerDifferential.residue_mapSemilinear_algEquiv]

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

end EtaleChart

end AlgEquiv

namespace TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential

/-- Over an algebraically closed coefficient field `K` of characteristic zero, the intrinsic
residue `residue K L` on `Ω¹_cont(L/K)` agrees with `Level.residueOfFinrankEq` applied to the
`dt`-coordinate `equivSelf K L ω`. -/
theorem residue_eq_residueOfFinrankEq {K L : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    [Field L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
    [Algebra.FormallyEtale K⸨X⸩ L] {d : ℕ+} (h : Module.finrank K⸨X⸩ L = d)
    (ω : ContinuousKaehlerDifferential K L) :
    residue K L ω = Level.residueOfFinrankEq h (equivSelf K L ω) := by
  rw [residue_eq_coeff_neg_one_trace, Level.residueOfFinrankEq_eq_coeff_neg_one_trace]

end TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential
