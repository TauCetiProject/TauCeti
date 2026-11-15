/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Etale
public import TauCeti.RingTheory.LaurentSeries.Level.Adjoin
public import TauCeti.RingTheory.LaurentSeries.Level.ModuleTopology

/-!
# Differential traces and residues in finite Laurent extensions

Write `F = K⸨X⸩` and `Ω = ContinuousKaehlerDifferential K`. The trace on the scalar extension
`L ⊗[F] Ω` sends `x ⊗ ω` to `Tr_{L/F}(x) ω`. For a formally étale `F`-algebra `L` (in particular
any finite separable extension of `F`, or any ramified level `Level K d` with `d` nonzero in `K`),
`LaurentSeries.KaehlerDifferential.Etale` identifies `L ⊗[F] Ω` with the intrinsic quotient
`Extension.ContinuousKaehlerDifferential K L` of `Ω[L⁄K]`. Transporting along this equivalence
yields:

* the intrinsic differential trace `Tr_{L/F} : Ω¹_cont(L/K) → Ω¹_cont(F/K)`, together with the
  relative trace `Tr_{E/L} : Ω¹_cont(E/K) → Ω¹_cont(L/K)` in towers `F → L → E` and its
  transitivity `Tr_{L/F} ∘ Tr_{E/L} = Tr_{E/F}`;
* the `K`-linear residue `Res_L : Ω¹_cont(L/K) → K`, `Res_L(ω) = Res_F(Tr_{L/F} ω)`, invariant
  under `F`-algebra equivalences and under relative differential traces in finite towers, and
  continuous for the `F`-module topology on finite extensions and any topology on `K`;
* on a separable ramified level `Level K d` (`[NeZero ((d : ℕ) : K)]`), the continuous
  `Level K d`-linear equivalence `Level.ContinuousKaehlerDifferential.equivExtension` between
  `Extension.ContinuousKaehlerDifferential K (Level K d)` and
  `Level.ContinuousKaehlerDifferential K d`, sending the étale differential `d x` to the level
  differential `d_u x` and intertwining the two differential traces;
* for any level chart `e : L ≃ₐ[F] Level K d` with `d` nonzero in `K`, the `F`-linear equivalence
  `e.laurentDifferentialEquiv` (and its automatic topological upgrade
  `e.laurentDifferentialContinuousEquiv` when `L` carries the `F`-module topology), proving that
  `Res_L(ω)` equals the `u⁻¹`-coefficient residue in every separable level chart and is therefore
  independent of the chosen chart.

When `K` is algebraically closed of characteristic zero, every finite extension of `F` admits such
a chart by `Level.algEquivOfFinrankEq` from `LaurentSeries.Puiseux.FiniteExtension`.

## Main definitions

* `TauCeti.ContinuousKaehlerDifferential.traceBaseChange`, `residueBaseChange`: trace and residue
  on scalar-extended forms `L ⊗[F] Ω`.
* `Extension.ContinuousKaehlerDifferential.trace`, `traceTower`, `residue`: intrinsic differential
  trace, relative tower trace, and `K`-linear residue on `Ω¹_cont(L/K)`.
* `Level.ContinuousKaehlerDifferential.equivExtension`: continuous linear equivalence identifying
  the étale and explicit level one-forms of `Level K d` when `d` is nonzero in `K`.
* `AlgEquiv.laurentDifferentialTensorEquiv`, `laurentDifferentialEquiv`,
  `laurentDifferentialContinuousEquiv`: algebraic and continuous level-chart equivalences on
  scalar-extended and intrinsic continuous one-forms.

## Main results

* `Extension.ContinuousKaehlerDifferential.trace_traceTower`, `residue_traceTower`: transitivity of
  differential trace and trace-invariance of residues in finite towers.
* `Level.ContinuousKaehlerDifferential.equivExtension_D`, `trace_equivExtension`,
  `residue_eq_coeff_equivExtension`: compatibility of `equivExtension` with `d`, trace, and
  residues.
* `AlgEquiv.laurentDifferentialEquiv_D`, `trace_laurentDifferentialEquiv`,
  `residue_eq_coeff_laurentDifferentialEquiv`, `coeff_laurentDifferentialEquiv_eq`: chart transport
  of `d` and trace, trace-residue compatibility, and chart-independence of the level residue.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968), for the compatibility of
  residues with the trace of differentials.
-/

public section

open HahnSeries LaurentSeries TensorProduct
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

namespace TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential

variable (K : Type*) [Field K] (L : Type*) [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]

/-! ### Intrinsic differential trace and residue on étale extensions -/

/-- **The trace of continuous one-forms.** For a formally étale `K⸨X⸩`-algebra `L`, the trace
`Tr_{L/F} : Ω¹_cont(L/K) → Ω¹_cont(F/K)`, `x dt ↦ Tr_{L/F}(x) dt`, transported from
`TauCeti.ContinuousKaehlerDifferential.traceBaseChange` along `tensorEquiv`. -/
noncomputable def trace :
    ContinuousKaehlerDifferential K L →ₗ[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K :=
  TauCeti.ContinuousKaehlerDifferential.traceBaseChange L ∘ₗ
    ((tensorEquiv K L).symm.restrictScalars K⸨X⸩).toLinearMap

/-- **The `K`-linear residue of continuous one-forms.** For a formally étale `K⸨X⸩`-algebra `L`,
`Res_L : Ω¹_cont(L/K) → K` is the residue at `t` of the differential trace `Tr_{L/F}(ω)`. -/
noncomputable def residue : ContinuousKaehlerDifferential K L →ₗ[K] K :=
  HahnSeries.coeff.linearMap (-1) ∘ₗ
    (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).toLinearMap.restrictScalars K ∘ₗ
      (trace K L).restrictScalars K

variable {K L}

@[simp]
theorem trace_tensorEquiv (η : L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (tensorEquiv K L η) =
      TauCeti.ContinuousKaehlerDifferential.traceBaseChange L η := by
  simp [trace]

/-- For a base one-form `ω`, the trace of `x • map ω` is `Tr_{L/F}(x) • ω`. -/
@[simp]
theorem trace_smul_map (x : L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (x • map K L ω) = Algebra.trace K⸨X⸩ L x • ω := by
  rw [← tensorEquiv_tmul, trace_tensorEquiv,
    TauCeti.ContinuousKaehlerDifferential.traceBaseChange_tmul]

/-- The trace of a pulled-back base one-form multiplies it by the degree of `L` over `K⸨X⸩`. -/
@[simp]
theorem trace_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (map K L ω) = Module.finrank K⸨X⸩ L • ω := by
  rw [← one_smul L (map K L ω), ← tensorEquiv_tmul, trace_tensorEquiv,
    TauCeti.ContinuousKaehlerDifferential.traceBaseChange_one_tmul]

/-- In coordinates relative to `dt`, the differential trace applies `Algebra.trace K⸨X⸩ L` to the
coordinate `equivSelf K L ω`. -/
@[simp]
theorem equivLaurentSeries_trace (ω : ContinuousKaehlerDifferential K L) :
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K (trace K L ω) =
      Algebra.trace K⸨X⸩ L (equivSelf K L ω) := by
  conv_lhs => rw [← equivSelf_smul_D_algebraMap_single_one ω, ← map_D, trace_smul_map]
  simp

/-- The differential trace is invariant under `K⸨X⸩`-algebra equivalences. -/
@[simp]
theorem trace_mapAlgEquiv {E : Type*} [CommRing E] [Algebra K⸨X⸩ E] [Algebra K E]
    [IsScalarTower K K⸨X⸩ E] [Algebra.FormallyEtale K⸨X⸩ E] (e : L ≃ₐ[K⸨X⸩] E)
    (ω : ContinuousKaehlerDifferential K L) :
    trace K E (mapAlgEquiv e ω) = trace K L ω := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [equivLaurentSeries_trace, equivLaurentSeries_trace, equivSelf_mapAlgEquiv,
    Algebra.trace_eq_of_algEquiv]

@[simp]
theorem trace_mapLinearEquiv {E : Type*} [CommRing E] [Algebra K⸨X⸩ E] [Algebra K E]
    [IsScalarTower K K⸨X⸩ E] [Algebra.FormallyEtale K⸨X⸩ E] (e : L ≃ₐ[K⸨X⸩] E)
    (ω : ContinuousKaehlerDifferential K L) :
    trace K E (mapLinearEquiv e ω) = trace K L ω := by
  rw [mapLinearEquiv_apply, ← mapAlgEquiv_apply, trace_mapAlgEquiv]

/-- On a finite formally étale `K⸨X⸩`-algebra carrying the `K⸨X⸩`-module topology, the differential
trace is continuous. -/
@[fun_prop]
theorem continuous_trace [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L] [Module.Finite K⸨X⸩ L] :
    Continuous (trace K L) :=
  IsModuleTopology.continuous_of_linearMap (trace K L)

section Tower

variable {E : Type*} [CommRing E] [Algebra K⸨X⸩ E] [Algebra K E]
  [IsScalarTower K K⸨X⸩ E] [Algebra.FormallyEtale K⸨X⸩ E]
  [Algebra L E] [IsScalarTower K⸨X⸩ L E]

variable (K L E) in
/-- **Relative differential trace in a tower.** In a tower `K⸨X⸩ → L → E` of formally étale
`K⸨X⸩`-algebras, the relative differential trace `Tr_{E/L} : Ω¹_cont(E/K) → Ω¹_cont(L/K)`,
`y dt ↦ Tr_{E/L}(y) dt`. -/
noncomputable def traceTower :
    ContinuousKaehlerDifferential K E →ₗ[K⸨X⸩] ContinuousKaehlerDifferential K L :=
  (equivSelf K L).symm.toLinearMap.restrictScalars K⸨X⸩ ∘ₗ
    (Algebra.trace L E).restrictScalars K⸨X⸩ ∘ₗ
      (equivSelf K E).toLinearMap.restrictScalars K⸨X⸩

/-- In the frame `dt`, the relative differential trace applies `Algebra.trace L E`. -/
@[simp]
theorem equivSelf_traceTower (ω : ContinuousKaehlerDifferential K E) :
    equivSelf K L (traceTower K L E ω) = Algebra.trace L E (equivSelf K E ω) := by
  simp [traceTower, -equivSelf_symm_apply]

@[simp]
theorem traceTower_smul_mapTower (y : E) (ω : ContinuousKaehlerDifferential K L) :
    traceTower K L E (y • mapTower K L E ω) = Algebra.trace L E y • ω := by
  apply (equivSelf K L).injective
  rw [equivSelf_traceTower, LinearEquiv.map_smul, equivSelf_mapTower, smul_eq_mul, mul_comm,
    ← Algebra.smul_def, LinearMap.map_smul, LinearEquiv.map_smul, smul_eq_mul, smul_eq_mul,
    mul_comm]

/-- `traceTower` is `L`-semilinear: `Tr_{E/L}((algebraMap L E x) • ω) = x • Tr_{E/L}(ω)`. -/
@[simp]
theorem traceTower_algebraMap_smul (x : L) (ω : ContinuousKaehlerDifferential K E) :
    traceTower K L E (algebraMap L E x • ω) = x • traceTower K L E ω := by
  apply (equivSelf K L).injective
  rw [equivSelf_traceTower, LinearEquiv.map_smul, LinearEquiv.map_smul, equivSelf_traceTower,
    smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul]

/-- **Transitivity of the differential trace in finite towers.** -/
theorem trace_traceTower [Module.Finite K⸨X⸩ L] [Module.Free L E] [Module.Finite L E]
    (ω : ContinuousKaehlerDifferential K E) :
    trace K L (traceTower K L E ω) = trace K E ω := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  simp [Algebra.trace_trace]

@[fun_prop]
theorem continuous_traceTower [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L] [Module.Finite K⸨X⸩ L]
    [TopologicalSpace E] [IsModuleTopology K⸨X⸩ E] [Module.Finite K⸨X⸩ E] :
    Continuous (traceTower K L E) :=
  IsModuleTopology.continuous_of_linearMap (traceTower K L E)

end Tower

theorem residue_apply (ω : ContinuousKaehlerDifferential K L) :
    residue K L ω =
      (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K (trace K L ω)).coeff (-1) :=
  (rfl)

/-- In coordinates relative to `dt`, the residue of `ω` is the `t⁻¹`-coefficient of
`Tr_{L/K⸨X⸩}(equivSelf K L ω)`. -/
theorem residue_eq_coeff_neg_one_trace (ω : ContinuousKaehlerDifferential K L) :
    residue K L ω = (Algebra.trace K⸨X⸩ L (equivSelf K L ω)).coeff (-1) := by
  rw [residue_apply, equivLaurentSeries_trace]

@[simp]
theorem residue_tensorEquiv (η : L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    residue K L (tensorEquiv K L η) =
      TauCeti.ContinuousKaehlerDifferential.residueBaseChange L η := by
  simp [residue_apply, TauCeti.ContinuousKaehlerDifferential.residueBaseChange_apply]

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
      Module.finrank K⸨X⸩ L •
        (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K ω).coeff (-1) := by
  rw [← one_smul L (map K L ω), ← tensorEquiv_tmul, residue_tensorEquiv,
    TauCeti.ContinuousKaehlerDifferential.residueBaseChange_one_tmul]

/-- The `K`-linear residue is invariant under `K⸨X⸩`-algebra equivalences. -/
@[simp]
theorem residue_mapAlgEquiv {E : Type*} [CommRing E] [Algebra K⸨X⸩ E] [Algebra K E]
    [IsScalarTower K K⸨X⸩ E] [Algebra.FormallyEtale K⸨X⸩ E] (e : L ≃ₐ[K⸨X⸩] E)
    (ω : ContinuousKaehlerDifferential K L) :
    residue K E (mapAlgEquiv e ω) = residue K L ω := by
  rw [residue_apply, trace_mapAlgEquiv, ← residue_apply]

@[simp]
theorem residue_mapLinearEquiv {E : Type*} [CommRing E] [Algebra K⸨X⸩ E] [Algebra K E]
    [IsScalarTower K K⸨X⸩ E] [Algebra.FormallyEtale K⸨X⸩ E] (e : L ≃ₐ[K⸨X⸩] E)
    (ω : ContinuousKaehlerDifferential K L) :
    residue K E (mapLinearEquiv e ω) = residue K L ω := by
  rw [mapLinearEquiv_apply, ← mapAlgEquiv_apply, residue_mapAlgEquiv]

/-- **Differential trace preserves residues in finite towers.** -/
theorem residue_traceTower {E : Type*} [CommRing E] [Algebra K⸨X⸩ E] [Algebra K E]
    [IsScalarTower K K⸨X⸩ E] [Algebra.FormallyEtale K⸨X⸩ E] [Algebra L E]
    [IsScalarTower K⸨X⸩ L E] [Module.Finite K⸨X⸩ L] [Module.Free L E] [Module.Finite L E]
    (ω : ContinuousKaehlerDifferential K E) :
    residue K L (traceTower K L E ω) = residue K E ω := by
  rw [residue_apply, trace_traceTower, ← residue_apply]

/-- The `K`-linear residue on a finite formally étale extension carrying the `K⸨X⸩`-module topology
is continuous for every topology on `K`. -/
@[fun_prop]
theorem continuous_residue [TopologicalSpace K] [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L]
    [Module.Finite K⸨X⸩ L] : Continuous (residue K L) := by
  -- Coefficient extraction on `K⸨X⸩` is continuous into the discrete topology `⊥`, hence into any
  -- topology on `K`.
  have hcoeff : @Continuous K⸨X⸩ K _ ⊥ (fun f ↦ f.coeff (-1)) := by
    rw [← UniformSpace.toTopologicalSpace_bot]
    exact @UniformContinuous.continuous _ _ _ ⊥ _
      (_root_.LaurentSeries.uniformContinuous_coeff (uK := ⊥) (-1))
  exact (continuous_le_rng bot_le hcoeff).comp
    ((TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).continuous.comp continuous_trace)

end TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential

namespace TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential

/-! ### Identification with étale continuous one-forms on a separable level -/

variable (K : Type*) [Field K] (d : ℕ+) [NeZero ((d : ℕ) : K)]

/-- **Étale and explicit one-forms of a separable level coincide.** When `d` is nonzero in `K`,
`Level K d` is étale over `K⸨X⸩`, and its abstract continuous one-forms
`Extension.ContinuousKaehlerDifferential K (Level K d)` are continuously `Level K d`-linearly
equivalent to `Level.ContinuousKaehlerDifferential K d`, compatibly with `d`, pullbacks, and
differential traces. -/
noncomputable def equivExtension :
    Extension.ContinuousKaehlerDifferential K (Level K d) ≃L[Level K d]
      Level.ContinuousKaehlerDifferential K d :=
  ((Extension.ContinuousKaehlerDifferential.tensorEquiv K (Level K d)).symm.trans
    (tensorEquiv K d)).toContinuousLinearEquivOfIsModuleTopology

variable {K d}

@[simp]
theorem equivExtension_tensorEquiv
    (η : Level K d ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    equivExtension K d
        (Extension.ContinuousKaehlerDifferential.tensorEquiv K (Level K d) η) =
      tensorEquiv K d η := by
  simp [equivExtension]

theorem equivExtension_smul_map (g : Level K d) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    equivExtension K d (g • Extension.ContinuousKaehlerDifferential.map K (Level K d) ω) =
      g • map K d ω := by
  rw [← Extension.ContinuousKaehlerDifferential.tensorEquiv_tmul, equivExtension_tensorEquiv,
    tensorEquiv_tmul]

@[simp]
theorem equivExtension_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    equivExtension K d (Extension.ContinuousKaehlerDifferential.map K (Level K d) ω) =
      map K d ω := by
  simpa using equivExtension_smul_map (1 : Level K d) ω

/-- `equivExtension` intertwines the étale universal derivation `d` with the level differential
`d_u` in the level parameter. -/
@[simp]
theorem equivExtension_D (x : Level K d) :
    equivExtension K d (Extension.ContinuousKaehlerDifferential.D K (Level K d) x) =
      D K d x := by
  have h : (equivExtension K d).toLinearMap.compDer
      (Extension.ContinuousKaehlerDifferential.D K (Level K d)) = D K d :=
    Derivation.eq_of_formallyUnramified (S := K⸨X⸩) fun f ↦ by
      simp [← Extension.ContinuousKaehlerDifferential.map_D]
  exact congr($h x)

/-- In the level variable `u`, the étale derivation `d/dt` of `Level K d` is
`(dx / du) / (d u ^ (d - 1))`. -/
theorem _root_.TauCeti.LaurentSeries.Level.ringEquivLaurentSeries_extensionDerivation
    (x : Level K d) :
    ringEquivLaurentSeries K d (Extension.derivation K (Level K d) x) =
      _root_.LaurentSeries.derivative K (ringEquivLaurentSeries K d x) /
        _root_.LaurentSeries.derivative K (HahnSeries.single (d : ℤ) 1) := by
  have hne : _root_.LaurentSeries.derivative K (HahnSeries.single (d : ℤ) (1 : K)) ≠ 0 := by
    simp [NeZero.ne]
  have h := congrArg (fun ω ↦ ringEquivLaurentSeries K d (equivLevel K d (equivExtension K d ω)))
    (Extension.ContinuousKaehlerDifferential.derivation_smul_D_algebraMap_single_one x)
  rw [← Extension.ContinuousKaehlerDifferential.map_D, equivExtension_smul_map, equivExtension_D,
    equivLevel_D, RingEquiv.apply_symm_apply, map_smul, equivLevel_map, smul_eq_mul, map_mul,
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D_single_one, map_one, one_mul,
    RingEquiv.apply_symm_apply] at h
  exact eq_div_of_mul_eq hne h

/-- `equivExtension` intertwines the intrinsic and explicit differential traces on `Level K d`. -/
@[simp]
theorem trace_equivExtension
    (ω : Extension.ContinuousKaehlerDifferential K (Level K d)) :
    trace K d (equivExtension K d ω) =
      Extension.ContinuousKaehlerDifferential.trace K (Level K d) ω := by
  obtain ⟨η, rfl⟩ :=
    (Extension.ContinuousKaehlerDifferential.tensorEquiv K (Level K d)).surjective ω
  rw [equivExtension_tensorEquiv, Extension.ContinuousKaehlerDifferential.trace_tensorEquiv]
  induction η using TensorProduct.inductionOn with
  | tmul g η => simp
  | add η₁ η₂ h₁ h₂ => simp [h₁, h₂]

/-- On a separable ramified level, the intrinsic `K`-linear residue equals the `u⁻¹`-coefficient
residue in the level parameter. -/
theorem residue_eq_coeff_equivExtension
    (ω : Extension.ContinuousKaehlerDifferential K (Level K d)) :
    Extension.ContinuousKaehlerDifferential.residue K (Level K d) ω =
      (ringEquivLaurentSeries K d (equivLevel K d (equivExtension K d ω))).coeff (-1) := by
  rw [Extension.ContinuousKaehlerDifferential.residue_apply, ← trace_equivExtension,
    coeff_neg_one_equivLaurentSeries_trace]

end TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential

namespace AlgEquiv

open TauCeti TauCeti.ContinuousKaehlerDifferential
open TauCeti.LaurentSeries
open TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential

section LevelChartTopology

variable {K : Type*} [Field K] {L : Type*} [CommRing L] [Algebra K⸨X⸩ L]
  [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L] {d : ℕ+}

/-- An algebraic level chart on an extension carrying the `K⸨X⸩`-module topology is automatically a
continuous `K⸨X⸩`-linear equivalence (also in inseparable degrees). -/
noncomputable def laurentContinuousLinearEquiv (e : L ≃ₐ[K⸨X⸩] Level K d) :
    L ≃L[K⸨X⸩] Level K d :=
  e.toLinearEquiv.toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem laurentContinuousLinearEquiv_apply (e : L ≃ₐ[K⸨X⸩] Level K d) (x : L) :
    e.laurentContinuousLinearEquiv x = e x := by
  simp [laurentContinuousLinearEquiv]

end LevelChartTopology

section Tensor

variable {K : Type*} [Field K] {L : Type*} [CommRing L] [Algebra K⸨X⸩ L]
  {d : ℕ+} [NeZero ((d : ℕ) : K)]

/-- A level chart identifies scalar-extended forms with the continuous forms of that
level. This is an equivalence over the base Laurent field; scalar multiplication by
`x : L` corresponds to multiplication by `e x` on the target. -/
noncomputable def laurentDifferentialTensorEquiv (e : L ≃ₐ[K⸨X⸩] Level K d) :
    L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K ≃ₗ[K⸨X⸩]
      Level.ContinuousKaehlerDifferential K d :=
  (TensorProduct.congr e.toLinearEquiv (.refl K⸨X⸩ _)).trans
    ((Level.ContinuousKaehlerDifferential.tensorEquiv K d).restrictScalars K⸨X⸩)

@[simp]
theorem laurentDifferentialTensorEquiv_tmul (e : L ≃ₐ[K⸨X⸩] Level K d)
    (x : L) (ω : ContinuousKaehlerDifferential K) :
    e.laurentDifferentialTensorEquiv (x ⊗ₜ ω) =
      e x • Level.ContinuousKaehlerDifferential.map K d ω := by
  simp [laurentDifferentialTensorEquiv]

/-- The inverse chart comparison sends a scalar multiple of a pulled-back form to
its corresponding pure tensor. -/
@[simp]
theorem laurentDifferentialTensorEquiv_symm_smul_map
    (e : L ≃ₐ[K⸨X⸩] Level K d)
    (x : Level K d) (ω : ContinuousKaehlerDifferential K) :
    e.laurentDifferentialTensorEquiv.symm
        (x • Level.ContinuousKaehlerDifferential.map K d ω) =
      e.symm x ⊗ₜ ω := by
  apply e.laurentDifferentialTensorEquiv.symm_apply_eq.mpr
  simp

/-- The chart comparison respects the extension's scalar action through the chart. -/
theorem laurentDifferentialTensorEquiv_smul
    (e : L ≃ₐ[K⸨X⸩] Level K d)
    (x : L) (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    e.laurentDifferentialTensorEquiv (x • η) = e x • e.laurentDifferentialTensorEquiv η := by
  induction η using TensorProduct.inductionOn with
  | tmul y ω => simp [smul_tmul', smul_eq_mul, mul_smul]
  | add η θ hη hθ => simp [smul_add, hη, hθ]

/-- Differential trace commutes with every level chart. In particular the trace
transported from the explicit level is the trace on the first tensor factor. -/
@[simp]
theorem trace_laurentDifferentialTensorEquiv
    (e : L ≃ₐ[K⸨X⸩] Level K d)
    (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    Level.ContinuousKaehlerDifferential.trace K d
        (e.laurentDifferentialTensorEquiv η) = traceBaseChange L η := by
  induction η using TensorProduct.inductionOn with
  | tmul x ω =>
    simp only [laurentDifferentialTensorEquiv_tmul,
      Level.ContinuousKaehlerDifferential.trace_smul_map,
      traceBaseChange_tmul]
    rw [Algebra.trace_eq_of_algEquiv e]
  | add η θ hη hθ => simp [hη, hθ]

/-- **Trace-residue compatibility in any level chart.** The residue of the trace
of a scalar-extended form is the coefficient residue in the level parameter. -/
theorem residueBaseChange_eq_coeff (e : L ≃ₐ[K⸨X⸩] Level K d)
    (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    residueBaseChange L η =
      (Level.ringEquivLaurentSeries K d
        (Level.ContinuousKaehlerDifferential.equivLevel K d
          (e.laurentDifferentialTensorEquiv η))).coeff (-1) := by
  rw [residueBaseChange_apply, ← trace_laurentDifferentialTensorEquiv e]
  exact coeff_neg_one_equivLaurentSeries_trace _

/-- **Independence of the level chart.** Two isomorphisms with ramified levels give
the same coefficient residue on scalar-extended forms. The levels need not be
identified in advance. -/
theorem coeff_laurentDifferentialTensorEquiv_eq {n : ℕ+} [NeZero ((n : ℕ) : K)]
    (e : L ≃ₐ[K⸨X⸩] Level K d)
    (e' : L ≃ₐ[K⸨X⸩] Level K n)
    (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    (Level.ringEquivLaurentSeries K d
      (Level.ContinuousKaehlerDifferential.equivLevel K d
        (e.laurentDifferentialTensorEquiv η))).coeff (-1) =
    (Level.ringEquivLaurentSeries K n
      (Level.ContinuousKaehlerDifferential.equivLevel K n
        (e'.laurentDifferentialTensorEquiv η))).coeff (-1) := by
  rw [← residueBaseChange_eq_coeff e, ← residueBaseChange_eq_coeff e']

end Tensor

section Intrinsic

variable {K : Type*} [Field K] {L : Type*} [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]
  {d : ℕ+} [NeZero ((d : ℕ) : K)]

/-- **Intrinsic level-chart equivalence on continuous one-forms.** A separable level chart
`e : L ≃ₐ[K⸨X⸩] Level K d` identifies the intrinsic continuous one-forms
`Extension.ContinuousKaehlerDifferential K L` with `Level.ContinuousKaehlerDifferential K d`,
sending `d x` to `d_u (e x)`. -/
noncomputable def laurentDifferentialEquiv (e : L ≃ₐ[K⸨X⸩] Level K d) :
    Extension.ContinuousKaehlerDifferential K L ≃ₗ[K⸨X⸩]
      Level.ContinuousKaehlerDifferential K d :=
  (Extension.ContinuousKaehlerDifferential.mapLinearEquiv e).trans
    ((equivExtension K d).toLinearEquiv.restrictScalars K⸨X⸩)

theorem laurentDifferentialEquiv_apply (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    e.laurentDifferentialEquiv ω =
      equivExtension K d (Extension.ContinuousKaehlerDifferential.mapLinearEquiv e ω) :=
  (rfl)

@[simp]
theorem laurentDifferentialEquiv_tensorEquiv (e : L ≃ₐ[K⸨X⸩] Level K d)
    (η : L ⊗[K⸨X⸩] ContinuousKaehlerDifferential K) :
    e.laurentDifferentialEquiv
        (Extension.ContinuousKaehlerDifferential.tensorEquiv K L η) =
      e.laurentDifferentialTensorEquiv η := by
  induction η using TensorProduct.inductionOn with
  | tmul x ω =>
    simp [laurentDifferentialEquiv_apply]
  | add η₁ η₂ h₁ h₂ => simp [h₁, h₂]

theorem laurentDifferentialEquiv_smul (e : L ≃ₐ[K⸨X⸩] Level K d) (x : L)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    e.laurentDifferentialEquiv (x • ω) = e x • e.laurentDifferentialEquiv ω := by
  simp [laurentDifferentialEquiv_apply]

@[simp]
theorem laurentDifferentialEquiv_map (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : ContinuousKaehlerDifferential K) :
    e.laurentDifferentialEquiv (Extension.ContinuousKaehlerDifferential.map K L ω) =
      Level.ContinuousKaehlerDifferential.map K d ω := by
  simp [laurentDifferentialEquiv_apply]

/-- A level chart sends the étale differential `d x` on `L` to the level differential `d_u (e x)`
in the level parameter `u`. -/
@[simp]
theorem laurentDifferentialEquiv_D (e : L ≃ₐ[K⸨X⸩] Level K d) (x : L) :
    e.laurentDifferentialEquiv (Extension.ContinuousKaehlerDifferential.D K L x) =
      Level.ContinuousKaehlerDifferential.D K d (e x) := by
  simp [laurentDifferentialEquiv_apply]

/-- Every separable level chart intertwines the explicit level trace and the intrinsic differential
trace on `Ω¹_cont(L/K)`. -/
@[simp]
theorem trace_laurentDifferentialEquiv (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    Level.ContinuousKaehlerDifferential.trace K d (e.laurentDifferentialEquiv ω) =
      Extension.ContinuousKaehlerDifferential.trace K L ω := by
  simp [laurentDifferentialEquiv_apply]

/-- **Trace-residue compatibility on intrinsic continuous one-forms.** For any separable level
chart `e : L ≃ₐ[K⸨X⸩] Level K d`, the intrinsic `K`-linear residue `Res_L(ω)` equals the
`u⁻¹`-coefficient residue of `e.laurentDifferentialEquiv ω` in the level parameter. -/
theorem residue_eq_coeff_laurentDifferentialEquiv (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    Extension.ContinuousKaehlerDifferential.residue K L ω =
      (Level.ringEquivLaurentSeries K d
        (equivLevel K d (e.laurentDifferentialEquiv ω))).coeff (-1) := by
  rw [laurentDifferentialEquiv_apply, ← residue_eq_coeff_equivExtension,
    Extension.ContinuousKaehlerDifferential.residue_mapLinearEquiv]

/-- **Chart-independence of residues on intrinsic continuous one-forms.** Any two separable level
charts yield the same coefficient residue on `Ω¹_cont(L/K)`. -/
theorem coeff_laurentDifferentialEquiv_eq {n : ℕ+} [NeZero ((n : ℕ) : K)]
    (e : L ≃ₐ[K⸨X⸩] Level K d) (e' : L ≃ₐ[K⸨X⸩] Level K n)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    (Level.ringEquivLaurentSeries K d
      (equivLevel K d (e.laurentDifferentialEquiv ω))).coeff (-1) =
    (Level.ringEquivLaurentSeries K n
      (equivLevel K n (e'.laurentDifferentialEquiv ω))).coeff (-1) := by
  rw [← residue_eq_coeff_laurentDifferentialEquiv e,
    ← residue_eq_coeff_laurentDifferentialEquiv e']

section Topology

variable [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L]

/-- **Topological level-chart equivalence on continuous one-forms.** When `L` carries the
`K⸨X⸩`-module topology, any algebraic separable level chart `e : L ≃ₐ[K⸨X⸩] Level K d` upgrades
automatically to a continuous `K⸨X⸩`-linear equivalence on continuous one-forms, without assuming
continuity of `e` or `Module.Finite K⸨X⸩ L` separately. -/
noncomputable def laurentDifferentialContinuousEquiv (e : L ≃ₐ[K⸨X⸩] Level K d) :
    Extension.ContinuousKaehlerDifferential K L ≃L[K⸨X⸩]
      Level.ContinuousKaehlerDifferential K d :=
  have : Module.Finite K⸨X⸩ L := Module.Finite.equiv e.symm.toLinearEquiv
  e.laurentDifferentialEquiv.toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem laurentDifferentialContinuousEquiv_apply (e : L ≃ₐ[K⸨X⸩] Level K d)
    (ω : Extension.ContinuousKaehlerDifferential K L) :
    e.laurentDifferentialContinuousEquiv ω = e.laurentDifferentialEquiv ω := by
  simp [laurentDifferentialContinuousEquiv]

@[simp]
theorem toLinearEquiv_laurentDifferentialContinuousEquiv (e : L ≃ₐ[K⸨X⸩] Level K d) :
    e.laurentDifferentialContinuousEquiv.toLinearEquiv = e.laurentDifferentialEquiv := by
  simp [laurentDifferentialContinuousEquiv]

end Topology

end Intrinsic

end AlgEquiv
