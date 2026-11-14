/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Etale

/-!
# Differential traces and residues for étale extensions of Laurent series

Let `K` be a field, `F = K⸨X⸩`, and `L` a formally étale `F`-algebra. By
`TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.tensorEquiv`, the module of
continuous one-forms `Ω¹_cont(L/K)` identifies `L`-linearly with the scalar extension
`L ⊗_F Ω¹_cont(F/K)`. Applying the algebra trace `Tr_{L/F} : L →ₗ[F] F` to the left tensor factor
defines the differential trace `trace K L : Ω¹_cont(L/K) →ₗ[F] Ω¹_cont(F/K)`, sending `x • map ω`
to `Tr_{L/F}(x) • ω` and `x dt` to `Tr_{L/F}(x) dt` (and vanishing when `L` is not finite and free
over `F`, matching `Algebra.trace`).

More generally, in a tower `F → M → L` of formally étale `F`-algebras, the relative base-change
equivalence `L ⊗_M Ω¹_cont(M/K) ≃ Ω¹_cont(L/K)` (`relativeTensorEquiv K M L`) induces the relative
differential trace `relativeTrace K M L : Ω¹_cont(L/K) →ₗ[F] Ω¹_cont(M/K)`. To avoid global
`Module M Ω¹_cont(L/K)` instance diamonds when `M = L` or `M = F`, `relativeTrace` is bundled as an
`F`-linear map together with its `M`-linearity law `relativeTrace_algebraMap_smul`; it sends `x`
times the pullback of `ω ∈ Ω¹_cont(M/K)` to `Tr_{L/M}(x) • ω` and is transitive in finite free
towers (`trace_relativeTrace`, `relativeTrace_relativeTrace`). When `L` (and `M`) are finite
`F`-algebras carrying the `F`-module topology, `trace K L` and `relativeTrace K M L` are continuous
for the canonical module topologies on continuous one-forms.

Taking the `X⁻¹`-coefficient of `trace K L ω` defines the intrinsic `K`-linear residue
`residue K L : Ω¹_cont(L/K) →ₗ[K] K`. It is invariant under `F`-algebra isomorphisms
(`residue_mapAlgEquiv`) and preserved by relative differential traces in finite free towers
(`residue_relativeTrace : residue K M (relativeTrace K M L ω) = residue K L ω`). Compatibility with
explicit ramified levels `Level K d` and level charts is established in
`TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Level`.

## Main definitions

* `TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.trace K L`: the differential trace
  `Ω¹_cont(L/K) →ₗ[K⸨X⸩] Ω¹_cont(K⸨X⸩/K)`.
* `TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.relativeTrace K M L`: the relative
  differential trace `Ω¹_cont(L/K) →ₗ[K⸨X⸩] Ω¹_cont(M/K)` in a tower `K⸨X⸩ → M → L`.
* `TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.residue K L`: the intrinsic
  `K`-linear residue `Ω¹_cont(L/K) →ₗ[K] K`, defined as the `X⁻¹`-coefficient of `trace K L`.

## Main results

* `Extension.ContinuousKaehlerDifferential.trace_smul_map` and `equivLaurentSeries_trace`:
  `trace K L` sends `x • map K L ω` to `Tr_{L/K⸨X⸩}(x) • ω` and `x dt` to `Tr_{L/K⸨X⸩}(x) dt`.
* `Extension.ContinuousKaehlerDifferential.trace_mapAlgEquiv` and `residue_mapAlgEquiv`:
  `trace` and `residue` are invariant under `K⸨X⸩`-algebra isomorphisms.
* `Extension.ContinuousKaehlerDifferential.continuous_trace` and `continuous_relativeTrace`:
  continuity for the module topologies when `L` is finite over `K⸨X⸩`.
* `Extension.ContinuousKaehlerDifferential.trace_relativeTrace`, `relativeTrace_relativeTrace`, and
  `residue_relativeTrace`: transitivity of differential traces and trace-invariance of residues in
  finite free towers.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968), for the construction of
  the residue on finite separable extensions via the differential trace.
-/

public section

open HahnSeries TensorProduct
open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential

section Trace

variable (K L : Type*) [Field K] [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]

/-- **The trace of continuous one-forms.** For a formally étale `K⸨X⸩`-algebra `L`, the
differential trace `Tr_{L/K⸨X⸩} : Ω¹_cont(L/K) →ₗ[K⸨X⸩] Ω¹_cont(K⸨X⸩/K)` applies `Algebra.trace`
to the first factor of `L ⊗_{K⸨X⸩} Ω¹_cont(K⸨X⸩/K) ≃ Ω¹_cont(L/K)`. As with `Algebra.trace`, this
map is zero when `L` is not finite and free over `K⸨X⸩`. -/
noncomputable def trace :
    ContinuousKaehlerDifferential K L →ₗ[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K :=
  (TensorProduct.lid K⸨X⸩ _).toLinearMap ∘ₗ
    (Algebra.trace K⸨X⸩ L).rTensor _ ∘ₗ
      ((tensorEquiv K L).symm.restrictScalars K⸨X⸩).toLinearMap

variable {K L}

/-- For a continuous one-form `ω` on `K⸨X⸩`, the trace of `x` times its pullback to `L` is
`Tr_{L/K⸨X⸩}(x) • ω`. -/
@[simp]
theorem trace_smul_map (x : L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (x • map K L ω) = Algebra.trace K⸨X⸩ L x • ω := by
  rw [← tensorEquiv_tmul]
  simp [trace, -tensorEquiv_tmul]

/-- Tracing a pulled-back continuous one-form multiplies it by the `K⸨X⸩`-rank of `L`. -/
@[simp]
theorem trace_map [Module.Free K⸨X⸩ L] (ω : TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (map K L ω) = Module.finrank K⸨X⸩ L • ω := by
  rw [← one_smul L (map K L ω), trace_smul_map, ← map_one (algebraMap K⸨X⸩ L),
    Algebra.trace_algebraMap, smul_assoc, one_smul]

/-- Every traced one-form is `Tr_{L/K⸨X⸩}(equivSelf K L ω) • dX`. -/
theorem trace_eq_trace_equivSelf_smul_D_single_one (ω : ContinuousKaehlerDifferential K L) :
    trace K L ω =
      Algebra.trace K⸨X⸩ L (equivSelf K L ω) •
        TauCeti.ContinuousKaehlerDifferential.D K (single 1 1) := by
  conv_lhs =>
    rw [← equivSelf_smul_D_algebraMap_single_one ω, ← map_D (L := L) (single 1 1), trace_smul_map]

/-- In the coordinate `dX`, the differential trace applies `Algebra.trace K⸨X⸩ L` to the
coefficient of `dt`. -/
@[simp]
theorem equivLaurentSeries_trace (ω : ContinuousKaehlerDifferential K L) :
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K (trace K L ω) =
      Algebra.trace K⸨X⸩ L (equivSelf K L ω) := by
  rw [trace_eq_trace_equivSelf_smul_D_single_one, map_smul,
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D]
  simp

/-- Differential trace is invariant under `K⸨X⸩`-algebra isomorphisms between formally étale
`K⸨X⸩`-algebras. -/
@[simp]
theorem trace_mapAlgEquiv {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M] (e : M ≃ₐ[K⸨X⸩] L)
    (ω : ContinuousKaehlerDifferential K M) :
    trace K L (mapAlgEquiv e ω) = trace K M ω := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [equivLaurentSeries_trace, equivLaurentSeries_trace, mapAlgEquiv_apply, equivSelf_mapAlgHom,
    AlgEquiv.toAlgHom_apply, Algebra.trace_eq_of_algEquiv e]

/-- When `L` is a finite `K⸨X⸩`-algebra carrying the `K⸨X⸩`-module topology, the differential trace
is continuous for the module topologies on continuous one-forms. -/
@[fun_prop]
theorem continuous_trace [TopologicalSpace L] [Module.Finite K⸨X⸩ L] [IsModuleTopology K⸨X⸩ L] :
    Continuous (trace K L) :=
  IsModuleTopology.continuous_of_linearMap (trace K L)

end Trace

/-! ### Relative differential trace in extension towers -/

section RelativeTrace

variable (K M L : Type*) [Field K] [CommRing M] [CommRing L]
  [Algebra K⸨X⸩ M] [Algebra K M] [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M]
  [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]
  [Algebra M L] [IsScalarTower K⸨X⸩ M L]

/-- **Relative differential trace in a tower.** For a tower `K⸨X⸩ → M → L` of formally étale
`K⸨X⸩`-algebras, `relativeTrace K M L : Ω¹_cont(L/K) →ₗ[K⸨X⸩] Ω¹_cont(M/K)` applies
`Algebra.trace M L` to the first factor of `L ⊗_M Ω¹_cont(M/K) ≃ Ω¹_cont(L/K)`. It is bundled over
`K⸨X⸩` rather than `M` to avoid global `Module M Ω¹_cont(L/K)` diamonds; `M`-linearity is recorded
by `relativeTrace_algebraMap_smul`. -/
noncomputable def relativeTrace :
    ContinuousKaehlerDifferential K L →ₗ[K⸨X⸩] ContinuousKaehlerDifferential K M :=
  ((TensorProduct.lid M (ContinuousKaehlerDifferential K M)).toLinearMap ∘ₗ
      (Algebra.trace M L).rTensor (ContinuousKaehlerDifferential K M)).restrictScalars K⸨X⸩ ∘ₗ
    ((relativeTensorEquiv K M L).symm.restrictScalars K⸨X⸩).toLinearMap

variable {K M L}

/-- On `L ⊗_M Ω¹_cont(M/K)`, `relativeTrace` contracts the left tensor factor with
`Algebra.trace M L`. -/
theorem relativeTrace_relativeTensorEquiv (η : L ⊗[M] ContinuousKaehlerDifferential K M) :
    relativeTrace K M L (relativeTensorEquiv K M L η) =
      TensorProduct.lid M _ ((Algebra.trace M L).rTensor _ η) := by
  simp [relativeTrace]

/-- For `ω ∈ Ω¹_cont(M/K)`, the relative trace of `x` times its pullback along `M → L` is
`Tr_{L/M}(x) • ω`. -/
@[simp]
theorem relativeTrace_smul_mapAlgHom (x : L) (ω : ContinuousKaehlerDifferential K M) :
    relativeTrace K M L (x • mapAlgHom (IsScalarTower.toAlgHom K⸨X⸩ M L) ω) =
      Algebra.trace M L x • ω := by
  rw [← relativeTensorEquiv_tmul, relativeTrace_relativeTensorEquiv]
  simp

/-- Tracing a pulled-back continuous one-form along `M → L` multiplies it by `[L : M]`. -/
@[simp]
theorem relativeTrace_mapAlgHom [StrongRankCondition M] [Module.Free M L]
    (ω : ContinuousKaehlerDifferential K M) :
    relativeTrace K M L (mapAlgHom (IsScalarTower.toAlgHom K⸨X⸩ M L) ω) =
      Module.finrank M L • ω := by
  rw [← one_smul L (mapAlgHom _ ω), relativeTrace_smul_mapAlgHom, ← map_one (algebraMap M L),
    Algebra.trace_algebraMap, smul_assoc, one_smul]

/-- In the coordinate `dt`, the relative differential trace applies `Algebra.trace M L` to the
coefficient. -/
@[simp]
theorem equivSelf_relativeTrace (ω : ContinuousKaehlerDifferential K L) :
    equivSelf K M (relativeTrace K M L ω) = Algebra.trace M L (equivSelf K L ω) := by
  have hdt : D K L (algebraMap K⸨X⸩ L (single 1 1)) =
      mapAlgHom (IsScalarTower.toAlgHom K⸨X⸩ M L) (D K M (algebraMap K⸨X⸩ M (single 1 1))) := by
    rw [mapAlgHom_D, IsScalarTower.toAlgHom_apply, IsScalarTower.algebraMap_apply K⸨X⸩ M L]
  conv_lhs => rw [← equivSelf_smul_D_algebraMap_single_one ω, hdt, relativeTrace_smul_mapAlgHom]
  rw [map_smul, equivSelf_D, derivation_algebraMap_single_one, smul_eq_mul, mul_one]

/-- `relativeTrace K M L` is `M`-linear for the algebra action of `M` on `L`. -/
theorem relativeTrace_algebraMap_smul (y : M) (ω : ContinuousKaehlerDifferential K L) :
    relativeTrace K M L (algebraMap M L y • ω) = y • relativeTrace K M L ω := by
  apply (equivSelf K M).injective
  rw [equivSelf_relativeTrace, map_smul, smul_eq_mul, ← Algebra.smul_def, LinearMap.map_smul,
    map_smul, equivSelf_relativeTrace, smul_eq_mul]

/-- **Transitivity of differential trace.** In a tower `K⸨X⸩ → M → L` of finite free formally étale
algebras, composing `relativeTrace K M L` with `trace K M` recovers `trace K L`. -/
@[simp]
theorem trace_relativeTrace [Module.Free K⸨X⸩ M] [Module.Finite K⸨X⸩ M]
    [Module.Free M L] [Module.Finite M L] (ω : ContinuousKaehlerDifferential K L) :
    trace K M (relativeTrace K M L ω) = trace K L ω := by
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  rw [equivLaurentSeries_trace, equivSelf_relativeTrace, equivLaurentSeries_trace,
    Algebra.trace_trace]

/-- **Transitivity of relative differential trace.** In a tower `K⸨X⸩ → M → E → L` of formally
étale `K⸨X⸩`-algebras with `E/M` and `L/E` finite and free, relative differential traces compose. -/
@[simp]
theorem relativeTrace_relativeTrace {E : Type*} [CommRing E] [Algebra K⸨X⸩ E] [Algebra K E]
    [IsScalarTower K K⸨X⸩ E] [Algebra.FormallyEtale K⸨X⸩ E] [Algebra M E] [Algebra E L]
    [IsScalarTower K⸨X⸩ M E] [IsScalarTower K⸨X⸩ E L] [IsScalarTower M E L]
    [Module.Free M E] [Module.Finite M E] [Module.Free E L] [Module.Finite E L]
    (ω : ContinuousKaehlerDifferential K L) :
    relativeTrace K M E (relativeTrace K E L ω) = relativeTrace K M L ω := by
  apply (equivSelf K M).injective
  rw [equivSelf_relativeTrace, equivSelf_relativeTrace, equivSelf_relativeTrace,
    Algebra.trace_trace]

/-- When `M` and `L` are finite `K⸨X⸩`-algebras carrying `K⸨X⸩`-module topologies, the relative
differential trace is continuous for the module topologies on continuous one-forms. -/
@[fun_prop]
theorem continuous_relativeTrace [TopologicalSpace M] [TopologicalSpace L]
    [Module.Finite K⸨X⸩ M] [IsModuleTopology K⸨X⸩ M]
    [Module.Finite K⸨X⸩ L] [IsModuleTopology K⸨X⸩ L] :
    Continuous (relativeTrace K M L) :=
  IsModuleTopology.continuous_of_linearMap (relativeTrace K M L)

end RelativeTrace

/-! ### Intrinsic residue of continuous one-forms -/

section Residue

variable (K L : Type*) [Field K] [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]

/-- **Intrinsic residue of a continuous one-form.** For a formally étale `K⸨X⸩`-algebra `L`, the
residue `Res_L : Ω¹_cont(L/K) →ₗ[K] K` is the `X⁻¹`-coefficient of the differential trace
`trace K L ω` in `Ω¹_cont(K⸨X⸩/K) ≃ K⸨X⸩`. -/
noncomputable def residue : ContinuousKaehlerDifferential K L →ₗ[K] K where
  toFun ω := (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K (trace K L ω)).coeff (-1)
  map_add' ω η := by simp
  map_smul' c ω := by
    rw [← smul_one_smul K⸨X⸩ c ω, map_smul, map_smul, smul_eq_mul, ← C_mul_eq_smul, mul_one,
      C_mul_eq_smul, coeff_smul, RingHom.id_apply]

variable {K L}

/-- The residue of `ω` is the `X⁻¹`-coefficient of its differential trace. -/
theorem residue_apply (ω : ContinuousKaehlerDifferential K L) :
    residue K L ω =
      (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K (trace K L ω)).coeff (-1) :=
  (rfl)

/-- In terms of `equivSelf`, `residue K L ω` is the `X⁻¹`-coefficient of
`Tr_{L/K⸨X⸩}(equivSelf K L ω)`. -/
theorem residue_eq_coeff_neg_one_trace (ω : ContinuousKaehlerDifferential K L) :
    residue K L ω = (Algebra.trace K⸨X⸩ L (equivSelf K L ω)).coeff (-1) := by
  rw [residue_apply, equivLaurentSeries_trace]

/-- On `x • map K L ω`, the residue is the `X⁻¹`-coefficient of `Tr_{L/K⸨X⸩}(x)` times the
coefficient of `ω`. -/
@[simp]
theorem residue_smul_map (x : L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    residue K L (x • map K L ω) =
      (Algebra.trace K⸨X⸩ L x *
        TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K ω).coeff (-1) := by
  simp [residue_apply]

/-- Pulling back a continuous one-form from `K⸨X⸩` multiplies its residue by `[L : K⸨X⸩]`. -/
theorem residue_map [Module.Free K⸨X⸩ L] (ω : TauCeti.ContinuousKaehlerDifferential K) :
    residue K L (map K L ω) =
      Module.finrank K⸨X⸩ L •
        (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K ω).coeff (-1) := by
  rw [residue_apply, trace_map, map_nsmul, coeff_nsmul, Pi.smul_apply]

/-- The intrinsic residue is invariant under `K⸨X⸩`-algebra isomorphisms between formally étale
`K⸨X⸩`-algebras. -/
@[simp]
theorem residue_mapAlgEquiv {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M] (e : M ≃ₐ[K⸨X⸩] L)
    (ω : ContinuousKaehlerDifferential K M) :
    residue K L (mapAlgEquiv e ω) = residue K M ω := by
  rw [residue_apply, residue_apply, trace_mapAlgEquiv]

/-- **Relative differential trace preserves residues.** In a tower `K⸨X⸩ → M → L` of finite free
formally étale `K⸨X⸩`-algebras, `Res_M (Tr_{L/M} ω) = Res_L ω`. -/
@[simp]
theorem residue_relativeTrace {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M] [Algebra M L]
    [IsScalarTower K⸨X⸩ M L] [Module.Free K⸨X⸩ M] [Module.Finite K⸨X⸩ M]
    [Module.Free M L] [Module.Finite M L] (ω : ContinuousKaehlerDifferential K L) :
    residue K M (relativeTrace K M L ω) = residue K L ω := by
  rw [residue_apply, residue_apply, trace_relativeTrace]

end Residue

end TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential
