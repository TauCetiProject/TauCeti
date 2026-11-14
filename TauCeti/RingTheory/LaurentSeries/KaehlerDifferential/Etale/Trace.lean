/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.Determinant
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Etale.Topology
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.FiniteExtension

/-!
# Differential trace and residue on étale Laurent extensions

Let `F = K⸨X⸩` and let `L` be a formally étale `F`-algebra (for instance any finite separable field
extension of `F`). Using the canonical scalar-extension isomorphism
`L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)` (`Extension.ContinuousKaehlerDifferential.tensorEquiv`), we
define the intrinsic differential trace

`Extension.ContinuousKaehlerDifferential.trace K L : Ω¹_cont(L/K) →ₗ[F] Ω¹_cont(F/K)`

by applying `Algebra.trace F L` on the first tensor factor. In the coordinate `dt` this sends
`x dt` to `Tr_{L/F}(x) dt` (`equivLaurentSeries_trace`), and when `L` has no finite `F`-basis it
vanishes by convention with `Algebra.trace`.

Because the extended formal derivative `D_L = d/dt` commutes with `Algebra.trace`
(`Extension.derivation_trace`, proved via `Derivation.map_trace`), the differential trace commutes
with the universal continuous derivations:

`trace K L (D K L x) = D K (Algebra.trace F L x)` (`trace_D`).

Composing `trace K L` with the `X⁻¹`-coefficient of `Ω¹_cont(F/K) ≃ F` defines a `K`-linear residue
`Extension.ContinuousKaehlerDifferential.residue K L : Ω¹_cont(L/K) →ₗ[K] K` directly on the
continuous Kähler quotient `Ω¹_cont(L/K)`, without choosing a level chart or primitive element. In
particular exact continuous one-forms have residue zero (`residue_D`) in every characteristic.

In any tower `K → F → M → L` of formally étale extensions, `relativeTrace K M L` traces continuous
one-forms from `L` to `M`, commutes with `D`, and composes transitively with `trace` and `residue`
when `M/F` and `L/M` are finite free (`trace_relativeTrace`, `residue_relativeTrace`).

## Main definitions

* `Extension.ContinuousKaehlerDifferential.trace K L`: the `K⸨X⸩`-linear differential trace
  `Ω¹_cont(L/K) →ₗ[K⸨X⸩] Ω¹_cont(K⸨X⸩/K)` via `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)`.
* `Extension.ContinuousKaehlerDifferential.relativeTrace K M L`: relative differential trace in a
  tower `K → K⸨X⸩ → M → L` of formally étale extensions.
* `Extension.ContinuousKaehlerDifferential.residue K L`: the intrinsic `K`-linear residue on
  `Ω¹_cont(L/K)`.

## Main results

* `TauCeti.LaurentSeries.Extension.derivation_trace`: `d/dt` commutes with `Algebra.trace`.
* `Extension.ContinuousKaehlerDifferential.trace_D`: differential trace commutes with `d`.
* `Extension.ContinuousKaehlerDifferential.trace_relativeTrace` and `residue_relativeTrace`:
  transitivity of differential trace and residue in finite free étale towers.
* `Extension.ContinuousKaehlerDifferential.residue_D`: exact continuous one-forms have residue zero
  in every characteristic.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968).
-/

public section

open HahnSeries TensorProduct
open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Extension

section DerivationTrace

variable {K : Type*} [Field K]
  {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M] [IsScalarTower K K⸨X⸩ M]
    [Algebra.FormallyEtale K⸨X⸩ M]
  {L : Type*} [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
    [Algebra.FormallyEtale K⸨X⸩ L]

/-- The formal derivative of `K⸨X⸩` commutes with `Algebra.trace K⸨X⸩ L`. -/
theorem derivation_trace (x : L) :
    laurentSeriesDerivation K (Algebra.trace K⸨X⸩ L x) =
      Algebra.trace K⸨X⸩ L (derivation K L x) := by
  let fn : K⸨X⸩ → K⸨X⸩ := _root_.LaurentSeries.derivative K
  have hadd (f g : K⸨X⸩) : fn (f + g) = fn f + fn g :=
    (_root_.LaurentSeries.derivative K).map_add f g
  have h1 : fn 1 = 0 := by
    change _root_.LaurentSeries.derivative K 1 = 0
    rw [← laurentSeriesDerivation_apply, Derivation.map_one_eq_zero]
  have hleib (f g : K⸨X⸩) : fn (f * g) = f * fn g + g * fn f := by
    change _root_.LaurentSeries.derivative K (f * g) = _
    rw [_root_.LaurentSeries.derivative_mul]
    ring
  have hsmul (c : K) (f : K⸨X⸩) :
      fn (algebraMap K K⸨X⸩ c * f) = algebraMap K K⸨X⸩ c * fn f := by
    change _root_.LaurentSeries.derivative K _ = _
    rw [laurentSeries_algebraMap_mul_eq_smul, laurentSeries_algebraMap_mul_eq_smul]
    exact (_root_.LaurentSeries.derivative K).map_smul c f
  let d₀ : @Derivation K K⸨X⸩ K⸨X⸩ _ _ _ _ _ Algebra.toModule :=
    letI : Module K K⸨X⸩ := Algebra.toModule
    { toFun := fn
      map_add' := hadd
      map_smul' c f := by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def]
        exact hsmul c f
      map_one_eq_zero' := h1
      leibniz' := hleib }
  have hd (f : K⸨X⸩) : derivation K L (algebraMap K⸨X⸩ L f) = algebraMap K⸨X⸩ L (d₀ f) := by
    simp [d₀, fn]
  simpa [d₀, fn] using Derivation.map_trace d₀ (derivation K L) hd x

/-- In a tower `K → K⸨X⸩ → M → L` of formally étale extensions, `D_M` commutes with
`Algebra.trace M L`. -/
theorem derivation_trace_tower [Algebra M L] [IsScalarTower K⸨X⸩ M L] (x : L) :
    derivation K M (Algebra.trace M L x) = Algebra.trace M L (derivation K L x) :=
  Derivation.map_trace (R := K) (derivation K M) (derivation K L)
    (fun m ↦ derivation_algebraMap_tower m) x

end DerivationTrace

namespace ContinuousKaehlerDifferential

section BaseTrace

variable (K : Type*) [Field K] (L : Type*) [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]

/-- **Differential trace on an étale Laurent extension.** Under the canonical scalar-extension
equivalence `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)` (`F = K⸨X⸩`), `trace K L` applies
`Algebra.trace F L` to the first tensor factor, sending `x dt` to `Tr_{L/F}(x) dt`. -/
noncomputable def trace :
    ContinuousKaehlerDifferential K L →ₗ[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K :=
  (TensorProduct.lid K⸨X⸩ _).toLinearMap ∘ₗ
    (Algebra.trace K⸨X⸩ L).rTensor _ ∘ₗ
      ((tensorEquiv K L).symm.restrictScalars K⸨X⸩).toLinearMap

variable {K L}

/-- Tracing `x` times the pullback of a base form `ω` yields `Tr_{L/F}(x) • ω`. -/
@[simp]
theorem trace_smul_map (x : L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (x • map K L ω) = Algebra.trace K⸨X⸩ L x • ω := by
  rw [← tensorEquiv_tmul]
  simp [trace, -tensorEquiv_tmul]

/-- In the coordinate `dt`, the differential trace applies `Algebra.trace K⸨X⸩ L` to the
`dt`-coordinate. -/
@[simp]
theorem equivLaurentSeries_trace (ω : ContinuousKaehlerDifferential K L) :
    TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K (trace K L ω) =
      Algebra.trace K⸨X⸩ L (equivSelf K L ω) := by
  conv_lhs => rw [← equivSelf_smul_D_algebraMap_single_one ω, ← map_D, trace_smul_map]
  rw [map_smul, TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D_single_one,
    smul_eq_mul, mul_one]

/-- Tracing a pulled-back base one-form multiplies it by the rank of `L` over `K⸨X⸩`. -/
@[simp]
theorem trace_map [Module.Free K⸨X⸩ L] (ω : TauCeti.ContinuousKaehlerDifferential K) :
    trace K L (map K L ω) = Module.finrank K⸨X⸩ L • ω := by
  rw [← one_smul L (map K L ω), trace_smul_map, ← map_one (algebraMap K⸨X⸩ L),
    Algebra.trace_algebraMap, smul_assoc, one_smul]

/-- **Differential trace commutes with `d`.** The trace of an exact continuous one-form `dx` is the
differential of `Tr_{L/F}(x)`. -/
@[simp]
theorem trace_D (x : L) :
    trace K L (D K L x) =
      TauCeti.ContinuousKaehlerDifferential.D K (Algebra.trace K⸨X⸩ L x) :=
  (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective <| by
    rw [equivLaurentSeries_trace, equivSelf_D,
      TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D,
      ← laurentSeriesDerivation_apply, derivation_trace]

/-- For a finite separable field extension, `trace K E` transports `traceBaseChange` across
`tensorEquiv K E`. -/
@[simp]
theorem trace_tensorEquiv {E : Type*} [Field E] [Algebra K⸨X⸩ E] [Algebra K E]
    [IsScalarTower K K⸨X⸩ E] [Algebra.FormallyEtale K⸨X⸩ E]
    (η : E ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    trace K E (tensorEquiv K E η) =
      TauCeti.ContinuousKaehlerDifferential.traceBaseChange E η := by
  induction η using TensorProduct.inductionOn with
  | tmul x ω => simp
  | add a b ha hb => simp [ha, hb]

/-- Differential trace is invariant under `K⸨X⸩`-algebra isomorphisms. -/
@[simp]
theorem trace_mapAlgHom_algEquiv {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M]
    (e : M ≃ₐ[K⸨X⸩] L) (ω : ContinuousKaehlerDifferential K M) :
    trace K L (mapAlgHom e.toAlgHom ω) = trace K M ω :=
  (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective <| by
    simp only [equivLaurentSeries_trace, equivSelf_mapAlgHom, AlgEquiv.coe_toAlgHom,
      Algebra.trace_eq_of_algEquiv]

@[simp]
theorem trace_equivAlgEquiv {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M]
    (e : M ≃ₐ[K⸨X⸩] L) (ω : ContinuousKaehlerDifferential K M) :
    trace K L (equivAlgEquiv e ω) = trace K M ω := by
  rw [equivAlgEquiv_apply, trace_mapAlgHom_algEquiv]

/-- Differential trace is continuous for the `K⸨X⸩`-module topology on a finite étale extension. -/
theorem continuous_trace [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L] [Module.Finite K⸨X⸩ L] :
    Continuous (trace K L) :=
  IsModuleTopology.continuous_of_linearMap (trace K L)

end BaseTrace

/-! ### Relative differential trace in towers -/

section Tower

variable (K : Type*) [Field K]
  (M : Type*) [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M] [IsScalarTower K K⸨X⸩ M]
    [Algebra.FormallyEtale K⸨X⸩ M]
  (L : Type*) [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
    [Algebra.FormallyEtale K⸨X⸩ L] [Algebra M L] [IsScalarTower K⸨X⸩ M L]

/-- **Relative differential trace** `Tr_{L/M} : Ω¹_cont(L/K) → Ω¹_cont(M/K)` in a tower
`K → K⸨X⸩ → M → L` of formally étale extensions, sending `x dt` to `Tr_{L/M}(x) dt`. -/
noncomputable def relativeTrace :
    ContinuousKaehlerDifferential K L →ₗ[K⸨X⸩] ContinuousKaehlerDifferential K M :=
  (equivSelf K M).symm.toLinearMap.restrictScalars K⸨X⸩ ∘ₗ
    (Algebra.trace M L).restrictScalars K⸨X⸩ ∘ₗ
      (equivSelf K L).toLinearMap.restrictScalars K⸨X⸩

variable {K M L}

@[simp]
theorem equivSelf_relativeTrace (ω : ContinuousKaehlerDifferential K L) :
    equivSelf K M (relativeTrace K M L ω) = Algebra.trace M L (equivSelf K L ω) :=
  (equivSelf K M).apply_symm_apply _

/-- `relativeTrace K M L` is `M`-linear with respect to the `M`-action via `algebraMap M L`. -/
theorem relativeTrace_algebraMap_smul (m : M) (ω : ContinuousKaehlerDifferential K L) :
    relativeTrace K M L (algebraMap M L m • ω) = m • relativeTrace K M L ω :=
  (equivSelf K M).injective <| by
    simp only [equivSelf_relativeTrace, map_smul]
    rw [IsScalarTower.algebraMap_smul L m (equivSelf K L ω), LinearMap.map_smul]

/-- Tracing `x` times a form pulled back from `M` multiplies that form by `Tr_{L/M}(x)`. -/
@[simp]
theorem relativeTrace_smul_mapAlgHom (x : L) (ω : ContinuousKaehlerDifferential K M) :
    relativeTrace K M L (x • mapAlgHom (IsScalarTower.toAlgHom K⸨X⸩ M L) ω) =
      Algebra.trace M L x • ω :=
  (equivSelf K M).injective <| by
    rw [equivSelf_relativeTrace, map_smul, equivSelf_mapAlgHom, IsScalarTower.toAlgHom_apply,
      smul_eq_mul, mul_comm, ← Algebra.smul_def, LinearMap.map_smul, map_smul, smul_eq_mul,
      mul_comm, ← smul_eq_mul]

theorem relativeTrace_mapAlgHom [Module.Free M L] (ω : ContinuousKaehlerDifferential K M) :
    relativeTrace K M L (mapAlgHom (IsScalarTower.toAlgHom K⸨X⸩ M L) ω) =
      Module.finrank M L • ω := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · exact (equivSelf K M).injective (Subsingleton.elim _ _)
  · rw [← one_smul L (mapAlgHom _ ω), relativeTrace_smul_mapAlgHom, ← map_one (algebraMap M L),
      Algebra.trace_algebraMap, smul_assoc, one_smul]

/-- Relative differential trace commutes with the universal continuous derivations. -/
@[simp]
theorem relativeTrace_D (x : L) :
    relativeTrace K M L (D K L x) = D K M (Algebra.trace M L x) :=
  (equivSelf K M).injective <| by
    rw [equivSelf_relativeTrace, equivSelf_D, equivSelf_D, derivation_trace_tower]

/-- **Transitivity of differential trace in towers.** When `M/K⸨X⸩` and `L/M` are finite free (in
particular for any tower of finite separable field extensions), tracing from `L` to `M` and then to
`K⸨X⸩` equals tracing directly from `L` to `K⸨X⸩`. -/
theorem trace_relativeTrace [Module.Free K⸨X⸩ M] [Module.Finite K⸨X⸩ M]
    [Module.Free M L] [Module.Finite M L] (ω : ContinuousKaehlerDifferential K L) :
    trace K M (relativeTrace K M L ω) = trace K L ω :=
  (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective <| by
    rw [equivLaurentSeries_trace, equivSelf_relativeTrace, equivLaurentSeries_trace,
      Algebra.trace_trace]

end Tower

/-! ### Intrinsic `K`-linear residue on `Ω¹_cont(L/K)` -/

section Residue

variable (K : Type*) [Field K] (L : Type*) [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]

/-- **Intrinsic residue on `Ω¹_cont(L/K)`.** The `K`-linear residue of a continuous one-form on a
formally étale `K⸨X⸩`-algebra `L`, defined as the `X⁻¹`-coefficient of its differential trace down
to `K⸨X⸩`. -/
noncomputable def residue : ContinuousKaehlerDifferential K L →ₗ[K] K where
  toFun ω := (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K (trace K L ω)).coeff (-1)
  map_add' ω η := by simp
  map_smul' c ω := by
    rw [equivLaurentSeries_trace, equivLaurentSeries_trace, ← algebraMap_smul L c ω,
      IsScalarTower.algebraMap_apply K K⸨X⸩ L, LinearEquiv.map_smul,
      IsScalarTower.algebraMap_smul L (algebraMap K K⸨X⸩ c) (equivSelf K L ω),
      LinearMap.map_smul, smul_eq_mul, laurentSeries_algebraMap_mul_eq_smul, coeff_smul,
      RingHom.id_apply]

variable {K L}

theorem residue_apply (ω : ContinuousKaehlerDifferential K L) :
    residue K L ω =
      (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K (trace K L ω)).coeff (-1) :=
  (rfl)

theorem residue_eq_coeff_neg_one_trace (ω : ContinuousKaehlerDifferential K L) :
    residue K L ω = (Algebra.trace K⸨X⸩ L (equivSelf K L ω)).coeff (-1) :=
  congrArg (fun f : K⸨X⸩ ↦ f.coeff (-1)) (equivLaurentSeries_trace ω)

@[simp]
theorem residue_smul_map (x : L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    residue K L (x • map K L ω) =
      (Algebra.trace K⸨X⸩ L x *
        TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K ω).coeff (-1) := by
  simp [residue_apply]

theorem residue_map [Module.Free K⸨X⸩ L] (ω : TauCeti.ContinuousKaehlerDifferential K) :
    residue K L (map K L ω) =
      Module.finrank K⸨X⸩ L •
        (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K ω).coeff (-1) := by
  rw [residue_apply, trace_map]
  simp only [map_nsmul, coeff_nsmul, Pi.smul_apply]

/-- **Exact continuous one-forms have residue zero**, in every characteristic. -/
@[simp]
theorem residue_D (x : L) : residue K L (D K L x) = 0 := by
  rw [residue_apply, trace_D, TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D,
    _root_.LaurentSeries.coeff_neg_one_derivative]

/-- On a field extension, `residue K E` agrees with `residueBaseChange E` across `tensorEquiv`. -/
@[simp]
theorem residue_tensorEquiv {E : Type*} [Field E] [Algebra K⸨X⸩ E] [Algebra K E]
    [IsScalarTower K K⸨X⸩ E] [Algebra.FormallyEtale K⸨X⸩ E]
    (η : E ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    residue K E (tensorEquiv K E η) =
      TauCeti.ContinuousKaehlerDifferential.residueBaseChange E η := by
  rw [residue_apply, trace_tensorEquiv,
    TauCeti.ContinuousKaehlerDifferential.residueBaseChange_apply]

/-- The intrinsic residue is invariant under `K⸨X⸩`-algebra isomorphisms. -/
@[simp]
theorem residue_mapAlgHom_algEquiv {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M]
    (e : M ≃ₐ[K⸨X⸩] L) (ω : ContinuousKaehlerDifferential K M) :
    residue K L (mapAlgHom e.toAlgHom ω) = residue K M ω := by
  rw [residue_apply, trace_mapAlgHom_algEquiv, ← residue_apply]

@[simp]
theorem residue_equivAlgEquiv {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M]
    (e : M ≃ₐ[K⸨X⸩] L) (ω : ContinuousKaehlerDifferential K M) :
    residue K L (equivAlgEquiv e ω) = residue K M ω := by
  rw [equivAlgEquiv_apply, residue_mapAlgHom_algEquiv]

/-- **Residue compatibility in towers (`Res_M(Tr_{L/M} ω) = Res_L(ω)`).** In a tower of finite free
formally étale extensions `K⸨X⸩ → M → L`, the residue on `M` of the relative differential trace
equals the residue on `L`. -/
theorem residue_relativeTrace {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M]
    [Algebra M L] [IsScalarTower K⸨X⸩ M L]
    [Module.Free K⸨X⸩ M] [Module.Finite K⸨X⸩ M] [Module.Free M L] [Module.Finite M L]
    (ω : ContinuousKaehlerDifferential K L) :
    residue K M (relativeTrace K M L ω) = residue K L ω := by
  rw [residue_apply, trace_relativeTrace, ← residue_apply]

end Residue

end ContinuousKaehlerDifferential

end TauCeti.LaurentSeries.Extension
