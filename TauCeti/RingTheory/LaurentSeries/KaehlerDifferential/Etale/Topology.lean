/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.ModuleTopology
public import TauCeti.RingTheory.Kaehler.MapSemilinear
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Etale.Basic
public import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Functoriality and module topology of continuous one-forms on étale Laurent extensions

Let `F = K⸨X⸩` and let `M`, `L` be formally étale `F`-algebras. Every `F`-algebra homomorphism
`φ : M →ₐ[F] L` intertwines the extended formal derivatives `D_M` and `D_L`
(`TauCeti.LaurentSeries.Extension.derivation_algHom`), because `M` is formally unramified over `F`.
Consequently `φ` induces a semilinear pullback map
`ContinuousKaehlerDifferential.mapAlgHom φ : Ω¹_cont(M/K) → Ω¹_cont(L/K)` induced on the continuous
quotient by `KaehlerDifferential.mapSemilinear` and commuting with `d`, the rank-one coordinate in
`dt`, and pullback from `Ω¹_cont(F/K)`. An `F`-algebra isomorphism lifts to a semilinear equivalence
`ContinuousKaehlerDifferential.equivAlgEquiv`.

When `L` carries a topology, `Ω¹_cont(L/K)` carries the `L`-module topology (`moduleTopology L _`),
making it a topological additive group; when `L` is a topological semiring, the coordinate
`Ω¹_cont(L/K) ≃ L` (`x dt ↦ x`) is a continuous `L`-linear equivalence
(`ContinuousKaehlerDifferential.continuousEquivSelf`).

When `L` is module-finite over `F` and carries the `F`-module topology — for instance any finite
separable extension equipped with `moduleTopology F L`, or a separable ramified level `K⸨u⸩` with
its valuation topology — restriction of scalars gives `IsModuleTopology F Ω¹_cont(L/K)`. Both
`D_L : L → L` and `d : L → Ω¹_cont(L/K)` are continuous, the scalar-extension isomorphism
`L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)` is a continuous `F`-linear equivalence, and a `K`-derivation
`δ : L → N` into a Hausdorff `L`-module with continuous `L`-scalar multiplication is continuous on
`L` if and only if its restriction to `F` is continuous. Thus `d : L → Ω¹_cont(L/K)` is the
universal continuous `K`-derivation of `L`.

## Main definitions

* `Extension.ContinuousKaehlerDifferential.mapAlgHom`: semilinear pullback of continuous one-forms
  along `φ : M →ₐ[K⸨X⸩] L`.
* `Extension.ContinuousKaehlerDifferential.equivAlgEquiv`: semilinear equivalence induced by a
  `K⸨X⸩`-algebra isomorphism.
* `Extension.ContinuousKaehlerDifferential.continuousEquivSelf`: the continuous `L`-linear
  coordinate `Ω¹_cont(L/K) ≃L[L] L`.
* `Extension.ContinuousKaehlerDifferential.continuousTensorEquiv`: the continuous `K⸨X⸩`-linear
  scalar-extension equivalence `L ⊗[K⸨X⸩] Ω¹_cont(K⸨X⸩/K) ≃L[K⸨X⸩] Ω¹_cont(L/K)`.

## Main results

* `TauCeti.LaurentSeries.Extension.derivation_algHom`: `K⸨X⸩`-algebra maps commute with `d/dt`.
* `Extension.ContinuousKaehlerDifferential.mapAlgHom_mk`: pullback is induced on the quotient by
  `KaehlerDifferential.mapSemilinear`.
* `TauCeti.LaurentSeries.Extension.continuous_derivation` and
  `Extension.ContinuousKaehlerDifferential.continuous_D`: `d/dt` and `d` are continuous for the
  `K⸨X⸩`-module topology on a finite étale extension.
* `Extension.ContinuousKaehlerDifferential.exists_compDer_eq_iff_continuous` and
  `existsUnique_compDer_eq_of_continuous`: universal property of `Ω¹_cont(L/K)` for continuous
  `K`-derivations on `L`.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968).
-/

public section

open HahnSeries TensorProduct
open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Extension

section Functoriality

variable {K : Type*} [Field K]
  {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M] [IsScalarTower K K⸨X⸩ M]
    [Algebra.FormallyEtale K⸨X⸩ M]
  {L : Type*} [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L] [IsScalarTower K K⸨X⸩ L]
    [Algebra.FormallyEtale K⸨X⸩ L]
  {P : Type*} [CommRing P] [Algebra K⸨X⸩ P] [Algebra K P] [IsScalarTower K K⸨X⸩ P]
    [Algebra.FormallyEtale K⸨X⸩ P]

/-- Every `K⸨X⸩`-algebra homomorphism between formally étale `K⸨X⸩`-algebras commutes with the
extended formal derivative `d/dt`. -/
@[simp]
theorem derivation_algHom (φ : M →ₐ[K⸨X⸩] L) (x : M) :
    derivation K L (φ x) = φ (derivation K M x) :=
  Derivation.algHom_apply_of_formallyUnramified (S := K⸨X⸩) (derivation K M) (derivation K L) φ
    (fun f ↦ by rw [derivation_algebraMap, derivation_algebraMap, φ.commutes]) x

/-- In a tower `K → K⸨X⸩ → M → L` of formally étale extensions, `D_L` extends `D_M`. -/
theorem derivation_algebraMap_tower [Algebra M L] [IsScalarTower K⸨X⸩ M L] (x : M) :
    derivation K L (algebraMap M L x) = algebraMap M L (derivation K M x) :=
  derivation_algHom (IsScalarTower.toAlgHom K⸨X⸩ M L) x

namespace ContinuousKaehlerDifferential

/-- Pullback of continuous one-forms along a `K⸨X⸩`-algebra homomorphism `φ : M →ₐ[K⸨X⸩] L` between
formally étale extensions, sending `x dt` to `φ x dt`. -/
noncomputable def mapAlgHom (φ : M →ₐ[K⸨X⸩] L) :
    ContinuousKaehlerDifferential K M →ₛₗ[(φ : M →+* L)] ContinuousKaehlerDifferential K L where
  toFun ω := (equivSelf K L).symm (φ (equivSelf K M ω))
  map_add' ω η := by rw [map_add, map_add, map_add]
  map_smul' c ω := by
    rw [map_smul, smul_eq_mul, map_mul, ← smul_eq_mul, LinearEquiv.map_smul]
    rfl

/-- The `K⸨X⸩`-linear pullback of continuous one-forms along `φ : M →ₐ[K⸨X⸩] L`. -/
noncomputable def linearMapAlgHom (φ : M →ₐ[K⸨X⸩] L) :
    ContinuousKaehlerDifferential K M →ₗ[K⸨X⸩] ContinuousKaehlerDifferential K L :=
  (equivSelf K L).symm.toLinearMap.restrictScalars K⸨X⸩ ∘ₗ φ.toLinearMap ∘ₗ
    (equivSelf K M).toLinearMap.restrictScalars K⸨X⸩

@[simp]
theorem linearMapAlgHom_apply (φ : M →ₐ[K⸨X⸩] L) (ω : ContinuousKaehlerDifferential K M) :
    linearMapAlgHom φ ω = mapAlgHom φ ω := (rfl)

theorem mapAlgHom_smul (φ : M →ₐ[K⸨X⸩] L) (c : M) (ω : ContinuousKaehlerDifferential K M) :
    mapAlgHom φ (c • ω) = φ c • mapAlgHom φ ω :=
  (mapAlgHom φ).map_smulₛₗ c ω

@[simp]
theorem equivSelf_mapAlgHom (φ : M →ₐ[K⸨X⸩] L) (ω : ContinuousKaehlerDifferential K M) :
    equivSelf K L (mapAlgHom φ ω) = φ (equivSelf K M ω) :=
  (equivSelf K L).apply_symm_apply _

/-- Pullback along `φ : M →ₐ[K⸨X⸩] L` commutes with the universal continuous derivations. -/
@[simp]
theorem mapAlgHom_D (φ : M →ₐ[K⸨X⸩] L) (x : M) :
    mapAlgHom φ (D K M x) = D K L (φ x) :=
  (equivSelf K L).injective <| by
    rw [equivSelf_mapAlgHom, equivSelf_D, equivSelf_D, derivation_algHom]

/-- Pullback along `φ : M →ₐ[K⸨X⸩] L` is compatible with pullback from `K⸨X⸩`. -/
@[simp]
theorem mapAlgHom_map (φ : M →ₐ[K⸨X⸩] L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    mapAlgHom φ (map K M ω) = map K L ω :=
  (equivSelf K L).injective <| by rw [equivSelf_mapAlgHom, equivSelf_map, equivSelf_map, φ.commutes]

/-- Pullback of continuous one-forms along `φ : M →ₐ[K⸨X⸩] L` is induced on the quotient by
`KaehlerDifferential.mapSemilinear`. -/
@[simp]
theorem mapAlgHom_mk (φ : M →ₐ[K⸨X⸩] L) (ω : Ω[M⁄K]) :
    mapAlgHom φ (mk K M ω) =
      mk K L (KaehlerDifferential.mapSemilinear (φ.restrictScalars K) ω) := by
  have hω : ω ∈ Submodule.span M (Set.range (KaehlerDifferential.D K M)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨x, rfl⟩ := hx
    rw [← D_apply, mapAlgHom_D, KaehlerDifferential.mapSemilinear_D, D_apply,
      AlgHom.restrictScalars_apply]
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add _ _ _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | smul a _ _ hx =>
    rw [map_smul, mapAlgHom_smul, KaehlerDifferential.mapSemilinear_smul, map_smul,
      AlgHom.restrictScalars_apply, hx]

@[simp]
theorem mapAlgHom_id (ω : ContinuousKaehlerDifferential K L) :
    mapAlgHom (AlgHom.id K⸨X⸩ L) ω = ω :=
  (equivSelf K L).injective <| by rw [equivSelf_mapAlgHom, AlgHom.id_apply]

theorem mapAlgHom_comp (φ : M →ₐ[K⸨X⸩] L) (ψ : L →ₐ[K⸨X⸩] P)
    (ω : ContinuousKaehlerDifferential K M) :
    mapAlgHom (ψ.comp φ) ω = mapAlgHom ψ (mapAlgHom φ ω) :=
  (equivSelf K P).injective <| by
    rw [equivSelf_mapAlgHom, equivSelf_mapAlgHom, equivSelf_mapAlgHom, AlgHom.comp_apply]

theorem mapAlgHom_injective {φ : M →ₐ[K⸨X⸩] L} (hφ : Function.Injective φ) :
    Function.Injective (mapAlgHom (K := K) φ) := by
  intro ω η h
  apply (equivSelf K M).injective
  apply hφ
  rw [← equivSelf_mapAlgHom, ← equivSelf_mapAlgHom, h]

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- A `K⸨X⸩`-algebra isomorphism between formally étale extensions induces a semilinear equivalence
on their continuous one-forms. -/
noncomputable def equivAlgEquiv (e : M ≃ₐ[K⸨X⸩] L) :
    ContinuousKaehlerDifferential K M ≃ₛₗ[(e.toRingEquiv : M →+* L)]
      ContinuousKaehlerDifferential K L where
  toFun := mapAlgHom e.toAlgHom
  invFun := mapAlgHom e.symm.toAlgHom
  map_add' := map_add _
  map_smul' c ω := by
    rw [mapAlgHom_smul]
    rfl
  left_inv ω := by rw [← mapAlgHom_comp, AlgEquiv.symm_comp, mapAlgHom_id]
  right_inv ω := by rw [← mapAlgHom_comp, AlgEquiv.comp_symm, mapAlgHom_id]

/-- A `K⸨X⸩`-algebra isomorphism induces a `K⸨X⸩`-linear equivalence on continuous one-forms. -/
noncomputable def linearEquivAlgEquiv (e : M ≃ₐ[K⸨X⸩] L) :
    ContinuousKaehlerDifferential K M ≃ₗ[K⸨X⸩] ContinuousKaehlerDifferential K L :=
  LinearEquiv.ofLinearMap (linearMapAlgHom e.toAlgHom) (linearMapAlgHom e.symm.toAlgHom)
    (LinearMap.ext fun ω ↦ by
      rw [LinearMap.comp_apply, LinearMap.id_apply, linearMapAlgHom_apply, linearMapAlgHom_apply,
        ← mapAlgHom_comp, AlgEquiv.comp_symm, mapAlgHom_id])
    (LinearMap.ext fun ω ↦ by
      rw [LinearMap.comp_apply, LinearMap.id_apply, linearMapAlgHom_apply, linearMapAlgHom_apply,
        ← mapAlgHom_comp, AlgEquiv.symm_comp, mapAlgHom_id])

@[simp]
theorem equivAlgEquiv_apply (e : M ≃ₐ[K⸨X⸩] L) (ω : ContinuousKaehlerDifferential K M) :
    equivAlgEquiv e ω = mapAlgHom e.toAlgHom ω := (rfl)

@[simp]
theorem linearEquivAlgEquiv_apply (e : M ≃ₐ[K⸨X⸩] L) (ω : ContinuousKaehlerDifferential K M) :
    linearEquivAlgEquiv e ω = mapAlgHom e.toAlgHom ω := (rfl)

@[simp]
theorem equivAlgEquiv_symm_apply (e : M ≃ₐ[K⸨X⸩] L) (ω : ContinuousKaehlerDifferential K L) :
    (equivAlgEquiv (K := K) e).symm ω = mapAlgHom e.symm.toAlgHom ω := (rfl)

@[simp]
theorem linearEquivAlgEquiv_symm (e : M ≃ₐ[K⸨X⸩] L) :
    (linearEquivAlgEquiv (K := K) e).symm = linearEquivAlgEquiv e.symm := (rfl)

end ContinuousKaehlerDifferential

end Functoriality

/-! ### Module topology -/

namespace ContinuousKaehlerDifferential

section ExtensionTopology

variable (K : Type*) [Field K] (L : Type*) [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L] [TopologicalSpace L]

/-- Continuous one-forms of `L` carry the `L`-module topology. -/
noncomputable instance : TopologicalSpace (ContinuousKaehlerDifferential K L) :=
  moduleTopology L _

instance : IsModuleTopology L (ContinuousKaehlerDifferential K L) := ⟨rfl⟩

instance : IsTopologicalAddGroup (ContinuousKaehlerDifferential K L) :=
  IsModuleTopology.isTopologicalAddGroup L _

section Semiring

variable [IsTopologicalSemiring L]

/-- When `L` is a topological semiring, the rank-one coordinate `Ω¹_cont(L/K) ≃ L` (`x dt ↦ x`) is a
continuous `L`-linear equivalence. -/
noncomputable def continuousEquivSelf :
    ContinuousKaehlerDifferential K L ≃L[L] L :=
  (equivSelf K L).toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem coe_continuousEquivSelf :
    ⇑(continuousEquivSelf K L) = equivSelf K L := by
  simp [continuousEquivSelf]

@[simp]
theorem toLinearEquiv_continuousEquivSelf :
    (continuousEquivSelf K L).toLinearEquiv = equivSelf K L := by
  simp [continuousEquivSelf]

@[simp]
theorem continuousEquivSelf_symm_apply (x : L) :
    (continuousEquivSelf K L).symm x = (equivSelf K L).symm x := by
  simp [continuousEquivSelf]

instance [T2Space L] : T2Space (ContinuousKaehlerDifferential K L) :=
  (continuousEquivSelf K L).toHomeomorph.isEmbedding.t2Space

end Semiring

variable {K L} in
/-- When addition and `L`-scalar multiplication on `N` are continuous, the linear factorization of
`δ` through `Ω¹_cont(L/K)` is continuous for the `L`-module topology. -/
theorem continuous_lift {N : Type*} [AddCommGroup N] [Module L N] [Module K N]
    [IsScalarTower K L N] [Module K⸨X⸩ N] [IsScalarTower K⸨X⸩ L N] [IsScalarTower K K⸨X⸩ N]
    [TopologicalSpace N] [ContinuousAdd N] [ContinuousSMul L N] [ContinuousSMul K⸨X⸩ N] [T2Space N]
    (δ : Derivation K L N) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) :
    Continuous (lift δ hδ) :=
  IsModuleTopology.continuous_of_linearMap (lift δ hδ)

end ExtensionTopology

section BaseModuleTopology

variable (K : Type*) [Field K] (L : Type*) [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]
  [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L] [Module.Finite K⸨X⸩ L]

/-- When `L` is module-finite over `K⸨X⸩` and carries the `K⸨X⸩`-module topology, the `L`-module
topology on `Ω¹_cont(L/K)` agrees with its `K⸨X⸩`-module topology. -/
instance : IsModuleTopology K⸨X⸩ (ContinuousKaehlerDifferential K L) :=
  IsModuleTopology.restrictScalars K⸨X⸩ L _

/-- On a module-finite formally étale `K⸨X⸩`-algebra carrying the `K⸨X⸩`-module topology, the
extended formal derivative `D_L = d/dt : L → L` is continuous. -/
theorem _root_.TauCeti.LaurentSeries.Extension.continuous_derivation :
    Continuous (derivation K L) := by
  have : IsTopologicalRing L := IsModuleTopology.isTopologicalRing K⸨X⸩ L
  have hcomp : Continuous (Algebra.linearMap K⸨X⸩ L ∘ _root_.LaurentSeries.derivative K) :=
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap K⸨X⸩ L)).comp
      (_root_.LaurentSeries.continuous_derivative (K := K))
  exact Derivation.continuous_of_continuous_compAlgebraMap (A := K⸨X⸩)
    (hcomp.congr fun f ↦ by simp)

/-- The universal continuous derivation `d : L → Ω¹_cont(L/K)` is continuous for the `K⸨X⸩`-module
topology on `L`. -/
theorem continuous_D : Continuous (D K L) := by
  have : IsTopologicalRing L := IsModuleTopology.isTopologicalRing K⸨X⸩ L
  have h : (D K L : L → ContinuousKaehlerDifferential K L) =
      (continuousEquivSelf K L).symm ∘ derivation K L := by
    ext x
    simp [derivation_smul_D_algebraMap_single_one]
  rw [h]
  exact (continuousEquivSelf K L).symm.continuous.comp
    (Extension.continuous_derivation K L)

/-- Pullback `Ω¹_cont(K⸨X⸩/K) → Ω¹_cont(L/K)` is continuous. -/
theorem continuous_map : Continuous (map K L) :=
  IsModuleTopology.continuous_of_linearMap (map K L)

section TensorTopology

open scoped TauCeti.ModuleTopology

/-- With the `K⸨X⸩`-module topology on the tensor product, the scalar-extension isomorphism
`L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)` is a continuous `K⸨X⸩`-linear equivalence. -/
noncomputable def continuousTensorEquiv :
    L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K ≃L[K⸨X⸩]
      ContinuousKaehlerDifferential K L :=
  ((tensorEquiv K L).restrictScalars K⸨X⸩).toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem continuousTensorEquiv_apply (η : L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    continuousTensorEquiv K L η = tensorEquiv K L η := by
  simp [continuousTensorEquiv]

@[simp]
theorem continuousTensorEquiv_symm_apply (ω : ContinuousKaehlerDifferential K L) :
    (continuousTensorEquiv K L).symm ω = (tensorEquiv K L).symm ω := by
  simp [continuousTensorEquiv]

end TensorTopology

variable {K L}

/-- Pullback of continuous one-forms along `φ : M →ₐ[K⸨X⸩] L` is continuous for the `K⸨X⸩`-module
topologies. -/
theorem continuous_mapAlgHom {M : Type*} [CommRing M] [Algebra K⸨X⸩ M] [Algebra K M]
    [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M]
    [TopologicalSpace M] [IsModuleTopology K⸨X⸩ M] [Module.Finite K⸨X⸩ M]
    (φ : M →ₐ[K⸨X⸩] L) : Continuous (mapAlgHom (K := K) φ) :=
  IsModuleTopology.continuous_of_linearMap (linearMapAlgHom φ)

/-- A `K⸨X⸩`-algebra isomorphism lifts to a continuous `K⸨X⸩`-linear equivalence of continuous
one-forms. -/
noncomputable def continuousLinearEquivAlgEquiv {M : Type*} [CommRing M] [Algebra K⸨X⸩ M]
    [Algebra K M] [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M]
    [TopologicalSpace M] [IsModuleTopology K⸨X⸩ M] [Module.Finite K⸨X⸩ M]
    (e : M ≃ₐ[K⸨X⸩] L) :
    ContinuousKaehlerDifferential K M ≃L[K⸨X⸩] ContinuousKaehlerDifferential K L :=
  (linearEquivAlgEquiv e).toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem continuousLinearEquivAlgEquiv_apply {M : Type*} [CommRing M] [Algebra K⸨X⸩ M]
    [Algebra K M] [IsScalarTower K K⸨X⸩ M] [Algebra.FormallyEtale K⸨X⸩ M]
    [TopologicalSpace M] [IsModuleTopology K⸨X⸩ M] [Module.Finite K⸨X⸩ M]
    (e : M ≃ₐ[K⸨X⸩] L) (ω : ContinuousKaehlerDifferential K M) :
    continuousLinearEquivAlgEquiv e ω = mapAlgHom e.toAlgHom ω := by
  simp [continuousLinearEquivAlgEquiv]

/-! ### Universal property for continuous derivations on `L` -/

section UniversalContinuous

variable {N : Type*} [AddCommGroup N] [Module L N] [Module K N] [IsScalarTower K L N]
  [TopologicalSpace N] [ContinuousSMul L N]

/-- Every `L`-linear map out of `Ω¹_cont(L/K)` composes with `d` to a continuous `K`-derivation of
`L`, without requiring continuous addition or Hausdorffness on the target. -/
theorem continuous_compDer (ℓ : ContinuousKaehlerDifferential K L →ₗ[L] N) :
    Continuous (ℓ.compDer (D K L)) := by
  have h : (ℓ.compDer (D K L) : L → N) =
      fun x ↦ derivation K L x • ℓ (D K L (algebraMap K⸨X⸩ L (single 1 1))) := by
    ext x
    simp [← derivation_smul_D_algebraMap_single_one x]
  rw [h]
  exact (Extension.continuous_derivation K L).smul continuous_const

section Hausdorff

variable [Module K⸨X⸩ N] [IsScalarTower K⸨X⸩ L N] [IsScalarTower K K⸨X⸩ N] [T2Space N]

/-- A `K`-derivation `δ : L → N` into a Hausdorff module with continuous `L`-scalar multiplication
is continuous on `L` if and only if its restriction to `K⸨X⸩` is continuous (using `T2Space N` in
place of the `ContinuousAdd N` hypothesis of `Derivation.continuous_iff_continuous_compAlgebraMap`).
-/
theorem continuous_iff_continuous_compAlgebraMap (δ : Derivation K L N) :
    Continuous δ ↔ Continuous (δ.compAlgebraMap K⸨X⸩) := by
  have : ContinuousAdd L := IsModuleTopology.toContinuousAdd K⸨X⸩ L
  have : ContinuousSMul K⸨X⸩ L := IsModuleTopology.toContinuousSMul K⸨X⸩ L
  have : ContinuousSMul K⸨X⸩ N := IsScalarTower.continuousSMul L
  refine ⟨fun hδ ↦ hδ.comp (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap K⸨X⸩ L)),
    fun hδ ↦ ?_⟩
  exact ((Extension.continuous_derivation K L).smul continuous_const).congr fun x ↦
    (apply_eq_derivation_smul δ hδ x).symm

/-- **Universal property of `Ω¹_cont(L/K)` for continuous derivations.** A `K`-derivation
`δ : L → N` into a Hausdorff module with continuous `L`-scalar multiplication factors through `d`
if and only if `δ` is continuous on `L`. -/
theorem exists_compDer_eq_iff_continuous (δ : Derivation K L N) :
    (∃ ℓ : ContinuousKaehlerDifferential K L →ₗ[L] N, ℓ.compDer (D K L) = δ) ↔
      Continuous δ := by
  have : ContinuousSMul K⸨X⸩ L := IsModuleTopology.toContinuousSMul K⸨X⸩ L
  have : ContinuousSMul K⸨X⸩ N := IsScalarTower.continuousSMul L
  rw [exists_compDer_eq_iff, ← continuous_iff_continuous_compAlgebraMap]

/-- Every continuous `K`-derivation `δ : L → N` into a Hausdorff module with continuous `L`-scalar
multiplication factors uniquely through `d` by an `L`-linear map, which is continuous whenever
addition on `N` is continuous. -/
theorem existsUnique_compDer_eq_of_continuous (δ : Derivation K L N) (hδ : Continuous δ) :
    ∃! ℓ : ContinuousKaehlerDifferential K L →ₗ[L] N, ℓ.compDer (D K L) = δ := by
  have : ContinuousSMul K⸨X⸩ L := IsModuleTopology.toContinuousSMul K⸨X⸩ L
  have : ContinuousSMul K⸨X⸩ N := IsScalarTower.continuousSMul L
  exact existsUnique_compDer_eq δ ((continuous_iff_continuous_compAlgebraMap δ).mp hδ)

end Hausdorff

end UniversalContinuous

end BaseModuleTopology

end ContinuousKaehlerDifferential

end TauCeti.LaurentSeries.Extension
