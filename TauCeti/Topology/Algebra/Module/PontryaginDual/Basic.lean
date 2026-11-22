/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
import TauCeti.Topology.CompactOpen

/-!
# The compact-open topological dual of a module

For a commutative topological semiring `R` and topological `R`-modules `E` and `M`,
`TauCeti.ModulePontryaginDual R E M` is the `R`-module of continuous `R`-linear maps `M →L[R] E`
with the compact-open topology induced from `C(M, E)`. For discrete `M` this coincides with
pointwise convergence (`isClosedEmbedding_coe`); for compact `M` and discrete `E` it is discrete
(`instDiscreteTopology`). We provide contravariant (`map`, `congr`) and covariant (`mapCodomain`,
`congrCodomain`) functoriality and evaluation (`eval`, continuous when `M` is discrete via
`continuous_eval_of_discrete` or when `M` is compact and `E` is discrete via
`continuous_eval_of_compact`).

## References

* A. Brumer, *Pseudocompact algebras, profinite groups and class formations*, J. Algebra 4 (1966),
  §1.
* V. Paškūnas, *The image of Colmez's Montreal functor*, Publ. Math. IHÉS 118 (2013), §2.
-/

public section

open Filter Topology

namespace TauCeti

universe u v w w'

/-- The continuous `R`-linear dual `Hom_R^cont(M, E)` equipped with the compact-open topology
induced from `C(M, E)`. -/
structure ModulePontryaginDual (R : Type u) (E : Type v) (M : Type w)
    [Semiring R] [AddCommMonoid E] [Module R E] [TopologicalSpace E]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M] where
  /-- The underlying continuous `R`-linear map. -/
  toContinuousLinearMap : M →L[R] E

namespace ModulePontryaginDual

section Basic

variable {R : Type u} {E : Type v} {M : Type w}
  [Semiring R] [AddCommMonoid E] [Module R E] [TopologicalSpace E]
  [AddCommMonoid M] [Module R M] [TopologicalSpace M]

instance : FunLike (ModulePontryaginDual R E M) M E where
  coe φ := φ.toContinuousLinearMap
  coe_injective := fun ⟨_⟩ ⟨_⟩ h ↦ congrArg mk (DFunLike.coe_injective h)

instance : ContinuousLinearMapClass (ModulePontryaginDual R E M) R M E where
  map_add φ := map_add φ.toContinuousLinearMap
  map_smulₛₗ φ := map_smul φ.toContinuousLinearMap
  map_continuous φ := φ.toContinuousLinearMap.continuous

/-- Extensionality for elements of `ModulePontryaginDual R E M`. -/
@[ext] theorem ext {φ ψ : ModulePontryaginDual R E M} (h : ∀ x : M, φ x = ψ x) : φ = ψ :=
  DFunLike.ext φ ψ h

@[simp] theorem coe_mk (f : M →L[R] E) : ⇑(mk f : ModulePontryaginDual R E M) = ⇑f := (rfl)
@[simp] theorem mk_apply (f : M →L[R] E) (x : M) :
    (mk f : ModulePontryaginDual R E M) x = f x := (rfl)
@[simp] theorem toContinuousLinearMap_apply (φ : ModulePontryaginDual R E M) (x : M) :
    φ.toContinuousLinearMap x = φ x := (rfl)
@[simp] theorem mk_toContinuousLinearMap (φ : ModulePontryaginDual R E M) :
    mk φ.toContinuousLinearMap = φ := (rfl)

/-- The underlying continuous map `M → E`. -/
def toContinuousMap (φ : ModulePontryaginDual R E M) : C(M, E) := ⟨φ, map_continuous φ⟩

@[simp] theorem coe_toContinuousMap (φ : ModulePontryaginDual R E M) :
    ⇑φ.toContinuousMap = ⇑φ := (rfl)
@[simp] theorem toContinuousMap_apply (φ : ModulePontryaginDual R E M) (x : M) :
    φ.toContinuousMap x = φ x := (rfl)

theorem toContinuousMap_injective :
    Function.Injective (toContinuousMap : ModulePontryaginDual R E M → C(M, E)) :=
  fun _ _ h ↦ ext fun x ↦ DFunLike.congr_fun h x

/-- The compact-open topology on `ModulePontryaginDual R E M`, induced from `C(M, E)`. -/
instance : TopologicalSpace (ModulePontryaginDual R E M) :=
  TopologicalSpace.induced toContinuousMap ContinuousMap.compactOpen

theorem isInducing_toContinuousMap :
    IsInducing (toContinuousMap : ModulePontryaginDual R E M → C(M, E)) := ⟨rfl⟩
theorem isEmbedding_toContinuousMap :
    IsEmbedding (toContinuousMap : ModulePontryaginDual R E M → C(M, E)) :=
  ⟨isInducing_toContinuousMap, toContinuousMap_injective⟩
theorem continuous_toContinuousMap :
    Continuous (toContinuousMap : ModulePontryaginDual R E M → C(M, E)) :=
  isInducing_toContinuousMap.continuous

instance : ContinuousEvalConst (ModulePontryaginDual R E M) M E :=
  .of_continuous_forget continuous_toContinuousMap
instance [T2Space E] : T2Space (ModulePontryaginDual R E M) :=
  isEmbedding_toContinuousMap.t2Space

theorem range_toContinuousMap :
    Set.range (toContinuousMap : ModulePontryaginDual R E M → C(M, E)) =
      {f : C(M, E) | (∀ x y : M, f (x + y) = f x + f y) ∧
        ∀ (r : R) (x : M), f (r • x) = r • f x} := by
  ext f
  refine ⟨fun ⟨φ, hφ⟩ ↦ hφ ▸ ⟨fun x y ↦ map_add φ x y, fun r x ↦ map_smul φ r x⟩,
    fun ⟨hadd, hsmul⟩ ↦
      ⟨⟨{ toFun := f, map_add' := hadd, map_smul' := hsmul, cont := f.continuous }⟩,
        ContinuousMap.ext fun _ ↦ rfl⟩⟩

/-- The image of `ModulePontryaginDual R E M` in `C(M, E)` is closed when `E` is Hausdorff with
continuous addition and scalar action. -/
theorem isClosedEmbedding_toContinuousMap [ContinuousAdd E] [ContinuousConstSMul R E] [T2Space E] :
    IsClosedEmbedding (toContinuousMap : ModulePontryaginDual R E M → C(M, E)) where
  toIsEmbedding := isEmbedding_toContinuousMap
  isClosed_range := by
    simp only [range_toContinuousMap, Set.ofPred_and, Set.ofPred_forall]
    refine .inter
      (isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
        isClosed_eq (continuous_eval_const (x + y))
          ((continuous_eval_const x).add (continuous_eval_const y)))
      (isClosed_iInter fun r ↦ isClosed_iInter fun x ↦
        isClosed_eq (continuous_eval_const (r • x)) ((continuous_eval_const x).const_smul r))

/-- For discrete `M`, the compact-open topology coincides with pointwise convergence on `M → E`. -/
theorem isEmbedding_coe [DiscreteTopology M] :
    IsEmbedding ((⇑) : ModulePontryaginDual R E M → M → E) :=
  ContinuousMap.isHomeomorph_coe.isEmbedding.comp isEmbedding_toContinuousMap

/-- For discrete `M`, `ModulePontryaginDual R E M` embeds as a closed subspace of `M → E`. -/
theorem isClosedEmbedding_coe [DiscreteTopology M] [ContinuousAdd E] [ContinuousConstSMul R E]
    [T2Space E] : IsClosedEmbedding ((⇑) : ModulePontryaginDual R E M → M → E) :=
  ContinuousMap.isHomeomorph_coe.isClosedEmbedding.comp isClosedEmbedding_toContinuousMap

/-- Universal property of the pointwise topology on `ModulePontryaginDual R E M` for discrete `M`:
a map into it is continuous iff evaluation at every element of `M` is continuous. -/
theorem continuous_of_continuous_eval [DiscreteTopology M] {X : Type*} [TopologicalSpace X]
    {f : X → ModulePontryaginDual R E M} (h : ∀ x : M, Continuous fun a : X ↦ f a x) :
    Continuous f := isEmbedding_coe.continuous_iff.mpr (continuous_pi h)

end Basic

section AddCommGroup

variable {R : Type u} {E : Type v} {M : Type w}
  [Semiring R] [AddCommGroup E] [Module R E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]

instance : AddCommGroup (ModulePontryaginDual R E M) :=
  letI : Zero (ModulePontryaginDual R E M) := ⟨⟨0⟩⟩
  letI : Add (ModulePontryaginDual R E M) :=
    ⟨fun φ ψ ↦ ⟨φ.toContinuousLinearMap + ψ.toContinuousLinearMap⟩⟩
  letI : Neg (ModulePontryaginDual R E M) :=
    ⟨fun φ ↦ ⟨⟨-φ.toContinuousLinearMap.toLinearMap, (map_continuous φ).neg⟩⟩⟩
  letI : Sub (ModulePontryaginDual R E M) :=
    ⟨fun φ ψ ↦ ⟨⟨φ.toContinuousLinearMap.toLinearMap - ψ.toContinuousLinearMap.toLinearMap,
      (map_continuous φ).sub (map_continuous ψ)⟩⟩⟩
  letI : SMul ℕ (ModulePontryaginDual R E M) :=
    ⟨fun n φ ↦ ⟨n • φ.toContinuousLinearMap⟩⟩
  letI : SMul ℤ (ModulePontryaginDual R E M) :=
    ⟨fun n φ ↦ ⟨⟨n • φ.toContinuousLinearMap.toLinearMap,
      (continuous_const_smul n).comp (map_continuous φ)⟩⟩⟩
  DFunLike.coe_injective.addCommGroup (⇑) rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[simp] theorem zero_apply (x : M) : (0 : ModulePontryaginDual R E M) x = 0 := (rfl)
@[simp] theorem add_apply (φ ψ : ModulePontryaginDual R E M) (x : M) :
    (φ + ψ) x = φ x + ψ x := (rfl)
@[simp] theorem neg_apply (φ : ModulePontryaginDual R E M) (x : M) : (-φ) x = -φ x := (rfl)
@[simp] theorem sub_apply (φ ψ : ModulePontryaginDual R E M) (x : M) :
    (φ - ψ) x = φ x - ψ x := (rfl)

instance : IsTopologicalAddGroup (ModulePontryaginDual R E M) where
  continuous_add := isInducing_toContinuousMap.continuous_iff.mpr <|
    (continuous_add.comp (continuous_toContinuousMap.prodMap continuous_toContinuousMap)).congr
      fun _ ↦ ContinuousMap.ext fun _ ↦ rfl
  continuous_neg := isInducing_toContinuousMap.continuous_iff.mpr <|
    (continuous_neg.comp continuous_toContinuousMap).congr fun _ ↦ ContinuousMap.ext fun _ ↦ rfl

/-- When `M` is compact and `E` is discrete, `ModulePontryaginDual R E M` is discrete. -/
instance instDiscreteTopology [CompactSpace M] [DiscreteTopology E] :
    DiscreteTopology (ModulePontryaginDual R E M) :=
  .of_continuous_injective continuous_toContinuousMap toContinuousMap_injective

end AddCommGroup

section SMul

variable {R : Type u} {S : Type*} {E : Type v} {M : Type w}
  [Semiring R] [Semiring S] [AddCommGroup E] [Module R E] [Module S E] [SMulCommClass R S E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul S E]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]

instance : Module S (ModulePontryaginDual R E M) :=
  letI : SMul S (ModulePontryaginDual R E M) := ⟨fun s φ ↦ ⟨s • φ.toContinuousLinearMap⟩⟩
  DFunLike.coe_injective.module S
    { toFun := (⇑), map_zero' := rfl, map_add' := fun _ _ ↦ rfl } (fun _ _ ↦ rfl)

@[simp] theorem smul_apply (s : S) (φ : ModulePontryaginDual R E M) (x : M) :
    (s • φ) x = s • φ x := (rfl)

instance [TopologicalSpace S] [ContinuousSMul S E] :
    ContinuousSMul S (ModulePontryaginDual R E M) where
  continuous_smul := isInducing_toContinuousMap.continuous_iff.mpr <|
    (continuous_smul.comp (continuous_id.prodMap continuous_toContinuousMap)).congr
      fun _ ↦ ContinuousMap.ext fun _ ↦ rfl

instance {S₁ S₂ : Type*} [Semiring S₁] [Semiring S₂] [SMul S₁ S₂]
    [Module S₁ E] [Module S₂ E] [SMulCommClass R S₁ E] [SMulCommClass R S₂ E]
    [ContinuousConstSMul S₁ E] [ContinuousConstSMul S₂ E] [IsScalarTower S₁ S₂ E] :
    IsScalarTower S₁ S₂ (ModulePontryaginDual R E M) where
  smul_assoc _ _ _ := ext fun _ ↦ smul_assoc _ _ _

end SMul

section Module

variable {R : Type u} {E : Type v} {M : Type w}
  [CommSemiring R] [AddCommGroup E] [Module R E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousConstSMul R E] [AddCommGroup M] [Module R M] [TopologicalSpace M]

variable (R E M) in
/-- The underlying `R`-module of `ModulePontryaginDual R E M` is `M →L[R] E`. -/
def equivContinuousLinearMap : ModulePontryaginDual R E M ≃ₗ[R] (M →L[R] E) :=
  { toFun := toContinuousLinearMap, invFun := mk, left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl,
    map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
@[simp] theorem equivContinuousLinearMap_apply (φ : ModulePontryaginDual R E M) (x : M) :
    equivContinuousLinearMap R E M φ x = φ x := (rfl)
@[simp] theorem equivContinuousLinearMap_symm_apply (f : M →L[R] E) (x : M) :
    (equivContinuousLinearMap R E M).symm f x = f x := (rfl)

variable (R E M) in
/-- For discrete `M`, `ModulePontryaginDual R E M` is linearly equivalent to `M →ₗ[R] E`. -/
def equivLinearMap [DiscreteTopology M] : ModulePontryaginDual R E M ≃ₗ[R] (M →ₗ[R] E) :=
  { toFun := fun φ ↦ φ.toContinuousLinearMap.toLinearMap,
    invFun := fun f ↦ ⟨⟨f, continuous_of_discreteTopology⟩⟩,
    left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl,
    map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
@[simp] theorem equivLinearMap_apply [DiscreteTopology M] (φ : ModulePontryaginDual R E M) (x : M) :
    equivLinearMap R E M φ x = φ x := (rfl)
@[simp] theorem equivLinearMap_symm_apply [DiscreteTopology M] (f : M →ₗ[R] E) (x : M) :
    (equivLinearMap R E M).symm f x = f x := (rfl)

section Domain

variable {N : Type w'} [AddCommGroup N] [Module R N] [TopologicalSpace N]

/-- Contravariant functoriality: precomposition by `f : M →L[R] N` is continuous. -/
def map (f : M →L[R] N) : ModulePontryaginDual R E N →L[R] ModulePontryaginDual R E M where
  toFun ψ := ⟨ψ.toContinuousLinearMap.comp f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := isInducing_toContinuousMap.continuous_iff.mpr <|
    (ContinuousMap.continuous_precomp ⟨f, f.continuous⟩).comp continuous_toContinuousMap
@[simp] theorem map_apply (f : M →L[R] N) (ψ : ModulePontryaginDual R E N) (x : M) :
    map (E := E) f ψ x = ψ (f x) := (rfl)
@[simp] theorem map_id :
    map (E := E) (ContinuousLinearMap.id R M) = ContinuousLinearMap.id R _ := by ext; rfl
@[simp] theorem map_comp {P : Type*} [AddCommGroup P] [Module R P] [TopologicalSpace P]
    (g : N →L[R] P) (f : M →L[R] N) :
    map (E := E) (g.comp f) = (map (E := E) f).comp (map (E := E) g) := by ext; rfl

/-- A continuous linear equivalence dualizes to one in the opposite direction. -/
def congr (e : M ≃L[R] N) : ModulePontryaginDual R E N ≃L[R] ModulePontryaginDual R E M :=
  let f := map (E := E) e.toContinuousLinearMap; let g := map (E := E) e.symm.toContinuousLinearMap
  { toFun := f, invFun := g, left_inv := fun _ ↦ ext fun _ ↦ by simp [f, g],
    right_inv := fun _ ↦ ext fun _ ↦ by simp [f, g], map_add' := map_add f,
    map_smul' := map_smul f, continuous_toFun := f.continuous, continuous_invFun := g.continuous }
@[simp] theorem congr_apply (e : M ≃L[R] N) (ψ : ModulePontryaginDual R E N) (x : M) :
    congr (E := E) e ψ x = ψ (e x) := (rfl)
@[simp] theorem congr_symm (e : M ≃L[R] N) :
    (congr (E := E) e).symm = congr (E := E) e.symm := (rfl)
@[simp] theorem congr_refl :
    congr (E := E) (ContinuousLinearEquiv.refl R M) = ContinuousLinearEquiv.refl R _ := by ext; rfl
@[simp] theorem congr_trans {P : Type*} [AddCommGroup P] [Module R P] [TopologicalSpace P]
    (e : M ≃L[R] N) (e' : N ≃L[R] P) :
    congr (E := E) (e.trans e') = (congr (E := E) e').trans (congr (E := E) e) := by ext; rfl

end Domain

section Codomain

variable {F : Type*} [AddCommGroup F] [Module R F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousConstSMul R F]

/-- Covariant functoriality in the dualizing module: postcomposition by `f : E →L[R] F`. -/
def mapCodomain (f : E →L[R] F) : ModulePontryaginDual R E M →L[R] ModulePontryaginDual R F M where
  toFun φ := ⟨f.comp φ.toContinuousLinearMap⟩
  map_add' _ _ := ext fun _ ↦ map_add f _ _
  map_smul' _ _ := ext fun _ ↦ map_smul f _ _
  cont := isInducing_toContinuousMap.continuous_iff.mpr <|
    (ContinuousMap.continuous_postcomp ⟨f, f.continuous⟩).comp continuous_toContinuousMap
@[simp] theorem mapCodomain_apply (f : E →L[R] F) (φ : ModulePontryaginDual R E M) (x : M) :
    mapCodomain (M := M) f φ x = f (φ x) := (rfl)
@[simp] theorem mapCodomain_id :
    mapCodomain (M := M) (ContinuousLinearMap.id R E) = ContinuousLinearMap.id R _ := by ext; rfl
@[simp] theorem mapCodomain_comp {G : Type*} [AddCommGroup G] [Module R G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousConstSMul R G] (g : F →L[R] G) (f : E →L[R] F) :
    mapCodomain (M := M) (g.comp f) =
      (mapCodomain (M := M) g).comp (mapCodomain (M := M) f) := by ext; rfl

/-- A continuous linear equivalence of dualizing modules induces one on Pontryagin duals. -/
def congrCodomain (e : E ≃L[R] F) :
    ModulePontryaginDual R E M ≃L[R] ModulePontryaginDual R F M :=
  let f := mapCodomain (M := M) e.toContinuousLinearMap
  let g := mapCodomain (M := M) e.symm.toContinuousLinearMap
  { toFun := f, invFun := g, left_inv := fun _ ↦ ext fun _ ↦ by simp [f, g],
    right_inv := fun _ ↦ ext fun _ ↦ by simp [f, g], map_add' := map_add f,
    map_smul' := map_smul f, continuous_toFun := f.continuous, continuous_invFun := g.continuous }
@[simp] theorem congrCodomain_apply (e : E ≃L[R] F) (φ : ModulePontryaginDual R E M) (x : M) :
    congrCodomain (M := M) e φ x = e (φ x) := (rfl)
@[simp] theorem congrCodomain_symm (e : E ≃L[R] F) :
    (congrCodomain (M := M) e).symm = congrCodomain (M := M) e.symm := (rfl)
@[simp] theorem congrCodomain_refl :
    congrCodomain (M := M) (ContinuousLinearEquiv.refl R E) = .refl R _ := by ext; rfl
@[simp] theorem congrCodomain_trans {G : Type*} [AddCommGroup G] [Module R G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousConstSMul R G] (e : E ≃L[R] F) (e' : F ≃L[R] G) :
    congrCodomain (M := M) (e.trans e') =
      (congrCodomain (M := M) e).trans (congrCodomain (M := M) e') := by ext; rfl

end Codomain

variable (R E M) in
/-- Evaluation into the double dual, sending `x : M` to the continuous functional `φ ↦ φ x`. -/
def eval : M →ₗ[R] ModulePontryaginDual R E (ModulePontryaginDual R E M) where
  toFun x := ⟨{ toFun := (· x), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl,
                cont := continuous_eval_const x }⟩
  map_add' _ _ := ext fun φ ↦ map_add φ _ _
  map_smul' _ _ := ext fun φ ↦ map_smul φ _ _
@[simp] theorem eval_apply (x : M) (φ : ModulePontryaginDual R E M) : eval R E M x φ = φ x := (rfl)

/-- Naturality of evaluation with respect to continuous linear maps. -/
theorem map_map_eval {N : Type w'} [AddCommGroup N] [Module R N] [TopologicalSpace N]
    (f : M →L[R] N) (x : M) :
    map (E := E) (map (E := E) f) (eval R E M x) = eval R E N (f x) := ext fun _ ↦ rfl

/-- Evaluation into the double dual is continuous when `M` is discrete. -/
theorem continuous_eval_of_discrete [DiscreteTopology M] : Continuous (eval R E M) :=
  continuous_of_discreteTopology

/-- Evaluation into the double dual is continuous when `M` is compact and `E` is discrete. -/
theorem continuous_eval_of_compact [CompactSpace M] [DiscreteTopology E] :
    Continuous (eval R E M) := continuous_of_continuous_eval fun φ ↦ map_continuous φ

end Module

end ModulePontryaginDual

end TauCeti
