/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.Completion
public import TauCeti.Topology.Algebra.Nonarchimedean.Lattice
public import TauCeti.Topology.Algebra.UniformMulAction

/-!
# The completed tensor product of topological modules

Let `A` be a commutative topological ring and `V`, `W` topological `A`-modules. The *tensor
topology* `TauCeti.Huber.banachTensorTopology A V W` is the finest nonarchimedean additive group
topology on `V ⊗[A] W` for which the action of `A` and the map `(v, w) ↦ v ⊗ w` are continuous: the
infimum, in Mathlib's order on topologies, of all such topologies (the indiscrete topology is one of
them). The *completed tensor product* `V ⊗̂_A W` is the separated completion
`TauCeti.Huber.BanachModule.CompletedTensor A V W` of `V ⊗[A] W` for the additive uniformity of
this topology.

No chosen lattice enters the definition, and no hypothesis is placed on `A`, `V` or `W`. For
Banach modules with lattices `V₀`, `W₀` over a complete Tate ring, Kedlaya–Liu describe the
completed tensor product by the neighbourhoods `ϖⁿ·(V₀ ⊗ W₀)` or by the product seminorm; that
description is not proved here. What the definition gives directly is the universal property:

* a linear map out of `V ⊗[A] W` into a nonarchimedean topological `A`-module is continuous for the
  tensor topology exactly when its composite with `(v, w) ↦ v ⊗ w` is continuous
  (`TauCeti.Huber.continuous_banachTensorTopology_iff`), because the topology induced by such a map
  is one of those the infimum runs over;
* consequently every continuous `A`-bilinear map `β : V × W → M` into a complete Hausdorff
  nonarchimedean topological `A`-module factors uniquely through a continuous `A`-linear map
  `V ⊗̂_A W → M` (`TauCeti.Huber.BanachModule.CompletedTensor.lift`, `lift_tmul`, `ext`).

From the universal property, continuous linear maps `f : V → V'`, `g : W → W'` induce
`f ⊗̂ g : V ⊗̂_A W → V' ⊗̂_A W'` (`TauCeti.Huber.BanachModule.CompletedTensor.map`), functorially.
For a complete Hausdorff nonarchimedean topological `A`-module `M` with continuous action,
`A ⊗̂_A M ≃ M` (`TauCeti.Huber.BanachModule.CompletedTensor.lid`), and for a finite projective
`A`-module `P` with its natural topology no completion is needed: the canonical map
`P ⊗[A] M → P ⊗̂_A M` is an isomorphism
(`TauCeti.Huber.BanachModule.CompletedTensor.finiteProjectiveEquiv`), so completed tensor
products with a finite projective factor can be computed with the algebraic tensor product.

## Main definitions

* `TauCeti.Huber.banachTensorTopology A V W`: the tensor topology on `V ⊗[A] W`.
* `TauCeti.Huber.banachTensorUniformSpace A V W`: its additive uniformity.
* `TauCeti.Huber.BanachModule.CompletedTensor A V W`: the completed tensor product `V ⊗̂_A W`.
* `TauCeti.Huber.BanachModule.CompletedTensor.equivCompletion`: the continuous `A`-linear
  identification of `V ⊗̂_A W` with Mathlib's `UniformSpace.Completion (V ⊗[A] W)`.
* `TauCeti.Huber.BanachModule.CompletedTensor.toCompletion`: the map `V ⊗[A] W → V ⊗̂_A W`.
* `TauCeti.Huber.BanachModule.CompletedTensor.tmul`: the bilinear map `(v, w) ↦ v ⊗ w`.
* `TauCeti.Huber.BanachModule.CompletedTensor.lift`: the continuous linear map `V ⊗̂_A W → M`
  induced by a continuous bilinear map.
* `TauCeti.Huber.BanachModule.CompletedTensor.map`: the completed tensor product of two continuous
  linear maps.
* `TauCeti.Huber.BanachModule.CompletedTensor.lid`: the unit isomorphism `A ⊗̂_A M ≃ M`.
* `TauCeti.Huber.BanachModule.CompletedTensor.finiteProjectiveEquiv`: the isomorphism
  `P ⊗[A] M ≃ P ⊗̂_A M` for a finite projective `A`-module `P`.

## Main results

* `TauCeti.Huber.banachTensorTopology_le`: the tensor topology is finer than every nonarchimedean
  additive group topology making the action and `(v, w) ↦ v ⊗ w` continuous, and
  `nonarchimedeanAddGroup_banachTensorTopology`, `continuousSMul_banachTensorTopology` and
  `continuous_tmul_banachTensorTopology` show that it is one of them.
* `TauCeti.Huber.continuous_banachTensorTopology_iff`: continuity of linear maps out of
  `V ⊗[A] W`.
* `TauCeti.Huber.BanachModule.CompletedTensor.continuous_tmul`: `(v, w) ↦ v ⊗ w` is continuous,
  and `dense_span_range_tmul`: the elementary tensors span a dense submodule.
* `TauCeti.Huber.BanachModule.CompletedTensor.lift_tmul` and `ext`: the universal property.
* `TauCeti.Huber.BanachModule.CompletedTensor.map_tmul`, `map_id`, `map_comp`: functoriality.
* `TauCeti.Huber.BanachModule.CompletedTensor.prodLeft`: completed tensoring in the first
  variable preserves binary products, with component formulas `prodLeft_apply` and
  `prodLeft_symm_apply`.
* `TauCeti.Huber.BanachModule.CompletedTensor.lid_tmul`: the unit isomorphism sends `a ⊗ m` to
  `a • m`.
* `TauCeti.Huber.BanachModule.CompletedTensor.toCompletion_bijective_of_finite_projective`:
  tensoring with a finite projective module needs no completion.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  Definitions 2.1.10 and 2.2.7, and Lemma 2.2.12(a).
-/

public section

open TensorProduct UniformSpace Topology

namespace TauCeti.Huber

section Topology

variable (A : Type*) [CommRing A] [TopologicalSpace A]
  (V : Type*) [AddCommGroup V] [Module A V] [TopologicalSpace V]
  (W : Type*) [AddCommGroup W] [Module A W] [TopologicalSpace W]

/-- **The tensor topology** on `V ⊗[A] W`: the finest nonarchimedean additive group topology for
which the action of `A` and the map `(v, w) ↦ v ⊗ w` are continuous. It is the infimum, in
Mathlib's order on topologies, of all topologies with these three properties; the indiscrete
topology is one of them, and the infimum is one of them too
(`nonarchimedeanAddGroup_banachTensorTopology`, `continuousSMul_banachTensorTopology`,
`continuous_tmul_banachTensorTopology`). -/
@[instance_reducible] noncomputable def banachTensorTopology : TopologicalSpace (V ⊗[A] W) :=
  sInf {t | @NonarchimedeanAddGroup (V ⊗[A] W) _ t ∧ @ContinuousSMul A (V ⊗[A] W) _ _ t ∧
    Continuous[_, t] fun p : V × W ↦ p.1 ⊗ₜ[A] p.2}

variable {A V W} in
/-- The tensor topology is finer than every nonarchimedean additive group topology on `V ⊗[A] W`
for which the action of `A` and `(v, w) ↦ v ⊗ w` are continuous. -/
theorem banachTensorTopology_le {t : TopologicalSpace (V ⊗[A] W)}
    (h₁ : @NonarchimedeanAddGroup (V ⊗[A] W) _ t) (h₂ : @ContinuousSMul A (V ⊗[A] W) _ _ t)
    (h₃ : Continuous[_, t] fun p : V × W ↦ p.1 ⊗ₜ[A] p.2) : banachTensorTopology A V W ≤ t :=
  sInf_le ⟨h₁, h₂, h₃⟩

/-- The tensor topology is a nonarchimedean additive group topology. -/
theorem nonarchimedeanAddGroup_banachTensorTopology :
    @NonarchimedeanAddGroup (V ⊗[A] W) _ (banachTensorTopology A V W) :=
  nonarchimedeanAddGroup_sInf fun _ ht ↦ ht.1

/-- The action of `A` on `V ⊗[A] W` is continuous for the tensor topology. -/
theorem continuousSMul_banachTensorTopology :
    @ContinuousSMul A (V ⊗[A] W) _ _ (banachTensorTopology A V W) :=
  continuousSMul_sInf fun _ ht ↦ ht.2.1

/-- The map `(v, w) ↦ v ⊗ w` is continuous for the tensor topology. -/
theorem continuous_tmul_banachTensorTopology :
    Continuous[_, banachTensorTopology A V W] fun p : V × W ↦ p.1 ⊗ₜ[A] p.2 :=
  continuous_sInf_rng.mpr fun _ ht ↦ ht.2.2

variable {A V W} in
/-- **Continuity of linear maps out of the tensor topology.** A linear map from `V ⊗[A] W` to a
nonarchimedean topological `A`-module with continuous action is continuous for the tensor topology
exactly when its composite with `(v, w) ↦ v ⊗ w` is continuous. -/
theorem continuous_banachTensorTopology_iff {M : Type*} [AddCommGroup M] [Module A M]
    [TopologicalSpace M] [NonarchimedeanAddGroup M] [ContinuousSMul A M]
    (f : V ⊗[A] W →ₗ[A] M) :
    Continuous[banachTensorTopology A V W, _] f ↔
      Continuous fun p : V × W ↦ f (p.1 ⊗ₜ[A] p.2) := by
  let := banachTensorTopology A V W
  refine ⟨fun hf ↦ hf.comp (continuous_tmul_banachTensorTopology A V W), fun hf ↦ ?_⟩
  -- the topology induced by `f` is one of those the infimum runs over
  refine continuous_iff_le_induced.mpr (banachTensorTopology_le
    (nonarchimedeanAddGroup_induced f) (continuousSMul_induced f) ?_)
  exact continuous_induced_rng.mpr hf

end Topology

section Uniformity

variable (A : Type*) [CommRing A] [TopologicalSpace A]
  (V : Type*) [AddCommGroup V] [Module A V] [TopologicalSpace V]
  (W : Type*) [AddCommGroup W] [Module A W] [TopologicalSpace W]

/-- The additive uniformity of the tensor topology on `V ⊗[A] W`. -/
@[instance_reducible] noncomputable def banachTensorUniformSpace : UniformSpace (V ⊗[A] W) :=
  @IsTopologicalAddGroup.rightUniformSpace _ _ (banachTensorTopology A V W)
    (nonarchimedeanAddGroup_banachTensorTopology A V W).toIsTopologicalAddGroup

/-- The uniformity of the tensor topology is that of a uniform additive group. -/
theorem isUniformAddGroup_banachTensorUniformSpace :
    @IsUniformAddGroup (V ⊗[A] W) (banachTensorUniformSpace A V W) _ :=
  @isUniformAddGroup_of_addCommGroup _ _ (banachTensorTopology A V W)
    (nonarchimedeanAddGroup_banachTensorTopology A V W).toIsTopologicalAddGroup

/-- The topology of `banachTensorUniformSpace A V W` is the tensor topology. -/
theorem banachTensorUniformSpace_toTopologicalSpace :
    (banachTensorUniformSpace A V W).toTopologicalSpace = banachTensorTopology A V W :=
  (rfl)

end Uniformity

namespace BanachModule

variable (A : Type*) [CommRing A] [TopologicalSpace A]
  (V : Type*) [AddCommGroup V] [Module A V] [TopologicalSpace V]
  (W : Type*) [AddCommGroup W] [Module A W] [TopologicalSpace W]

/-- The uniformity of the tensor topology, registered locally on the algebraic tensor product. -/
noncomputable local instance tensorUniformSpace : UniformSpace (V ⊗[A] W) :=
  banachTensorUniformSpace A V W

local instance tensorUniformAddGroup : IsUniformAddGroup (V ⊗[A] W) :=
  isUniformAddGroup_banachTensorUniformSpace A V W

local instance tensorNonarchimedeanAddGroup : NonarchimedeanAddGroup (V ⊗[A] W) :=
  nonarchimedeanAddGroup_banachTensorTopology A V W

local instance tensorContinuousSMul : ContinuousSMul A (V ⊗[A] W) :=
  continuousSMul_banachTensorTopology A V W

local instance tensorUniformContinuousConstSMul : UniformContinuousConstSMul A (V ⊗[A] W) :=
  uniformContinuousConstSMul_of_continuousConstSMul A (V ⊗[A] W)

/-- **The completed tensor product** `V ⊗̂_A W`: the separated completion of `V ⊗[A] W` for the
additive uniformity of the tensor topology `banachTensorTopology A V W`. -/
def CompletedTensor := Completion (V ⊗[A] W)

namespace CompletedTensor

noncomputable instance : AddCommGroup (CompletedTensor A V W) :=
  inferInstanceAs (AddCommGroup (Completion (V ⊗[A] W)))

noncomputable instance : Module A (CompletedTensor A V W) :=
  inferInstanceAs (Module A (Completion (V ⊗[A] W)))

noncomputable instance : UniformSpace (CompletedTensor A V W) :=
  inferInstanceAs (UniformSpace (Completion (V ⊗[A] W)))

instance isUniformAddGroup : IsUniformAddGroup (CompletedTensor A V W) :=
  inferInstanceAs (IsUniformAddGroup (Completion (V ⊗[A] W)))

instance : NonarchimedeanAddGroup (CompletedTensor A V W) :=
  inferInstanceAs (NonarchimedeanAddGroup (Completion (V ⊗[A] W)))

instance : CompleteSpace (CompletedTensor A V W) :=
  inferInstanceAs (CompleteSpace (Completion (V ⊗[A] W)))

instance : T2Space (CompletedTensor A V W) :=
  inferInstanceAs (T2Space (Completion (V ⊗[A] W)))

instance : UniformContinuousConstSMul A (CompletedTensor A V W) :=
  inferInstanceAs (UniformContinuousConstSMul A (Completion (V ⊗[A] W)))

/-- The action of `A` on `V ⊗̂_A W` is continuous. -/
instance continuousSMul [IsTopologicalRing A] : ContinuousSMul A (CompletedTensor A V W) :=
  inferInstanceAs (ContinuousSMul A (Completion (V ⊗[A] W)))

/-- The canonical map `V ⊗[A] W → V ⊗̂_A W` into the completion. -/
noncomputable def toCompletion : V ⊗[A] W →ₗ[A] CompletedTensor A V W :=
  (Completion.toComplL : V ⊗[A] W →L[A] Completion (V ⊗[A] W)).toLinearMap

/-- The identification of `V ⊗̂_A W` with Mathlib's `UniformSpace.Completion (V ⊗[A] W)` for the
uniformity `banachTensorUniformSpace A V W`, as a continuous `A`-linear equivalence. -/
noncomputable def equivCompletion :
    CompletedTensor A V W ≃L[A] @Completion (V ⊗[A] W) (banachTensorUniformSpace A V W) :=
  ContinuousLinearEquiv.refl A _

/-- Under `equivCompletion`, `toCompletion` is Mathlib's canonical map `Completion.coe'`. -/
@[simp]
theorem equivCompletion_toCompletion (x : V ⊗[A] W) :
    equivCompletion A V W (toCompletion A V W x) =
      @Completion.coe' _ (banachTensorUniformSpace A V W) x :=
  (rfl)

/-- The map into the completion is continuous for the tensor topology. -/
theorem continuous_toCompletion :
    Continuous[banachTensorTopology A V W, _] (toCompletion A V W) :=
  Completion.continuous_coe _

/-- The image of `V ⊗[A] W` is dense in `V ⊗̂_A W`. -/
theorem denseRange_toCompletion : DenseRange (toCompletion A V W) :=
  Completion.denseRange_coe

/-- **The elementary tensor map** `V → W → V ⊗̂_A W`, `(v, w) ↦ v ⊗ w`. -/
noncomputable def tmul : V →ₗ[A] W →ₗ[A] CompletedTensor A V W :=
  (TensorProduct.mk A V W).compr₂ (toCompletion A V W)

/-- The elementary tensor `v ⊗ w` of `V ⊗̂_A W` is the image of `v ⊗ₜ w`. -/
@[simp]
theorem toCompletion_tmul (v : V) (w : W) :
    toCompletion A V W (v ⊗ₜ[A] w) = tmul A V W v w :=
  (rfl)

/-- Under `equivCompletion`, the elementary tensor `v ⊗ w` of `V ⊗̂_A W` is the image of `v ⊗ₜ w`
under Mathlib's canonical map `Completion.coe'`. -/
@[simp]
theorem equivCompletion_tmul (v : V) (w : W) :
    equivCompletion A V W (tmul A V W v w) =
      @Completion.coe' _ (banachTensorUniformSpace A V W) (v ⊗ₜ[A] w) :=
  (rfl)

/-- The map `(v, w) ↦ v ⊗ w` into `V ⊗̂_A W` is continuous. -/
theorem continuous_tmul : Continuous fun p : V × W ↦ tmul A V W p.1 p.2 :=
  (continuous_toCompletion A V W).comp (continuous_tmul_banachTensorTopology A V W)

/-- The elementary tensors span a dense submodule of `V ⊗̂_A W`. -/
theorem dense_span_range_tmul :
    Dense (Submodule.span A (Set.range fun p : V × W ↦ tmul A V W p.1 p.2) :
      Set (CompletedTensor A V W)) := by
  refine (denseRange_toCompletion A V W).mono ?_
  rintro _ ⟨x, rfl⟩
  induction x using TensorProduct.inductionOn with
  | tmul v w => exact Submodule.subset_span ⟨(v, w), rfl⟩
  | add x y hx hy => simpa using Submodule.add_mem _ hx hy

variable {A V W}

/-- **Extensionality.** Two continuous linear maps out of `V ⊗̂_A W` into a Hausdorff topological
`A`-module agree as soon as they agree on all elementary tensors `v ⊗ w`. -/
@[ext]
theorem ext {M : Type*} [AddCommGroup M] [Module A M] [TopologicalSpace M] [T2Space M]
    {f g : CompletedTensor A V W →L[A] M} (h : ∀ v w, f (tmul A V W v w) = g (tmul A V W v w)) :
    f = g := by
  refine ContinuousLinearMap.ext fun x ↦ (denseRange_toCompletion A V W).induction_on x
    (isClosed_eq f.continuous g.continuous) fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul v w => simpa using h v w
  | add x y hx hy => simp only [map_add, hx, hy]

section Lift

variable {M : Type*} [AddCommGroup M] [Module A M] [UniformSpace M] [IsUniformAddGroup M]
  [NonarchimedeanAddGroup M] [ContinuousSMul A M] [CompleteSpace M] [T0Space M]

/-- **The universal property of the completed tensor product.** A continuous `A`-bilinear map
`β : V × W → M` into a complete Hausdorff nonarchimedean topological `A`-module with continuous
action induces the continuous `A`-linear map `V ⊗̂_A W → M` sending `v ⊗ w` to `β v w`
(`lift_tmul`); it is the only one (`ext`). -/
noncomputable def lift (β : V →ₗ[A] W →ₗ[A] M) (hβ : Continuous fun p : V × W ↦ β p.1 p.2) :
    CompletedTensor A V W →L[A] M :=
  have := uniformContinuousConstSMul_of_continuousConstSMul A M
  ContinuousLinearMap.fromCompletion
    ⟨TensorProduct.lift β, (continuous_banachTensorTopology_iff _).mpr (by simpa using hβ)⟩

/-- `lift β` extends `TensorProduct.lift β` from `V ⊗[A] W`. -/
@[simp]
theorem lift_toCompletion (β : V →ₗ[A] W →ₗ[A] M) (hβ : Continuous fun p : V × W ↦ β p.1 p.2)
    (x : V ⊗[A] W) : lift β hβ (toCompletion A V W x) = TensorProduct.lift β x :=
  have := uniformContinuousConstSMul_of_continuousConstSMul A M
  ContinuousLinearMap.fromCompletion_apply_coe _ x

/-- `lift β` sends `v ⊗ w` to `β v w`. -/
@[simp]
theorem lift_tmul (β : V →ₗ[A] W →ₗ[A] M) (hβ : Continuous fun p : V × W ↦ β p.1 p.2)
    (v : V) (w : W) : lift β hβ (tmul A V W v w) = β v w := by
  rw [← toCompletion_tmul, lift_toCompletion, TensorProduct.lift.tmul]

/-- `lift β` is the only continuous linear map sending each `v ⊗ w` to `β v w`. -/
theorem lift_unique (β : V →ₗ[A] W →ₗ[A] M) (hβ : Continuous fun p : V × W ↦ β p.1 p.2)
    (f : CompletedTensor A V W →L[A] M) (hf : ∀ v w, f (tmul A V W v w) = β v w) :
    f = lift β hβ :=
  ext fun v w ↦ by rw [hf, lift_tmul]

section Lid

variable (A M)

/-- **The unit isomorphism** `A ⊗̂_A M ≃ M` of a complete Hausdorff nonarchimedean topological
`A`-module `M` with continuous action: it sends `a ⊗ m` to `a • m` (`lid_tmul`), and its inverse
sends `m` to `1 ⊗ m` (`lid_symm_apply`). -/
noncomputable def lid : CompletedTensor A A M ≃L[A] M :=
  .equivOfInverse' (lift (LinearMap.lsmul A M) (continuous_smul.congr fun _ ↦ by simp))
    ⟨tmul A A M 1, (continuous_tmul A A M).comp (continuous_const.prodMk continuous_id)⟩
    (by ext m; simp) (ext fun a m ↦ by simp [← LinearMap.map_smul₂])

/-- The unit isomorphism sends `a ⊗ m` to `a • m`. -/
@[simp]
theorem lid_tmul (a : A) (m : M) : lid A M (tmul A A M a m) = a • m := by
  simp [lid]

/-- The inverse of the unit isomorphism sends `m` to `1 ⊗ m`. -/
@[simp]
theorem lid_symm_apply (m : M) : (lid A M).symm m = tmul A A M 1 m :=
  (rfl)

/-- The unit isomorphism extends Mathlib's algebraic unit map `A ⊗[A] M ≃ M`. -/
@[simp]
theorem lid_toCompletion (x : A ⊗[A] M) :
    lid A M (toCompletion A A M x) = TensorProduct.lid A M x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end Lid

end Lift

section Map

variable [IsTopologicalRing A]
  {V' : Type*} [AddCommGroup V'] [Module A V'] [TopologicalSpace V']
  {W' : Type*} [AddCommGroup W'] [Module A W'] [TopologicalSpace W']
  {V'' : Type*} [AddCommGroup V''] [Module A V''] [TopologicalSpace V'']
  {W'' : Type*} [AddCommGroup W''] [Module A W''] [TopologicalSpace W'']

/-- **The completed tensor product of continuous linear maps** `f ⊗̂ g : V ⊗̂_A W → V' ⊗̂_A W'`,
sending `v ⊗ w` to `f v ⊗ g w` (`map_tmul`). -/
noncomputable def map (f : V →L[A] V') (g : W →L[A] W') :
    CompletedTensor A V W →L[A] CompletedTensor A V' W' :=
  lift ((tmul A V' W').compl₁₂ f.toLinearMap g.toLinearMap)
    (((continuous_tmul A V' W').comp (f.continuous.prodMap g.continuous)).congr fun _ ↦ by simp)

/-- `f ⊗̂ g` sends `v ⊗ w` to `f v ⊗ g w`. -/
@[simp]
theorem map_tmul (f : V →L[A] V') (g : W →L[A] W') (v : V) (w : W) :
    map f g (tmul A V W v w) = tmul A V' W' (f v) (g w) := by
  simp [map]

/-- The completed tensor product of identities is the identity. -/
@[simp]
theorem map_id :
    map (.id A V) (.id A W) = ContinuousLinearMap.id A (CompletedTensor A V W) :=
  ext fun v w ↦ by simp

/-- The completed tensor product of maps is compatible with composition. -/
theorem map_comp (f₂ : V' →L[A] V'') (g₂ : W' →L[A] W'') (f₁ : V →L[A] V') (g₁ : W →L[A] W') :
    map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) :=
  ext fun v w ↦ by simp

end Map

section Product

variable [IsTopologicalRing A]
  {U : Type*} [AddCommGroup U] [Module A U] [TopologicalSpace U]
  {Q : Type*} [AddCommGroup Q] [Module A Q] [TopologicalSpace Q]

/-- Completed tensoring in the first variable preserves binary products. -/
noncomputable def prodLeft :
    CompletedTensor A (U × Q) W ≃L[A]
      CompletedTensor A U W × CompletedTensor A Q W :=
  ContinuousLinearEquiv.equivOfInverse'
    ((map (ContinuousLinearMap.fst A U Q) (.id A W)).prod
      (map (ContinuousLinearMap.snd A U Q) (.id A W)))
    ((map (ContinuousLinearMap.inl A U Q) (.id A W)).coprod
      (map (ContinuousLinearMap.inr A U Q) (.id A W)))
    (by ext v w <;> simp)
    (by
      apply ext
      intro v w
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.coprod_apply, map_tmul, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
      rw [← LinearMap.add_apply, ← map_add]
      simp)

/-- The product comparison is given by the two completed tensor projections. -/
theorem prodLeft_apply (z : CompletedTensor A (U × Q) W) :
    prodLeft z =
      (map (ContinuousLinearMap.fst A U Q) (.id A W) z,
        map (ContinuousLinearMap.snd A U Q) (.id A W) z) :=
  (rfl)

/-- The first component of the product comparison is the completed tensor projection. -/
@[simp]
theorem prodLeft_fst (z : CompletedTensor A (U × Q) W) :
    (prodLeft z).1 = map (ContinuousLinearMap.fst A U Q) (.id A W) z :=
  (rfl)

/-- The second component of the product comparison is the completed tensor projection. -/
@[simp]
theorem prodLeft_snd (z : CompletedTensor A (U × Q) W) :
    (prodLeft z).2 = map (ContinuousLinearMap.snd A U Q) (.id A W) z :=
  (rfl)

/-- The product comparison sends an elementary tensor to its two component tensors. -/
@[simp]
theorem prodLeft_tmul (v : U × Q) (w : W) :
    prodLeft (tmul A (U × Q) W v w) = (tmul A U W v.1 w, tmul A Q W v.2 w) := by
  simp [prodLeft]

/-- The inverse product comparison is the sum of the two completed tensor inclusions. -/
@[simp]
theorem prodLeft_symm_apply (x : CompletedTensor A U W) (y : CompletedTensor A Q W) :
    prodLeft.symm (x, y) =
      map (ContinuousLinearMap.inl A U Q) (.id A W) x +
        map (ContinuousLinearMap.inr A U Q) (.id A W) y := by
  rfl

end Product

section FiniteProjective

variable [IsTopologicalRing A] (P : Type*) [AddCommGroup P] [Module A P] [TopologicalSpace P]
  [IsModuleTopology A P] [Module.Finite A P] [Module.Projective A P]
  (M : Type*) [AddCommGroup M] [Module A M] [UniformSpace M] [IsUniformAddGroup M]
  [NonarchimedeanAddGroup M] [ContinuousSMul A M] [CompleteSpace M] [T0Space M]

variable (A) in
/-- For a finite projective `A`-module `P` with its natural topology, the map
`P ⊗[A] M → P ⊗̂_A M` is bijective: tensoring with `P` needs no completion. -/
theorem toCompletion_bijective_of_finite_projective :
    Function.Bijective (toCompletion A P M) := by
  classical
  -- `P` is a retract `f ∘ g = id` of some `Aⁿ`; the coordinates of `g` are continuous
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  have hg : Continuous g := IsModuleTopology.continuous_of_linearMap g
  -- `c i : P ⊗̂ M → M` extends `p ⊗ m ↦ (g p)ᵢ • m`
  let c (i : Fin n) : CompletedTensor A P M →L[A] M :=
    lift ((LinearMap.lsmul A M).comp ((LinearMap.proj i).comp g))
      ((((continuous_apply i).comp (hg.comp continuous_fst)).smul continuous_snd).congr
        fun _ ↦ by simp)
  -- the inverse `x ↦ ∑ᵢ f(eᵢ) ⊗ c i x`
  let ψ : CompletedTensor A P M →ₗ[A] P ⊗[A] M :=
    ∑ i, (TensorProduct.mk A P M (f (Pi.single i 1))).comp (c i).toLinearMap
  have hf (p : P) : ∑ i, g p i • f (Pi.single i 1) = p := by
    have h : f (g p) = p := LinearMap.congr_fun hfg p
    rw [pi_eq_sum_univ' (g p)] at h
    simpa [map_sum, map_smul] using h
  have hψ (x : P ⊗[A] M) : ψ (toCompletion A P M x) = x := by
    induction x using TensorProduct.inductionOn with
    | tmul p m =>
      conv_rhs => rw [← hf p]
      simp [ψ, c, LinearMap.sum_apply, TensorProduct.sum_tmul, TensorProduct.smul_tmul']
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hcont : Continuous fun x ↦ toCompletion A P M (ψ x) := by
    simp only [ψ, LinearMap.sum_apply, map_sum, LinearMap.comp_apply,
      TensorProduct.mk_apply, toCompletion_tmul, ContinuousLinearMap.coe_coe]
    exact continuous_finsetSum _ fun i _ ↦
      (continuous_tmul A P M).comp (continuous_const.prodMk (c i).continuous)
  -- `toCompletion ∘ ψ` is continuous and the identity on the dense image of `toCompletion`
  refine ⟨Function.LeftInverse.injective hψ, fun x ↦ ⟨ψ x, ?_⟩⟩
  refine (denseRange_toCompletion A P M).induction_on x (isClosed_eq hcont continuous_id) ?_
  exact fun y ↦ by rw [hψ]

variable (A) in
/-- **The completed tensor product with a finite projective module**: for a finite projective
`A`-module `P` with its natural topology, `P ⊗[A] M → P ⊗̂_A M` is an isomorphism. -/
noncomputable def finiteProjectiveEquiv : P ⊗[A] M ≃ₗ[A] CompletedTensor A P M :=
  .ofBijective (toCompletion A P M) (toCompletion_bijective_of_finite_projective A P M)

/-- `finiteProjectiveEquiv` is the canonical map `P ⊗[A] M → P ⊗̂_A M`. -/
@[simp]
theorem finiteProjectiveEquiv_apply (x : P ⊗[A] M) :
    finiteProjectiveEquiv A P M x = toCompletion A P M x :=
  (rfl)

/-- `finiteProjectiveEquiv` sends `p ⊗ m` to the elementary tensor `p ⊗ m` of `P ⊗̂_A M`. -/
theorem finiteProjectiveEquiv_tmul (p : P) (m : M) :
    finiteProjectiveEquiv A P M (p ⊗ₜ m) = tmul A P M p m := by
  simp

/-- The inverse of `finiteProjectiveEquiv` sends the elementary tensor `p ⊗ m` of `P ⊗̂_A M` to
`p ⊗ₜ m`. -/
@[simp]
theorem finiteProjectiveEquiv_symm_tmul (p : P) (m : M) :
    (finiteProjectiveEquiv A P M).symm (tmul A P M p m) = p ⊗ₜ m :=
  (finiteProjectiveEquiv A P M).symm_apply_eq.mpr (finiteProjectiveEquiv_tmul P M p m).symm

/-- The inverse of `finiteProjectiveEquiv` sends the image of `x : P ⊗[A] M` back to `x`. -/
@[simp]
theorem finiteProjectiveEquiv_symm_toCompletion (x : P ⊗[A] M) :
    (finiteProjectiveEquiv A P M).symm (toCompletion A P M x) = x :=
  (finiteProjectiveEquiv A P M).symm_apply_apply x

end FiniteProjective

end CompletedTensor

end BanachModule

end TauCeti.Huber
