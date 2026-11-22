/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.TensorProduct.Free
public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RingTheory.Deformation.Lift

import TauCeti.RingTheory.Ideal.Operations

/-!
# Module deformations of a residual representation

Let `ρbar : G →* GL n k` be a residual representation and `A` an object of the Artinian
coefficient category `C_Λ`. Besides the matrix description of deformations by lifts
(`TauCeti.Deformation.Lift`), Mazur's deformation theory describes them as modules: a *module
deformation* of `ρbar` to `A` is a finite free `A`-module `V` with an `A`-linear action of `G`,
continuous for the discrete topology on `V`, together with an identification `V ⊗_A k ≅ kⁿ` of
`G`-modules, where `kⁿ` carries the action of `ρbar`. Isomorphisms are `G`-equivariant `A`-linear
isomorphisms compatible with these identifications; a *framed* module deformation carries in
addition an `A`-basis lifting the standard basis of `kⁿ`, and its isomorphisms preserve the bases.

We record the identification `V ⊗_A k ≅ kⁿ` as its composite with `V → V ⊗_A k`: a reduction map
`V → kⁿ`, semilinear over the augmentation `A → k`, surjective, with kernel `𝔪_A V`, intertwining
the action on `V` with `ρbar`. Base change along a morphism `f : A ⟶ B` of `C_Λ` sends `V` to
`B ⊗_A V`, with the action `1 ⊗ ρ(g)`, the reduction map `b ⊗ v ↦ aug_B(b) • red(v)` and, for a
framed deformation, the basis `1 ⊗ bᵢ`. Up to isomorphism, base change is functorial, which makes
the isomorphism classes into the module deformation functors `Def^mod_ρbar` and
`Def^{mod,□}_ρbar` from `C_Λ` to types. By Nakayama's lemma every module deformation admits a
framing, so forgetting the framing is surjective on isomorphism classes.

The identification `V ⊗_A k ≅ kⁿ` is part of the data: for `ρbar = 1 ⊕ 1`, the dual-number
deformations `diag(1 + εx, 1)` and `diag(1, 1 + εx)` of a nonzero additive character `x` are
isomorphic as `G`-modules by swapping the basis vectors, but the swap does not reduce to the
identity of `kⁿ`, so they are different module deformations.

## Main definitions

* `TauCeti.Deformation.ModuleDeformation ρbar A`: module deformations of `ρbar` to `A`, with
  isomorphisms `TauCeti.Deformation.ModuleDeformation.Equiv`.
* `TauCeti.Deformation.ModuleDeformation.baseChange f`: base change `V ↦ B ⊗_A V` along a
  morphism `f : A ⟶ B` of `C_Λ`, with the canonical map
  `TauCeti.Deformation.ModuleDeformation.toBaseChange f` and the bases
  `TauCeti.Deformation.ModuleDeformation.baseChangeBasis f b`.
* `TauCeti.Deformation.FramedModuleDeformation ρbar A`: framed module deformations.
* `TauCeti.Deformation.ModuleDeformationClass ρbar A` and
  `TauCeti.Deformation.FramedModuleDeformationClass ρbar A`: their isomorphism classes.
* `TauCeti.Deformation.moduleDeformationFunctor Λ ρbar` and
  `TauCeti.Deformation.framedModuleDeformationFunctor Λ ρbar`: the functors `Def^mod_ρbar` and
  `Def^{mod,□}_ρbar : C_Λ ⥤ Type`, with the natural transformation
  `TauCeti.Deformation.forgetFraming Λ ρbar` forgetting the framing.

## Main results

* `TauCeti.Deformation.ModuleDeformation.exists_basis`: every module deformation has a basis
  lifting the standard basis of `kⁿ`.
* `TauCeti.Deformation.ModuleDeformation.baseChangeEquiv`: an isomorphism out of a base change,
  induced by a semilinear map sending a basis to a basis; it gives the isomorphisms
  `TauCeti.Deformation.ModuleDeformation.baseChangeId` and
  `TauCeti.Deformation.ModuleDeformation.baseChangeComp` behind the functor laws.
* `TauCeti.Deformation.FramedModuleDeformationClass.forget_surjective`: forgetting the framing is
  surjective on isomorphism classes.
* Over the residue field `k` there is at most one isomorphism class of (framed) module
  deformations.

## References

* B. Mazur, *Deforming Galois representations*, in *Galois groups over `ℚ`*, MSRI Publ. 16
  (1989), 385–437, §1.2.
* M. Kisin, *Moduli of finite flat group schemes and modularity*, Ann. of Math. 170 (2009),
  §1.1 (lecture notes version: *Lectures on deformations of Galois representations*, Lecture 1,
  (1.1.1)).
-/

public section

open CategoryTheory Matrix IsLocalRing TensorProduct

universe u v w x

namespace TauCeti.Deformation

variable {Λ : Type u} [CommRing Λ] {k : Type v} [Field k] [Algebra Λ k]
  {n : Type x} [Fintype n] [DecidableEq n] {G : Type w} [Monoid G] [TopologicalSpace G]

open ArtinLocalAlg

/-- A *module deformation* of the residual representation `ρbar : G →* GL n k` to an object `A`
of `C_Λ`: a free `A`-module `V` with an `A`-linear action of `G`, continuous for the discrete
topology, and a reduction map `V → kⁿ` over the augmentation `A → k` which is surjective with
kernel `𝔪_A V` and intertwines the action with `ρbar`. Equivalently, the reduction map is an
identification `V ⊗_A k ≅ kⁿ` of `G`-modules. Such a `V` is finite over `A` (see the instance
below), of rank `n`. -/
structure ModuleDeformation (ρbar : G →* GL n k) (A : ArtinLocalAlg Λ k) where
  /-- The underlying `A`-module. -/
  carrier : Type v
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module A.obj.left carrier]
  [instFree : Module.Free A.obj.left carrier]
  /-- The `A`-linear action of `G`. -/
  action : Representation A.obj.left G carrier
  /-- The action is continuous for the discrete topology on the module. -/
  isLocallyConstant_action : IsLocallyConstant action
  /-- The reduction map `V → kⁿ`, semilinear over the augmentation `A → k`. -/
  reduction : carrier →ₛₗ[(A.augmentation : A.obj.left →+* k)] n → k
  /-- The reduction map is surjective. -/
  surjective_reduction : Function.Surjective reduction
  /-- The kernel of the reduction map is contained in `𝔪_A V`. -/
  ker_reduction_le : LinearMap.ker reduction ≤ maximalIdeal A.obj.left • ⊤
  /-- The reduction map intertwines the action with `ρbar`. -/
  reduction_action (g : G) (v : carrier) :
    reduction (action g v) = (ρbar g : Matrix n n k) *ᵥ reduction v

namespace ModuleDeformation

attribute [instance] instAddCommGroup instModule instFree

variable {ρbar : G →* GL n k} {A B C : ArtinLocalAlg Λ k}

instance : CoeSort (ModuleDeformation ρbar A) (Type v) :=
  ⟨carrier⟩

/-- The kernel of the reduction map of a module deformation is `𝔪_A V`. -/
theorem ker_reduction (D : ModuleDeformation ρbar A) :
    LinearMap.ker D.reduction = maximalIdeal A.obj.left • ⊤ := by
  refine le_antisymm D.ker_reduction_le (Submodule.smul_le.mpr fun a ha v _ ↦ ?_)
  rw [LinearMap.mem_ker, LinearMap.map_smulₛₗ]
  simp [augmentation_eq_zero_iff.mpr ha]

/-- A vector of a module deformation reduces to zero exactly when it lies in `𝔪_A V`. -/
theorem reduction_eq_zero_iff (D : ModuleDeformation ρbar A) {v : D} :
    D.reduction v = 0 ↔ v ∈ maximalIdeal A.obj.left • (⊤ : Submodule A.obj.left D) := by
  rw [← LinearMap.mem_ker, ker_reduction]

/-- The reduction of a basis of a module deformation is linearly independent over `k`. -/
theorem linearIndependent_reduction (D : ModuleDeformation ρbar A) {ι : Type*}
    (b : Module.Basis ι A.obj.left D) : LinearIndependent k (D.reduction ∘ b) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc i hi
  choose a ha using A.augmentation_surjective
  have h0 : D.reduction (∑ j ∈ s, a (c j) • b j) = 0 := by
    simpa [map_sum, ha] using hc
  have hmem : a (c i) ∈ maximalIdeal A.obj.left := by
    simpa [Finset.sum_apply', Finsupp.single_apply, hi] using
      b.mem_smul_top_iff.mp ((reduction_eq_zero_iff D).mp h0) i
  rw [← ha (c i)]
  exact augmentation_eq_zero_iff.mpr hmem

/-- The underlying module of a module deformation is finite: a basis reduces to a linearly
independent family in `kⁿ`, so it is finite. -/
instance (D : ModuleDeformation ρbar A) : Module.Finite A.obj.left D :=
  have := (D.linearIndependent_reduction (Module.Free.chooseBasis A.obj.left D)).finite
  Module.Finite.of_basis (Module.Free.chooseBasis A.obj.left D)

/-- Every module deformation has a basis lifting the standard basis of `kⁿ`. -/
theorem exists_basis (D : ModuleDeformation ρbar A) :
    ∃ e : Module.Basis n A.obj.left D, ∀ i, D.reduction (e i) = Pi.single i 1 := by
  classical
  let b := Module.Free.chooseBasis A.obj.left D
  have hspan : ⊤ ≤ Submodule.span k (Set.range (D.reduction ∘ b)) := by
    rintro y -
    obtain ⟨v, rfl⟩ := D.surjective_reduction y
    rw [← b.sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcard : Fintype.card n = Module.finrank A.obj.left D := by
    rw [Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_fintype_fun_eq_card (R := k),
      Module.finrank_eq_card_basis (Module.Basis.mk (D.linearIndependent_reduction b) hspan)]
  choose e he using fun i : n ↦ D.surjective_reduction (Pi.single i 1)
  have hspan' : ⊤ ≤ Submodule.span A.obj.left (Set.range e) := by
    rw [top_le_iff, ← IsLocalRing.map_mkQ_eq_top, eq_top_iff]
    rintro q -
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ q
    choose a ha using A.augmentation_surjective
    refine ⟨∑ i, a (D.reduction v i) • e i, Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
      ← reduction_eq_zero_iff, map_sub, map_sum]
    simp only [LinearMap.map_smulₛₗ, he, ha, RingHom.coe_coe]
    rw [sub_eq_zero]
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  exact ⟨basisOfTopLeSpanOfCardEqFinrank e hspan' hcard, fun i ↦ by simp [he]⟩

/-- Over the residue field `k`, the reduction map of a module deformation is injective. -/
theorem reduction_injective_residue (D : ModuleDeformation ρbar (residue Λ k)) :
    Function.Injective D.reduction := by
  have h : maximalIdeal (residue Λ k).obj.left = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun a ha ↦ ?_
    have h := augmentation_eq_zero_iff.mpr ha
    rw [augmentation_residue] at h
    -- The carrier of `residue Λ k` is `k`, on which `AlgHom.id Λ k` is the identity.
    exact h
  rw [← LinearMap.ker_eq_bot, ker_reduction, h, Submodule.bot_smul]

/-- An *isomorphism* of module deformations: an `A`-linear isomorphism of the underlying modules
intertwining the actions of `G` and compatible with the reduction maps. -/
structure Equiv (D D' : ModuleDeformation ρbar A) where
  /-- The underlying `A`-linear isomorphism. -/
  toLinearEquiv : D ≃ₗ[A.obj.left] D'
  /-- The isomorphism intertwines the actions. -/
  map_action (g : G) (v : D) : toLinearEquiv (D.action g v) = D'.action g (toLinearEquiv v)
  /-- The isomorphism is compatible with the reduction maps. -/
  reduction_apply (v : D) : D'.reduction (toLinearEquiv v) = D.reduction v

namespace Equiv

attribute [simp] reduction_apply

/-- The identity isomorphism of a module deformation. -/
def refl (D : ModuleDeformation ρbar A) : D.Equiv D where
  toLinearEquiv := LinearEquiv.refl _ _
  map_action _ _ := rfl
  reduction_apply _ := rfl

@[simp]
theorem refl_toLinearEquiv (D : ModuleDeformation ρbar A) :
    (refl D).toLinearEquiv = LinearEquiv.refl _ _ :=
  (rfl)

/-- The inverse of an isomorphism of module deformations. -/
def symm {D D' : ModuleDeformation ρbar A} (e : D.Equiv D') : D'.Equiv D where
  toLinearEquiv := e.toLinearEquiv.symm
  map_action g v := e.toLinearEquiv.injective (by simp [e.map_action])
  reduction_apply v := by
    rw [← e.reduction_apply, LinearEquiv.apply_symm_apply]

@[simp]
theorem symm_toLinearEquiv {D D' : ModuleDeformation ρbar A} (e : D.Equiv D') :
    e.symm.toLinearEquiv = e.toLinearEquiv.symm :=
  (rfl)

/-- The composite of two isomorphisms of module deformations. -/
def trans {D D' D'' : ModuleDeformation ρbar A} (e : D.Equiv D') (e' : D'.Equiv D'') :
    D.Equiv D'' where
  toLinearEquiv := e.toLinearEquiv.trans e'.toLinearEquiv
  map_action g v := by simp [e.map_action, e'.map_action]
  reduction_apply v := by simp

@[simp]
theorem trans_toLinearEquiv {D D' D'' : ModuleDeformation ρbar A} (e : D.Equiv D')
    (e' : D'.Equiv D'') : (e.trans e').toLinearEquiv = e.toLinearEquiv.trans e'.toLinearEquiv :=
  (rfl)

end Equiv

section BaseChange

variable (f : A ⟶ B)

/-- The reduction map `B ⊗_A V → kⁿ`, `b ⊗ v ↦ aug_B(b) • red(v)`, of the base change of a module
deformation along `f : A ⟶ B`. -/
private noncomputable def baseChangeReduction (D : ModuleDeformation ρbar A) :
    letI : Algebra A.obj.left B.obj.left := f.hom.left.hom.toAlgebra
    B.obj.left ⊗[A.obj.left] D →ₛₗ[(B.augmentation : B.obj.left →+* k)] n → k :=
  letI : Algebra A.obj.left B.obj.left := f.hom.left.hom.toAlgebra
  let φ : B.obj.left →+ D →+ n → k := AddMonoidHom.mk'
    (fun b ↦ (DistribSMul.toAddMonoidHom _ (B.augmentation b)).comp
      D.reduction.toAddMonoidHom)
    fun b b' ↦ by ext; simp [add_mul]
  have hφ (a : A.obj.left) (b : B.obj.left) (v : D) : φ (a • b) v = φ b (a • v) := by
    simp only [φ, AddMonoidHom.mk'_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      DistribSMul.toAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe, LinearMap.map_smulₛₗ,
      Algebra.smul_def, RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, map_mul,
      RingHom.coe_coe, augmentation_hom_apply]
    ring
  { toFun := TensorProduct.liftAddHom φ hφ
    map_add' := map_add _
    map_smul' b t := by
      induction t using TensorProduct.inductionOn with
      | tmul b' v => simp [φ, TensorProduct.smul_tmul', mul_smul]
      | add t t' ht ht' => simp only [smul_add, map_add, ht, ht'] }

private theorem baseChangeReduction_tmul (D : ModuleDeformation ρbar A) (b : B.obj.left) (v : D) :
    letI : Algebra A.obj.left B.obj.left := f.hom.left.hom.toAlgebra
    baseChangeReduction f D (b ⊗ₜ v) = B.augmentation b • D.reduction v :=
  rfl

/-- The *base change* `B ⊗_A V` of a module deformation `V` along a morphism `f : A ⟶ B` of
`C_Λ`, with the action `g ↦ 1 ⊗ ρ(g)` and the reduction map `b ⊗ v ↦ aug_B(b) • red(v)`. -/
noncomputable def baseChange (D : ModuleDeformation ρbar A) : ModuleDeformation ρbar B :=
  letI : Algebra A.obj.left B.obj.left := f.hom.left.hom.toAlgebra
  { carrier := B.obj.left ⊗[A.obj.left] D
    action := D.action.baseChange B.obj.left
    isLocallyConstant_action := by
      have h : ⇑(D.action.baseChange B.obj.left) =
          (fun φ ↦ LinearMap.baseChange B.obj.left φ) ∘ D.action :=
        funext fun g ↦ Representation.baseChange_apply D.action g
      rw [h]
      exact D.isLocallyConstant_action.comp _
    reduction := baseChangeReduction f D
    surjective_reduction y := by
      obtain ⟨v, rfl⟩ := D.surjective_reduction y
      exact ⟨1 ⊗ₜ v, by simp [baseChangeReduction_tmul]⟩
    ker_reduction_le t ht := by
      obtain ⟨e, he⟩ := D.exists_basis
      let e' := Algebra.TensorProduct.basis B.obj.left e
      rw [← e'.sum_repr t]
      refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul ?_ trivial
      have h := congrFun (LinearMap.mem_ker.mp ht) i
      rw [← e'.sum_repr t, map_sum] at h
      simpa [e', Algebra.TensorProduct.basis_apply, baseChangeReduction_tmul, he,
        Finset.sum_apply, Pi.single_apply] using h
    reduction_action g t := by
      induction t using TensorProduct.inductionOn with
      | tmul b v =>
        simp [baseChangeReduction_tmul, D.reduction_action, Matrix.mulVec_smul]
      | add t t' ht ht' => simp only [map_add, ht, ht', Matrix.mulVec_add] }

/-- The map `v ↦ 1 ⊗ v` from a module deformation to its base change along `f : A ⟶ B`,
semilinear over `f`. -/
noncomputable def toBaseChange (D : ModuleDeformation ρbar A) :
    D →ₛₗ[(f.hom.left.hom : A.obj.left →+* B.obj.left)] D.baseChange f :=
  letI : Algebra A.obj.left B.obj.left := f.hom.left.hom.toAlgebra
  { toFun v := (1 : B.obj.left) ⊗ₜ[A.obj.left] v
    map_add' := TensorProduct.tmul_add 1
    map_smul' a v := by
      rw [TensorProduct.tmul_smul, ← algebraMap_smul (A := B.obj.left),
        RingHom.algebraMap_toAlgebra]
      rfl }

/-- The map `V → B ⊗_A V` intertwines the actions. -/
@[simp]
theorem baseChange_action_toBaseChange (D : ModuleDeformation ρbar A) (g : G) (v : D) :
    (D.baseChange f).action g (D.toBaseChange f v) = D.toBaseChange f (D.action g v) := by
  let _ : Algebra A.obj.left B.obj.left := f.hom.left.hom.toAlgebra
  exact (LinearMap.congr_fun (Representation.baseChange_apply D.action g) _).trans
    (LinearMap.baseChange_tmul _ _ _)

/-- The map `V → B ⊗_A V` is compatible with the reduction maps. -/
@[simp]
theorem baseChange_reduction_toBaseChange (D : ModuleDeformation ρbar A) (v : D) :
    (D.baseChange f).reduction (D.toBaseChange f v) = D.reduction v := by
  let _ : Algebra A.obj.left B.obj.left := f.hom.left.hom.toAlgebra
  exact (baseChangeReduction_tmul f D 1 v).trans (by simp)

/-- The basis `1 ⊗ bᵢ` of the base change `B ⊗_A V` induced by a basis `b` of `V`. -/
noncomputable def baseChangeBasis (D : ModuleDeformation ρbar A) {ι : Type*}
    (b : Module.Basis ι A.obj.left D) : Module.Basis ι B.obj.left (D.baseChange f) :=
  letI : Algebra A.obj.left B.obj.left := f.hom.left.hom.toAlgebra
  Algebra.TensorProduct.basis B.obj.left b

@[simp]
theorem baseChangeBasis_apply (D : ModuleDeformation ρbar A) {ι : Type*}
    (b : Module.Basis ι A.obj.left D) (i : ι) :
    D.baseChangeBasis f b i = D.toBaseChange f (b i) := by
  let _ : Algebra A.obj.left B.obj.left := f.hom.left.hom.toAlgebra
  exact Algebra.TensorProduct.basis_apply b i

variable {f} in
private theorem baseChangeBasis_equiv_toBaseChange {D : ModuleDeformation ρbar A}
    {D' : ModuleDeformation ρbar B} (ψ : D →ₛₗ[(f.hom.left.hom : A.obj.left →+* B.obj.left)] D')
    {ι : Type*} (b : Module.Basis ι A.obj.left D) (b' : Module.Basis ι B.obj.left D')
    (hb : ∀ i, ψ (b i) = b' i) (v : D) :
    (D.baseChangeBasis f b).equiv b' (_root_.Equiv.refl ι) (D.toBaseChange f v) = ψ v :=
  LinearMap.congr_fun (b.ext
    (f₁ := ((D.baseChangeBasis f b).equiv b' (_root_.Equiv.refl ι)).toLinearMap ∘ₛₗ
      D.toBaseChange f)
    (f₂ := ψ) fun i ↦ by simp [← baseChangeBasis_apply, hb]) v

variable {f} in
/-- An isomorphism `B ⊗_A V ≅ V'` of module deformations over `B`, induced by a map `ψ : V → V'`,
semilinear over `f : A ⟶ B`, which intertwines the actions, is compatible with the reduction maps
and sends a basis of `V` to a basis of `V'`. -/
noncomputable def baseChangeEquiv {D : ModuleDeformation ρbar A} {D' : ModuleDeformation ρbar B}
    (ψ : D →ₛₗ[(f.hom.left.hom : A.obj.left →+* B.obj.left)] D')
    (hψ : ∀ g v, ψ (D.action g v) = D'.action g (ψ v))
    (hψ' : ∀ v, D'.reduction (ψ v) = D.reduction v) {ι : Type*}
    (b : Module.Basis ι A.obj.left D) (b' : Module.Basis ι B.obj.left D')
    (hb : ∀ i, ψ (b i) = b' i) : (D.baseChange f).Equiv D' where
  toLinearEquiv := (D.baseChangeBasis f b).equiv b' (_root_.Equiv.refl ι)
  map_action g := LinearMap.congr_fun ((D.baseChangeBasis f b).ext
    (f₁ := ((D.baseChangeBasis f b).equiv b' (_root_.Equiv.refl ι)).toLinearMap ∘ₗ
      (D.baseChange f).action g)
    (f₂ := D'.action g ∘ₗ ((D.baseChangeBasis f b).equiv b' (_root_.Equiv.refl ι)).toLinearMap)
    fun i ↦ by simp [baseChangeBasis_equiv_toBaseChange ψ b b' hb, hψ])
  reduction_apply := LinearMap.congr_fun ((D.baseChangeBasis f b).ext
    (f₁ := D'.reduction ∘ₛₗ ((D.baseChangeBasis f b).equiv b' (_root_.Equiv.refl ι)).toLinearMap)
    (f₂ := (D.baseChange f).reduction)
    fun i ↦ by simp [baseChangeBasis_equiv_toBaseChange ψ b b' hb, hψ'])

variable {f} in
@[simp]
theorem baseChangeEquiv_toBaseChange {D : ModuleDeformation ρbar A}
    {D' : ModuleDeformation ρbar B} (ψ : D →ₛₗ[(f.hom.left.hom : A.obj.left →+* B.obj.left)] D')
    (hψ : ∀ g v, ψ (D.action g v) = D'.action g (ψ v))
    (hψ' : ∀ v, D'.reduction (ψ v) = D.reduction v) {ι : Type*}
    (b : Module.Basis ι A.obj.left D) (b' : Module.Basis ι B.obj.left D')
    (hb : ∀ i, ψ (b i) = b' i) (v : D) :
    (baseChangeEquiv ψ hψ hψ' b b' hb).toLinearEquiv (D.toBaseChange f v) = ψ v :=
  baseChangeBasis_equiv_toBaseChange ψ b b' hb v

variable {f} in
/-- The isomorphism `baseChangeEquiv ψ hψ hψ' b b' hb` sends the basis `1 ⊗ bᵢ` to `b'`. -/
theorem baseChangeEquiv_baseChangeBasis {D : ModuleDeformation ρbar A}
    {D' : ModuleDeformation ρbar B} (ψ : D →ₛₗ[(f.hom.left.hom : A.obj.left →+* B.obj.left)] D')
    (hψ : ∀ g v, ψ (D.action g v) = D'.action g (ψ v))
    (hψ' : ∀ v, D'.reduction (ψ v) = D.reduction v) {ι : Type*}
    (b : Module.Basis ι A.obj.left D) (b' : Module.Basis ι B.obj.left D')
    (hb : ∀ i, ψ (b i) = b' i) (i : ι) :
    (baseChangeEquiv ψ hψ hψ' b b' hb).toLinearEquiv (D.baseChangeBasis f b i) = b' i := by
  simp [hb]

/-- Base change along the identity of `A` is isomorphic to the original deformation. -/
noncomputable def baseChangeId (D : ModuleDeformation ρbar A) : (D.baseChange (𝟙 A)).Equiv D :=
  baseChangeEquiv
    { toFun := id
      map_add' _ _ := rfl
      map_smul' _ _ := by simp }
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (Module.Free.chooseBasis A.obj.left D)
    (Module.Free.chooseBasis A.obj.left D) fun _ ↦ rfl

@[simp]
theorem baseChangeId_toBaseChange (D : ModuleDeformation ρbar A) (v : D) :
    (baseChangeId D).toLinearEquiv (D.toBaseChange (𝟙 A) v) = v :=
  baseChangeEquiv_toBaseChange _ _ _ _ _ _ v

/-- The map `v ↦ 1 ⊗ (1 ⊗ v)` from a module deformation to its iterated base change along `f` and
`g`, semilinear over `f ≫ g`. -/
private noncomputable def toBaseChangeComp (g : B ⟶ C) (D : ModuleDeformation ρbar A) :
    D →ₛₗ[((f ≫ g).hom.left.hom : A.obj.left →+* C.obj.left)] (D.baseChange f).baseChange g where
  toFun v := (D.baseChange f).toBaseChange g (D.toBaseChange f v)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

private theorem toBaseChangeComp_apply (g : B ⟶ C) (D : ModuleDeformation ρbar A) (v : D) :
    toBaseChangeComp f g D v = (D.baseChange f).toBaseChange g (D.toBaseChange f v) :=
  rfl

/-- Base change along a composite `f ≫ g` is isomorphic to the iterated base change. -/
noncomputable def baseChangeComp (g : B ⟶ C) (D : ModuleDeformation ρbar A) :
    (D.baseChange (f ≫ g)).Equiv ((D.baseChange f).baseChange g) :=
  baseChangeEquiv (toBaseChangeComp f g D)
    (fun _ _ ↦ by rw [toBaseChangeComp_apply, toBaseChangeComp_apply]; simp)
    (fun _ ↦ by rw [toBaseChangeComp_apply]; simp) (Module.Free.chooseBasis A.obj.left D)
    ((D.baseChange f).baseChangeBasis g (D.baseChangeBasis f (Module.Free.chooseBasis _ _)))
    fun _ ↦ by rw [toBaseChangeComp_apply]; simp

@[simp]
theorem baseChangeComp_toBaseChange (g : B ⟶ C) (D : ModuleDeformation ρbar A) (v : D) :
    (baseChangeComp f g D).toLinearEquiv (D.toBaseChange (f ≫ g) v) =
      (D.baseChange f).toBaseChange g (D.toBaseChange f v) :=
  baseChangeEquiv_toBaseChange _ _ _ _ _ _ v

/-- The base change of an isomorphism of module deformations. -/
noncomputable def Equiv.baseChange {D D' : ModuleDeformation ρbar A} (e : D.Equiv D') :
    (D.baseChange f).Equiv (D'.baseChange f) :=
  baseChangeEquiv ((D'.toBaseChange f).comp e.toLinearEquiv.toLinearMap)
    (fun _ _ ↦ by simp [e.map_action]) (fun _ ↦ by simp) (Module.Free.chooseBasis A.obj.left D)
    (D'.baseChangeBasis f ((Module.Free.chooseBasis A.obj.left D).map e.toLinearEquiv))
    fun _ ↦ by simp

@[simp]
theorem Equiv.baseChange_toBaseChange {D D' : ModuleDeformation ρbar A} (e : D.Equiv D')
    (v : D) :
    (e.baseChange f).toLinearEquiv (D.toBaseChange f v) = D'.toBaseChange f (e.toLinearEquiv v) :=
  baseChangeEquiv_toBaseChange _ _ _ _ _ _ v

end BaseChange

variable (ρbar A) in
/-- The setoid on module deformations given by isomorphism. -/
def isoSetoid : Setoid (ModuleDeformation ρbar A) where
  r D D' := Nonempty (D.Equiv D')
  iseqv := ⟨fun D ↦ ⟨Equiv.refl D⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e.trans e'⟩⟩

end ModuleDeformation

/-- The *isomorphism classes* of module deformations of `ρbar` to `A`. These are the values of the
module deformation functor `Def^mod_ρbar`. -/
-- Exposed as a quotient type: code generation needs its representation in other modules.
@[expose] def ModuleDeformationClass (ρbar : G →* GL n k) (A : ArtinLocalAlg Λ k) :=
  Quotient (ModuleDeformation.isoSetoid ρbar A)

namespace ModuleDeformationClass

variable {ρbar : G →* GL n k} {A B C : ArtinLocalAlg Λ k}

/-- The isomorphism class of a module deformation. -/
def mk (D : ModuleDeformation ρbar A) : ModuleDeformationClass ρbar A :=
  Quotient.mk _ D

/-- Every isomorphism class is the class of a module deformation. -/
theorem mk_surjective :
    Function.Surjective (mk : ModuleDeformation ρbar A → ModuleDeformationClass ρbar A) :=
  Quotient.mk_surjective

/-- Two module deformations have the same class exactly when they are isomorphic. -/
theorem mk_eq_mk_iff {D D' : ModuleDeformation ρbar A} : mk D = mk D' ↔ Nonempty (D.Equiv D') :=
  Quotient.eq

/-- Isomorphic module deformations have the same class. -/
theorem mk_eq_mk {D D' : ModuleDeformation ρbar A} (e : D.Equiv D') : mk D = mk D' :=
  mk_eq_mk_iff.mpr ⟨e⟩

/-- A function on module deformations that is invariant under isomorphism descends to
isomorphism classes. -/
def lift {β : Sort*} (F : ModuleDeformation ρbar A → β)
    (hF : ∀ D D' : ModuleDeformation ρbar A, D.Equiv D' → F D = F D') :
    ModuleDeformationClass ρbar A → β :=
  Quotient.lift F fun D D' ⟨e⟩ ↦ hF D D' e

@[simp]
theorem lift_mk {β : Sort*} (F : ModuleDeformation ρbar A → β)
    (hF : ∀ D D' : ModuleDeformation ρbar A, D.Equiv D' → F D = F D')
    (D : ModuleDeformation ρbar A) : lift F hF (mk D) = F D :=
  (rfl)

/-- The base change of isomorphism classes along a morphism `f : A ⟶ B` of `C_Λ`. -/
noncomputable def map (f : A ⟶ B) : ModuleDeformationClass ρbar A → ModuleDeformationClass ρbar B :=
  Quotient.map (ModuleDeformation.baseChange f) fun _ _ ⟨e⟩ ↦ ⟨e.baseChange f⟩

@[simp]
theorem map_mk (f : A ⟶ B) (D : ModuleDeformation ρbar A) : map f (mk D) = mk (D.baseChange f) :=
  (rfl)

/-- Base change of isomorphism classes along the identity is the identity. -/
@[simp]
theorem map_id (c : ModuleDeformationClass ρbar A) : map (𝟙 A) c = c := by
  obtain ⟨D, rfl⟩ := mk_surjective c
  exact mk_eq_mk D.baseChangeId

/-- Base change of isomorphism classes along a composite is the composite of the base changes. -/
theorem map_comp (f : A ⟶ B) (g : B ⟶ C) (c : ModuleDeformationClass ρbar A) :
    map (f ≫ g) c = map g (map f c) := by
  obtain ⟨D, rfl⟩ := mk_surjective c
  exact mk_eq_mk (D.baseChangeComp f g)

end ModuleDeformationClass

variable (ρbar : G →* GL n k)

variable (Λ) in
/-- The *module deformation functor* `Def^mod_ρbar : C_Λ ⥤ Type` of the residual representation
`ρbar`, sending `A` to the isomorphism classes of module deformations of `ρbar` to `A` and a
morphism to base change. -/
-- Exposed so that `(moduleDeformationFunctor Λ ρbar).obj A` unfolds to
-- `ModuleDeformationClass ρbar A` in statements.
@[expose] noncomputable def moduleDeformationFunctor :
    ArtinLocalAlg Λ k ⥤ Type (max (v + 1) w x) where
  obj A := ModuleDeformationClass ρbar A
  map f := TypeCat.ofHom (ModuleDeformationClass.map f)
  map_id A := by
    ext c : 3
    exact ModuleDeformationClass.map_id c
  map_comp f g := by
    ext c : 3
    exact ModuleDeformationClass.map_comp f g c

variable (Λ) in
@[simp]
theorem moduleDeformationFunctor_obj (A : ArtinLocalAlg Λ k) :
    (moduleDeformationFunctor Λ ρbar).obj A = ModuleDeformationClass ρbar A :=
  (rfl)

variable (Λ) in
@[simp]
theorem moduleDeformationFunctor_map_apply {A B : ArtinLocalAlg Λ k} (f : A ⟶ B)
    (c : ModuleDeformationClass ρbar A) :
    (moduleDeformationFunctor Λ ρbar).map f c = ModuleDeformationClass.map f c :=
  (rfl)

/-- A *framed module deformation* of `ρbar` to `A`: a module deformation together with an
`A`-basis of the module reducing to the standard basis of `kⁿ`. -/
structure FramedModuleDeformation (ρbar : G →* GL n k) (A : ArtinLocalAlg Λ k)
    extends ModuleDeformation ρbar A where
  /-- The framing: an `A`-basis of the module. -/
  basis : Module.Basis n A.obj.left carrier
  /-- The framing lifts the standard basis of `kⁿ`. -/
  reduction_basis (i : n) : reduction (basis i) = Pi.single i 1

namespace FramedModuleDeformation

attribute [simp] reduction_basis

variable {ρbar} {A B C : ArtinLocalAlg Λ k}

instance : CoeSort (FramedModuleDeformation ρbar A) (Type v) :=
  ⟨fun D ↦ D.carrier⟩

/-- An *isomorphism* of framed module deformations: an isomorphism of module deformations
sending the framing of the source to the framing of the target. -/
structure Equiv (D D' : FramedModuleDeformation ρbar A) extends
    D.toModuleDeformation.Equiv D'.toModuleDeformation where
  /-- The isomorphism preserves the framings. -/
  map_basis (i : n) : toLinearEquiv (D.basis i) = D'.basis i

namespace Equiv

attribute [simp] map_basis

/-- The identity isomorphism of a framed module deformation. -/
def refl (D : FramedModuleDeformation ρbar A) : D.Equiv D where
  toEquiv := ModuleDeformation.Equiv.refl _
  map_basis _ := rfl

/-- The inverse of an isomorphism of framed module deformations. -/
def symm {D D' : FramedModuleDeformation ρbar A} (e : D.Equiv D') : D'.Equiv D where
  toEquiv := e.toEquiv.symm
  map_basis i := e.toLinearEquiv.symm_apply_eq.mpr (e.map_basis i).symm

/-- The composite of two isomorphisms of framed module deformations. -/
def trans {D D' D'' : FramedModuleDeformation ρbar A} (e : D.Equiv D') (e' : D'.Equiv D'') :
    D.Equiv D'' where
  toEquiv := e.toEquiv.trans e'.toEquiv
  map_basis i := by simp

end Equiv

section BaseChange

variable (f : A ⟶ B)

/-- The *base change* of a framed module deformation along a morphism `f : A ⟶ B` of `C_Λ`,
framed by the basis `1 ⊗ bᵢ`. -/
-- An abbreviation, so that the underlying module deformation of the base change is reducibly
-- the base change of the underlying module deformation.
noncomputable abbrev baseChange (D : FramedModuleDeformation ρbar A) :
    FramedModuleDeformation ρbar B where
  toModuleDeformation := D.toModuleDeformation.baseChange f
  basis := D.baseChangeBasis f D.basis
  reduction_basis i := by simp

theorem baseChange_basis (D : FramedModuleDeformation ρbar A) (i : n) :
    (D.baseChange f).basis i = D.toBaseChange f (D.basis i) :=
  ModuleDeformation.baseChangeBasis_apply f _ _ i

/-- Base change of a framed module deformation along the identity of `A` is isomorphic to the
original framed deformation. -/
noncomputable def baseChangeId (D : FramedModuleDeformation ρbar A) :
    (D.baseChange (𝟙 A)).Equiv D where
  toEquiv := D.toModuleDeformation.baseChangeId
  map_basis i := by
    rw [baseChange_basis]
    exact ModuleDeformation.baseChangeId_toBaseChange _ _

/-- Base change of a framed module deformation along a composite `f ≫ g` is isomorphic to the
iterated base change. -/
noncomputable def baseChangeComp (g : B ⟶ C) (D : FramedModuleDeformation ρbar A) :
    (D.baseChange (f ≫ g)).Equiv ((D.baseChange f).baseChange g) where
  toEquiv := D.toModuleDeformation.baseChangeComp f g
  map_basis i := by
    rw [baseChange_basis, baseChange_basis, baseChange_basis]
    exact ModuleDeformation.baseChangeComp_toBaseChange _ _ _ _

/-- The base change of an isomorphism of framed module deformations. -/
noncomputable def Equiv.baseChange {D D' : FramedModuleDeformation ρbar A} (e : D.Equiv D') :
    (D.baseChange f).Equiv (D'.baseChange f) where
  toEquiv := e.toEquiv.baseChange f
  map_basis i := by
    rw [baseChange_basis, baseChange_basis]
    exact (ModuleDeformation.Equiv.baseChange_toBaseChange _ _ _).trans
      (congrArg _ (e.map_basis i))

end BaseChange

section Residue

/-- The isomorphism `V ≅ V'` of the underlying modules of two framed module deformations sending
one framing to the other. -/
private noncomputable def basisEquiv (D D' : FramedModuleDeformation ρbar A) :
    D ≃ₗ[A.obj.left] D' :=
  D.basis.equiv D'.basis (_root_.Equiv.refl n)

private theorem basisEquiv_basis (D D' : FramedModuleDeformation ρbar A) (i : n) :
    basisEquiv D D' (D.basis i) = D'.basis i := by
  simp [basisEquiv]

private theorem reduction_basisEquiv (D D' : FramedModuleDeformation ρbar A) (v : D) :
    D'.reduction (basisEquiv D D' v) = D.reduction v :=
  LinearMap.congr_fun (D.basis.ext (f₁ := D'.reduction ∘ₛₗ (basisEquiv D D').toLinearMap)
    (f₂ := D.reduction) fun i ↦ by simp [basisEquiv_basis]) v

/-- Over the residue field `k`, any two framed module deformations are isomorphic. -/
noncomputable def equivOfResidue (D D' : FramedModuleDeformation ρbar (residue Λ k)) :
    D.Equiv D' where
  toLinearEquiv := basisEquiv D D'
  map_action g := LinearMap.congr_fun (D.basis.ext
    (f₁ := (basisEquiv D D').toLinearMap ∘ₗ D.action g)
    (f₂ := D'.action g ∘ₗ (basisEquiv D D').toLinearMap) fun i ↦
      D'.reduction_injective_residue (by
        simp [reduction_basisEquiv, basisEquiv_basis, ModuleDeformation.reduction_action]))
  reduction_apply := reduction_basisEquiv D D'
  map_basis := basisEquiv_basis D D'

end Residue

variable (ρbar A) in
/-- The setoid on framed module deformations given by isomorphism. -/
def isoSetoid : Setoid (FramedModuleDeformation ρbar A) where
  r D D' := Nonempty (D.Equiv D')
  iseqv := ⟨fun D ↦ ⟨Equiv.refl D⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e.trans e'⟩⟩

end FramedModuleDeformation

/-- The *isomorphism classes* of framed module deformations of `ρbar` to `A`. These are the values
of the framed module deformation functor `Def^{mod,□}_ρbar`. -/
-- Exposed as a quotient type: code generation needs its representation in other modules.
@[expose] def FramedModuleDeformationClass (ρbar : G →* GL n k) (A : ArtinLocalAlg Λ k) :=
  Quotient (FramedModuleDeformation.isoSetoid ρbar A)

namespace FramedModuleDeformationClass

variable {ρbar} {A B C : ArtinLocalAlg Λ k}

/-- The isomorphism class of a framed module deformation. -/
def mk (D : FramedModuleDeformation ρbar A) : FramedModuleDeformationClass ρbar A :=
  Quotient.mk _ D

/-- Every isomorphism class is the class of a framed module deformation. -/
theorem mk_surjective :
    Function.Surjective
      (mk : FramedModuleDeformation ρbar A → FramedModuleDeformationClass ρbar A) :=
  Quotient.mk_surjective

/-- Two framed module deformations have the same class exactly when they are isomorphic. -/
theorem mk_eq_mk_iff {D D' : FramedModuleDeformation ρbar A} :
    mk D = mk D' ↔ Nonempty (D.Equiv D') :=
  Quotient.eq

/-- Isomorphic framed module deformations have the same class. -/
theorem mk_eq_mk {D D' : FramedModuleDeformation ρbar A} (e : D.Equiv D') : mk D = mk D' :=
  mk_eq_mk_iff.mpr ⟨e⟩

/-- A function on framed module deformations that is invariant under isomorphism descends to
isomorphism classes. -/
def lift {β : Sort*} (F : FramedModuleDeformation ρbar A → β)
    (hF : ∀ D D' : FramedModuleDeformation ρbar A, D.Equiv D' → F D = F D') :
    FramedModuleDeformationClass ρbar A → β :=
  Quotient.lift F fun D D' ⟨e⟩ ↦ hF D D' e

@[simp]
theorem lift_mk {β : Sort*} (F : FramedModuleDeformation ρbar A → β)
    (hF : ∀ D D' : FramedModuleDeformation ρbar A, D.Equiv D' → F D = F D')
    (D : FramedModuleDeformation ρbar A) : lift F hF (mk D) = F D :=
  (rfl)

/-- The base change of isomorphism classes of framed module deformations along a morphism
`f : A ⟶ B` of `C_Λ`. -/
noncomputable def map (f : A ⟶ B) :
    FramedModuleDeformationClass ρbar A → FramedModuleDeformationClass ρbar B :=
  Quotient.map (FramedModuleDeformation.baseChange f) fun _ _ ⟨e⟩ ↦ ⟨e.baseChange f⟩

@[simp]
theorem map_mk (f : A ⟶ B) (D : FramedModuleDeformation ρbar A) :
    map f (mk D) = mk (D.baseChange f) :=
  (rfl)

/-- Base change of isomorphism classes along the identity is the identity. -/
@[simp]
theorem map_id (c : FramedModuleDeformationClass ρbar A) : map (𝟙 A) c = c := by
  obtain ⟨D, rfl⟩ := mk_surjective c
  exact mk_eq_mk D.baseChangeId

/-- Base change of isomorphism classes along a composite is the composite of the base changes. -/
theorem map_comp (f : A ⟶ B) (g : B ⟶ C) (c : FramedModuleDeformationClass ρbar A) :
    map (f ≫ g) c = map g (map f c) := by
  obtain ⟨D, rfl⟩ := mk_surjective c
  exact mk_eq_mk (D.baseChangeComp f g)

/-- The isomorphism class of the underlying module deformation of a framed module deformation. -/
def forget : FramedModuleDeformationClass ρbar A → ModuleDeformationClass ρbar A :=
  Quotient.map FramedModuleDeformation.toModuleDeformation fun _ _ ⟨e⟩ ↦ ⟨e.toEquiv⟩

@[simp]
theorem forget_mk (D : FramedModuleDeformation ρbar A) :
    forget (mk D) = ModuleDeformationClass.mk D.toModuleDeformation :=
  (rfl)

/-- Every module deformation admits a framing: forgetting the framing is surjective. -/
theorem forget_surjective :
    Function.Surjective (forget : FramedModuleDeformationClass ρbar A → _) :=
  fun c ↦ by
    obtain ⟨D, rfl⟩ := ModuleDeformationClass.mk_surjective c
    obtain ⟨e, he⟩ := D.exists_basis
    exact ⟨mk ⟨D, e, he⟩, rfl⟩

/-- Forgetting the framing commutes with base change. -/
theorem forget_map (f : A ⟶ B) (c : FramedModuleDeformationClass ρbar A) :
    forget (map f c) = ModuleDeformationClass.map f (forget c) := by
  obtain ⟨D, rfl⟩ := mk_surjective c
  rfl

/-- Over the residue field `k` there is at most one isomorphism class of framed module
deformations. -/
instance : Subsingleton (FramedModuleDeformationClass ρbar (residue Λ k)) where
  allEq c c' := by
    obtain ⟨D, rfl⟩ := mk_surjective c
    obtain ⟨D', rfl⟩ := mk_surjective c'
    exact mk_eq_mk (D.equivOfResidue D')

end FramedModuleDeformationClass

/-- Over the residue field `k` there is at most one isomorphism class of module deformations. -/
instance : Subsingleton (ModuleDeformationClass ρbar (residue Λ k)) where
  allEq c c' := by
    obtain ⟨c, rfl⟩ := FramedModuleDeformationClass.forget_surjective c
    obtain ⟨c', rfl⟩ := FramedModuleDeformationClass.forget_surjective c'
    rw [Subsingleton.elim c c']

variable (Λ) in
/-- The *framed module deformation functor* `Def^{mod,□}_ρbar : C_Λ ⥤ Type` of the residual
representation `ρbar`, sending `A` to the isomorphism classes of framed module deformations of
`ρbar` to `A` and a morphism to base change. -/
-- Exposed so that `(framedModuleDeformationFunctor Λ ρbar).obj A` unfolds to
-- `FramedModuleDeformationClass ρbar A` in statements.
@[expose] noncomputable def framedModuleDeformationFunctor :
    ArtinLocalAlg Λ k ⥤ Type (max (v + 1) w x) where
  obj A := FramedModuleDeformationClass ρbar A
  map f := TypeCat.ofHom (FramedModuleDeformationClass.map f)
  map_id A := by
    ext c : 3
    exact FramedModuleDeformationClass.map_id c
  map_comp f g := by
    ext c : 3
    exact FramedModuleDeformationClass.map_comp f g c

variable (Λ) in
@[simp]
theorem framedModuleDeformationFunctor_obj (A : ArtinLocalAlg Λ k) :
    (framedModuleDeformationFunctor Λ ρbar).obj A = FramedModuleDeformationClass ρbar A :=
  (rfl)

variable (Λ) in
@[simp]
theorem framedModuleDeformationFunctor_map_apply {A B : ArtinLocalAlg Λ k} (f : A ⟶ B)
    (c : FramedModuleDeformationClass ρbar A) :
    (framedModuleDeformationFunctor Λ ρbar).map f c = FramedModuleDeformationClass.map f c :=
  (rfl)

variable (Λ) in
/-- The natural transformation `Def^{mod,□}_ρbar ⟶ Def^mod_ρbar` forgetting the framing. -/
noncomputable def forgetFraming :
    framedModuleDeformationFunctor Λ ρbar ⟶ moduleDeformationFunctor Λ ρbar where
  app A := TypeCat.ofHom FramedModuleDeformationClass.forget
  naturality A B f := by
    ext c : 3
    exact FramedModuleDeformationClass.forget_map f c

variable (Λ) in
@[simp]
theorem forgetFraming_app_apply (A : ArtinLocalAlg Λ k) (c : FramedModuleDeformationClass ρbar A) :
    (forgetFraming Λ ρbar).app A c = FramedModuleDeformationClass.forget c :=
  (rfl)

end TauCeti.Deformation
