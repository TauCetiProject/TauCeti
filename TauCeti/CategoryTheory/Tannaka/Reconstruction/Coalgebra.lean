/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.DualCoalgebra
public import TauCeti.Algebra.Coalgebra.Comodule.DirectLimit
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Preadditive
public import TauCeti.CategoryTheory.Tannaka.Hull.Algebra

/-!
# The coalgebra of a fibre functor

Let `C` be an essentially small abelian category and `ω : C ⥤ ModuleCat K` an exact functor with
finite-dimensional values to vector spaces over a field `K`. This file constructs the coalgebra
`B = ω.reconstructionCoalgebra` of `ω` and lifts `ω` to a functor
`ω.toReconstructionComodule : C ⥤ FGComoduleCat K B` to finite right `B`-comodules, whose
underlying vector spaces are the values of `ω`
(`CategoryTheory.Functor.toReconstructionComoduleCompForget₂Iso`).

The coalgebra is the directed colimit of finite-dimensional coalgebras indexed by the finite sets
`s` of objects of a small model of `C`. To `s` belongs the direct sum
`TauCeti.Tannaka.smallModelBiproduct C s` of the objects of `s`, the algebra
`A_s = ω.hullAlgebra (smallModelBiproduct C s)` of endomorphisms of its fibre that come from
natural endomorphisms of `ω` on its hull `⟨X_s⟩` (`CategoryTheory.Functor.hullEndAlgEquiv`), and
the dual coalgebra `A_s^∨ = TauCeti.ConvolutionDual K A_s`. For `s ⊆ t` the hull of `X_s` lies in
the hull of `X_t`; restriction of natural endomorphisms is an algebra map `A_t → A_s`
(`CategoryTheory.Functor.hullRestrict`), whose dual coalgebra map `A_s^∨ → A_t^∨` is the
transition map. These maps need not be injective.

Every object `Y` of `C` lies in some hull `⟨X_s⟩`, so `A_s` acts on `ω Y`, making `ω Y` a right
`A_s^∨`-comodule (`TauCeti.Comodule.ofAlgebraAction`) and, through the canonical map
`A_s^∨ → B`, a `B`-comodule. The resulting coaction does not depend on `s`
(`CategoryTheory.Functor.reconstructionComodule_coact`), and `ω g` is a comodule morphism for
every morphism `g`. No tensor structure on `C` is used.

## Main definitions

* `TauCeti.Tannaka.smallModelBiproduct`: the direct sum of a finite set of objects of a small
  model.
* `CategoryTheory.Functor.ReconstructionStage`: the dual coalgebra `A_s^∨` of a stage.
* `CategoryTheory.Functor.reconstructionTransition`: the transition coalgebra maps.
* `CategoryTheory.Functor.reconstructionCoalgebra`: the coalgebra `B` of `ω`.
* `CategoryTheory.Functor.toReconstructionCoalgebra`: the canonical coalgebra maps `A_s^∨ → B`.
* `CategoryTheory.Functor.liftReconstructionCoalgebra`: the coalgebra map out of `B` induced by
  compatible coalgebra maps out of the stages, unique by
  `CategoryTheory.Functor.reconstructionCoalgebra_coalgHom_ext`.
* `CategoryTheory.Functor.reconstructionStageComodule`: the `A_s^∨`-comodule structure on `ω Y`
  for `Y` in the hull of `X_s`.
* `CategoryTheory.Functor.reconstructionComodule`: the `B`-comodule structure on `ω Y`.
* `CategoryTheory.Functor.toReconstructionComodule`: the lift of `ω` to finite `B`-comodules.
* `CategoryTheory.Functor.toReconstructionComoduleCompForget₂Iso`: its underlying vector spaces
  are the values of `ω`.

## References

* P. Deligne, J. S. Milne, *Tannakian categories*, Lemma 2.13 and the proof of Proposition 2.14.
* A. Huber, S. Müller-Stach, *Periods and Nori motives*, §§7.1–7.4.
-/

public section

open CategoryTheory Limits TauCeti
open scoped TensorProduct

universe w v u

namespace TauCeti.Tannaka

section SmallModel

variable (C : Type v) [Category.{w} C] [EssentiallySmall.{u} C] [Preadditive C]
  [HasFiniteBiproducts C]

/-- The direct sum of the objects of a finite set `s` of objects of the small model of `C`,
regarded as objects of `C`. -/
noncomputable abbrev smallModelBiproduct (s : Finset (SmallModel.{u} C)) : C :=
  ⨁ fun x : s ↦ (equivSmallModel C).inverse.obj x

variable {C}

/-- Every object of a finite set `s` of objects of the small model lies in the hull of
`smallModelBiproduct C s`. -/
theorem subquotientHull_smallModelBiproduct_of_mem {s : Finset (SmallModel.{u} C)}
    {x : SmallModel.{u} C} (hx : x ∈ s) :
    subquotientHull (smallModelBiproduct C s) ((equivSmallModel C).inverse.obj x) :=
  subquotientHull.of_mono (biproduct.ι (fun x : s ↦ (equivSmallModel C).inverse.obj x) ⟨x, hx⟩ ≫
    biproduct.ι (fun _ : Unit ↦ smallModelBiproduct C s) ())

/-- For `s ⊆ t`, the direct sum over `s` lies in the hull of the direct sum over `t`: it is a
direct summand. -/
theorem subquotientHull_smallModelBiproduct_of_le {s t : Finset (SmallModel.{u} C)}
    (h : s ≤ t) : subquotientHull (smallModelBiproduct C t) (smallModelBiproduct C s) := by
  let i : smallModelBiproduct C s ⟶ smallModelBiproduct C t :=
    biproduct.desc fun x ↦ biproduct.ι (fun y : t ↦ (equivSmallModel C).inverse.obj y)
      ⟨x, h x.property⟩
  have : IsSplitMono i := IsSplitMono.mk' ⟨biproduct.lift fun x ↦
    biproduct.π (fun y : t ↦ (equivSmallModel C).inverse.obj y) ⟨x, h x.property⟩, by
      refine biproduct.hom_ext' _ _ fun x ↦ biproduct.hom_ext _ _ fun y ↦ ?_
      by_cases hxy : x = y
      · subst hxy
        simp [i]
      · have hxy' : (⟨x, h x.property⟩ : t) ≠ ⟨y, h y.property⟩ := fun e ↦
          hxy (Subtype.ext (Subtype.mk.inj e))
        simp [i, biproduct.ι_π_ne _ hxy, biproduct.ι_π_ne _ hxy']⟩
  exact subquotientHull.of_mono (i ≫ biproduct.ι (fun _ : Unit ↦ smallModelBiproduct C t) ())

/-- An object `Y` of `C` lies in the hull of the direct sum over every finite set containing its
image in the small model. -/
theorem subquotientHull_smallModelBiproduct {s : Finset (SmallModel.{u} C)} {Y : C}
    (hY : (equivSmallModel C).functor.obj Y ∈ s) :
    subquotientHull (smallModelBiproduct C s) Y :=
  (subquotientHull _).prop_of_epi ((equivSmallModel C).unitIso.inv.app Y)
    (subquotientHull_smallModelBiproduct_of_mem hY)

/-- Any two objects of `C` lie in the hull of a common stage. -/
theorem exists_subquotientHull_smallModelBiproduct (Y Y' : C) :
    ∃ s : Finset (SmallModel.{u} C), subquotientHull (smallModelBiproduct C s) Y ∧
      subquotientHull (smallModelBiproduct C s) Y' := by
  classical
  exact ⟨{(equivSmallModel C).functor.obj Y, (equivSmallModel C).functor.obj Y'},
    subquotientHull_smallModelBiproduct (by simp), subquotientHull_smallModelBiproduct (by simp)⟩

end SmallModel

end TauCeti.Tannaka

namespace CategoryTheory.Functor

open TauCeti.Tannaka

attribute [local instance] Abelian.hasFiniteBiproducts

variable {K : Type u} [Field K] {C : Type v} [Category.{w} C] [EssentiallySmall.{u} C]
  [Abelian C] (ω : C ⥤ ModuleCat.{u} K) [ω.Additive]

/-- The dual coalgebra `A_s^∨` of the stage `s` of the coalgebra of `ω`: the convolution dual of
the algebra `ω.hullAlgebra (smallModelBiproduct C s)`. -/
@[expose] def ReconstructionStage (s : Finset (SmallModel.{u} C)) : Type u :=
  ConvolutionDual K (ω.hullAlgebra (smallModelBiproduct C s))

noncomputable instance (s : Finset (SmallModel.{u} C)) : AddCommGroup (ω.ReconstructionStage s) :=
  inferInstanceAs (AddCommGroup (ConvolutionDual K (ω.hullAlgebra (smallModelBiproduct C s))))

noncomputable instance (s : Finset (SmallModel.{u} C)) : Module K (ω.ReconstructionStage s) :=
  inferInstanceAs (Module K (ConvolutionDual K (ω.hullAlgebra (smallModelBiproduct C s))))

variable [∀ X, Module.Finite K (ω.obj X)]

/-- The stage `s` is the dual coalgebra of the finite-dimensional algebra
`ω.hullAlgebra (smallModelBiproduct C s)`. -/
noncomputable instance (s : Finset (SmallModel.{u} C)) : Coalgebra K (ω.ReconstructionStage s) :=
  inferInstanceAs (Coalgebra K (ConvolutionDual K (ω.hullAlgebra (smallModelBiproduct C s))))

variable [PreservesFiniteLimits ω] [ω.PreservesEpimorphisms]

/-- The transition map of the coalgebra of `ω` from the stage `s` to a larger stage `t`: the
dual of the restriction map `hullAlgebra X_t → hullAlgebra X_s` between the algebras of the
direct sums `X_s` and `X_t`. -/
@[expose] noncomputable def reconstructionTransition (s t : Finset (SmallModel.{u} C))
    (h : s ≤ t) : ω.ReconstructionStage s →ₗc[K] ω.ReconstructionStage t :=
  ConvolutionDual.coalgMap K (ω.hullRestrict (subquotientHull_smallModelBiproduct_of_le h))

/-- The transition map from a stage to itself is the identity. -/
@[simp]
theorem reconstructionTransition_self (s : Finset (SmallModel.{u} C)) (h : s ≤ s) :
    ω.reconstructionTransition s s h = CoalgHom.id K _ := by
  simp only [reconstructionTransition, hullRestrict_self]
  exact ConvolutionDual.coalgMap_id K

/-- The transition maps compose. -/
@[simp]
theorem reconstructionTransition_comp {s t u : Finset (SmallModel.{u} C)} (hst : s ≤ t)
    (htu : t ≤ u) :
    (ω.reconstructionTransition t u htu).comp (ω.reconstructionTransition s t hst) =
      ω.reconstructionTransition s u (hst.trans htu) := by
  have := ConvolutionDual.coalgMap_comp K (ω.hullRestrict
    (subquotientHull_smallModelBiproduct_of_le hst))
    (ω.hullRestrict (subquotientHull_smallModelBiproduct_of_le htu))
  rw [hullRestrict_comp] at this
  exact this.symm

/-- The stages and transition maps form a directed system. -/
instance : DirectedSystem ω.ReconstructionStage
    fun s t h ↦ (ω.reconstructionTransition s t h : ω.ReconstructionStage s →ₗ[K] _) where
  map_self s x := by
    rw [CoalgHom.coe_linearMapOfClass, reconstructionTransition_self, CoalgHom.id_apply]
  map_map {u t s} hst htu x := by
    rw [CoalgHom.coe_linearMapOfClass, CoalgHom.coe_linearMapOfClass,
      CoalgHom.coe_linearMapOfClass, ← reconstructionTransition_comp ω hst htu,
      CoalgHom.comp_apply]

open scoped Classical in
/-- **The coalgebra of a fibre functor.** The directed colimit, over the finite sets `s` of
objects of the small model of `C`, of the dual coalgebras of the algebras
`ω.hullAlgebra (smallModelBiproduct C s)`, along `reconstructionTransition`. -/
@[expose] def reconstructionCoalgebra : Type u :=
  Module.DirectLimit ω.ReconstructionStage
    fun s t h ↦ (ω.reconstructionTransition s t h : ω.ReconstructionStage s →ₗ[K] _)

open scoped Classical in
noncomputable instance : AddCommGroup ω.reconstructionCoalgebra :=
  inferInstanceAs (AddCommGroup (Module.DirectLimit ω.ReconstructionStage
    fun s t h ↦ (ω.reconstructionTransition s t h : ω.ReconstructionStage s →ₗ[K] _)))

open scoped Classical in
noncomputable instance : Module K ω.reconstructionCoalgebra :=
  inferInstanceAs (Module K (Module.DirectLimit ω.ReconstructionStage
    fun s t h ↦ (ω.reconstructionTransition s t h : ω.ReconstructionStage s →ₗ[K] _)))

open scoped Classical in
/-- The coalgebra structure of the directed colimit of the stages
(`Module.DirectLimit.instCoalgebra`). -/
noncomputable instance : Coalgebra K ω.reconstructionCoalgebra :=
  @Module.DirectLimit.instCoalgebra K _ _ _ _ ω.ReconstructionStage _ _ (fun _ ↦ inferInstance)
    fun s t h ↦ ω.reconstructionTransition s t h

open scoped Classical in
/-- The canonical coalgebra map from the dual coalgebra of the stage `s` to the coalgebra of
`ω`. -/
@[expose] noncomputable def toReconstructionCoalgebra (s : Finset (SmallModel.{u} C)) :
    ω.ReconstructionStage s →ₗc[K] ω.reconstructionCoalgebra :=
  @Module.DirectLimit.ofCoalgHom K _ _ _ _ ω.ReconstructionStage _ _ (fun _ ↦ inferInstance)
    (fun s t h ↦ ω.reconstructionTransition s t h) s

/-- The canonical maps are compatible with the transition maps. -/
@[simp]
theorem toReconstructionCoalgebra_comp_reconstructionTransition {s t : Finset (SmallModel.{u} C)}
    (h : s ≤ t) :
    (ω.toReconstructionCoalgebra t).comp (ω.reconstructionTransition s t h) =
      ω.toReconstructionCoalgebra s := by
  classical
  exact @Module.DirectLimit.ofCoalgHom_comp K _ _ _ _ ω.ReconstructionStage _ _
    (fun _ ↦ inferInstance) (fun s t h ↦ ω.reconstructionTransition s t h) s t h

section Lift

variable {D : Type*} [AddCommMonoid D] [Module K D] [Coalgebra K D]
  (g : ∀ s, ω.ReconstructionStage s →ₗc[K] D)
  (hg : ∀ s t h, (g t).comp (ω.reconstructionTransition s t h) = g s)

open scoped Classical in
/-- **The universal property of the coalgebra of `ω`.** A family of coalgebra maps out of the
stages, compatible with the transition maps, induces a coalgebra map out of the coalgebra
of `ω` (`Module.DirectLimit.liftCoalgHom`). -/
noncomputable def liftReconstructionCoalgebra : ω.reconstructionCoalgebra →ₗc[K] D :=
  @Module.DirectLimit.liftCoalgHom K _ _ _ _ ω.ReconstructionStage _ _ (fun _ ↦ inferInstance)
    (fun s t h ↦ ω.reconstructionTransition s t h) D _ _ _ g hg

/-- The coalgebra map induced by compatible stage maps restricts to them on each stage. -/
@[simp]
theorem liftReconstructionCoalgebra_comp_toReconstructionCoalgebra
    (s : Finset (SmallModel.{u} C)) :
    (ω.liftReconstructionCoalgebra g hg).comp (ω.toReconstructionCoalgebra s) = g s := by
  classical
  exact @Module.DirectLimit.liftCoalgHom_comp_ofCoalgHom K _ _ _ _ ω.ReconstructionStage _ _
    (fun _ ↦ inferInstance) (fun s t h ↦ ω.reconstructionTransition s t h) D _ _ _ g hg s

/-- The coalgebra map induced by compatible stage maps, evaluated on the image of a stage. -/
@[simp]
theorem liftReconstructionCoalgebra_toReconstructionCoalgebra_apply
    (s : Finset (SmallModel.{u} C)) (x : ω.ReconstructionStage s) :
    ω.liftReconstructionCoalgebra g hg (ω.toReconstructionCoalgebra s x) = g s x :=
  CoalgHom.congr_fun (ω.liftReconstructionCoalgebra_comp_toReconstructionCoalgebra g hg s) x

/-- Coalgebra maps out of the coalgebra of `ω` agree when they agree on every stage. -/
@[ext]
theorem reconstructionCoalgebra_coalgHom_ext {φ ψ : ω.reconstructionCoalgebra →ₗc[K] D}
    (h : ∀ s, φ.comp (ω.toReconstructionCoalgebra s) = ψ.comp (ω.toReconstructionCoalgebra s)) :
    φ = ψ := by
  classical
  exact @Module.DirectLimit.coalgHom_ext K _ _ _ _ ω.ReconstructionStage _ _
    (fun _ ↦ inferInstance) (fun s t h ↦ ω.reconstructionTransition s t h) D _ _ _ φ ψ h

end Lift

/-! ### The comodules of the values of `ω` -/

/-- For `Y` in the hull of `X_s`, the right comodule over the dual coalgebra `A_s^∨` of the stage
`s` on the fibre `ω Y` defined by the action of `A_s = ω.hullAlgebra X_s`
(`CategoryTheory.Functor.hullAction`). -/
@[expose, implicit_reducible]
noncomputable def reconstructionStageComodule {s : Finset (SmallModel.{u} C)} {Y : C}
    (h : subquotientHull (smallModelBiproduct C s) Y) :
    Comodule K (ω.ReconstructionStage s) (ω.obj Y) :=
  Comodule.ofAlgebraAction (ω.hullAction h)

/-- The stage comodules are compatible with the transition maps: corestricting the comodule of
the stage `s` along the transition map to a larger stage `t` gives the comodule of `t`. -/
theorem lTensor_reconstructionTransition_comp_coact {s t : Finset (SmallModel.{u} C)}
    (hst : s ≤ t) {Y : C} (h : subquotientHull (smallModelBiproduct C s) Y)
    (h' : subquotientHull (smallModelBiproduct C t) Y) :
    (ω.reconstructionTransition s t hst).toLinearMap.lTensor (ω.obj Y) ∘ₗ
        (ω.reconstructionStageComodule h).coact = (ω.reconstructionStageComodule h').coact := by
  have hc := congrArg (·.coact) (Comodule.corestrict_ofAlgebraAction
    (ω.hullRestrict (subquotientHull_smallModelBiproduct_of_le hst)) (ω.hullAction h))
  rw [ω.hullAction_comp_hullRestrict] at hc
  -- `hc` is the same equation, with the coaction of the corestriction unfolded to
  -- `lTensor ∘ coact` and the stage written as the convolution dual it is defined to be.
  exact hc

/-- A linear map between the fibres of two members of the hull of `X_s` is a morphism of the
stage comodules exactly when it commutes with the actions of `ω.hullAlgebra X_s`. -/
theorem map_comp_reconstructionStageComodule_coact_iff {s : Finset (SmallModel.{u} C)}
    {Y Y' : C} (h : subquotientHull (smallModelBiproduct C s) Y)
    (h' : subquotientHull (smallModelBiproduct C s) Y') (φ : ω.obj Y →ₗ[K] ω.obj Y') :
    TensorProduct.map φ LinearMap.id ∘ₗ (ω.reconstructionStageComodule h).coact =
        (ω.reconstructionStageComodule h').coact ∘ₗ φ ↔
      ∀ a, φ ∘ₗ ω.hullAction h a = ω.hullAction h' a ∘ₗ φ :=
  Comodule.map_coact_ofAlgebraAction_iff (ω.hullAction h) (ω.hullAction h') φ

/-- For a morphism `g` between members of the hull of `X_s`, the linear map `ω g` is a morphism of
the stage comodules. -/
theorem map_comp_reconstructionStageComodule_coact {s : Finset (SmallModel.{u} C)} {Y Y' : C}
    (h : subquotientHull (smallModelBiproduct C s) Y)
    (h' : subquotientHull (smallModelBiproduct C s) Y') (g : Y ⟶ Y') :
    TensorProduct.map (ω.map g).hom LinearMap.id ∘ₗ (ω.reconstructionStageComodule h).coact =
      (ω.reconstructionStageComodule h').coact ∘ₗ (ω.map g).hom :=
  (ω.map_comp_reconstructionStageComodule_coact_iff h h' (ω.map g).hom).2
    fun a ↦ LinearMap.ext fun y ↦ ω.map_hullAction_apply h h' g a y

/-- Passing from the stage `s` to a larger stage `t` does not change the `B`-coaction of the
fibre of a member `Y` of the hull of `X_s`. -/
private theorem lTensor_comp_coact_of_le {s t : Finset (SmallModel.{u} C)} (hst : s ≤ t)
    {Y : C} (h : subquotientHull (smallModelBiproduct C s) Y)
    (h' : subquotientHull (smallModelBiproduct C t) Y) :
    (ω.toReconstructionCoalgebra s).toLinearMap.lTensor (ω.obj Y) ∘ₗ
        (ω.reconstructionStageComodule h).coact =
      (ω.toReconstructionCoalgebra t).toLinearMap.lTensor (ω.obj Y) ∘ₗ
        (ω.reconstructionStageComodule h').coact := by
  rw [← ω.lTensor_reconstructionTransition_comp_coact hst h h', ← LinearMap.comp_assoc,
    ← LinearMap.lTensor_comp, ← ω.toReconstructionCoalgebra_comp_reconstructionTransition hst]
  simp only [CoalgHom.toLinearMap_eq_ofClass, CoalgHom.comp_toLinearMap]

/-- The right `B`-comodule structure on the fibre `ω Y`, for the coalgebra `B` of `ω`: the
comodule `reconstructionStageComodule` of a stage `s` with `Y` in the hull of `X_s`, corestricted
along the canonical map to `B`. It does not depend on `s`
(`CategoryTheory.Functor.reconstructionComodule_coact`). -/
@[expose, implicit_reducible]
noncomputable def reconstructionComodule (Y : C) :
    Comodule K ω.reconstructionCoalgebra (ω.obj Y) :=
  letI := ω.reconstructionStageComodule
    (subquotientHull_smallModelBiproduct (Y := Y) (Finset.mem_singleton_self _))
  Comodule.Corestrict (C := ω.ReconstructionStage {(equivSmallModel C).functor.obj Y})
    (ω.toReconstructionCoalgebra _)

/-- **Finite-piece comodules.** For every stage `s` whose hull contains `Y`, the coaction of
`ω Y` is the coaction of the comodule of the stage `s`, followed by the canonical map to `B`. -/
theorem reconstructionComodule_coact {s : Finset (SmallModel.{u} C)} {Y : C}
    (h : subquotientHull (smallModelBiproduct C s) Y) :
    (ω.reconstructionComodule Y).coact =
      (ω.toReconstructionCoalgebra s).toLinearMap.lTensor (ω.obj Y) ∘ₗ
        (ω.reconstructionStageComodule h).coact := by
  classical
  let := ω.reconstructionStageComodule
    (subquotientHull_smallModelBiproduct (Y := Y) (Finset.mem_singleton_self _))
  have hu : subquotientHull (smallModelBiproduct C ({(equivSmallModel C).functor.obj Y} ∪ s)) Y :=
    subquotientHull_le_of_mem (subquotientHull_smallModelBiproduct_of_le
      Finset.subset_union_right) _ h
  exact (Comodule.corestrictCoact_eq_lTensor _).trans
    ((lTensor_comp_coact_of_le ω Finset.subset_union_left _ hu).trans
      (lTensor_comp_coact_of_le ω Finset.subset_union_right h hu).symm)

/-- For every morphism `g`, the linear map `ω g` commutes with the coactions of
`reconstructionComodule`. -/
theorem map_comp_reconstructionComodule_coact {Y Y' : C} (g : Y ⟶ Y') :
    TensorProduct.map (ω.map g).hom LinearMap.id ∘ₗ (ω.reconstructionComodule Y).coact =
      (ω.reconstructionComodule Y').coact ∘ₗ (ω.map g).hom := by
  obtain ⟨s, h, h'⟩ := exists_subquotientHull_smallModelBiproduct Y Y'
  have hcomm : (ω.toReconstructionCoalgebra s).toLinearMap.lTensor (ω.obj Y') ∘ₗ
      TensorProduct.map (ω.map g).hom LinearMap.id =
        TensorProduct.map (ω.map g).hom LinearMap.id ∘ₗ
          (ω.toReconstructionCoalgebra s).toLinearMap.lTensor (ω.obj Y) :=
    TensorProduct.ext' fun _ _ ↦ rfl
  rw [ω.reconstructionComodule_coact h, ω.reconstructionComodule_coact h',
    ← LinearMap.comp_assoc, ← hcomm, LinearMap.comp_assoc,
    ω.map_comp_reconstructionStageComodule_coact h h' g, LinearMap.comp_assoc]

/-- **The lift of a fibre functor to comodules.** The functor sending `Y` to the fibre `ω Y` with
the coaction `reconstructionComodule` of the coalgebra of `ω`, and a morphism `g` to `ω g`. -/
@[expose] noncomputable def toReconstructionComodule :
    C ⥤ FGComoduleCat.{u, u, u} K ω.reconstructionCoalgebra where
  obj Y :=
    letI := ω.reconstructionComodule Y
    FGComoduleCat.of (ω.obj Y)
  map {Y Y'} g :=
    letI := ω.reconstructionComodule Y
    letI := ω.reconstructionComodule Y'
    FGComoduleCat.ofHom
      { toLinearMap := (ω.map g).hom
        map_coact := ω.map_comp_reconstructionComodule_coact g }
  -- Identities and composites of comodule morphisms act as identities and composites of
  -- functions (`TauCeti.ComoduleCat.id_apply`, `TauCeti.ComoduleCat.comp_apply`).
  map_id Y := by
    ext y
    simp
    rfl
  map_comp g g' := by
    ext y
    simp
    rfl

/-- The comodule attached to `Y` has the coaction `reconstructionComodule`. -/
theorem coact_toReconstructionComodule_obj (Y : C) :
    Comodule.coact (R := K) (C := ω.reconstructionCoalgebra)
        (M := ω.toReconstructionComodule.obj Y) = (ω.reconstructionComodule Y).coact :=
  (rfl)

/-- The comodule morphism attached to `g` acts as `ω g`. -/
@[simp]
theorem toReconstructionComodule_map_apply {Y Y' : C} (g : Y ⟶ Y')
    (y : ω.toReconstructionComodule.obj Y) :
    ω.toReconstructionComodule.map g y = (ω.map g).hom y :=
  (rfl)

/-- **The comparison of fibre functors.** The vector space underlying the comodule attached to
`Y` is `ω Y`; the components are the identity on elements. -/
noncomputable def toReconstructionComoduleCompForget₂Iso :
    ω.toReconstructionComodule ⋙
        forget₂ (FGComoduleCat.{u, u, u} K ω.reconstructionCoalgebra) (ModuleCat.{u} K) ≅ ω :=
  NatIso.ofComponents (fun _ ↦
    { hom := ModuleCat.homEquiv.symm LinearMap.id
      inv := ModuleCat.homEquiv.symm LinearMap.id })
    -- The components are identities on elements, so naturality is the equation `ω g = ω g`.
    fun _ ↦ by
      ext
      rfl

/-- The components of `toReconstructionComoduleCompForget₂Iso` are the identity on elements. -/
@[simp]
theorem toReconstructionComoduleCompForget₂Iso_hom_app_hom_apply (Y : C)
    (y : (ω.toReconstructionComodule ⋙
      forget₂ (FGComoduleCat.{u, u, u} K ω.reconstructionCoalgebra) (ModuleCat.{u} K)).obj Y) :
    dsimp% (ω.toReconstructionComoduleCompForget₂Iso.hom.app Y).hom y = y :=
  (rfl)

/-- The inverse components of `toReconstructionComoduleCompForget₂Iso` are the identity on
elements. -/
@[simp]
theorem toReconstructionComoduleCompForget₂Iso_inv_app_hom_apply (Y : C) (y : ω.obj Y) :
    dsimp% (ω.toReconstructionComoduleCompForget₂Iso.inv.app Y).hom y = y :=
  (rfl)

end CategoryTheory.Functor
