/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Fibration
public import TauCeti.AlgebraicTopology.LocalCoefficient.Constant
public import TauCeti.AlgebraicTopology.Singular.Fibration.LocalSystem
public import TauCeti.AlgebraicTopology.Singular.Torus.Family.Homology

/-!
# Trivialization of the fiber homology local system of a torus family

For a continuous family `P : Y → Λ →ₗ[ℤ] E` of full lattices in a finite-dimensional real normed
space `E` with `Λ` finite free over `ℤ`, `TauCeti.isHurewiczFibration_torusFamilyProjection` shows
that `π : (Y × E)/Λ → Y` is a Hurewicz fibration. For any lifting function `L` of `π`, this file
promotes `TauCeti.torusFamilyHomologyMarking` and `TauCeti.torusFamilyMarking` to global
trivializations of `TauCeti.fiberLocalSystem L ℤ n`:

* `TauCeti.torusFamilyHomologyMarking_transport`, `TauCeti.torusFamilyMarking_transport`: Hurewicz
  transport along any path preserves the canonical markings.
* `TauCeti.torusFamilyHomologyLocalSystemIso`, `TauCeti.torusFamilyFirstHomologyLocalSystemIso`:
  canonical trivializations by `⋀[ℤ]^n Λ` and `Λ`, with trivial monodromy
  (`TauCeti.isTrivial_monodromyRepresentation_torusFamilyFiberLocalSystem`,
  `TauCeti.torusFamilyHomologyMonodromyIsoTrivial`,
  `TauCeti.torusFamilyFirstHomologyMonodromyIsoTrivial`).
* Naturality under base change (`TauCeti.torusFamilyBaseChange_fiberLocalSystemMap_comp_iso`,
  `TauCeti.torusFamilyBaseChange_fiberLocalSystemMap_comp_firstHomologyIso`,
  `TauCeti.isIso_torusFamilyBaseChangeCommSq_fiberLocalSystemMap`) and lattice re-marking
  (`TauCeti.torusFamilyRemark_fiberLocalSystemMap_comp_iso`,
  `TauCeti.torusFamilyRemark_fiberLocalSystemMap_comp_firstHomologyIso`).
* `TauCeti.torusFamilyMarkingIsoEquivAut`: over path-connected `Y`, global markings of
  `TauCeti.fiberLocalSystem L ℤ 1` by `Λ` correspond bijectively to `Λ ≃ₗ[ℤ] Λ`.

As in `TauCeti.AlgebraicTopology.Singular.Torus.Family.Basic`, spaces carrying integer singular
chains live in `Type`.

## References

* C. Birkenhake and H. Lange, *Complex Abelian Varieties*, 2nd ed., Springer, 2004, §§1.1, 1.3, 8.
* C. Voisin, *Hodge Theory and Complex Algebraic Geometry I*, CUP, 2002, §9.1.
-/

public section

noncomputable section

open CategoryTheory Function TauCeti.LocalCoefficientSystem

namespace TauCeti

/-! ### Invariance under Hurewicz transport and trivialization of the fiber local system -/

section LocalSystem

variable {Y Λ E : Type} [TopologicalSpace Y] [AddCommGroup Λ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))

/-- `torusFamilyHomologyMarking` typed on `(TopCat.ofHom ...).fiber y`. -/
private def torusFamilyFiberHomologyMarking (y : Y) (n : ℕ) :
    letI := periodAddAction P
    ((singularChains ℤ).obj ((TopCat.ofHom ⟨torusFamilyProjection P,
      continuous_torusFamilyProjection P⟩).fiber y)).homology n ≃ₗ[ℤ] ⋀[ℤ]^n Λ :=
  torusFamilyHomologyMarking P hcont hinj y n

@[simp]
private theorem torusFamilyFiberHomologyMarking_apply (y : Y) (n : ℕ)
    (c : letI := periodAddAction P; ((singularChains ℤ).obj ((TopCat.ofHom
      ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).fiber y)).homology n) :
    letI := periodAddAction P
    torusFamilyFiberHomologyMarking P hcont hinj y n c =
      torusFamilyHomologyMarking P hcont hinj y n c :=
  rfl

variable [Module.Free ℤ Λ] [Module.Finite ℤ Λ]

/-- **Hurewicz transport preserves the canonical homology marking.** For any Hurewicz lifting
function `L` of `torusFamilyProjection P` and any path `γ : Path y₀ y₁`, the map induced on `Hₙ` by
`L.transport γ` intertwines the canonical markings over `y₀` and `y₁`. -/
theorem torusFamilyHomologyMarking_transport {y₀ y₁ : Y}
    (L : letI := periodAddAction P; LiftingFunction
      (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
    (γ : Path y₀ y₁) (n : ℕ)
    (c : letI := periodAddAction P; ((singularChains ℤ).obj ((TopCat.ofHom
      ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).fiber y₀)).homology n) :
    letI := periodAddAction P
    torusFamilyHomologyMarking P hcont hinj y₁ n
        (ContinuousMap.singularHomologyMap ℤ n (L.transport γ) c) =
      torusFamilyHomologyMarking P hcont hinj y₀ n c := by
  let _ := periodAddAction P
  rw [LinearMap.congr_fun (ContinuousMap.singularHomologyMap_eq_of_homotopic ℤ n
    (L.transport_homotopic_of_liftingFunction (torusFamilyLiftingFunction P hcont hinj) γ)) c]
  let g : C({z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y₀},
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y₁}) :=
    ⟨fun x ↦ (torusFamilyLiftingFunction P hcont hinj).transport γ x,
      ((torusFamilyLiftingFunction P hcont hinj).transport γ).continuous⟩
  let c₀ : ((singularChains ℤ).obj (TopCat.of
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y₀})).homology n := c
  -- `(TopCat.ofHom ...).fiber y₀` is definitionally the subtype `TopCat.of {z | ... = y₀}` on
  -- which `torusFamilyHomologyMarking` is stated.
  change torusFamilyHomologyMarking P hcont hinj y₁ n (ContinuousMap.singularHomologyMap ℤ n g c₀) =
    torusFamilyHomologyMarking P hcont hinj y₀ n c₀
  exact (torusFamilyHomologyMarking_map P hcont hinj y₀ P hcont hinj y₁ LinearMap.id
    (φ := (torusFamilyParallelTransport P hinj y₀ y₁).toLinearMap.restrictScalars ℤ)
    (torusFamilyParallelTransport P hinj y₀ y₁).continuous
    (torusFamilyParallelTransport_period P hinj y₀ y₁) g
    (torusFamilyLiftingFunction_transport_mk P hcont hinj γ) n c₀).trans (by simp)

/-- **Hurewicz transport preserves the degree-one marking.** -/
theorem torusFamilyMarking_transport {y₀ y₁ : Y}
    (L : letI := periodAddAction P; LiftingFunction
      (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
    (γ : Path y₀ y₁)
    (c : letI := periodAddAction P; ((singularChains ℤ).obj ((TopCat.ofHom
      ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).fiber y₀)).homology 1) :
    letI := periodAddAction P
    torusFamilyMarking P hcont hinj y₁ (ContinuousMap.singularHomologyMap ℤ 1 (L.transport γ) c) =
      torusFamilyMarking P hcont hinj y₀ c :=
  letI := periodAddAction P
  (oneEquiv_torusFamilyHomologyMarking P hcont hinj y₁ _).symm.trans <|
    (congrArg (exteriorPower.oneEquiv ℤ Λ)
      (torusFamilyHomologyMarking_transport P hcont hinj L γ 1 c)).trans
      (oneEquiv_torusFamilyHomologyMarking P hcont hinj y₀ c)

variable (L : letI := periodAddAction P; LiftingFunction
  (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)

/-- **Canonical trivialization of the `n`-th fiber homology local system** of a torus family,
identifying `TauCeti.fiberLocalSystem L ℤ n` with the constant local system `⋀[ℤ]^n Λ` over `Y`. -/
def torusFamilyHomologyLocalSystemIso (n : ℕ) :
    letI := periodAddAction P
    fiberLocalSystem L ℤ n ≅
      (constantFunctor (TopCat.of Y)).obj (ModuleCat.of ℤ (⋀[ℤ]^n Λ)) :=
  letI := periodAddAction P
  NatIso.ofComponents
    (fun b ↦ fiberLocalSystemSingularObjIso L ℤ n b ≪≫
      (torusFamilyFiberHomologyMarking P hcont hinj b.as n).toModuleIso)
    (by
      intro b₀ b₁ q
      induction q using Path.Homotopic.Quotient.ind with | mk γ =>
      dsimp [constantFunctor]
      ext x
      simp only [LinearEquiv.toModuleIso_hom, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom,
        LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        torusFamilyFiberHomologyMarking_apply, Category.comp_id, SetLike.coe_eq_coe]
      exact (congrArg (torusFamilyHomologyMarking P hcont hinj b₁.as n)
        (fiberLocalSystemSingularObjIso_hom_map_mk L ℤ n γ x)).trans
        (torusFamilyHomologyMarking_transport P hcont hinj L γ n _))

theorem torusFamilyHomologyLocalSystemIso_hom_app_apply
    (n : ℕ) (b : FundamentalGroupoid (TopCat.of Y))
    (x : letI := periodAddAction P; (fiberLocalSystem L ℤ n).obj b) :
    letI := periodAddAction P
    (torusFamilyHomologyLocalSystemIso P hcont hinj L n).hom.app b x =
      torusFamilyHomologyMarking P hcont hinj b.as n
        ((fiberLocalSystemSingularObjIso L ℤ n b).hom x) := by
  let _ := periodAddAction P
  -- `(NatIso.ofComponents app _).hom.app b` is definitionally `(app b).hom`, and typing its
  -- codomain as `ModuleCat.of ℤ _` crosses `((constantFunctor _).obj M).obj b = M`.
  let f : (fiberLocalSystem L ℤ n).obj b ⟶ ModuleCat.of ℤ (⋀[ℤ]^n Λ) :=
    (fiberLocalSystemSingularObjIso L ℤ n b ≪≫
      (torusFamilyFiberHomologyMarking P hcont hinj b.as n).toModuleIso).hom
  change f x = _
  simp [f]

theorem torusFamilyHomologyLocalSystemIso_inv_app_apply
    (n : ℕ) (b : FundamentalGroupoid (TopCat.of Y)) (w : ⋀[ℤ]^n Λ) :
    letI := periodAddAction P
    (torusFamilyHomologyLocalSystemIso P hcont hinj L n).inv.app b w =
      (fiberLocalSystemSingularObjIso L ℤ n b).inv
        ((torusFamilyHomologyMarking P hcont hinj b.as n).symm w) := by
  let _ := periodAddAction P
  -- Type the component isomorphism with codomain `ModuleCat.of ℤ _` across `constantFunctor`.
  let e : (fiberLocalSystem L ℤ n).obj b ≅ ModuleCat.of ℤ (⋀[ℤ]^n Λ) :=
    (torusFamilyHomologyLocalSystemIso P hcont hinj L n).app b
  change e.inv w = _
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  rw [e.inv_hom_id_apply]
  exact (((torusFamilyHomologyMarking P hcont hinj b.as n).apply_symm_apply w).symm.trans
    (congrArg (torusFamilyHomologyMarking P hcont hinj b.as n)
      ((fiberLocalSystemSingularObjIso L ℤ n b).inv_hom_id_apply _)).symm).trans
    (torusFamilyHomologyLocalSystemIso_hom_app_apply P hcont hinj L n b _).symm

/-- **Canonical trivialization of the first fiber homology local system** of a torus family,
identifying `TauCeti.fiberLocalSystem L ℤ 1` with the constant local system `Λ` over `Y`. -/
def torusFamilyFirstHomologyLocalSystemIso :
    letI := periodAddAction P
    fiberLocalSystem L ℤ 1 ≅ (constantFunctor (TopCat.of Y)).obj (ModuleCat.of ℤ Λ) :=
  letI := periodAddAction P
  torusFamilyHomologyLocalSystemIso P hcont hinj L 1 ≪≫
    (constantFunctor (TopCat.of Y)).mapIso (exteriorPower.oneEquiv ℤ Λ).toModuleIso

theorem torusFamilyFirstHomologyLocalSystemIso_hom_app_apply (b : FundamentalGroupoid (TopCat.of Y))
    (x : letI := periodAddAction P; (fiberLocalSystem L ℤ 1).obj b) :
    letI := periodAddAction P
    (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L).hom.app b x =
      torusFamilyMarking P hcont hinj b.as ((fiberLocalSystemSingularObjIso L ℤ 1 b).hom x) := by
  let _ := periodAddAction P
  simp only [torusFamilyFirstHomologyLocalSystemIso, Iso.trans_hom, Functor.mapIso_hom,
    NatTrans.comp_app, ModuleCat.comp_apply, torusFamilyHomologyLocalSystemIso_hom_app_apply]
  exact (ConcreteCategory.congr_hom
    (constantFunctor_map_app (TopCat.of Y) (exteriorPower.oneEquiv ℤ Λ).toModuleIso.hom b) _).trans
    (oneEquiv_torusFamilyHomologyMarking P hcont hinj b.as _)

theorem torusFamilyFirstHomologyLocalSystemIso_inv_app_apply
    (b : FundamentalGroupoid (TopCat.of Y)) (l : Λ) :
    letI := periodAddAction P
    (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L).inv.app b l =
      (fiberLocalSystemSingularObjIso L ℤ 1 b).inv
        ((torusFamilyMarking P hcont hinj b.as).symm l) := by
  let _ := periodAddAction P
  -- As above, type the component isomorphism with codomain `ModuleCat.of ℤ Λ`.
  let e : (fiberLocalSystem L ℤ 1).obj b ≅ ModuleCat.of ℤ Λ :=
    (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L).app b
  change e.inv l = _
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  rw [e.inv_hom_id_apply]
  exact ((LinearEquiv.apply_symm_apply (torusFamilyMarking P hcont hinj b.as) l).symm.trans
    (congrArg (torusFamilyMarking P hcont hinj b.as)
      ((fiberLocalSystemSingularObjIso L ℤ 1 b).inv_hom_id_apply _)).symm).trans
    (torusFamilyFirstHomologyLocalSystemIso_hom_app_apply P hcont hinj L b _).symm

include hcont hinj in
/-- **Trivial monodromy.** In every degree `n`, the monodromy representation of the fiber homology
local system of a continuous family of full lattices is trivial. -/
theorem isTrivial_monodromyRepresentation_torusFamilyFiberLocalSystem (n : ℕ) (y : Y) :
    letI := periodAddAction P
    (monodromyRepresentation (fiberLocalSystem L ℤ n) (y : TopCat.of Y)).IsTrivial :=
  letI := periodAddAction P
  isTrivial_monodromyRepresentation_of_iso_constant
    (torusFamilyHomologyLocalSystemIso P hcont hinj L n) (y : TopCat.of Y)

/-- The `n`-th monodromy representation of a torus family is isomorphic in `Rep` to the trivial
representation of `π₁(Y, y)` on `⋀[ℤ]^n Λ`. -/
def torusFamilyHomologyMonodromyIsoTrivial (n : ℕ) (y : Y) :
    letI := periodAddAction P
    (monodromyFunctor ℤ (TopCat.of Y) y).obj (fiberLocalSystem L ℤ n) ≅
      (Rep.trivialFunctor ℤ (FundamentalGroup (TopCat.of Y) y)).obj (ModuleCat.of ℤ (⋀[ℤ]^n Λ)) :=
  letI := periodAddAction P
  monodromyIsoTrivial (torusFamilyHomologyLocalSystemIso P hcont hinj L n) (y : TopCat.of Y)

/-- The degree-one monodromy representation of a torus family is isomorphic in `Rep` to the trivial
representation of `π₁(Y, y)` on `Λ`. -/
def torusFamilyFirstHomologyMonodromyIsoTrivial (y : Y) :
    letI := periodAddAction P
    (monodromyFunctor ℤ (TopCat.of Y) y).obj (fiberLocalSystem L ℤ 1) ≅
      (Rep.trivialFunctor ℤ (FundamentalGroup (TopCat.of Y) y)).obj (ModuleCat.of ℤ Λ) :=
  letI := periodAddAction P
  monodromyIsoTrivial (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L) (y : TopCat.of Y)

end LocalSystem

/-! ### Naturality under continuous base change -/

section BaseChange

variable {Y Z E : Type} [TopologicalSpace Y] [TopologicalSpace Z]

section

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Λ : Type} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y)) (f : C(Z, Y))
  (L : letI := periodAddAction P; LiftingFunction
    (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
  (L' : letI := periodAddAction (P ∘ f); LiftingFunction
    (TopCat.ofHom ⟨torusFamilyProjection (P ∘ f), continuous_torusFamilyProjection (P ∘ f)⟩).hom)

/-- **Base-change naturality of the local-system trivialization.** For any continuous map
`f : C(Z, Y)`, the comparison morphism `CommSq.fiberLocalSystemMap` of
`TauCeti.torusFamilyBaseChangeCommSq` is an isomorphism compatible with the canonical
trivializations by `⋀[ℤ]^n Λ`. -/
theorem torusFamilyBaseChange_fiberLocalSystemMap_comp_iso (n : ℕ) :
    letI := periodAddAction P; letI := periodAddAction (P ∘ f)
    (torusFamilyBaseChangeCommSq P f).fiberLocalSystemMap L' L ℤ n ≫
        (pullback (TopCat.ofHom f).hom).map
          (torusFamilyHomologyLocalSystemIso P hcont hinj L n).hom ≫
        (pullbackConstantIso (TopCat.ofHom f).hom (ModuleCat.of ℤ (⋀[ℤ]^n Λ))).hom =
      (torusFamilyHomologyLocalSystemIso (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
        (fun z ↦ hinj (f z)) L' n).hom := by
  let _ := periodAddAction P; let _ := periodAddAction (P ∘ f)
  ext b x
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hconst := ConcreteCategory.congr_hom
    (pullbackConstantIso_hom_app (TopCat.ofHom f).hom (ModuleCat.of ℤ (⋀[ℤ]^n Λ)) b)
    (((pullback (TopCat.ofHom f).hom).map
      (torusFamilyHomologyLocalSystemIso P hcont hinj L n).hom).app b
      (((torusFamilyBaseChangeCommSq P f).fiberLocalSystemMap L' L ℤ n).app b x))
  refine hconst.trans ?_
  simp only [pullback_map_app, torusFamilyHomologyLocalSystemIso_hom_app_apply]
  exact (congrArg (torusFamilyHomologyMarking P hcont hinj (f b.as) n)
    ((torusFamilyBaseChangeCommSq P f).fiberLocalSystemSingularObjIso_hom_fiberLocalSystemMap_app
      L' L ℤ n b x)).trans
    (torusFamilyHomologyMarking_baseChange P hcont hinj f b.as n _)

/-- **Base-change naturality of the degree-one local-system trivialization.** -/
theorem torusFamilyBaseChange_fiberLocalSystemMap_comp_firstHomologyIso :
    letI := periodAddAction P; letI := periodAddAction (P ∘ f)
    (torusFamilyBaseChangeCommSq P f).fiberLocalSystemMap L' L ℤ 1 ≫
        (pullback (TopCat.ofHom f).hom).map
          (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L).hom ≫
        (pullbackConstantIso (TopCat.ofHom f).hom (ModuleCat.of ℤ Λ)).hom =
      (torusFamilyFirstHomologyLocalSystemIso (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
        (fun z ↦ hinj (f z)) L').hom := by
  let _ := periodAddAction P; let _ := periodAddAction (P ∘ f)
  have hcomm :
      (pullback (TopCat.ofHom f).hom).map
          ((constantFunctor (TopCat.of Y)).map (exteriorPower.oneEquiv ℤ Λ).toModuleIso.hom) ≫
        (pullbackConstantIso (TopCat.ofHom f).hom (ModuleCat.of ℤ Λ)).hom =
      (pullbackConstantIso (TopCat.ofHom f).hom (ModuleCat.of ℤ (⋀[ℤ]^1 Λ))).hom ≫
        (constantFunctor (TopCat.of Z)).map (exteriorPower.oneEquiv ℤ Λ).toModuleIso.hom := by
    ext b x
    simp
  simp only [torusFamilyFirstHomologyLocalSystemIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, hcomm]
  slice_lhs 1 3 => rw [torusFamilyBaseChange_fiberLocalSystemMap_comp_iso P hcont hinj f L L' 1]

end

section

variable [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E] {Λ : Type*} [AddCommGroup Λ]

/-- Base change of a continuous period family induces an isomorphism of fiber homology local
systems in every degree. -/
theorem isIso_torusFamilyBaseChangeCommSq_fiberLocalSystemMap
    (P : Y → Λ →ₗ[ℤ] E) (hcont : ∀ l, Continuous fun y ↦ P y l) (f : C(Z, Y))
    (L : letI := periodAddAction P; LiftingFunction
      (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
    (L' : letI := periodAddAction (P ∘ f); LiftingFunction
      (TopCat.ofHom ⟨torusFamilyProjection (P ∘ f), continuous_torusFamilyProjection (P ∘ f)⟩).hom)
    (n : ℕ) :
    letI := periodAddAction P; letI := periodAddAction (P ∘ f)
    IsIso ((torusFamilyBaseChangeCommSq P f).fiberLocalSystemMap L' L ℤ n) :=
  letI := periodAddAction P; letI := periodAddAction (P ∘ f)
  @CommSq.isIso_fiberLocalSystemMap _ _ _ _ _ _ _ _ (torusFamilyBaseChangeCommSq P f) L' L ℤ _ n
    (isIso_torusFamilyBaseChangeCommSq_fiberMap P f hcont)

end

end BaseChange

/-! ### Change of lattice marking and classification by `Aut(Λ)` -/

section Remark

variable {Y E : Type} [TopologicalSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section

variable {Λ Λ' : Type} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  [AddCommGroup Λ'] [Module.Free ℤ Λ'] [Module.Finite ℤ Λ']
  (P : Y → Λ →ₗ[ℤ] E) (α : Λ' ≃ₗ[ℤ] Λ)
  [∀ y, DiscreteTopology (LinearMap.range (P y))] [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
  (L : letI := periodAddAction P; LiftingFunction
    (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
  (L' : letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap; LiftingFunction
    (TopCat.ofHom ⟨torusFamilyProjection fun y ↦ (P y).comp α.toLinearMap,
      continuous_torusFamilyProjection _⟩).hom)

/-- **Local-system compatibility under re-marking.** Re-marking `P` by `α : Λ' ≃ₗ[ℤ] Λ` intertwines
`TauCeti.torusFamilyHomologyLocalSystemIso` via `α.exteriorPower n`. -/
theorem torusFamilyRemark_fiberLocalSystemMap_comp_iso (n : ℕ) :
    letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap; letI := periodAddAction P
    (torusFamilyRemarkCommSq P α).fiberLocalSystemMap L' L ℤ n ≫
        (pullbackIdIso (TopCat.of Y)).hom.app (fiberLocalSystem L ℤ n) ≫
        (torusFamilyHomologyLocalSystemIso P hcont hinj L n).hom =
      (torusFamilyHomologyLocalSystemIso (fun y ↦ (P y).comp α.toLinearMap)
          (fun l' ↦ hcont (α l')) (fun y' ↦ (hinj y').comp α.injective) L' n).hom ≫
        (constantFunctor (TopCat.of Y)).map (α.exteriorPower n).toModuleIso.hom := by
  let _ := periodAddAction fun y ↦ (P y).comp α.toLinearMap; let _ := periodAddAction P
  ext b x
  simp only [NatTrans.comp_app, ModuleCat.comp_apply]
  have hid := ConcreteCategory.congr_hom
    (pullbackIdIso_hom_app_app (R := ℤ) (TopCat.of Y) (fiberLocalSystem L ℤ n) b)
    (((torusFamilyRemarkCommSq P α).fiberLocalSystemMap L' L ℤ n).app b x)
  have hlhs := (congrArg
      (fun z ↦ (torusFamilyHomologyLocalSystemIso P hcont hinj L n).hom.app b z) hid).trans
    (torusFamilyHomologyLocalSystemIso_hom_app_apply P hcont hinj L n b
      (((torusFamilyRemarkCommSq P α).fiberLocalSystemMap L' L ℤ n).app b x))
  have hrhs := (ConcreteCategory.congr_hom
      (constantFunctor_map_app (TopCat.of Y) (α.exteriorPower n).toModuleIso.hom b)
      ((torusFamilyHomologyLocalSystemIso (fun y ↦ (P y).comp α.toLinearMap)
        (fun l' ↦ hcont (α l')) (fun y' ↦ (hinj y').comp α.injective) L' n).hom.app b x)).trans
    (congrArg (α.exteriorPower n)
      (torusFamilyHomologyLocalSystemIso_hom_app_apply (fun y ↦ (P y).comp α.toLinearMap)
        (fun l' ↦ hcont (α l')) (fun y' ↦ (hinj y').comp α.injective) L' n b x))
  exact hlhs.trans (((congrArg (torusFamilyHomologyMarking P hcont hinj b.as n)
    ((torusFamilyRemarkCommSq P α).fiberLocalSystemSingularObjIso_hom_fiberLocalSystemMap_app
      L' L ℤ n b x)).trans
    (torusFamilyHomologyMarking_comp_equiv P α hcont hinj b.as n _)).trans hrhs.symm)

/-- **Degree-one local-system compatibility under re-marking.** Re-marking `P` by `α : Λ' ≃ₗ[ℤ] Λ`
intertwines `TauCeti.torusFamilyFirstHomologyLocalSystemIso` via `α`. -/
theorem torusFamilyRemark_fiberLocalSystemMap_comp_firstHomologyIso :
    letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap; letI := periodAddAction P
    (torusFamilyRemarkCommSq P α).fiberLocalSystemMap L' L ℤ 1 ≫
        (pullbackIdIso (TopCat.of Y)).hom.app (fiberLocalSystem L ℤ 1) ≫
        (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L).hom =
      (torusFamilyFirstHomologyLocalSystemIso (fun y ↦ (P y).comp α.toLinearMap)
          (fun l' ↦ hcont (α l')) (fun y' ↦ (hinj y').comp α.injective) L').hom ≫
        (constantFunctor (TopCat.of Y)).map α.toModuleIso.hom := by
  let _ := periodAddAction fun y ↦ (P y).comp α.toLinearMap; let _ := periodAddAction P
  have h1 : (α.exteriorPower 1).toModuleIso.hom ≫ (exteriorPower.oneEquiv ℤ Λ).toModuleIso.hom =
      (exteriorPower.oneEquiv ℤ Λ').toModuleIso.hom ≫ α.toModuleIso.hom :=
    ModuleCat.hom_ext (exteriorPower.oneEquiv_naturality α.toLinearMap)
  simp only [torusFamilyFirstHomologyLocalSystemIso, Iso.trans_hom, Functor.mapIso_hom,
    ← Category.assoc, torusFamilyRemark_fiberLocalSystemMap_comp_iso P α hcont hinj L L' 1]
  rw [Category.assoc, ← (constantFunctor (TopCat.of Y)).map_comp, h1,
    (constantFunctor (TopCat.of Y)).map_comp, ← Category.assoc]

end

section

variable [PathConnectedSpace Y] {Λ : Type}
  [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
  (L : letI := periodAddAction P; LiftingFunction
    (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)

/-- **Classification of global markings by `Aut(Λ)`.** Over a path-connected base `Y`, global
markings `fiberLocalSystem L ℤ 1 ≅ const(Λ)` of a torus family correspond bijectively to `ℤ`-linear
automorphisms `Λ ≃ₗ[ℤ] Λ`, with the canonical marking
`TauCeti.torusFamilyFirstHomologyLocalSystemIso` corresponding to `LinearEquiv.refl ℤ Λ`. -/
def torusFamilyMarkingIsoEquivAut :
    letI := periodAddAction P
    (fiberLocalSystem L ℤ 1 ≅ (constantFunctor (TopCat.of Y)).obj (ModuleCat.of ℤ Λ)) ≃
      (Λ ≃ₗ[ℤ] Λ) :=
  letI := periodAddAction P
  trivializationEquivLinearEquiv (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L)
    (ModuleCat.of ℤ Λ)

@[simp]
theorem torusFamilyMarkingIsoEquivAut_self :
    letI := periodAddAction P
    torusFamilyMarkingIsoEquivAut P hcont hinj L
      (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L) = LinearEquiv.refl ℤ Λ :=
  letI := periodAddAction P
  trivializationEquivLinearEquiv_self (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L)

@[simp]
theorem torusFamilyMarkingIsoEquivAut_symm_apply (α : Λ ≃ₗ[ℤ] Λ) :
    letI := periodAddAction P
    (torusFamilyMarkingIsoEquivAut P hcont hinj L).symm α =
      torusFamilyFirstHomologyLocalSystemIso P hcont hinj L ≪≫
        (constantFunctor (TopCat.of Y)).mapIso α.toModuleIso := by
  let _ := periodAddAction P
  rw [torusFamilyMarkingIsoEquivAut]
  exact trivializationEquivLinearEquiv_symm_apply
    (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L) (ModuleCat.of ℤ Λ) α

theorem torusFamilyMarkingIsoEquivAut_apply
    (e : letI := periodAddAction P
      fiberLocalSystem L ℤ 1 ≅ (constantFunctor (TopCat.of Y)).obj (ModuleCat.of ℤ Λ))
    (y : Y) (l : Λ) :
    letI := periodAddAction P
    torusFamilyMarkingIsoEquivAut P hcont hinj L e l =
      e.hom.app (.mk y)
        ((fiberLocalSystemSingularObjIso L ℤ 1 (.mk y)).inv
          ((torusFamilyMarking P hcont hinj y).symm l)) := by
  let _ := periodAddAction P
  let i := ((torusFamilyFirstHomologyLocalSystemIso P hcont hinj L).app (.mk y)).symm ≪≫
    e.app (.mk y)
  have h₁ : torusFamilyMarkingIsoEquivAut P hcont hinj L e l = i.toLinearEquiv l :=
    LinearEquiv.congr_fun
      (trivializationEquivLinearEquiv_apply
        (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L) (ModuleCat.of ℤ Λ) e (.mk y)) l
  have h₂ : i.hom l = e.hom.app (.mk y)
      (((torusFamilyFirstHomologyLocalSystemIso P hcont hinj L).inv.app (.mk y)) l) := by
    simp only [i, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
    exact ModuleCat.comp_apply
      ((torusFamilyFirstHomologyLocalSystemIso P hcont hinj L).inv.app (.mk y))
      (e.hom.app (.mk y)) l
  exact h₁.trans ((Iso.toLinearEquiv_apply i l).trans (h₂.trans
    (congrArg (e.hom.app (.mk y))
      (torusFamilyFirstHomologyLocalSystemIso_inv_app_apply P hcont hinj L (.mk y) l))))

end

end Remark

end TauCeti
