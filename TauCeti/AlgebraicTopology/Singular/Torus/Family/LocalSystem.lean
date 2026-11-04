/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Fibration
public import TauCeti.AlgebraicTopology.LocalCoefficient.Constant
public import TauCeti.AlgebraicTopology.Singular.Fibration.LocalSystem
public import TauCeti.AlgebraicTopology.Singular.Torus.Family.Basic
public import TauCeti.AlgebraicTopology.Singular.Torus.ZLattice

/-!
# Trivialization of the fiber homology local system of a torus family

Let `P : Y → Λ →ₗ[ℤ] E` be a continuous family of full lattices in a finite-dimensional real normed
space `E`. By `TauCeti.isHurewiczFibration_torusFamilyProjection`, the projection
`π : (Y × E)/Λ → Y` is a Hurewicz fibration; for any Hurewicz lifting function `L` of `π`, the
integral singular homology of its fibers forms the local coefficient system
`TauCeti.fiberLocalSystem L ℤ n` over `Y`.

This file extends the canonical degree-one marking `H₁(T_y; ℤ) ≃ₗ[ℤ] Λ` of
`TauCeti.torusFamilyMarking` to all degrees via `Submodule.orbitRelQuotientHomologyEquiv`:

* `TauCeti.torusFamilyHomologyMarking`: the canonical marking `Hₙ(T_y; ℤ) ≃ₗ[ℤ] ⋀[ℤ]^n Λ` of every
  fiber, agreeing with `TauCeti.torusFamilyMarking` in degree `1`
  (`TauCeti.oneEquiv_torusFamilyHomologyMarking`).
* `TauCeti.torusFamilyHomologyMarking_transport` and `TauCeti.torusFamilyMarking_transport`:
  Hurewicz transport along any path `γ : Path y₀ y₁` and any lifting function `L` preserves the
  canonical markings.
* `TauCeti.torusFamilyHomologyLocalSystemIso` and `TauCeti.torusFamilyFirstHomologyLocalSystemIso`:
  the resulting canonical trivializations of `TauCeti.fiberLocalSystem L ℤ n` by `⋀[ℤ]^n Λ` and of
  `TauCeti.fiberLocalSystem L ℤ 1` by `Λ`, together with triviality of the monodromy representation
  (`TauCeti.isTrivial_monodromyRepresentation_torusFamilyFiberLocalSystem`,
  `TauCeti.torusFamilyHomologyMonodromyIsoTrivial`,
  `TauCeti.torusFamilyFirstHomologyMonodromyIsoTrivial`).
* Naturality under continuous base change `f : C(Z, Y)`
  (`TauCeti.torusFamilyHomologyMarking_baseChange`,
  `TauCeti.torusFamilyBaseChange_fiberLocalSystemMap_comp_iso`) and under re-marking by
  `α : Λ' ≃ₗ[ℤ] Λ` (`TauCeti.torusFamilyHomologyMarking_comp_equiv`,
  `TauCeti.torusFamilyRemark_fiberLocalSystemMap_comp_iso`).
* `TauCeti.torusFamilyMarkingIsoEquivAut`: over a path-connected base `Y`, global markings of
  `TauCeti.fiberLocalSystem L ℤ 1` by `Λ` correspond bijectively to automorphisms `Λ ≃ₗ[ℤ] Λ`.

As in `TauCeti.AlgebraicTopology.Singular.Torus.Family.Basic`, spaces carrying integer singular
chains live in `Type`.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1, Sections 1.1 and
  1.3, and Chapter 8.
* Claire Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Studies in Advanced
  Mathematics 76, Cambridge University Press, 2002, Chapter 9, Section 9.1.
-/

public section

noncomputable section

open CategoryTheory Function TauCeti.LocalCoefficientSystem

namespace TauCeti

/-! ### Canonical markings in all homology degrees -/

section HomologyMarking

variable {Y E : Type} [TopologicalSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {Λ : Type*} [AddCommGroup Λ]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y)) (y : Y)

/-- **Canonical marking of fiber homology in degree `n`.** Identifies the `n`-th integral singular
homology of the torus fiber `T_y` over `y` with `⋀[ℤ]^n Λ`, via
`TauCeti.torusFamilyFiberHomeomorph`, `Submodule.orbitRelQuotientHomologyEquiv`, and
`(LinearEquiv.ofInjective (P y) (hinj y)).symm`. -/
def torusFamilyHomologyMarking (n : ℕ) :
    letI := periodAddAction P
    ((singularChains ℤ).obj (TopCat.of
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y})).homology n
      ≃ₗ[ℤ] ⋀[ℤ]^n Λ :=
  letI := periodAddAction P
  (LinearEquiv.trans
    (M₁ := ((singularChains ℤ).obj (TopCat.of
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y})).homology n)
    (M₂ := ((singularChains ℤ).obj (TopCat.of (AddAction.orbitRel.Quotient
      (LinearMap.range (P y)) E))).homology n)
    ((torusFamilyFiberHomeomorph P y hcont).toHomotopyEquiv.singularHomologyIso
      (ModuleCat.of ℤ ℤ) n).symm.toLinearEquiv
    ((LinearMap.range (P y)).orbitRelQuotientHomologyEquiv n)) ≪≫ₗ
    (LinearEquiv.ofInjective (P y) (hinj y)).symm.exteriorPower n

/-- `TauCeti.torusFamilyHomologyMarking` transports a homology class along the inverse fiber
homeomorphism, applies `Submodule.orbitRelQuotientHomologyEquiv`, and pulls back along `P y`. -/
theorem torusFamilyHomologyMarking_apply (n : ℕ)
    (c : letI := periodAddAction P
      ((singularChains ℤ).obj (TopCat.of
        {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y})).homology n) :
    torusFamilyHomologyMarking P hcont hinj y n c =
      ((LinearEquiv.ofInjective (P y) (hinj y)).symm.exteriorPower n)
        ((LinearMap.range (P y)).orbitRelQuotientHomologyEquiv n
          (ContinuousMap.singularHomologyMap ℤ n
            ((torusFamilyFiberHomeomorph P y hcont).symm : C(_, _)) c)) := by
  rw [torusFamilyHomologyMarking, LinearEquiv.trans_apply]
  refine congrArg _ ((LinearEquiv.trans_apply c).trans (congrArg _ ?_))
  exact congrArg (fun f ↦ ModuleCat.Hom.hom f c)
    ((torusFamilyFiberHomeomorph P y hcont).toHomotopyEquiv.singularHomologyIso_inv
      (ModuleCat.of ℤ ℤ) n)

/-- The inverse of `TauCeti.torusFamilyHomologyMarking` pushes `w ∈ ⋀[ℤ]^n Λ` forward along `P y`,
maps to `Hₙ(E / range (P y); ℤ)`, and carries the class into the fiber by
`TauCeti.torusFamilyFiberHomeomorph`. -/
theorem torusFamilyHomologyMarking_symm_apply (n : ℕ) (w : ⋀[ℤ]^n Λ) :
    (torusFamilyHomologyMarking P hcont hinj y n).symm w =
      ContinuousMap.singularHomologyMap ℤ n (torusFamilyFiberHomeomorph P y hcont : C(_, _))
        (((LinearMap.range (P y)).orbitRelQuotientHomologyEquiv n).symm
          (((LinearEquiv.ofInjective (P y) (hinj y)).exteriorPower n) w)) := by
  rw [torusFamilyHomologyMarking, LinearEquiv.symm_trans_apply, LinearEquiv.exteriorPower_symm,
    LinearEquiv.symm_symm]
  refine (LinearEquiv.symm_trans_apply _).trans ?_
  exact congrArg (fun f ↦ ModuleCat.Hom.hom f _)
    ((torusFamilyFiberHomeomorph P y hcont).toHomotopyEquiv.singularHomologyIso_hom
      (ModuleCat.of ℤ ℤ) n)

/-- **Compatibility with the fiber homeomorphism.** On a class carried from
`E / LinearMap.range (P y)` by `TauCeti.torusFamilyFiberHomeomorph`, pushing the marking forward by
`P y` recovers `Submodule.orbitRelQuotientHomologyEquiv`. -/
@[simp]
theorem torusFamilyHomologyMarking_singularHomologyMap (n : ℕ)
    (c : ((singularChains ℤ).obj (TopCat.of
      (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E))).homology n) :
    ((LinearEquiv.ofInjective (P y) (hinj y)).exteriorPower n)
        (torusFamilyHomologyMarking P hcont hinj y n
          (ContinuousMap.singularHomologyMap ℤ n
            (torusFamilyFiberHomeomorph P y hcont : C(_, _)) c)) =
      (LinearMap.range (P y)).orbitRelQuotientHomologyEquiv n c := by
  let _ := periodAddAction P
  rw [torusFamilyHomologyMarking_apply, ← LinearEquiv.exteriorPower_symm,
    LinearEquiv.apply_symm_apply, ← ContinuousMap.singularHomologyMap_comp]
  simp only [Homeomorph.symm_comp_toContinuousMap, ContinuousMap.singularHomologyMap_id]

/-- **Agreement in degree one.** Under `exteriorPower.oneEquiv ℤ Λ : ⋀[ℤ]^1 Λ ≃ₗ[ℤ] Λ`, the
degree-one marking `TauCeti.torusFamilyHomologyMarking P hcont hinj y 1` is
`TauCeti.torusFamilyMarking`. -/
@[simp]
theorem oneEquiv_torusFamilyHomologyMarking
    (c : letI := periodAddAction P
      ((singularChains ℤ).obj (TopCat.of
        {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y})).homology 1) :
    exteriorPower.oneEquiv ℤ Λ (torusFamilyHomologyMarking P hcont hinj y 1 c) =
      torusFamilyMarking P hcont hinj y c := by
  let _ := periodAddAction P
  let e_symm : C({z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y},
      AddAction.orbitRel.Quotient (LinearMap.range (P y)) E) :=
    (torusFamilyFiberHomeomorph P y hcont).symm
  set d := ContinuousMap.singularHomologyMap ℤ 1 e_symm c
  apply hinj y
  rw [torusFamilyHomologyMarking_apply, torusFamilyMarking_apply]
  have hnat := LinearMap.congr_fun
    (exteriorPower.oneEquiv_naturality (LinearEquiv.ofInjective (P y) (hinj y)).symm.toLinearMap)
    ((LinearMap.range (P y)).orbitRelQuotientHomologyEquiv 1 d)
  change exteriorPower.oneEquiv ℤ Λ
      (((LinearEquiv.ofInjective (P y) (hinj y)).symm.exteriorPower 1)
        ((LinearMap.range (P y)).orbitRelQuotientHomologyEquiv 1 d)) =
    (LinearEquiv.ofInjective (P y) (hinj y)).symm
      (exteriorPower.oneEquiv ℤ (LinearMap.range (P y))
        ((LinearMap.range (P y)).orbitRelQuotientHomologyEquiv 1 d)) at hnat
  have hrhs (x : LinearMap.range (P y)) :
      P y ((LinearEquiv.ofInjective (P y) (hinj y)).symm x) = x.1 :=
    congrArg Subtype.val ((LinearEquiv.ofInjective (P y) (hinj y)).apply_symm_apply x)
  rw [hnat, hrhs, hrhs, Submodule.coe_oneEquiv_orbitRelQuotientHomologyEquiv]

end HomologyMarking

/-- Common fiberwise naturality calculation for `torusFamilyHomologyMarking`: if a continuous map
`g` between torus fibers is intertwined by `torusFamilyFiberHomeomorph` with
`Submodule.orbitRelQuotientMap` of a continuous additive map `φ : E →ₗ[ℤ] E` satisfying
`φ (P₀ y₀ l) = P₁ y₁ (α l)`, then `g` acts on `Hₙ(-; ℤ)` via `α.exteriorPower n`. -/
private theorem torusFamilyHomologyMarking_map {Y₀ Y₁ E : Type}
    [TopologicalSpace Y₀] [TopologicalSpace Y₁]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Λ₀ Λ₁ : Type*} [AddCommGroup Λ₀] [AddCommGroup Λ₁]
    (P₀ : Y₀ → Λ₀ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P₀ y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P₀ y))]
    (hcont₀ : ∀ l, Continuous fun y ↦ P₀ y l) (hinj₀ : ∀ y, Injective (P₀ y)) (y₀ : Y₀)
    (P₁ : Y₁ → Λ₁ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P₁ y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P₁ y))]
    (hcont₁ : ∀ l, Continuous fun y ↦ P₁ y l) (hinj₁ : ∀ y, Injective (P₁ y)) (y₁ : Y₁)
    (α : Λ₀ ≃ₗ[ℤ] Λ₁) {φ : E →ₗ[ℤ] E} (hφ : Continuous φ)
    (hφL : LinearMap.range (P₀ y₀) ≤ (LinearMap.range (P₁ y₁)).comap φ)
    (hP : ∀ l, φ (P₀ y₀ l) = P₁ y₁ (α l))
    (g : letI := periodAddAction P₀; letI := periodAddAction P₁
      C({z : AddAction.orbitRel.Quotient Λ₀ (Y₀ × E) | torusFamilyProjection P₀ z = y₀},
        {z : AddAction.orbitRel.Quotient Λ₁ (Y₁ × E) | torusFamilyProjection P₁ z = y₁}))
    (hg : letI := periodAddAction P₀; letI := periodAddAction P₁
      ∀ w, (torusFamilyFiberHomeomorph P₁ y₁ hcont₁).symm
          (g (torusFamilyFiberHomeomorph P₀ y₀ hcont₀ w)) =
        (LinearMap.range (P₀ y₀)).orbitRelQuotientMap (LinearMap.range (P₁ y₁)) φ hφL w)
    (n : ℕ)
    (c : letI := periodAddAction P₀
      ((singularChains ℤ).obj (TopCat.of
        {z : AddAction.orbitRel.Quotient Λ₀ (Y₀ × E) |
          torusFamilyProjection P₀ z = y₀})).homology n) :
    letI := periodAddAction P₀
    letI := periodAddAction P₁
    torusFamilyHomologyMarking P₁ hcont₁ hinj₁ y₁ n (ContinuousMap.singularHomologyMap ℤ n g c) =
      (α.exteriorPower n) (torusFamilyHomologyMarking P₀ hcont₀ hinj₀ y₀ n c) := by
  let _ := periodAddAction P₀
  let _ := periodAddAction P₁
  let e₀s : C({z : AddAction.orbitRel.Quotient Λ₀ (Y₀ × E) | torusFamilyProjection P₀ z = y₀},
      AddAction.orbitRel.Quotient (LinearMap.range (P₀ y₀)) E) :=
    (torusFamilyFiberHomeomorph P₀ y₀ hcont₀).symm
  let e₁s : C({z : AddAction.orbitRel.Quotient Λ₁ (Y₁ × E) | torusFamilyProjection P₁ z = y₁},
      AddAction.orbitRel.Quotient (LinearMap.range (P₁ y₁)) E) :=
    (torusFamilyFiberHomeomorph P₁ y₁ hcont₁).symm
  have hcomp : e₁s.comp g =
      (ContinuousMap.mk
        ((LinearMap.range (P₀ y₀)).orbitRelQuotientMap (LinearMap.range (P₁ y₁)) φ hφL)
        ((LinearMap.range (P₀ y₀)).continuous_orbitRelQuotientMap (LinearMap.range (P₁ y₁))
          hφL hφ)).comp e₀s := by
    ext x
    obtain ⟨w, rfl⟩ := (torusFamilyFiberHomeomorph P₀ y₀ hcont₀).surjective x
    simpa [e₀s, e₁s] using hg w
  rw [torusFamilyHomologyMarking_apply, torusFamilyHomologyMarking_apply]
  change exteriorPower.map n (LinearEquiv.ofInjective (P₁ y₁) (hinj₁ y₁)).symm.toLinearMap
      ((LinearMap.range (P₁ y₁)).orbitRelQuotientHomologyEquiv n
        (ContinuousMap.singularHomologyMap ℤ n e₁s
          (ContinuousMap.singularHomologyMap ℤ n g c))) =
    exteriorPower.map n α.toLinearMap
      (exteriorPower.map n (LinearEquiv.ofInjective (P₀ y₀) (hinj₀ y₀)).symm.toLinearMap
        ((LinearMap.range (P₀ y₀)).orbitRelQuotientHomologyEquiv n
          (ContinuousMap.singularHomologyMap ℤ n e₀s c)))
  rw [← ContinuousMap.singularHomologyMap_comp, hcomp, ContinuousMap.singularHomologyMap_comp,
    Submodule.orbitRelQuotientHomologyEquiv_singularHomologyMap _ _ hφ hφL,
    ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← exteriorPower.map_comp, ← exteriorPower.map_comp]
  congr 2
  refine LinearMap.ext fun ⟨_, ⟨l, rfl⟩⟩ ↦ hinj₁ y₁ ?_
  have h₁ (x : LinearMap.range (P₁ y₁)) :
      P₁ y₁ ((LinearEquiv.ofInjective (P₁ y₁) (hinj₁ y₁)).symm x) = x.1 :=
    congrArg Subtype.val ((LinearEquiv.ofInjective (P₁ y₁) (hinj₁ y₁)).apply_symm_apply x)
  have h₀ : (LinearEquiv.ofInjective (P₀ y₀) (hinj₀ y₀)).symm ⟨P₀ y₀ l, ⟨l, rfl⟩⟩ = l :=
    (LinearEquiv.ofInjective (P₀ y₀) (hinj₀ y₀)).symm_apply_eq.mpr rfl
  simp [h₁, h₀, hP]

/-! ### Invariance under Hurewicz transport and trivialization of the fiber local system -/

section LocalSystem

variable {Y Λ E : Type} [TopologicalSpace Y]
  [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))

/-- **Hurewicz transport preserves the canonical homology marking.** For any Hurewicz lifting
function `L` of `torusFamilyProjection P` and any path `γ : Path y₀ y₁`, the map induced on `Hₙ` by
`L.transport γ` intertwines the canonical markings over `y₀` and `y₁`. -/
theorem torusFamilyHomologyMarking_transport {y₀ y₁ : Y}
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
    (γ : Path y₀ y₁) (n : ℕ)
    (c : letI := periodAddAction P
      ((singularChains ℤ).obj
        ((TopCat.ofHom ⟨torusFamilyProjection P,
          continuous_torusFamilyProjection P⟩).fiber y₀)).homology n) :
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
  change torusFamilyHomologyMarking P hcont hinj y₁ n (ContinuousMap.singularHomologyMap ℤ n g c₀) =
    torusFamilyHomologyMarking P hcont hinj y₀ n c₀
  exact (torusFamilyHomologyMarking_map P hcont hinj y₀ P hcont hinj y₁ (.refl ℤ Λ)
    (torusFamilyParallelTransport P hinj y₀ y₁).continuous
    (torusFamilyParallelTransport_le_comap_range P hinj y₀ y₁)
    (torusFamilyParallelTransport_period P hinj y₀ y₁) g
    (torusFamilyLiftingFunction_transport_fiberHomeomorph P hcont hinj γ) n c₀).trans
    (by simp [LinearEquiv.exteriorPower])

/-- **Hurewicz transport preserves the degree-one marking.** -/
theorem torusFamilyMarking_transport {y₀ y₁ : Y}
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
    (γ : Path y₀ y₁)
    (c : letI := periodAddAction P
      ((singularChains ℤ).obj
        ((TopCat.ofHom ⟨torusFamilyProjection P,
          continuous_torusFamilyProjection P⟩).fiber y₀)).homology 1) :
    letI := periodAddAction P
    torusFamilyMarking P hcont hinj y₁ (ContinuousMap.singularHomologyMap ℤ 1 (L.transport γ) c) =
      torusFamilyMarking P hcont hinj y₀ c :=
  letI := periodAddAction P
  (oneEquiv_torusFamilyHomologyMarking P hcont hinj y₁ _).symm.trans <|
    (congrArg (exteriorPower.oneEquiv ℤ Λ)
      (torusFamilyHomologyMarking_transport P hcont hinj L γ 1 c)).trans
      (oneEquiv_torusFamilyHomologyMarking P hcont hinj y₀ c)

variable (L : letI := periodAddAction P
  LiftingFunction
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
      (torusFamilyHomologyMarking P hcont hinj b.as n).toModuleIso)
    (by
      intro b₀ b₁ q
      induction q using Path.Homotopic.Quotient.ind with | mk γ =>
      ext x
      change torusFamilyHomologyMarking P hcont hinj b₁.as n
          ((fiberLocalSystemSingularObjIso L ℤ n b₁).hom
            ((fiberLocalSystem L ℤ n).map (Path.Homotopic.Quotient.mk γ) x)) =
        torusFamilyHomologyMarking P hcont hinj b₀.as n
          ((fiberLocalSystemSingularObjIso L ℤ n b₀).hom x)
      rw [fiberLocalSystemSingularObjIso_hom_map_mk, torusFamilyHomologyMarking_transport])

theorem constantAppIso_torusFamilyHomologyLocalSystemIso_hom_apply
    (n : ℕ) (b : FundamentalGroupoid (TopCat.of Y))
    (x : letI := periodAddAction P; (fiberLocalSystem L ℤ n).obj b) :
    letI := periodAddAction P
    (constantAppIso (torusFamilyHomologyLocalSystemIso P hcont hinj L n) b).hom x =
      torusFamilyHomologyMarking P hcont hinj b.as n
        ((fiberLocalSystemSingularObjIso L ℤ n b).hom x) := by
  let _ := periodAddAction P
  rw [constantAppIso_hom]
  rfl

theorem constantAppIso_torusFamilyHomologyLocalSystemIso_inv_apply
    (n : ℕ) (b : FundamentalGroupoid (TopCat.of Y)) (w : ⋀[ℤ]^n Λ) :
    letI := periodAddAction P
    (constantAppIso (torusFamilyHomologyLocalSystemIso P hcont hinj L n) b).inv w =
      (fiberLocalSystemSingularObjIso L ℤ n b).inv
        ((torusFamilyHomologyMarking P hcont hinj b.as n).symm w) := by
  let _ := periodAddAction P
  rw [constantAppIso_inv]
  rfl

/-- **Canonical trivialization of the first fiber homology local system** of a torus family,
identifying `TauCeti.fiberLocalSystem L ℤ 1` with the constant local system `Λ` over `Y`. -/
def torusFamilyFirstHomologyLocalSystemIso :
    letI := periodAddAction P
    fiberLocalSystem L ℤ 1 ≅ (constantFunctor (TopCat.of Y)).obj (ModuleCat.of ℤ Λ) :=
  letI := periodAddAction P
  torusFamilyHomologyLocalSystemIso P hcont hinj L 1 ≪≫
    (constantFunctor (TopCat.of Y)).mapIso (exteriorPower.oneEquiv ℤ Λ).toModuleIso

theorem constantAppIso_torusFamilyFirstHomologyLocalSystemIso_hom_apply
    (b : FundamentalGroupoid (TopCat.of Y))
    (x : letI := periodAddAction P; (fiberLocalSystem L ℤ 1).obj b) :
    letI := periodAddAction P
    (constantAppIso (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L) b).hom x =
      torusFamilyMarking P hcont hinj b.as ((fiberLocalSystemSingularObjIso L ℤ 1 b).hom x) := by
  let _ := periodAddAction P
  rw [constantAppIso_hom]
  exact oneEquiv_torusFamilyHomologyMarking P hcont hinj b.as _

theorem constantAppIso_torusFamilyFirstHomologyLocalSystemIso_inv_apply
    (b : FundamentalGroupoid (TopCat.of Y)) (l : Λ) :
    letI := periodAddAction P
    (constantAppIso (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L) b).inv l =
      (fiberLocalSystemSingularObjIso L ℤ 1 b).inv
        ((torusFamilyMarking P hcont hinj b.as).symm l) := by
  let _ := periodAddAction P
  let e := constantAppIso (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L) b
  apply e.toLinearEquiv.injective
  change e.hom _ = e.hom _
  rw [e.inv_hom_id_apply, constantAppIso_torusFamilyFirstHomologyLocalSystemIso_hom_apply,
    (fiberLocalSystemSingularObjIso L ℤ 1 b).inv_hom_id_apply
      ((torusFamilyMarking P hcont hinj b.as).symm l)]
  exact ((torusFamilyMarking P hcont hinj b.as).apply_symm_apply l).symm

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
      (Rep.trivialFunctor ℤ (FundamentalGroup (TopCat.of Y) y)).obj
        (ModuleCat.of ℤ (⋀[ℤ]^n Λ)) :=
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

/-- Pulling back a family of discrete period subgroups along `f : Z → Y` preserves discreteness. -/
theorem discreteTopology_range_baseChange {Y Z Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E]
    [TopologicalSpace E] (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
    (f : Z → Y) (z : Z) : DiscreteTopology (LinearMap.range ((P ∘ f) z)) :=
  inferInstanceAs (DiscreteTopology (LinearMap.range (P (f z))))

attribute [local instance] discreteTopology_range_baseChange

/-- Pulling back a family of full lattices along `f : Z → Y` preserves fullness. -/
theorem isZLattice_range_baseChange {Y Z Λ E : Type*} [AddCommGroup Λ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
    (f : Z → Y) (z : Z) : IsZLattice ℝ (LinearMap.range ((P ∘ f) z)) :=
  inferInstanceAs (IsZLattice ℝ (LinearMap.range (P (f z))))

attribute [local instance] isZLattice_range_baseChange

variable {Y Z E : Type} [TopologicalSpace Y] [TopologicalSpace Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section

variable {Λ : Type*} [AddCommGroup Λ]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y)) (f : C(Z, Y)) (z : Z)

/-- **Naturality of the canonical homology marking under base change.** Pulling back a continuous
family of full lattices along `f : C(Z, Y)` preserves the canonical markings in all degrees. -/
theorem torusFamilyHomologyMarking_baseChange (n : ℕ)
    (c : letI := periodAddAction (P ∘ f)
      ((singularChains ℤ).obj
        ((TopCat.ofHom ⟨torusFamilyProjection (P ∘ f),
          continuous_torusFamilyProjection (P ∘ f)⟩).fiber z)).homology n) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    torusFamilyHomologyMarking P hcont hinj (f z) n
        (ContinuousMap.singularHomologyMap ℤ n
          ((torusFamilyBaseChangeCommSq P f).fiberMap z).hom c) =
      torusFamilyHomologyMarking (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
        (fun z' ↦ hinj (f z')) z n c := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let g : C({w : AddAction.orbitRel.Quotient Λ (Z × E) | torusFamilyProjection (P ∘ f) w = z},
      {w : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P w = f z}) :=
    ⟨fun x ↦ ((torusFamilyBaseChangeCommSq P f).fiberMap z).hom x,
      ((torusFamilyBaseChangeCommSq P f).fiberMap z).hom.continuous⟩
  let c₀ : ((singularChains ℤ).obj (TopCat.of
      {w : AddAction.orbitRel.Quotient Λ (Z × E) |
        torusFamilyProjection (P ∘ f) w = z})).homology n := c
  change torusFamilyHomologyMarking P hcont hinj (f z) n
      (ContinuousMap.singularHomologyMap ℤ n g c₀) =
    torusFamilyHomologyMarking (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
      (fun z' ↦ hinj (f z')) z n c₀
  exact (torusFamilyHomologyMarking_map (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
    (fun z' ↦ hinj (f z')) z P hcont hinj (f z) (.refl ℤ Λ)
    (φ := LinearMap.id) continuous_id le_rfl (fun _ ↦ rfl) g
    (fun w ↦ ((Homeomorph.symm_apply_eq (torusFamilyFiberHomeomorph P (f z) hcont)).mpr
      (torusFamilyBaseChangeCommSq_fiberMap_fiberHomeomorph P f hcont z w)).trans
      (DFunLike.congr_fun ((LinearMap.range (P (f z))).orbitRelQuotientMap_id le_rfl).symm w))
    n c₀).trans (by simp [LinearEquiv.exteriorPower])

/-- **Naturality of the degree-one marking under base change.** -/
theorem torusFamilyMarking_baseChange
    (c : letI := periodAddAction (P ∘ f)
      ((singularChains ℤ).obj
        ((TopCat.ofHom ⟨torusFamilyProjection (P ∘ f),
          continuous_torusFamilyProjection (P ∘ f)⟩).fiber z)).homology 1) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    torusFamilyMarking P hcont hinj (f z)
        (ContinuousMap.singularHomologyMap ℤ 1
          ((torusFamilyBaseChangeCommSq P f).fiberMap z).hom c) =
      torusFamilyMarking (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
        (fun z' ↦ hinj (f z')) z c :=
  letI := periodAddAction P
  letI := periodAddAction (P ∘ f)
  (oneEquiv_torusFamilyHomologyMarking P hcont hinj (f z) _).symm.trans <|
    (congrArg (exteriorPower.oneEquiv ℤ Λ)
      (torusFamilyHomologyMarking_baseChange P hcont hinj f z 1 c)).trans
      (oneEquiv_torusFamilyHomologyMarking (P ∘ f) _ _ z c)

end

section

variable {Λ : Type} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y)) (f : C(Z, Y))
  (L : letI := periodAddAction P
    LiftingFunction
      (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
  (L' : letI := periodAddAction (P ∘ f)
    LiftingFunction
      (TopCat.ofHom ⟨torusFamilyProjection (P ∘ f),
        continuous_torusFamilyProjection (P ∘ f)⟩).hom)

/-- **Base-change naturality of the local-system trivialization.** For any continuous map
`f : C(Z, Y)`, the comparison morphism `CommSq.fiberLocalSystemMap` of
`TauCeti.torusFamilyBaseChangeCommSq` is an isomorphism compatible with the canonical
trivializations by `⋀[ℤ]^n Λ`. -/
theorem torusFamilyBaseChange_fiberLocalSystemMap_comp_iso (n : ℕ) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    (torusFamilyBaseChangeCommSq P f).fiberLocalSystemMap L' L ℤ n ≫
        (pullback (TopCat.ofHom f).hom).map
          (torusFamilyHomologyLocalSystemIso P hcont hinj L n).hom ≫
        (pullbackConstantIso (TopCat.ofHom f).hom (ModuleCat.of ℤ (⋀[ℤ]^n Λ))).hom =
      (torusFamilyHomologyLocalSystemIso (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
        (fun z ↦ hinj (f z)) L' n).hom := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  ext b x
  have hconst := ConcreteCategory.congr_hom
    (pullbackConstantIso_hom_app (TopCat.ofHom f).hom (ModuleCat.of ℤ (⋀[ℤ]^n Λ)) b)
    (((pullback (TopCat.ofHom f).hom).map
      (torusFamilyHomologyLocalSystemIso P hcont hinj L n).hom).app b
      (((torusFamilyBaseChangeCommSq P f).fiberLocalSystemMap L' L ℤ n).app b x))
  simp only [NatTrans.comp_app, ModuleCat.comp_apply]
  refine hconst.trans ?_
  change torusFamilyHomologyMarking P hcont hinj (f b.as) n
      ((fiberLocalSystemSingularObjIso L ℤ n (.mk ((TopCat.ofHom f) b.as))).hom
        (((torusFamilyBaseChangeCommSq P f).fiberLocalSystemMap L' L ℤ n).app b x)) =
    torusFamilyHomologyMarking (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
      (fun z ↦ hinj (f z)) b.as n ((fiberLocalSystemSingularObjIso L' ℤ n b).hom x)
  rw [(torusFamilyBaseChangeCommSq P f).fiberLocalSystemSingularObjIso_hom_fiberLocalSystemMap_app,
    torusFamilyHomologyMarking_baseChange]

/-- **Base-change naturality of the degree-one local-system trivialization.** -/
theorem torusFamilyBaseChange_fiberLocalSystemMap_comp_firstHomologyIso :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    (torusFamilyBaseChangeCommSq P f).fiberLocalSystemMap L' L ℤ 1 ≫
        (pullback (TopCat.ofHom f).hom).map
          (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L).hom ≫
        (pullbackConstantIso (TopCat.ofHom f).hom (ModuleCat.of ℤ Λ)).hom =
      (torusFamilyFirstHomologyLocalSystemIso (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
        (fun z ↦ hinj (f z)) L').hom := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  ext b x
  have hconst := ConcreteCategory.congr_hom
    (pullbackConstantIso_hom_app (TopCat.ofHom f).hom (ModuleCat.of ℤ Λ) b)
    (((pullback (TopCat.ofHom f).hom).map
      (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L).hom).app b
      (((torusFamilyBaseChangeCommSq P f).fiberLocalSystemMap L' L ℤ 1).app b x))
  simp only [NatTrans.comp_app, ModuleCat.comp_apply]
  refine hconst.trans ?_
  change exteriorPower.oneEquiv ℤ Λ
      (torusFamilyHomologyMarking P hcont hinj (f b.as) 1
        ((fiberLocalSystemSingularObjIso L ℤ 1 (.mk ((TopCat.ofHom f) b.as))).hom
          (((torusFamilyBaseChangeCommSq P f).fiberLocalSystemMap L' L ℤ 1).app b x))) =
    exteriorPower.oneEquiv ℤ Λ
      (torusFamilyHomologyMarking (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
        (fun z ↦ hinj (f z)) b.as 1 ((fiberLocalSystemSingularObjIso L' ℤ 1 b).hom x))
  rw [(torusFamilyBaseChangeCommSq P f).fiberLocalSystemSingularObjIso_hom_fiberLocalSystemMap_app,
    torusFamilyHomologyMarking_baseChange]

end

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Base change of a continuous family of full lattices induces an isomorphism of fiber homology
local systems in every degree. -/
theorem isIso_torusFamilyBaseChangeCommSq_fiberLocalSystemMap {Λ : Type*} [AddCommGroup Λ]
    (P : Y → Λ →ₗ[ℤ] E) (hcont : ∀ l, Continuous fun y ↦ P y l) (f : C(Z, Y))
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
    (L' : letI := periodAddAction (P ∘ f)
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection (P ∘ f),
          continuous_torusFamilyProjection (P ∘ f)⟩).hom)
    (n : ℕ) :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    IsIso ((torusFamilyBaseChangeCommSq P f).fiberLocalSystemMap L' L ℤ n) :=
  letI := periodAddAction P
  letI := periodAddAction (P ∘ f)
  @CommSq.isIso_fiberLocalSystemMap _ _ _ _ _ _ _ _ (torusFamilyBaseChangeCommSq P f) L' L ℤ _ n
    (isIso_torusFamilyBaseChangeCommSq_fiberMap P f hcont)

end BaseChange

/-! ### Change of lattice marking and classification by `Aut(Λ)` -/

section Remark

/-- Re-marking a period map by `α : Λ' ≃ₗ[ℤ] Λ` preserves discreteness of the period subgroup. -/
theorem discreteTopology_range_comp_equiv {Y Λ Λ' E : Type*} [AddCommGroup Λ] [AddCommGroup Λ']
    [AddCommGroup E] [TopologicalSpace E]
    (P : Y → Λ →ₗ[ℤ] E) (α : Λ' ≃ₗ[ℤ] Λ) [∀ y, DiscreteTopology (LinearMap.range (P y))]
    (y : Y) : DiscreteTopology (LinearMap.range ((P y).comp α.toLinearMap)) :=
  α.range_comp (P y) ▸ inferInstance

attribute [local instance] discreteTopology_range_comp_equiv

/-- Re-marking a period map by `α : Λ' ≃ₗ[ℤ] Λ` preserves fullness of the period lattice. -/
theorem isZLattice_range_comp_equiv {Y Λ Λ' E : Type*} [AddCommGroup Λ] [AddCommGroup Λ']
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Y → Λ →ₗ[ℤ] E) (α : Λ' ≃ₗ[ℤ] Λ) [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))] (y : Y) :
    IsZLattice ℝ (LinearMap.range ((P y).comp α.toLinearMap)) := by
  suffices ∀ (L : Submodule ℤ E) [DiscreteTopology L],
      L = LinearMap.range (P y) → IsZLattice ℝ L from this _ (α.range_comp (P y))
  rintro _ _ rfl
  convert (inferInstance : IsZLattice ℝ (LinearMap.range (P y)))

attribute [local instance] isZLattice_range_comp_equiv

variable {Y E : Type} [TopologicalSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section

variable {Λ Λ' : Type*} [AddCommGroup Λ] [AddCommGroup Λ']
  (P : Y → Λ →ₗ[ℤ] E) (α : Λ' ≃ₗ[ℤ] Λ)
  [∀ y, DiscreteTopology (LinearMap.range (P y))] [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y)) (y : Y)

/-- **Effect of re-marking the lattice on fiber homology.** Precomposing `P` with a `ℤ`-linear
equivalence `α : Λ' ≃ₗ[ℤ] Λ` leaves the period lattices and total space unchanged; under
`TauCeti.torusFamilyRemarkCommSq`, the `P`-marking of a homology class equals `α.exteriorPower n`
applied to its `(P ∘ α)`-marking. -/
theorem torusFamilyHomologyMarking_comp_equiv (n : ℕ)
    (c : letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
      ((singularChains ℤ).obj
        ((TopCat.ofHom ⟨torusFamilyProjection fun y ↦ (P y).comp α.toLinearMap,
          continuous_torusFamilyProjection _⟩).fiber y)).homology n) :
    letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
    letI := periodAddAction P
    torusFamilyHomologyMarking P hcont hinj y n
        (ContinuousMap.singularHomologyMap ℤ n
          ((torusFamilyRemarkCommSq P α).fiberMap y).hom c) =
      (α.exteriorPower n)
        (torusFamilyHomologyMarking (fun y ↦ (P y).comp α.toLinearMap)
          (fun l' ↦ hcont (α l')) (fun y' ↦ (hinj y').comp α.injective) y n c) :=
  letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
  letI := periodAddAction P
  torusFamilyHomologyMarking_map (fun y ↦ (P y).comp α.toLinearMap) (fun l' ↦ hcont (α l'))
    (fun y' ↦ (hinj y').comp α.injective) y P hcont hinj y α
    (φ := LinearMap.id) continuous_id (by simp) (fun _ ↦ rfl)
    ((torusFamilyRemarkCommSq P α).fiberMap y).hom
    (fun w ↦ (Homeomorph.symm_apply_eq _).mpr
      (torusFamilyRemarkCommSq_fiberMap_fiberHomeomorph P α hcont y w))
    n c

/-- **Effect of re-marking the lattice in degree one.** Under `TauCeti.torusFamilyRemarkCommSq`,
the `P`-marking of a degree-one class equals `α` applied to its `(P ∘ α)`-marking. -/
theorem torusFamilyMarking_comp_equiv
    (c : letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
      ((singularChains ℤ).obj
        ((TopCat.ofHom ⟨torusFamilyProjection fun y ↦ (P y).comp α.toLinearMap,
          continuous_torusFamilyProjection _⟩).fiber y)).homology 1) :
    letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
    letI := periodAddAction P
    torusFamilyMarking P hcont hinj y
        (ContinuousMap.singularHomologyMap ℤ 1
          ((torusFamilyRemarkCommSq P α).fiberMap y).hom c) =
      α (torusFamilyMarking (fun y ↦ (P y).comp α.toLinearMap)
        (fun l' ↦ hcont (α l')) (fun y' ↦ (hinj y').comp α.injective) y c) := by
  let _ := periodAddAction fun y ↦ (P y).comp α.toLinearMap
  let _ := periodAddAction P
  refine (oneEquiv_torusFamilyHomologyMarking P hcont hinj y _).symm.trans ?_
  refine (congrArg (exteriorPower.oneEquiv ℤ Λ)
    (torusFamilyHomologyMarking_comp_equiv P α hcont hinj y 1 c)).trans ?_
  exact (LinearMap.congr_fun (exteriorPower.oneEquiv_naturality α.toLinearMap) _).trans
    (congrArg α (oneEquiv_torusFamilyHomologyMarking (fun y ↦ (P y).comp α.toLinearMap) _ _ y c))

end

section

variable {Λ Λ' : Type} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  [AddCommGroup Λ'] [Module.Free ℤ Λ'] [Module.Finite ℤ Λ']
  (P : Y → Λ →ₗ[ℤ] E) (α : Λ' ≃ₗ[ℤ] Λ)
  [∀ y, DiscreteTopology (LinearMap.range (P y))] [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
  (L : letI := periodAddAction P
    LiftingFunction
      (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
  (L' : letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
    LiftingFunction
      (TopCat.ofHom ⟨torusFamilyProjection fun y ↦ (P y).comp α.toLinearMap,
        continuous_torusFamilyProjection _⟩).hom)

/-- **Local-system compatibility under re-marking.** Re-marking `P` by `α : Λ' ≃ₗ[ℤ] Λ` intertwines
`TauCeti.torusFamilyHomologyLocalSystemIso` via `α.exteriorPower n`. -/
theorem torusFamilyRemark_fiberLocalSystemMap_comp_iso (n : ℕ) :
    letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
    letI := periodAddAction P
    (torusFamilyRemarkCommSq P α).fiberLocalSystemMap L' L ℤ n ≫
        (pullbackIdIso (TopCat.of Y)).hom.app (fiberLocalSystem L ℤ n) ≫
        (torusFamilyHomologyLocalSystemIso P hcont hinj L n).hom =
      (torusFamilyHomologyLocalSystemIso (fun y ↦ (P y).comp α.toLinearMap)
          (fun l' ↦ hcont (α l')) (fun y' ↦ (hinj y').comp α.injective) L' n).hom ≫
        (constantFunctor (TopCat.of Y)).map (α.exteriorPower n).toModuleIso.hom := by
  let _ := periodAddAction fun y ↦ (P y).comp α.toLinearMap
  let _ := periodAddAction P
  ext b x
  simp only [NatTrans.comp_app, ModuleCat.comp_apply]
  have hid := ConcreteCategory.congr_hom
    (pullbackIdIso_hom_app_app (R := ℤ) (TopCat.of Y) (fiberLocalSystem L ℤ n) b)
    (((torusFamilyRemarkCommSq P α).fiberLocalSystemMap L' L ℤ n).app b x)
  refine (congrArg
    (fun z ↦ (torusFamilyHomologyLocalSystemIso P hcont hinj L n).hom.app b z) hid).trans ?_
  change torusFamilyHomologyMarking P hcont hinj b.as n
      ((fiberLocalSystemSingularObjIso L ℤ n (.mk ((𝟙 (TopCat.of Y)) b.as))).hom
        (((torusFamilyRemarkCommSq P α).fiberLocalSystemMap L' L ℤ n).app b x)) =
    (α.exteriorPower n)
      (torusFamilyHomologyMarking (fun y ↦ (P y).comp α.toLinearMap)
        (fun l' ↦ hcont (α l')) (fun y' ↦ (hinj y').comp α.injective) b.as n
        ((fiberLocalSystemSingularObjIso L' ℤ n b).hom x))
  rw [(torusFamilyRemarkCommSq P α).fiberLocalSystemSingularObjIso_hom_fiberLocalSystemMap_app,
    torusFamilyHomologyMarking_comp_equiv]

/-- **Degree-one local-system compatibility under re-marking.** Re-marking `P` by `α : Λ' ≃ₗ[ℤ] Λ`
intertwines `TauCeti.torusFamilyFirstHomologyLocalSystemIso` via `α`. -/
theorem torusFamilyRemark_fiberLocalSystemMap_comp_firstHomologyIso :
    letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
    letI := periodAddAction P
    (torusFamilyRemarkCommSq P α).fiberLocalSystemMap L' L ℤ 1 ≫
        (pullbackIdIso (TopCat.of Y)).hom.app (fiberLocalSystem L ℤ 1) ≫
        (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L).hom =
      (torusFamilyFirstHomologyLocalSystemIso (fun y ↦ (P y).comp α.toLinearMap)
          (fun l' ↦ hcont (α l')) (fun y' ↦ (hinj y').comp α.injective) L').hom ≫
        (constantFunctor (TopCat.of Y)).map α.toModuleIso.hom := by
  let _ := periodAddAction fun y ↦ (P y).comp α.toLinearMap
  let _ := periodAddAction P
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
  (L : letI := periodAddAction P
    LiftingFunction
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
      (constantAppIso e (.mk y)).hom
        ((fiberLocalSystemSingularObjIso L ℤ 1 (.mk y)).inv
          ((torusFamilyMarking P hcont hinj y).symm l)) := by
  let _ := periodAddAction P
  rw [torusFamilyMarkingIsoEquivAut, trivializationEquivLinearEquiv_apply _ _ e (.mk y)]
  change (constantAppIso e (.mk y)).hom
      ((constantAppIso (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L) (.mk y)).inv l) = _
  rw [constantAppIso_torusFamilyFirstHomologyLocalSystemIso_inv_apply]

end

end Remark

end TauCeti
