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
integral singular homology of its fibers assembles into the local coefficient systems
`TauCeti.fiberLocalSystem L ℤ n` over `Y`.

This file extends the canonical degree-one marking `H₁(T_y; ℤ) ≃ₗ[ℤ] Λ` of
`TauCeti.torusFamilyMarking` to all degrees via the exterior-power isomorphism
`Submodule.orbitRelQuotientHomologyEquiv`:

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
* Naturality of the markings and local-system trivializations under continuous base change
  `f : C(Z, Y)` (`TauCeti.torusFamilyHomologyMarking_baseChange`,
  `TauCeti.torusFamilyBaseChange_fiberLocalSystemMap_comp_iso`) and under re-marking of the lattice
  by `α : Λ' ≃ₗ[ℤ] Λ` (`TauCeti.torusFamilyHomologyMarking_comp_equiv`,
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
  -- Rewrite the linear-map composition in `hnat` to pointwise application of `exteriorPower 1`.
  change exteriorPower.oneEquiv ℤ Λ
      (((LinearEquiv.ofInjective (P y) (hinj y)).symm.exteriorPower 1)
        ((LinearMap.range (P y)).orbitRelQuotientHomologyEquiv 1 d)) =
    (LinearEquiv.ofInjective (P y) (hinj y)).symm
      (exteriorPower.oneEquiv ℤ (LinearMap.range (P y))
        ((LinearMap.range (P y)).orbitRelQuotientHomologyEquiv 1 d)) at hnat
  have hrhs : ∀ x : LinearMap.range (P y),
      P y ((LinearEquiv.ofInjective (P y) (hinj y)).symm x) = x.1 :=
    fun x ↦ congrArg Subtype.val ((LinearEquiv.ofInjective (P y) (hinj y)).apply_symm_apply x)
  rw [hnat, hrhs, hrhs, Submodule.coe_oneEquiv_orbitRelQuotientHomologyEquiv]

end HomologyMarking

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
  -- Any lifting function `L` has transport homotopic to `torusFamilyLiftingFunction`.
  have hhom := ContinuousMap.singularHomologyMap_eq_of_homotopic ℤ n
    (L.transport_homotopic_of_liftingFunction (torusFamilyLiftingFunction P hcont hinj) γ)
  rw [LinearMap.congr_fun hhom c]
  let e₀ : C(AddAction.orbitRel.Quotient (LinearMap.range (P y₀)) E,
      (⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩ : C(_, Y)) ⁻¹' {y₀}) :=
    ⟨fun x ↦ torusFamilyFiberHomeomorph P y₀ hcont x,
      (torusFamilyFiberHomeomorph P y₀ hcont).continuous⟩
  let e₀s : C((⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩ : C(_, Y)) ⁻¹' {y₀},
      AddAction.orbitRel.Quotient (LinearMap.range (P y₀)) E) :=
    ⟨fun x ↦ (torusFamilyFiberHomeomorph P y₀ hcont).symm x,
      (torusFamilyFiberHomeomorph P y₀ hcont).continuous_symm⟩
  let e₁s : C((⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩ : C(_, Y)) ⁻¹' {y₁},
      AddAction.orbitRel.Quotient (LinearMap.range (P y₁)) E) :=
    ⟨fun x ↦ (torusFamilyFiberHomeomorph P y₁ hcont).symm x,
      (torusFamilyFiberHomeomorph P y₁ hcont).continuous_symm⟩
  set d := ContinuousMap.singularHomologyMap ℤ n e₀s c
  have hc : ContinuousMap.singularHomologyMap ℤ n e₀ d = c := by
    rw [← ContinuousMap.singularHomologyMap_comp]
    have hid : e₀.comp e₀s = ContinuousMap.id _ :=
      ContinuousMap.ext fun x ↦ (torusFamilyFiberHomeomorph P y₀ hcont).apply_symm_apply x
    rw [hid, ContinuousMap.singularHomologyMap_id]
  let c₀ : ((singularChains ℤ).obj (TopCat.of
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y₀})).homology n := c
  let c₁ : ((singularChains ℤ).obj (TopCat.of
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y₁})).homology n :=
    ContinuousMap.singularHomologyMap ℤ n ((torusFamilyLiftingFunction P hcont hinj).transport γ) c
  -- Align `TopCat.Hom.fiber` with `{z | torusFamilyProjection P z = y}` before rewriting.
  change torusFamilyHomologyMarking P hcont hinj y₁ n c₁ =
    torusFamilyHomologyMarking P hcont hinj y₀ n c₀
  rw [torusFamilyHomologyMarking_apply, torusFamilyHomologyMarking_apply]
  -- Identify the fiber homeomorphism `.symm` maps with `e₁s` and `e₀s` on the preimage subtypes.
  change ((LinearEquiv.ofInjective (P y₁) (hinj y₁)).symm.exteriorPower n)
      ((LinearMap.range (P y₁)).orbitRelQuotientHomologyEquiv n
        (ContinuousMap.singularHomologyMap ℤ n e₁s
          (ContinuousMap.singularHomologyMap ℤ n
            ((torusFamilyLiftingFunction P hcont hinj).transport γ) c))) =
    ((LinearEquiv.ofInjective (P y₀) (hinj y₀)).symm.exteriorPower n)
      ((LinearMap.range (P y₀)).orbitRelQuotientHomologyEquiv n d)
  have hcomp : (e₁s.comp ((torusFamilyLiftingFunction P hcont hinj).transport γ)).comp e₀ =
      ⟨(LinearMap.range (P y₀)).orbitRelQuotientMap (LinearMap.range (P y₁))
          ((torusFamilyParallelTransport P hinj y₀ y₁).toLinearMap.restrictScalars ℤ)
          (torusFamilyParallelTransport_le_comap_range P hinj y₀ y₁),
        (LinearMap.range (P y₀)).continuous_orbitRelQuotientMap (LinearMap.range (P y₁))
          (torusFamilyParallelTransport_le_comap_range P hinj y₀ y₁)
          (torusFamilyParallelTransport P hinj y₀ y₁).continuous⟩ :=
    (ContinuousMap.comp_assoc _ _ _).trans
      (torusFamilyLiftingFunction_transport_comp_fiberHomeomorph P hcont hinj γ)
  rw [← hc, ← ContinuousMap.singularHomologyMap_comp, ← ContinuousMap.singularHomologyMap_comp,
    hcomp, Submodule.orbitRelQuotientHomologyEquiv_singularHomologyMap]
  · -- Rewrite `LinearEquiv.exteriorPower` as `exteriorPower.map`
    -- to fuse the two exterior powers.
    change exteriorPower.map n (LinearEquiv.ofInjective (P y₁) (hinj y₁)).symm.toLinearMap
        (exteriorPower.map n _ ((LinearMap.range (P y₀)).orbitRelQuotientHomologyEquiv n d)) =
      exteriorPower.map n (LinearEquiv.ofInjective (P y₀) (hinj y₀)).symm.toLinearMap
        ((LinearMap.range (P y₀)).orbitRelQuotientHomologyEquiv n d)
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
    congr 2
    ext x
    obtain ⟨l, hl⟩ := x.2
    have hx : x = LinearEquiv.ofInjective (P y₀) (hinj y₀) l := Subtype.ext hl.symm
    rw [hx]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply]
    apply (LinearEquiv.ofInjective (P y₁) (hinj y₁)).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    simp [LinearEquiv.ofInjective_apply]
  · exact (torusFamilyParallelTransport P hinj y₀ y₁).continuous

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
      torusFamilyMarking P hcont hinj y₀ c := by
  let _ := periodAddAction P
  let c₀ : ((singularChains ℤ).obj (TopCat.of
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y₀})).homology 1 := c
  let c₁ : ((singularChains ℤ).obj (TopCat.of
      {z : AddAction.orbitRel.Quotient Λ (Y × E) | torusFamilyProjection P z = y₁})).homology 1 :=
    ContinuousMap.singularHomologyMap ℤ 1 (L.transport γ) c
  -- Align `TopCat.Hom.fiber` with `{z | torusFamilyProjection P z = y}` before rewriting.
  change torusFamilyMarking P hcont hinj y₁ c₁ = torusFamilyMarking P hcont hinj y₀ c₀
  rw [← oneEquiv_torusFamilyHomologyMarking, ← oneEquiv_torusFamilyHomologyMarking]
  exact congrArg (exteriorPower.oneEquiv ℤ Λ)
    (torusFamilyHomologyMarking_transport P hcont hinj L γ 1 c)

/-- **Canonical trivialization of the `n`-th fiber homology local system** of a torus family,
identifying `TauCeti.fiberLocalSystem L ℤ n` with the constant local system `⋀[ℤ]^n Λ` over `Y`. -/
def torusFamilyHomologyLocalSystemIso
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
    (n : ℕ) :
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
      -- Unfold `Functor.const` on morphisms (the identity of `⋀[ℤ]^n Λ`) and evaluate both sides.
      change torusFamilyHomologyMarking P hcont hinj b₁.as n
          ((fiberLocalSystemSingularObjIso L ℤ n b₁).hom
            ((fiberLocalSystem L ℤ n).map (Path.Homotopic.Quotient.mk γ) x)) =
        torusFamilyHomologyMarking P hcont hinj b₀.as n
          ((fiberLocalSystemSingularObjIso L ℤ n b₀).hom x)
      rw [fiberLocalSystemSingularObjIso_hom_map_mk, torusFamilyHomologyMarking_transport])

theorem constantAppIso_torusFamilyHomologyLocalSystemIso_hom_apply
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
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
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
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
def torusFamilyFirstHomologyLocalSystemIso
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom) :
    letI := periodAddAction P
    fiberLocalSystem L ℤ 1 ≅ (constantFunctor (TopCat.of Y)).obj (ModuleCat.of ℤ Λ) :=
  letI := periodAddAction P
  torusFamilyHomologyLocalSystemIso P hcont hinj L 1 ≪≫
    (constantFunctor (TopCat.of Y)).mapIso (exteriorPower.oneEquiv ℤ Λ).toModuleIso

theorem constantAppIso_torusFamilyFirstHomologyLocalSystemIso_hom_apply
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
    (b : FundamentalGroupoid (TopCat.of Y))
    (x : letI := periodAddAction P; (fiberLocalSystem L ℤ 1).obj b) :
    letI := periodAddAction P
    (constantAppIso (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L) b).hom x =
      torusFamilyMarking P hcont hinj b.as ((fiberLocalSystemSingularObjIso L ℤ 1 b).hom x) := by
  let _ := periodAddAction P
  rw [constantAppIso_hom]
  -- Unfold `torusFamilyFirstHomologyLocalSystemIso` at `b` to `oneEquiv` on the degree-`1` iso.
  change exteriorPower.oneEquiv ℤ Λ
      (torusFamilyHomologyMarking P hcont hinj b.as 1
        ((fiberLocalSystemSingularObjIso L ℤ 1 b).hom x)) = _
  exact oneEquiv_torusFamilyHomologyMarking P hcont hinj b.as _

theorem constantAppIso_torusFamilyFirstHomologyLocalSystemIso_inv_apply
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
    (b : FundamentalGroupoid (TopCat.of Y)) (l : Λ) :
    letI := periodAddAction P
    (constantAppIso (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L) b).inv l =
      (fiberLocalSystemSingularObjIso L ℤ 1 b).inv
        ((torusFamilyMarking P hcont hinj b.as).symm l) := by
  let _ := periodAddAction P
  apply (constantAppIso
    (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L) b).toLinearEquiv.injective
  -- `toLinearEquiv` evaluates as `.hom` on `ModuleCat`.
  change (constantAppIso (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L) b).hom _ =
    (constantAppIso (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L) b).hom _
  let w : ((singularChains ℤ).obj
      ((TopCat.ofHom ⟨torusFamilyProjection P,
        continuous_torusFamilyProjection P⟩).fiber b.as)).homology 1 :=
    (torusFamilyMarking P hcont hinj b.as).symm l
  rw [(constantAppIso (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L) b).inv_hom_id_apply,
    constantAppIso_torusFamilyFirstHomologyLocalSystemIso_hom_apply,
    show (torusFamilyMarking P hcont hinj b.as).symm l = w from rfl,
    (fiberLocalSystemSingularObjIso L ℤ 1 b).inv_hom_id_apply w]
  exact ((torusFamilyMarking P hcont hinj b.as).apply_symm_apply l).symm

include hcont hinj in
/-- **Trivial monodromy.** In every degree `n`, the monodromy representation of the fiber homology
local system of a continuous family of full lattices is trivial. -/
theorem isTrivial_monodromyRepresentation_torusFamilyFiberLocalSystem
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
    (n : ℕ) (y : Y) :
    letI := periodAddAction P
    (monodromyRepresentation (fiberLocalSystem L ℤ n) (y : TopCat.of Y)).IsTrivial :=
  letI := periodAddAction P
  isTrivial_monodromyRepresentation_of_iso_constant
    (torusFamilyHomologyLocalSystemIso P hcont hinj L n) (y : TopCat.of Y)

/-- The `n`-th monodromy representation of a torus family is isomorphic in `Rep` to the trivial
representation of `π₁(Y, y)` on `⋀[ℤ]^n Λ`. -/
def torusFamilyHomologyMonodromyIsoTrivial
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
    (n : ℕ) (y : Y) :
    letI := periodAddAction P
    (monodromyFunctor ℤ (TopCat.of Y) y).obj (fiberLocalSystem L ℤ n) ≅
      (Rep.trivialFunctor ℤ (FundamentalGroup (TopCat.of Y) y)).obj
        (ModuleCat.of ℤ (⋀[ℤ]^n Λ)) :=
  letI := periodAddAction P
  monodromyIsoTrivial (torusFamilyHomologyLocalSystemIso P hcont hinj L n) (y : TopCat.of Y)

/-- The degree-one monodromy representation of a torus family is isomorphic in `Rep` to the trivial
representation of `π₁(Y, y)` on `Λ`. -/
def torusFamilyFirstHomologyMonodromyIsoTrivial
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
    (y : Y) :
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

/-- **Naturality of the canonical homology marking under base change.** Pulling back a continuous
family of full lattices along `f : C(Z, Y)` preserves the canonical markings in all degrees. -/
theorem torusFamilyHomologyMarking_baseChange {Λ : Type*} [AddCommGroup Λ]
    (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
    (f : C(Z, Y)) (z : Z) (n : ℕ)
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
  let e₀ : C(AddAction.orbitRel.Quotient (LinearMap.range ((P ∘ f) z)) E,
      (TopCat.ofHom ⟨torusFamilyProjection (P ∘ f),
        continuous_torusFamilyProjection (P ∘ f)⟩).fiber z) :=
    ⟨fun x ↦ torusFamilyFiberHomeomorph (P ∘ f) z (fun l ↦ (hcont l).comp f.continuous) x,
      (torusFamilyFiberHomeomorph (P ∘ f) z (fun l ↦ (hcont l).comp f.continuous)).continuous⟩
  let e₀s : C((TopCat.ofHom ⟨torusFamilyProjection (P ∘ f),
        continuous_torusFamilyProjection (P ∘ f)⟩).fiber z,
      AddAction.orbitRel.Quotient (LinearMap.range ((P ∘ f) z)) E) :=
    ⟨fun x ↦ (torusFamilyFiberHomeomorph (P ∘ f) z (fun l ↦ (hcont l).comp f.continuous)).symm x,
      (torusFamilyFiberHomeomorph (P ∘ f) z
        (fun l ↦ (hcont l).comp f.continuous)).continuous_symm⟩
  let e₁s : C((TopCat.ofHom ⟨torusFamilyProjection P,
        continuous_torusFamilyProjection P⟩).fiber ((TopCat.ofHom f) z),
      AddAction.orbitRel.Quotient (LinearMap.range (P (f z))) E) :=
    ⟨fun x ↦ (torusFamilyFiberHomeomorph P (f z) hcont).symm x,
      (torusFamilyFiberHomeomorph P (f z) hcont).continuous_symm⟩
  set d := ContinuousMap.singularHomologyMap ℤ n e₀s c
  have hc : ContinuousMap.singularHomologyMap ℤ n e₀ d = c := by
    rw [← ContinuousMap.singularHomologyMap_comp]
    have hid : e₀.comp e₀s = ContinuousMap.id _ :=
      ContinuousMap.ext fun x ↦ (torusFamilyFiberHomeomorph (P ∘ f) z
        (fun l ↦ (hcont l).comp f.continuous)).apply_symm_apply x
    rw [hid, ContinuousMap.singularHomologyMap_id]
  let c₀ : ((singularChains ℤ).obj (TopCat.of
      {w : AddAction.orbitRel.Quotient Λ (Z × E) |
        torusFamilyProjection (P ∘ f) w = z})).homology n := c
  let c₁ : ((singularChains ℤ).obj (TopCat.of
      {w : AddAction.orbitRel.Quotient Λ (Y × E) |
        torusFamilyProjection P w = f z})).homology n :=
    ContinuousMap.singularHomologyMap ℤ n ((torusFamilyBaseChangeCommSq P f).fiberMap z).hom c
  -- Align `TopCat.Hom.fiber` with `{w | torusFamilyProjection _ w = _}` before rewriting.
  change torusFamilyHomologyMarking P hcont hinj (f z) n c₁ =
    torusFamilyHomologyMarking (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
      (fun z' ↦ hinj (f z')) z n c₀
  rw [torusFamilyHomologyMarking_apply, torusFamilyHomologyMarking_apply]
  -- Align the inverse fiber homeomorphisms with `e₁s` and `e₀s` on the `TopCat.Hom.fiber` subtypes.
  change ((LinearEquiv.ofInjective (P (f z)) (hinj (f z))).symm.exteriorPower n)
      ((LinearMap.range (P (f z))).orbitRelQuotientHomologyEquiv n
        (ContinuousMap.singularHomologyMap ℤ n e₁s
          (ContinuousMap.singularHomologyMap ℤ n
            ((torusFamilyBaseChangeCommSq P f).fiberMap z).hom c))) =
    ((LinearEquiv.ofInjective (P (f z)) (hinj (f z))).symm.exteriorPower n)
      ((LinearMap.range (P (f z))).orbitRelQuotientHomologyEquiv n d)
  have hcomp : (e₁s.comp ((torusFamilyBaseChangeCommSq P f).fiberMap z).hom).comp e₀ =
      ContinuousMap.id _ :=
    (ContinuousMap.comp_assoc _ _ _).trans
      (torusFamilyBaseChangeCommSq_fiberMap_comp_fiberHomeomorph P f hcont z)
  rw [← hc, ← ContinuousMap.singularHomologyMap_comp, ← ContinuousMap.singularHomologyMap_comp,
    hcomp, ContinuousMap.singularHomologyMap_id]

/-- **Naturality of the degree-one marking under base change.** -/
theorem torusFamilyMarking_baseChange {Λ : Type*} [AddCommGroup Λ]
    (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
    (f : C(Z, Y)) (z : Z)
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
        (fun z' ↦ hinj (f z')) z c := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let c₀ : ((singularChains ℤ).obj (TopCat.of
      {w : AddAction.orbitRel.Quotient Λ (Z × E) |
        torusFamilyProjection (P ∘ f) w = z})).homology 1 := c
  let c₁ : ((singularChains ℤ).obj (TopCat.of
      {w : AddAction.orbitRel.Quotient Λ (Y × E) |
        torusFamilyProjection P w = f z})).homology 1 :=
    ContinuousMap.singularHomologyMap ℤ 1 ((torusFamilyBaseChangeCommSq P f).fiberMap z).hom c
  -- Align `TopCat.Hom.fiber` with `{w | torusFamilyProjection _ w = _}` before rewriting.
  change torusFamilyMarking P hcont hinj (f z) c₁ =
    torusFamilyMarking (P ∘ f) (fun l ↦ (hcont l).comp f.continuous) (fun z' ↦ hinj (f z')) z c₀
  rw [← oneEquiv_torusFamilyHomologyMarking, ← oneEquiv_torusFamilyHomologyMarking]
  exact congrArg (exteriorPower.oneEquiv ℤ Λ)
    (torusFamilyHomologyMarking_baseChange P hcont hinj f z 1 c)

/-- **Base-change naturality of the local-system trivialization.** For any continuous map
`f : C(Z, Y)`, the comparison morphism `CommSq.fiberLocalSystemMap` of
`TauCeti.torusFamilyBaseChangeCommSq` is an isomorphism compatible with the canonical
trivializations by `⋀[ℤ]^n Λ`. -/
theorem torusFamilyBaseChange_fiberLocalSystemMap_comp_iso {Λ : Type}
    [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
    (f : C(Z, Y))
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
  -- Unfold `𝟙` and `(pullback f).map` at `b` to evaluate on `⋀[ℤ]^n Λ`.
  change torusFamilyHomologyMarking P hcont hinj (f b.as) n
      ((fiberLocalSystemSingularObjIso L ℤ n (.mk ((TopCat.ofHom f) b.as))).hom
        (((torusFamilyBaseChangeCommSq P f).fiberLocalSystemMap L' L ℤ n).app b x)) =
    torusFamilyHomologyMarking (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
      (fun z ↦ hinj (f z)) b.as n ((fiberLocalSystemSingularObjIso L' ℤ n b).hom x)
  rw [(torusFamilyBaseChangeCommSq P f).fiberLocalSystemSingularObjIso_hom_fiberLocalSystemMap_app,
    torusFamilyHomologyMarking_baseChange]

/-- **Base-change naturality of the degree-one local-system trivialization.** -/
theorem torusFamilyBaseChange_fiberLocalSystemMap_comp_firstHomologyIso {Λ : Type}
    [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
    (f : C(Z, Y))
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
    (L' : letI := periodAddAction (P ∘ f)
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection (P ∘ f),
          continuous_torusFamilyProjection (P ∘ f)⟩).hom) :
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
  -- Unfold `𝟙` and `(pullback f).map` at `b` to evaluate on `Λ`.
  change exteriorPower.oneEquiv ℤ Λ
      (torusFamilyHomologyMarking P hcont hinj (f b.as) 1
        ((fiberLocalSystemSingularObjIso L ℤ 1 (.mk ((TopCat.ofHom f) b.as))).hom
          (((torusFamilyBaseChangeCommSq P f).fiberLocalSystemMap L' L ℤ 1).app b x))) =
    exteriorPower.oneEquiv ℤ Λ
      (torusFamilyHomologyMarking (P ∘ f) (fun l ↦ (hcont l).comp f.continuous)
        (fun z ↦ hinj (f z)) b.as 1 ((fiberLocalSystemSingularObjIso L' ℤ 1 b).hom x))
  rw [(torusFamilyBaseChangeCommSq P f).fiberLocalSystemSingularObjIso_hom_fiberLocalSystemMap_app,
    torusFamilyHomologyMarking_baseChange]

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
    (y : Y) : DiscreteTopology (LinearMap.range ((P y).comp α.toLinearMap)) := by
  suffices ∀ L : Submodule ℤ E, L = LinearMap.range (P y) → DiscreteTopology L from
    this _ (α.range_comp (P y))
  rintro _ rfl
  infer_instance

attribute [local instance] discreteTopology_range_comp_equiv

/-- Re-marking a period map by `α : Λ' ≃ₗ[ℤ] Λ` preserves fullness of the period lattice. -/
theorem isZLattice_range_comp_equiv {Y Λ Λ' E : Type*} [AddCommGroup Λ] [AddCommGroup Λ']
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Y → Λ →ₗ[ℤ] E) (α : Λ' ≃ₗ[ℤ] Λ) [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))] (y : Y) :
    IsZLattice ℝ (LinearMap.range ((P y).comp α.toLinearMap)) := by
  suffices ∀ (L : Submodule ℤ E) [DiscreteTopology L],
      L = LinearMap.range (P y) → IsZLattice ℝ L from
    this _ (α.range_comp (P y))
  rintro _ _ rfl
  convert (inferInstance : IsZLattice ℝ (LinearMap.range (P y)))

attribute [local instance] isZLattice_range_comp_equiv

variable {Y E : Type} [TopologicalSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Effect of re-marking the lattice on fiber homology.** Precomposing `P` with a `ℤ`-linear
equivalence `α : Λ' ≃ₗ[ℤ] Λ` leaves the period lattices and total space unchanged; under
`TauCeti.torusFamilyRemarkCommSq`, the `P`-marking of a homology class equals `α.exteriorPower n`
applied to its `(P ∘ α)`-marking. -/
theorem torusFamilyHomologyMarking_comp_equiv {Λ Λ' : Type*} [AddCommGroup Λ] [AddCommGroup Λ']
    (P : Y → Λ →ₗ[ℤ] E) (α : Λ' ≃ₗ[ℤ] Λ)
    [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
    (y : Y) (n : ℕ)
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
          (fun l' ↦ hcont (α l')) (fun y' ↦ (hinj y').comp α.injective) y n c) := by
  let _ := periodAddAction fun y ↦ (P y).comp α.toLinearMap
  let _ := periodAddAction P
  let P' : Y → Λ' →ₗ[ℤ] E := fun y ↦ (P y).comp α.toLinearMap
  let e₀ : C(AddAction.orbitRel.Quotient (LinearMap.range (P' y)) E,
      (TopCat.ofHom ⟨torusFamilyProjection P',
        continuous_torusFamilyProjection P'⟩).fiber y) :=
    ⟨fun x ↦ torusFamilyFiberHomeomorph P' y (fun l' ↦ hcont (α l')) x,
      (torusFamilyFiberHomeomorph P' y (fun l' ↦ hcont (α l'))).continuous⟩
  let e₀s : C((TopCat.ofHom ⟨torusFamilyProjection P',
        continuous_torusFamilyProjection P'⟩).fiber y,
      AddAction.orbitRel.Quotient (LinearMap.range (P' y)) E) :=
    ⟨fun x ↦ (torusFamilyFiberHomeomorph P' y (fun l' ↦ hcont (α l'))).symm x,
      (torusFamilyFiberHomeomorph P' y (fun l' ↦ hcont (α l'))).continuous_symm⟩
  let e₁s : C((TopCat.ofHom ⟨torusFamilyProjection P,
        continuous_torusFamilyProjection P⟩).fiber ((𝟙 (TopCat.of Y)) y),
      AddAction.orbitRel.Quotient (LinearMap.range (P y)) E) :=
    ⟨fun x ↦ (torusFamilyFiberHomeomorph P y hcont).symm x,
      (torusFamilyFiberHomeomorph P y hcont).continuous_symm⟩
  set d := ContinuousMap.singularHomologyMap ℤ n e₀s c
  have hc : ContinuousMap.singularHomologyMap ℤ n e₀ d = c := by
    rw [← ContinuousMap.singularHomologyMap_comp]
    have hid : e₀.comp e₀s = ContinuousMap.id _ :=
      ContinuousMap.ext fun x ↦
        (torusFamilyFiberHomeomorph P' y (fun l' ↦ hcont (α l'))).apply_symm_apply x
    rw [hid, ContinuousMap.singularHomologyMap_id]
  let c₀ : ((singularChains ℤ).obj (TopCat.of
      {w : AddAction.orbitRel.Quotient Λ' (Y × E) |
        torusFamilyProjection P' w = y})).homology n := c
  let c₁ : ((singularChains ℤ).obj (TopCat.of
      {w : AddAction.orbitRel.Quotient Λ (Y × E) |
        torusFamilyProjection P w = y})).homology n :=
    ContinuousMap.singularHomologyMap ℤ n ((torusFamilyRemarkCommSq P α).fiberMap y).hom c
  -- Align `TopCat.Hom.fiber` with `{w | torusFamilyProjection _ w = y}` before rewriting.
  change torusFamilyHomologyMarking P hcont hinj y n c₁ =
    (α.exteriorPower n)
      (torusFamilyHomologyMarking P' (fun l' ↦ hcont (α l'))
        (fun y' ↦ (hinj y').comp α.injective) y n c₀)
  rw [torusFamilyHomologyMarking_apply, torusFamilyHomologyMarking_apply]
  -- Align the inverse fiber homeomorphisms with `e₁s` and `e₀s` on the `TopCat.Hom.fiber` subtypes.
  change exteriorPower.map n (LinearEquiv.ofInjective (P y) (hinj y)).symm.toLinearMap
      ((LinearMap.range (P y)).orbitRelQuotientHomologyEquiv n
        (ContinuousMap.singularHomologyMap ℤ n e₁s
          (ContinuousMap.singularHomologyMap ℤ n
            ((torusFamilyRemarkCommSq P α).fiberMap y).hom c))) =
    exteriorPower.map n α.toLinearMap
      (exteriorPower.map n
        (LinearEquiv.ofInjective (P' y) ((hinj y).comp α.injective)).symm.toLinearMap
        ((LinearMap.range (P' y)).orbitRelQuotientHomologyEquiv n d))
  have hcomp : (e₁s.comp ((torusFamilyRemarkCommSq P α).fiberMap y).hom).comp e₀ =
      ⟨(LinearMap.range (P' y)).orbitRelQuotientMap (LinearMap.range (P y))
          LinearMap.id (by simp [P']),
        (LinearMap.range (P' y)).continuous_orbitRelQuotientMap
          (LinearMap.range (P y)) (by simp [P']) continuous_id⟩ :=
    (ContinuousMap.comp_assoc _ _ _).trans
      (torusFamilyRemarkCommSq_fiberMap_comp_fiberHomeomorph P α hcont y)
  rw [← hc, ← ContinuousMap.singularHomologyMap_comp, ← ContinuousMap.singularHomologyMap_comp,
    hcomp, Submodule.orbitRelQuotientHomologyEquiv_singularHomologyMap]
  · rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← exteriorPower.map_comp, ← exteriorPower.map_comp]
    congr 2
    ext x
    obtain ⟨l', hl'⟩ := x.2
    have hx : x = LinearEquiv.ofInjective (P' y) ((hinj y).comp α.injective) l' :=
      Subtype.ext hl'.symm
    rw [hx]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply]
    apply (LinearEquiv.ofInjective (P y) (hinj y)).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rfl
  · exact continuous_id

/-- **Effect of re-marking the lattice in degree one.** Under `TauCeti.torusFamilyRemarkCommSq`,
the `P`-marking of a degree-one class equals `α` applied to its `(P ∘ α)`-marking. -/
theorem torusFamilyMarking_comp_equiv {Λ Λ' : Type*} [AddCommGroup Λ] [AddCommGroup Λ']
    (P : Y → Λ →ₗ[ℤ] E) (α : Λ' ≃ₗ[ℤ] Λ)
    [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
    (y : Y)
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
  let P' : Y → Λ' →ₗ[ℤ] E := fun y ↦ (P y).comp α.toLinearMap
  let c₀ : ((singularChains ℤ).obj (TopCat.of
      {w : AddAction.orbitRel.Quotient Λ' (Y × E) |
        torusFamilyProjection P' w = y})).homology 1 := c
  let c₁ : ((singularChains ℤ).obj (TopCat.of
      {w : AddAction.orbitRel.Quotient Λ (Y × E) |
        torusFamilyProjection P w = y})).homology 1 :=
    ContinuousMap.singularHomologyMap ℤ 1 ((torusFamilyRemarkCommSq P α).fiberMap y).hom c
  -- Align `TopCat.Hom.fiber` with `{w | torusFamilyProjection _ w = y}` before rewriting.
  change torusFamilyMarking P hcont hinj y c₁ =
    α (torusFamilyMarking P' (fun l' ↦ hcont (α l')) (fun y' ↦ (hinj y').comp α.injective) y c₀)
  rw [← oneEquiv_torusFamilyHomologyMarking, ← oneEquiv_torusFamilyHomologyMarking,
    show c₁ = ContinuousMap.singularHomologyMap ℤ 1 ((torusFamilyRemarkCommSq P α).fiberMap y).hom c
      from rfl]
  refine (congrArg (exteriorPower.oneEquiv ℤ Λ)
    (torusFamilyHomologyMarking_comp_equiv P α hcont hinj y 1 c)).trans ?_
  exact LinearMap.congr_fun (exteriorPower.oneEquiv_naturality α.toLinearMap) _

/-- **Local-system compatibility under re-marking.** Re-marking `P` by `α : Λ' ≃ₗ[ℤ] Λ` intertwines
`TauCeti.torusFamilyHomologyLocalSystemIso` via `α.exteriorPower n`. -/
theorem torusFamilyRemark_fiberLocalSystemMap_comp_iso {Λ Λ' : Type}
    [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    [AddCommGroup Λ'] [Module.Free ℤ Λ'] [Module.Finite ℤ Λ']
    (P : Y → Λ →ₗ[ℤ] E) (α : Λ' ≃ₗ[ℤ] Λ)
    [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
    (L' : letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection fun y ↦ (P y).comp α.toLinearMap,
          continuous_torusFamilyProjection _⟩).hom)
    (n : ℕ) :
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
  -- Unfold `𝟙` and evaluate both sides in `⋀[ℤ]^n Λ`.
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
theorem torusFamilyRemark_fiberLocalSystemMap_comp_firstHomologyIso {Λ Λ' : Type}
    [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    [AddCommGroup Λ'] [Module.Free ℤ Λ'] [Module.Finite ℤ Λ']
    (P : Y → Λ →ₗ[ℤ] E) (α : Λ' ≃ₗ[ℤ] Λ)
    [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
    (L' : letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection fun y ↦ (P y).comp α.toLinearMap,
          continuous_torusFamilyProjection _⟩).hom) :
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
  calc (torusFamilyRemarkCommSq P α).fiberLocalSystemMap L' L ℤ 1 ≫
        (pullbackIdIso (TopCat.of Y)).hom.app (fiberLocalSystem L ℤ 1) ≫
        (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L).hom
      = ((torusFamilyRemarkCommSq P α).fiberLocalSystemMap L' L ℤ 1 ≫
          (pullbackIdIso (TopCat.of Y)).hom.app (fiberLocalSystem L ℤ 1) ≫
          (torusFamilyHomologyLocalSystemIso P hcont hinj L 1).hom) ≫
          (constantFunctor (TopCat.of Y)).map (exteriorPower.oneEquiv ℤ Λ).toModuleIso.hom := by
        simp [torusFamilyFirstHomologyLocalSystemIso]
    _ = (torusFamilyHomologyLocalSystemIso (fun y ↦ (P y).comp α.toLinearMap)
          (fun l' ↦ hcont (α l')) (fun y' ↦ (hinj y').comp α.injective) L' 1).hom ≫
          ((constantFunctor (TopCat.of Y)).map (α.exteriorPower 1).toModuleIso.hom ≫
            (constantFunctor (TopCat.of Y)).map (exteriorPower.oneEquiv ℤ Λ).toModuleIso.hom) := by
        rw [torusFamilyRemark_fiberLocalSystemMap_comp_iso P α hcont hinj L L' 1, Category.assoc]
    _ = (torusFamilyFirstHomologyLocalSystemIso (fun y ↦ (P y).comp α.toLinearMap)
          (fun l' ↦ hcont (α l')) (fun y' ↦ (hinj y').comp α.injective) L').hom ≫
          (constantFunctor (TopCat.of Y)).map α.toModuleIso.hom := by
        rw [← (constantFunctor (TopCat.of Y)).map_comp, h1,
          (constantFunctor (TopCat.of Y)).map_comp]
        simp [torusFamilyFirstHomologyLocalSystemIso]

/-- **Classification of global markings by `Aut(Λ)`.** Over a path-connected base `Y`, global
markings `fiberLocalSystem L ℤ 1 ≅ const(Λ)` of a torus family correspond bijectively to `ℤ`-linear
automorphisms `Λ ≃ₗ[ℤ] Λ`, with the canonical marking
`TauCeti.torusFamilyFirstHomologyLocalSystemIso` corresponding to `LinearEquiv.refl ℤ Λ`. -/
def torusFamilyMarkingIsoEquivAut [PathConnectedSpace Y] {Λ : Type}
    [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom) :
    letI := periodAddAction P
    (fiberLocalSystem L ℤ 1 ≅ (constantFunctor (TopCat.of Y)).obj (ModuleCat.of ℤ Λ)) ≃
      (Λ ≃ₗ[ℤ] Λ) :=
  letI := periodAddAction P
  trivializationEquivLinearEquiv (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L)
    (ModuleCat.of ℤ Λ)

@[simp]
theorem torusFamilyMarkingIsoEquivAut_self [PathConnectedSpace Y] {Λ : Type}
    [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom) :
    letI := periodAddAction P
    torusFamilyMarkingIsoEquivAut P hcont hinj L
      (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L) = LinearEquiv.refl ℤ Λ :=
  letI := periodAddAction P
  trivializationEquivLinearEquiv_self (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L)

@[simp]
theorem torusFamilyMarkingIsoEquivAut_symm_apply [PathConnectedSpace Y] {Λ : Type}
    [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
    (α : Λ ≃ₗ[ℤ] Λ) :
    letI := periodAddAction P
    (torusFamilyMarkingIsoEquivAut P hcont hinj L).symm α =
      torusFamilyFirstHomologyLocalSystemIso P hcont hinj L ≪≫
        (constantFunctor (TopCat.of Y)).mapIso α.toModuleIso := by
  let _ := periodAddAction P
  rw [torusFamilyMarkingIsoEquivAut]
  exact trivializationEquivLinearEquiv_symm_apply
    (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L) (ModuleCat.of ℤ Λ) α

theorem torusFamilyMarkingIsoEquivAut_apply [PathConnectedSpace Y] {Λ : Type}
    [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))
    (L : letI := periodAddAction P
      LiftingFunction
        (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩).hom)
    (e : letI := periodAddAction P
      fiberLocalSystem L ℤ 1 ≅ (constantFunctor (TopCat.of Y)).obj (ModuleCat.of ℤ Λ))
    (y : Y) (l : Λ) :
    letI := periodAddAction P
    torusFamilyMarkingIsoEquivAut P hcont hinj L e l =
      (constantAppIso e (.mk y)).hom
        ((fiberLocalSystemSingularObjIso L ℤ 1 (.mk y)).inv
          ((torusFamilyMarking P hcont hinj y).symm l)) := by
  let _ := periodAddAction P
  rw [torusFamilyMarkingIsoEquivAut,
    trivializationEquivLinearEquiv_apply _ _ e (.mk y)]
  -- Unfold `(constantAppIso ...).symm ≪≫ constantAppIso e (.mk y)` and simplify `.inv l`.
  change (constantAppIso e (.mk y)).hom
      ((constantAppIso (torusFamilyFirstHomologyLocalSystemIso P hcont hinj L) (.mk y)).inv l) = _
  rw [constantAppIso_torusFamilyFirstHomologyLocalSystemIso_inv_apply]

end Remark

end TauCeti
