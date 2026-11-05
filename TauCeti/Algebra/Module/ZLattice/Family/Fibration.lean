/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient
public import TauCeti.Algebra.Module.ZLattice.Basic
public import TauCeti.Algebra.Module.ZLattice.Family.BaseChange.Basic
public import TauCeti.Algebra.Module.ZLattice.Family.Fiber
public import TauCeti.Algebra.Module.ZLattice.Family.HomeomorphProd
public import TauCeti.Topology.Algebra.Module.Quotient
public import TauCeti.Topology.Category.TopCat.Fiber
public import TauCeti.Topology.Homotopy.HurewiczFibration.Transport

/-!
# Parallel transport and Hurewicz fibration structure of a family of tori

Let `P : Y → (Λ →ₗ[ℤ] E)` be a continuous family of full lattices in a finite-dimensional real
normed space `E`, with `Λ` a finite free `ℤ`-module. At each `y : Y` the periods of any `ℤ`-basis
`b` of `Λ` form a real basis `TauCeti.periodBasis P b hinj y` of `E`. Composing its coordinate map
at `y` with the inverse coordinate map at `y'` defines the **period parallel transport**
`TauCeti.torusFamilyParallelTransport P hinj y y' : E ≃L[ℝ] E`, the unique real-linear isomorphism
carrying `P y l` to `P y' l` for every `l : Λ`; in particular it does not depend on the chosen
`ℤ`-basis of `Λ`.

Transferring the canonical lifting function of the product projection through the global
trivialization `TauCeti.torusFamilyHomeomorphProd` equips `(Y × E)/Λ → Y` with a canonical
Hurewicz lifting function `TauCeti.torusFamilyLiftingFunction`, lifting `[y, v]` along a path `γ`
with `γ 0 = y` to `t ↦ [γ t, torusFamilyParallelTransport P hinj y (γ t) v]`. Consequently,
`TauCeti.torusFamilyProjection` is a Hurewicz fibration (for test spaces in every universe) and a
Serre fibration, and under `TauCeti.torusFamilyFiberHomeomorph` its fiber transport along any path
from `y₀` to `y₁` is induced on translation quotients by
`torusFamilyParallelTransport P hinj y₀ y₁`.

Finally, we record the commutative squares of fibrations in `TopCat` attached to continuous base
change (`TauCeti.torusFamilyBaseChangeCommSq`) and to re-marking the abstract lattice by a linear
equivalence `α : Λ' ≃ₗ[ℤ] Λ` (`TauCeti.torusFamilyRemarkHomeomorph`,
`TauCeti.torusFamilyRemarkCommSq`), together with their action on fibers.

## Main definitions

* `TauCeti.torusFamilyParallelTransport`: the real-linear isomorphism `E ≃L[ℝ] E` sending
  `P y l` to `P y' l` for all `l : Λ`.
* `TauCeti.torusFamilyLiftingFunction`: the canonical `LiftingFunction` for
  `torusFamilyProjection P`.
* `TauCeti.torusFamilyRemarkHomeomorph`: the homeomorphism over `Y` comparing the period quotients
  for `P` and `fun y ↦ (P y).comp α.toLinearMap`.

## Main results

* `TauCeti.torusFamilyParallelTransport_period`, `TauCeti.eq_torusFamilyParallelTransport`,
  `TauCeti.torusFamilyParallelTransport_eq_of_basis`: `torusFamilyParallelTransport` is the unique
  real-linear map carrying periods at `y` to periods at `y'`, independent of the `ℤ`-basis of `Λ`.
* `TauCeti.torusFamilyLiftingFunction_transport_comp_fiberHomeomorph`,
  `TauCeti.torusFamilyLiftingFunction_transport_fiberHomeomorph`: transport along any path from `y₀`
  to `y₁` acts on `E / range (P y₀) → E / range (P y₁)` as `Submodule.orbitRelQuotientMap` of
  `torusFamilyParallelTransport`.
* `TauCeti.isHurewiczFibration_torusFamilyProjection`,
  `TauCeti.mem_serreFibrations_torusFamilyProjection`: `(Y × E)/Λ → Y` is a Hurewicz and Serre
  fibration.
* `TauCeti.torusFamilyBaseChangeCommSq`, `TauCeti.torusFamilyRemarkCommSq`: the commutative squares
  in `TopCat` for base change along `f : C(Z, Y)` and re-marking by `α : Λ' ≃ₗ[ℤ] Λ`.
-/

public section

noncomputable section

open CategoryTheory Function Module Set unitInterval

universe w u

namespace TauCeti

/-! ### Period parallel transport -/

section ParallelTransport

variable {Y Λ E : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))] (hinj : ∀ y, Injective (P y))

/-- **Period parallel transport** between the covering vector spaces at `y` and `y'`: the unique
continuous real-linear equivalence `E ≃L[ℝ] E` sending `P y l` to `P y' l` for all `l : Λ`. It is
constructed using a chosen `ℤ`-basis of `Λ` and shown independent of that choice in
`TauCeti.torusFamilyParallelTransport_eq_of_basis`. -/
def torusFamilyParallelTransport (y y' : Y) : E ≃L[ℝ] E :=
  let b := Module.Free.chooseBasis ℤ Λ
  (periodBasis P b hinj y).equivFunL.trans (periodBasis P b hinj y').equivFunL.symm

omit [Module.Free ℤ Λ] [Module.Finite ℤ Λ] in
private theorem periodBasis_equivFunL_trans_symm_period {ι : Type*} [Finite ι]
    (b : Basis ι ℤ Λ) (y y' : Y) (l : Λ) :
    ((periodBasis P b hinj y).equivFunL.trans (periodBasis P b hinj y').equivFunL.symm)
      (P y l) = P y' l := by
  -- Unfold the composition of `equivFunL` and `equivFunL.symm` to `equivFun` on `P y l`.
  change (periodBasis P b hinj y').equivFun.symm ((periodBasis P b hinj y).equivFun (P y l)) =
    P y' l
  rw [periodBasis_equivFun_period P b hinj y l, ← periodBasis_equivFun_period P b hinj y' l,
    LinearEquiv.symm_apply_apply]

/-- Period parallel transport carries each period `P y l` at `y` to the corresponding period
`P y' l` at `y'`. -/
@[simp]
theorem torusFamilyParallelTransport_period (y y' : Y) (l : Λ) :
    torusFamilyParallelTransport P hinj y y' (P y l) = P y' l :=
  periodBasis_equivFunL_trans_symm_period P hinj (Module.Free.chooseBasis ℤ Λ) y y' l

/-- Any real-linear map sending `P y l` to `P y' l` for all `l : Λ` agrees with
`torusFamilyParallelTransport`. -/
theorem eq_torusFamilyParallelTransport {y y' : Y} (f : E →ₗ[ℝ] E)
    (hf : ∀ l, f (P y l) = P y' l) :
    f = (torusFamilyParallelTransport P hinj y y').toLinearMap := by
  refine (periodBasis P (Module.Free.chooseBasis ℤ Λ) hinj y).ext fun i ↦ ?_
  simp [hf]

/-- **Basis independence of period parallel transport.** For any `ℤ`-basis `b` of `Λ`,
`torusFamilyParallelTransport` agrees with `(periodBasis P b hinj y).equivFunL` followed by
`(periodBasis P b hinj y').equivFunL.symm`. -/
theorem torusFamilyParallelTransport_eq_of_basis {ι : Type*} [Finite ι]
    (b : Basis ι ℤ Λ) (y y' : Y) :
    torusFamilyParallelTransport P hinj y y' =
      (periodBasis P b hinj y).equivFunL.trans (periodBasis P b hinj y').equivFunL.symm := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  exact (eq_torusFamilyParallelTransport P hinj _
    (periodBasis_equivFunL_trans_symm_period P hinj b y y')).symm

@[simp]
theorem torusFamilyParallelTransport_self (y : Y) :
    torusFamilyParallelTransport P hinj y y = ContinuousLinearEquiv.refl ℝ E := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  exact (eq_torusFamilyParallelTransport P hinj LinearMap.id fun _ ↦ rfl).symm

@[simp]
theorem torusFamilyParallelTransport_symm (y y' : Y) :
    (torusFamilyParallelTransport P hinj y y').symm = torusFamilyParallelTransport P hinj y' y := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  refine eq_torusFamilyParallelTransport P hinj _ fun l ↦ ?_
  exact (torusFamilyParallelTransport P hinj y y').symm_apply_eq.mpr
    (torusFamilyParallelTransport_period P hinj y y' l).symm

@[simp]
theorem torusFamilyParallelTransport_trans (y y' y'' : Y) :
    (torusFamilyParallelTransport P hinj y y').trans
        (torusFamilyParallelTransport P hinj y' y'') =
      torusFamilyParallelTransport P hinj y y'' := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  refine eq_torusFamilyParallelTransport P hinj _ fun l ↦ ?_
  simp

/-- Period parallel transport maps the period lattice at `y` into the period lattice at `y'`. -/
theorem torusFamilyParallelTransport_le_comap_range (y y' : Y) :
    LinearMap.range (P y) ≤
      (LinearMap.range (P y')).comap
        ((torusFamilyParallelTransport P hinj y y').toLinearMap.restrictScalars ℤ) := by
  rintro _ ⟨l, rfl⟩
  exact ⟨l, (torusFamilyParallelTransport_period P hinj y y' l).symm⟩

/-- Period parallel transport is jointly continuous in the source parameter, target parameter, and
vector when the periods vary continuously. -/
theorem continuous_torusFamilyParallelTransport [TopologicalSpace Y]
    (hcont : ∀ l, Continuous fun y ↦ P y l) :
    Continuous fun q : (Y × Y) × E ↦ torusFamilyParallelTransport P hinj q.1.1 q.1.2 q.2 := by
  let b := Module.Free.chooseBasis ℤ Λ
  have heq : (fun q : (Y × Y) × E ↦ torusFamilyParallelTransport P hinj q.1.1 q.1.2 q.2) =
      fun q : (Y × Y) × E ↦
        (periodBasis P b hinj q.1.2).equivFunL.symm
          ((periodBasis P b hinj q.1.1).equivFunL q.2) := by
    ext q
    rw [torusFamilyParallelTransport_eq_of_basis P hinj b]
    rfl
  rw [heq]
  exact ((continuous_periodBasis_equivFunL_symm P b hinj hcont).comp
    continuous_fst.snd).clm_apply
    (((continuous_periodBasis_equivFunL P b hinj hcont).comp continuous_fst.fst).clm_apply
      continuous_snd)

end ParallelTransport

/-! ### Canonical lifting function and fibration structure -/

section Fibration

variable {Y Λ E : Type*} [TopologicalSpace Y] [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))

/-- The canonical Hurewicz **lifting function** of a continuous family of full lattices, obtained by
transferring `LiftingFunction.fst` along `TauCeti.torusFamilyHomeomorphProd`. Lifting `[y, v]` along
a path `γ` starting at `y` traces `t ↦ [γ t, torusFamilyParallelTransport P hinj y (γ t) v]`. -/
def torusFamilyLiftingFunction :
    letI := periodAddAction P
    LiftingFunction ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩ :=
  letI := periodAddAction P
  let b := Module.Free.chooseBasis ℤ Λ
  (LiftingFunction.fst Y _).ofHomeomorphOver (torusFamilyHomeomorphProd P b hinj hcont)
    fun z ↦ show ContinuousMap.fst _ = (⟨torusFamilyProjection P, _⟩ : C(_, Y)) z from
      fst_torusFamilyHomeomorphProd P b hinj hcont z

/-- Lifting `[y, v]` along a path `γ` starting at `y` evaluates at `t` to
`[γ t, torusFamilyParallelTransport P hinj y (γ t) v]`. -/
@[simp]
theorem torusFamilyLiftingFunction_lift_mk (y : Y) (v : E) (γ : C(I, Y))
    (h : letI := periodAddAction P
      γ 0 = (⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩ : C(_, Y))
        (Quotient.mk _ (y, v)))
    (t : I) :
    letI := periodAddAction P
    (torusFamilyLiftingFunction P hcont hinj).lift (Quotient.mk _ (y, v)) γ h t =
      Quotient.mk _ (γ t, torusFamilyParallelTransport P hinj y (γ t) v) := by
  let _ := periodAddAction P
  dsimp only [torusFamilyLiftingFunction]
  rw [LiftingFunction.ofHomeomorphOver_lift_apply, LiftingFunction.fst_lift_apply,
    torusFamilyHomeomorphProd_mk, torusFamilyHomeomorphProd_symm_mk,
    torusFamilyParallelTransport_eq_of_basis P hinj (Module.Free.chooseBasis ℤ Λ)]
  rfl

/-- Transport along a path `γ : Path y₀ y₁` carries `[y₀, v]` to
`[y₁, torusFamilyParallelTransport P hinj y₀ y₁ v]`, depending only on the endpoints of `γ`. -/
theorem torusFamilyLiftingFunction_transport_mk {y₀ y₁ : Y} (γ : Path y₀ y₁) (v : E) :
    letI := periodAddAction P
    ((torusFamilyLiftingFunction P hcont hinj).transport γ
      ⟨Quotient.mk _ (y₀, v), torusFamilyProjection_mk P (y₀, v)⟩).1 =
      Quotient.mk _ (y₁, torusFamilyParallelTransport P hinj y₀ y₁ v) := by
  let _ := periodAddAction P
  refine (LiftingFunction.transport_apply_coe _ γ _).trans ?_
  rw [torusFamilyLiftingFunction_lift_mk]
  simp

/-- Read through `TauCeti.torusFamilyFiberHomeomorph`, transport along any path `γ : Path y₀ y₁` is
the continuous map `Submodule.orbitRelQuotientMap` induced on translation quotients by
`TauCeti.torusFamilyParallelTransport P hinj y₀ y₁`. -/
theorem torusFamilyLiftingFunction_transport_comp_fiberHomeomorph {y₀ y₁ : Y} (γ : Path y₀ y₁) :
    letI := periodAddAction P
    (ContinuousMap.mk (fun x ↦ (torusFamilyFiberHomeomorph P y₁ hcont).symm x)
        (torusFamilyFiberHomeomorph P y₁ hcont).continuous_symm).comp
        (((torusFamilyLiftingFunction P hcont hinj).transport γ).comp
          ⟨fun x ↦ torusFamilyFiberHomeomorph P y₀ hcont x,
            (torusFamilyFiberHomeomorph P y₀ hcont).continuous⟩) =
      ⟨(LinearMap.range (P y₀)).orbitRelQuotientMap (LinearMap.range (P y₁))
          ((torusFamilyParallelTransport P hinj y₀ y₁).toLinearMap.restrictScalars ℤ)
          (torusFamilyParallelTransport_le_comap_range P hinj y₀ y₁),
        (LinearMap.range (P y₀)).continuous_orbitRelQuotientMap (LinearMap.range (P y₁))
          (torusFamilyParallelTransport_le_comap_range P hinj y₀ y₁)
          (torusFamilyParallelTransport P hinj y₀ y₁).continuous⟩ := by
  let _ := periodAddAction P
  ext z
  induction z using Quotient.inductionOn with | h v =>
  refine (Homeomorph.symm_apply_eq (torusFamilyFiberHomeomorph P y₁ hcont)).mpr ?_
  apply Subtype.ext
  have hsub : ((⟨fun x ↦ torusFamilyFiberHomeomorph P y₀ hcont x,
        (torusFamilyFiberHomeomorph P y₀ hcont).continuous⟩ :
        C(_, (⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩ : C(_, Y)) ⁻¹' {y₀}))
        (Quotient.mk _ v)) =
      ⟨Quotient.mk _ (y₀, v), torusFamilyProjection_mk P (y₀, v)⟩ := by
    apply Subtype.ext
    -- Unfold the continuous map on `.1` to `torusFamilyFiberMap`.
    change (torusFamilyFiberHomeomorph P y₀ hcont (Quotient.mk _ v)).1 = Quotient.mk _ (y₀, v)
    simp
  refine (congrArg (fun x ↦ ((torusFamilyLiftingFunction P hcont hinj).transport γ x).1)
    hsub).trans ?_
  rw [torusFamilyLiftingFunction_transport_mk]
  -- Unfold `.1` on the target fiber homeomorphism to `torusFamilyFiberMap`.
  change Quotient.mk _ _ = (torusFamilyFiberHomeomorph P y₁ hcont _).1
  simp

/-- Pointwise form of `TauCeti.torusFamilyLiftingFunction_transport_comp_fiberHomeomorph`. -/
theorem torusFamilyLiftingFunction_transport_fiberHomeomorph {y₀ y₁ : Y} (γ : Path y₀ y₁)
    (z : AddAction.orbitRel.Quotient (LinearMap.range (P y₀)) E) :
    (torusFamilyFiberHomeomorph P y₁ hcont).symm
        ((torusFamilyLiftingFunction P hcont hinj).transport γ
          (torusFamilyFiberHomeomorph P y₀ hcont z)) =
      (LinearMap.range (P y₀)).orbitRelQuotientMap (LinearMap.range (P y₁))
        ((torusFamilyParallelTransport P hinj y₀ y₁).toLinearMap.restrictScalars ℤ)
        (torusFamilyParallelTransport_le_comap_range P hinj y₀ y₁) z :=
  DFunLike.congr_fun (torusFamilyLiftingFunction_transport_comp_fiberHomeomorph P hcont hinj γ) z

include hcont hinj in
/-- **A continuous family of full lattices is a Hurewicz fibration**, for test spaces in every
universe. -/
theorem isHurewiczFibration_torusFamilyProjection :
    letI := periodAddAction P
    IsHurewiczFibration.{w} (torusFamilyProjection P) :=
  letI := periodAddAction P
  (torusFamilyLiftingFunction P hcont hinj).isHurewiczFibration

/-- **A continuous family of full lattices is a Serre fibration.** -/
theorem mem_serreFibrations_torusFamilyProjection {Y E : Type u} {Λ : Type*} [TopologicalSpace Y]
    [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
    [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y)) :
    letI := periodAddAction P
    TopCat.serreFibrations
      (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩) :=
  letI := periodAddAction P
  (isHurewiczFibration_torusFamilyProjection.{0} P hcont hinj).mem_serreFibrations

end Fibration

/-! ### Base change and re-marking squares in `TopCat` -/

section BaseChangeSquare

variable {Y Z E : Type u} {Λ : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
  [AddCommGroup Λ] [AddCommGroup E] [TopologicalSpace E]
  (P : Y → Λ →ₗ[ℤ] E) (f : C(Z, Y))

/-- The commutative square in `TopCat` comparing the pulled-back torus family `(Z × E)/Λ → Z` with
`(Y × E)/Λ → Y` along `f : C(Z, Y)`. -/
theorem torusFamilyBaseChangeCommSq :
    letI := periodAddAction P
    letI := periodAddAction (P ∘ f)
    CommSq
      (TopCat.ofHom
        ⟨torusFamilyBaseChangeMap P f, continuous_torusFamilyBaseChangeMap P f f.continuous⟩)
      (TopCat.ofHom ⟨torusFamilyProjection (P ∘ f), continuous_torusFamilyProjection (P ∘ f)⟩)
      (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩)
      (TopCat.ofHom f) where
  w := by
    let _ := periodAddAction P
    let _ := periodAddAction (P ∘ f)
    ext x
    exact torusFamilyProjection_baseChangeMap P f x

/-- On the fiber over `z`, `torusFamilyBaseChangeCommSq` intertwines the canonical fiber
homeomorphisms of `P ∘ f` at `z` and of `P` at `f z`. -/
theorem torusFamilyBaseChangeCommSq_fiberMap_fiberHomeomorph [ContinuousAdd E]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (z : Z)
    (x : AddAction.orbitRel.Quotient (LinearMap.range ((P ∘ f) z)) E) :
    (torusFamilyBaseChangeCommSq P f).fiberMap z
        (torusFamilyFiberHomeomorph (P ∘ f) z (fun l ↦ (hcont l).comp f.continuous) x) =
      torusFamilyFiberHomeomorph P (f z) hcont x := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  induction x using Quotient.inductionOn with | h v =>
  apply Subtype.ext
  refine ((torusFamilyBaseChangeCommSq P f).fiberMap_apply_coe z _).trans ?_
  -- Align `Subtype.val` on `(TopCat.ofHom _).fiber _` with `{w | torusFamilyProjection _ w = _}`.
  change torusFamilyBaseChangeMap P f
      (torusFamilyFiberHomeomorph (P ∘ f) z (fun l ↦ (hcont l).comp f.continuous)
        (Quotient.mk _ v)).1 =
    (torusFamilyFiberHomeomorph P (f z) hcont (Quotient.mk _ v)).1
  rw [coe_torusFamilyFiberHomeomorph, coe_torusFamilyFiberHomeomorph,
    torusFamilyFiberMap_mk, torusFamilyFiberMap_mk, torusFamilyBaseChangeMap_mk]

/-- Read through `TauCeti.torusFamilyFiberHomeomorph`, the fiber map of
`torusFamilyBaseChangeCommSq` over `z` is the identity map of `E / range (P (f z))`. -/
theorem torusFamilyBaseChangeCommSq_fiberMap_comp_fiberHomeomorph [ContinuousAdd E]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (z : Z) :
    (ContinuousMap.mk (fun x ↦ (torusFamilyFiberHomeomorph P (f z) hcont).symm x)
        (torusFamilyFiberHomeomorph P (f z) hcont).continuous_symm).comp
        (((torusFamilyBaseChangeCommSq P f).fiberMap z).hom.comp
          ⟨fun x ↦ torusFamilyFiberHomeomorph (P ∘ f) z (fun l ↦ (hcont l).comp f.continuous) x,
            (torusFamilyFiberHomeomorph (P ∘ f) z
              (fun l ↦ (hcont l).comp f.continuous)).continuous⟩) =
      ContinuousMap.id _ := by
  ext x
  exact (Homeomorph.symm_apply_eq (torusFamilyFiberHomeomorph P (f z) hcont)).mpr
    (torusFamilyBaseChangeCommSq_fiberMap_fiberHomeomorph P f hcont z x)

/-- Base change of a continuous period family induces an isomorphism on every fiber in `TopCat`. -/
theorem isIso_torusFamilyBaseChangeCommSq_fiberMap [ContinuousAdd E]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (z : Z) :
    IsIso ((torusFamilyBaseChangeCommSq P f).fiberMap z) := by
  let _ := periodAddAction P
  let _ := periodAddAction (P ∘ f)
  let e := (torusFamilyFiberHomeomorph (P ∘ f) z (fun l ↦ (hcont l).comp f.continuous)).symm.trans
    (torusFamilyFiberHomeomorph P (f z) hcont)
  have heq : (torusFamilyBaseChangeCommSq P f).fiberMap z = (TopCat.isoOfHomeo e).hom := by
    ext x
    obtain ⟨w, rfl⟩ :=
      (torusFamilyFiberHomeomorph (P ∘ f) z (fun l ↦ (hcont l).comp f.continuous)).surjective x
    -- Compare the underlying elements in `AddAction.orbitRel.Quotient Λ (Y × E)`.
    change ((torusFamilyBaseChangeCommSq P f).fiberMap z _ :
        AddAction.orbitRel.Quotient Λ (Y × E)) =
      (e _ : AddAction.orbitRel.Quotient Λ (Y × E))
    rw [torusFamilyBaseChangeCommSq_fiberMap_fiberHomeomorph P f hcont z w]
    simp [e]
  rw [heq]
  infer_instance

end BaseChangeSquare

section Remark

variable {Y Λ Λ' E : Type*} [AddCommGroup Λ] [AddCommGroup Λ'] [AddCommGroup E]
  (P : Y → Λ →ₗ[ℤ] E) (α : Λ' ≃ₗ[ℤ] Λ)

private theorem mem_orbit_period_comp_equiv_iff {p q : Y × E} :
    (letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap; q ∈ AddAction.orbit Λ' p) ↔
      (letI := periodAddAction P; q ∈ AddAction.orbit Λ p) := by
  rw [mem_orbit_periodAddAction_iff, mem_orbit_periodAddAction_iff, LinearEquiv.range_comp]

/-- **Re-marking homeomorphism.** Precomposing every period map with a `ℤ`-linear equivalence
`α : Λ' ≃ₗ[ℤ] Λ` leaves the orbits on `Y × E` unchanged, inducing the identity homeomorphism
`[y, v] ↦ [y, v]` between the period quotients over `Y`. -/
def torusFamilyRemarkHomeomorph [TopologicalSpace Y] [TopologicalSpace E] :
    letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
    letI := periodAddAction P
    AddAction.orbitRel.Quotient Λ' (Y × E) ≃ₜ AddAction.orbitRel.Quotient Λ (Y × E) :=
  letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
  letI := periodAddAction P
  { toFun := Quotient.map id fun _ _ h ↦ (mem_orbit_period_comp_equiv_iff P α).1 h
    invFun := Quotient.map id fun _ _ h ↦ (mem_orbit_period_comp_equiv_iff P α).2 h
    left_inv := fun x ↦ by induction x using Quotient.inductionOn; rfl
    right_inv := fun x ↦ by induction x using Quotient.inductionOn; rfl
    continuous_toFun := continuous_id.quotient_map' _
    continuous_invFun := continuous_id.quotient_map' _ }

@[simp]
theorem torusFamilyRemarkHomeomorph_mk [TopologicalSpace Y] [TopologicalSpace E] (p : Y × E) :
    torusFamilyRemarkHomeomorph P α (Quotient.mk _ p) = Quotient.mk _ p :=
  (rfl)

@[simp]
theorem torusFamilyRemarkHomeomorph_symm_mk [TopologicalSpace Y] [TopologicalSpace E] (p : Y × E) :
    (torusFamilyRemarkHomeomorph P α).symm (Quotient.mk _ p) = Quotient.mk _ p :=
  (rfl)

@[simp]
theorem torusFamilyProjection_remarkHomeomorph [TopologicalSpace Y] [TopologicalSpace E]
    (x : letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
      AddAction.orbitRel.Quotient Λ' (Y × E)) :
    torusFamilyProjection P (torusFamilyRemarkHomeomorph P α x) =
      torusFamilyProjection (fun y ↦ (P y).comp α.toLinearMap) x := by
  induction x using Quotient.inductionOn
  simp

end Remark

section RemarkSquare

variable {Y E : Type u} {Λ Λ' : Type*} [TopologicalSpace Y] [AddCommGroup Λ] [AddCommGroup Λ']
  [AddCommGroup E] [TopologicalSpace E] (P : Y → Λ →ₗ[ℤ] E) (α : Λ' ≃ₗ[ℤ] Λ)

/-- The commutative square in `TopCat` over `𝟙 (TopCat.of Y)` induced by re-marking the lattice by
`α : Λ' ≃ₗ[ℤ] Λ`. -/
theorem torusFamilyRemarkCommSq :
    letI := periodAddAction fun y ↦ (P y).comp α.toLinearMap
    letI := periodAddAction P
    CommSq
      (TopCat.ofHom (torusFamilyRemarkHomeomorph P α : C(_, _)))
      (TopCat.ofHom ⟨torusFamilyProjection fun y ↦ (P y).comp α.toLinearMap,
        continuous_torusFamilyProjection _⟩)
      (TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩)
      (𝟙 (TopCat.of Y)) where
  w := by
    let _ := periodAddAction fun y ↦ (P y).comp α.toLinearMap
    let _ := periodAddAction P
    ext x
    exact torusFamilyProjection_remarkHomeomorph P α x

/-- On the fiber over `y`, `torusFamilyRemarkCommSq` intertwines the canonical fiber homeomorphisms
via the identity map of `E` between the equal period lattices. -/
theorem torusFamilyRemarkCommSq_fiberMap_fiberHomeomorph [ContinuousAdd E]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (y : Y)
    (x : AddAction.orbitRel.Quotient (LinearMap.range ((P y).comp α.toLinearMap)) E) :
    (torusFamilyRemarkCommSq P α).fiberMap y
        (torusFamilyFiberHomeomorph (fun y ↦ (P y).comp α.toLinearMap) y
          (fun l' ↦ hcont (α l')) x) =
      torusFamilyFiberHomeomorph P y hcont
        ((LinearMap.range ((P y).comp α.toLinearMap)).orbitRelQuotientMap (LinearMap.range (P y))
          LinearMap.id (by simp) x) := by
  let _ := periodAddAction fun y ↦ (P y).comp α.toLinearMap
  let _ := periodAddAction P
  induction x using Quotient.inductionOn with | h v =>
  apply Subtype.ext
  refine ((torusFamilyRemarkCommSq P α).fiberMap_apply_coe y _).trans ?_
  -- Align `Subtype.val` on `(TopCat.ofHom _).fiber _` with `{w | torusFamilyProjection _ w = y}`.
  change torusFamilyRemarkHomeomorph P α
      (torusFamilyFiberHomeomorph (fun y ↦ (P y).comp α.toLinearMap) y
        (fun l' ↦ hcont (α l')) (Quotient.mk _ v)).1 =
    (torusFamilyFiberHomeomorph P y hcont _).1
  simp

/-- Read through `TauCeti.torusFamilyFiberHomeomorph`, the fiber map of `torusFamilyRemarkCommSq`
over `y` is the `Submodule.orbitRelQuotientMap` induced by `LinearMap.id` between the equal period
lattices. -/
theorem torusFamilyRemarkCommSq_fiberMap_comp_fiberHomeomorph [ContinuousAdd E]
    (hcont : ∀ l, Continuous fun y ↦ P y l) (y : Y) :
    (ContinuousMap.mk (fun x ↦ (torusFamilyFiberHomeomorph P y hcont).symm x)
        (torusFamilyFiberHomeomorph P y hcont).continuous_symm).comp
        (((torusFamilyRemarkCommSq P α).fiberMap y).hom.comp
          ⟨fun x ↦ torusFamilyFiberHomeomorph (fun y ↦ (P y).comp α.toLinearMap) y
              (fun l' ↦ hcont (α l')) x,
            (torusFamilyFiberHomeomorph (fun y ↦ (P y).comp α.toLinearMap) y
              (fun l' ↦ hcont (α l'))).continuous⟩) =
      ⟨(LinearMap.range ((P y).comp α.toLinearMap)).orbitRelQuotientMap (LinearMap.range (P y))
          LinearMap.id (by simp),
        (LinearMap.range ((P y).comp α.toLinearMap)).continuous_orbitRelQuotientMap
          (LinearMap.range (P y)) (by simp) continuous_id⟩ := by
  ext x
  exact (Homeomorph.symm_apply_eq (torusFamilyFiberHomeomorph P y hcont)).mpr
    (torusFamilyRemarkCommSq_fiberMap_fiberHomeomorph P α hcont y x)

/-- Re-marking the lattice induces an isomorphism on every fiber in `TopCat`. -/
instance isIso_torusFamilyRemarkCommSq_fiberMap (y : Y) :
    IsIso ((torusFamilyRemarkCommSq P α).fiberMap y) := by
  let _ := periodAddAction fun y ↦ (P y).comp α.toLinearMap
  let _ := periodAddAction P
  let p' : TopCat.of (AddAction.orbitRel.Quotient Λ' (Y × E)) ⟶ TopCat.of Y :=
    TopCat.ofHom ⟨torusFamilyProjection fun y ↦ (P y).comp α.toLinearMap,
      continuous_torusFamilyProjection _⟩
  let p : TopCat.of (AddAction.orbitRel.Quotient Λ (Y × E)) ⟶ TopCat.of Y :=
    TopCat.ofHom ⟨torusFamilyProjection P, continuous_torusFamilyProjection P⟩
  have hmem₁ : ∀ x : p'.fiber y,
      torusFamilyRemarkHomeomorph P α x.1 ∈ p.hom ⁻¹' {(𝟙 (TopCat.of Y)) y} :=
    fun x ↦ (torusFamilyProjection_remarkHomeomorph P α x.1).trans x.2
  have hmem₂ : ∀ x : p.fiber ((𝟙 (TopCat.of Y)) y),
      (torusFamilyRemarkHomeomorph P α).symm x.1 ∈ p'.hom ⁻¹' {y} := fun x ↦ by
    have hproj :=
      torusFamilyProjection_remarkHomeomorph P α ((torusFamilyRemarkHomeomorph P α).symm x.1)
    rw [Homeomorph.apply_symm_apply] at hproj
    exact hproj.symm.trans x.2
  let e : p'.fiber y ≃ₜ p.fiber ((𝟙 (TopCat.of Y)) y) :=
    { toFun x := ⟨torusFamilyRemarkHomeomorph P α x.1, hmem₁ x⟩
      invFun x := ⟨(torusFamilyRemarkHomeomorph P α).symm x.1, hmem₂ x⟩
      left_inv x := Subtype.ext ((torusFamilyRemarkHomeomorph P α).symm_apply_apply x.1)
      right_inv x := Subtype.ext ((torusFamilyRemarkHomeomorph P α).apply_symm_apply x.1)
      continuous_toFun :=
        ((torusFamilyRemarkHomeomorph P α).continuous.comp continuous_subtype_val).subtype_mk hmem₁
      continuous_invFun :=
        ((torusFamilyRemarkHomeomorph P α).symm.continuous.comp
          continuous_subtype_val).subtype_mk hmem₂ }
  have heq : (torusFamilyRemarkCommSq P α).fiberMap y = (TopCat.isoOfHomeo e).hom := by
    ext x
    exact (torusFamilyRemarkCommSq P α).fiberMap_apply_coe y x
  rw [heq]
  infer_instance

end RemarkSquare

end TauCeti
