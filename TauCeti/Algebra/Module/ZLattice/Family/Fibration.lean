/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient
public import TauCeti.Algebra.Module.ZLattice.Family.Fiber
public import TauCeti.Algebra.Module.ZLattice.Family.HomeomorphProd
public import TauCeti.Topology.Algebra.Module.Quotient
public import TauCeti.Topology.Homotopy.HurewiczFibration.Transport

/-!
# Parallel transport and Hurewicz fibration structure of a family of tori

Let `P : Y → (Λ →ₗ[ℤ] E)` be a continuous family of full lattices in a finite-dimensional real
normed space `E`, with `Λ` finite free over `ℤ`. For any `ℤ`-basis `b` of `Λ`, composing the
coordinate map of `TauCeti.periodBasis P b hinj y` with the inverse coordinate map at `y'` defines
`TauCeti.torusFamilyParallelTransport P hinj y y' : E ≃L[ℝ] E`, the unique real-linear isomorphism
carrying `P y l` to `P y' l` for all `l : Λ` (independent of `b`).

Transferring `LiftingFunction.fst` along `TauCeti.torusFamilyHomeomorphProd` equips
`(Y × E)/Λ → Y` with `TauCeti.torusFamilyLiftingFunction`, lifting `[y, v]` along `γ` with `γ 0 = y`
to `t ↦ [γ t, torusFamilyParallelTransport P hinj y (γ t) v]`. Hence `TauCeti.torusFamilyProjection`
is a Hurewicz and Serre fibration, and under `TauCeti.torusFamilyFiberHomeomorph` its fiber
transport along any path is `Submodule.orbitRelQuotientMap` of `torusFamilyParallelTransport`.

## Main definitions

* `TauCeti.torusFamilyParallelTransport`: the isomorphism `E ≃L[ℝ] E` sending `P y l` to `P y' l`.
* `TauCeti.torusFamilyLiftingFunction`: canonical `LiftingFunction` for `torusFamilyProjection P`.

## Main results

* `TauCeti.torusFamilyParallelTransport_period`, `TauCeti.eq_torusFamilyParallelTransport`,
  `TauCeti.torusFamilyParallelTransport_eq_of_basis`: uniqueness and basis independence of
  `torusFamilyParallelTransport`.
* `TauCeti.torusFamilyLiftingFunction_transport_comp_fiberHomeomorph`,
  `TauCeti.torusFamilyLiftingFunction_transport_fiberHomeomorph`: path transport acts on translation
  quotients as `Submodule.orbitRelQuotientMap` of `torusFamilyParallelTransport`.
* `TauCeti.isHurewiczFibration_torusFamilyProjection`,
  `TauCeti.mem_serreFibrations_torusFamilyProjection`: Hurewicz and Serre fibration properties.
-/

public section

noncomputable section

open Function Module unitInterval

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
      (periodBasis P b hinj y).equivFunL.trans (periodBasis P b hinj y').equivFunL.symm :=
  ContinuousLinearEquiv.toLinearEquiv_injective <| LinearEquiv.toLinearMap_injective
    (eq_torusFamilyParallelTransport P hinj _
      (periodBasis_equivFunL_trans_symm_period P hinj b y y')).symm

@[simp]
theorem torusFamilyParallelTransport_self (y : Y) :
    torusFamilyParallelTransport P hinj y y = ContinuousLinearEquiv.refl ℝ E :=
  ContinuousLinearEquiv.toLinearEquiv_injective <| LinearEquiv.toLinearMap_injective
    (eq_torusFamilyParallelTransport P hinj LinearMap.id fun _ ↦ rfl).symm

@[simp]
theorem torusFamilyParallelTransport_symm (y y' : Y) :
    (torusFamilyParallelTransport P hinj y y').symm = torusFamilyParallelTransport P hinj y' y :=
  ContinuousLinearEquiv.toLinearEquiv_injective <| LinearEquiv.toLinearMap_injective <|
    eq_torusFamilyParallelTransport P hinj _ fun l ↦
      (torusFamilyParallelTransport P hinj y y').symm_apply_eq.mpr
        (torusFamilyParallelTransport_period P hinj y y' l).symm

@[simp]
theorem torusFamilyParallelTransport_trans (y y' y'' : Y) :
    (torusFamilyParallelTransport P hinj y y').trans
        (torusFamilyParallelTransport P hinj y' y'') =
      torusFamilyParallelTransport P hinj y y'' :=
  ContinuousLinearEquiv.toLinearEquiv_injective <| LinearEquiv.toLinearMap_injective <|
    eq_torusFamilyParallelTransport P hinj _ fun l ↦ by simp

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
  simp_rw [torusFamilyParallelTransport_eq_of_basis P hinj b, ContinuousLinearEquiv.trans_apply]
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
    fun z ↦ by simp

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
    torusFamilyParallelTransport_eq_of_basis P hinj (Module.Free.chooseBasis ℤ Λ),
    ContinuousLinearEquiv.trans_apply]
  simp [← ContinuousLinearEquiv.coe_toLinearEquiv]

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

end TauCeti
