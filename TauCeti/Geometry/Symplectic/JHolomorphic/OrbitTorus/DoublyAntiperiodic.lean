/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Antiperiodic
public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.ModeSobolev
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The orbit-torus operator twisted along both circle factors

Let `C = S¹ × γ` be the orbit torus of a closed orbit `γ` of the suspension flow of a surface
diffeomorphism, and let `D = ∂s + A`, `A ζ = J₀ (ζ' - S ζ)`, be its normal operator in a unitary
trivialization, as in `TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.ModeSobolev`.
Of the four real sign characters of the torus, two are nontrivial along the circle factor; for
these `D` acts on maps antiperiodic in `s`. The file `ModeSobolev` treats the one that is
trivial along `γ`. This file treats the remaining one, nontrivial along both factors, and proves
that `D` is invertible on it, along the whole path to the complex-linear operator `∂s + J₀ ∂t`.

**The spaces.** If `γ` has period `T / 2`, a map twisted along `γ` satisfies
`u (s, t + T / 2) = -u (s, t)`. Such a map has period `T` in `t`, and we realize it on that double
cover of `γ`: in the modes `u = ∑ₖ cos (ωₖ s) aₖ(t) + sin (ωₖ s) bₖ(t)` of
`TauCeti.torusModeSobolev F ω` with the antiperiodic frequencies `ωₖ = (2k + 1)π/ℓ`, every loop
`aₖ, bₖ` of period `T` is antiperiodic of antiperiod `T / 2`, that is, its even Fourier
coefficients vanish (`TauCeti.CircleSobolev.antiperiodic`,
`TauCeti.CircleSobolev.mem_antiperiodic_iff_toContinuousMap`). These maps form the closed subspace
`TauCeti.doublyAntiperiodicSobolev F ℓ` of the Sobolev space `H¹`, and the corresponding mode
sequences in `H⁰(F)²` form the subspace `TauCeti.doublyAntiperiodicL2 F` of the `L²` target. Both
are subspaces of the ambient spaces of mode sequences, the first contained in
`TauCeti.torusModeSobolev F ω` (`TauCeti.doublyAntiperiodicSobolev_le_torusModeSobolev`), rather
than subspaces of `TauCeti.torusModeSobolev F ω` itself: on a subspace of a subspace, instance
synthesis does not find the operator norm of the restricted operators, which their continuity and
determinant lines need.

**The operator.** The loop `S` of the orbit has period `T / 2`; read on the double cover it is a
loop of period `T` with `S (t + T / 2) = S t`. The rotation by `T / 2` then commutes with `A`
(`TauCeti.CircleSobolev.loopOperator_rotate_of_invariant`), so `D` maps the twisted maps to
twisted maps, and restricts to the operator `TauCeti.doublyAntiperiodicTorusOperator T ℓ S`
between the two subspaces.

**Invertibility.** On the double cover the operator `D` is invertible, for every infinitesimally
symplectic loop `S` (`TauCeti.isInvertible_torusModeOperator_antiperiodic`). It commutes with the
half rotation `R` of every mode, and the twisted maps are the solutions of `R x = -x`. If `D x` is
twisted, then `D (R x) = R (D x) = -D x = D (-x)`, so `R x = -x` by injectivity: the inverse of
`D` maps twisted targets to twisted maps. Hence the restricted operator is invertible
(`TauCeti.isInvertible_doublyAntiperiodicTorusOperator`, through
`ContinuousLinearMap.IsInvertible.codRestrictOfTower_comp`). For `S = 0` it is complex linear
(`TauCeti.doublyAntiperiodicTorusOperator_zero_apply_smul`,
`TauCeti.exists_restrictScalars_eq_doublyAntiperiodicTorusOperator_zero`). Since `τ • S` is again
infinitesimally symplectic and invariant under the half rotation, every operator of the path
`τ ↦ ∂s + J₀ (∂t - τ S)` is invertible.

**Continuity.** The restricted operator depends continuously, in operator norm, on the loop
(`TauCeti.continuous_doublyAntiperiodicTorusOperator`), and so along every continuous path of
invariant loops (`TauCeti.continuousOn_doublyAntiperiodicTorusOperator`): composed with the
inclusion of the target, which induces the topology of the operators, it is the operator
`∂s + A` of the double cover (`TauCeti.continuous_torusModeOperator`) composed with the inclusion
of the domain.

## Main definitions

* `TauCeti.doublyAntiperiodicSobolev F ℓ`: the maps of `TauCeti.torusModeSobolev F ω`, for the
  antiperiodic frequencies `ωₖ = (2k + 1)π/ℓ`, whose modes are antiperiodic of antiperiod `T / 2`
  in `t`.
* `TauCeti.doublyAntiperiodicL2 F`: the mode sequences in `H⁰(F)²` whose modes are antiperiodic.
* `TauCeti.doublyAntiperiodicTorusOperator T ℓ S hS`: for a loop `S` invariant under the rotation
  by `T / 2`, the restriction of `∂s + J₀ (∂t - S)` to these subspaces.

## Main results

* `TauCeti.torusModeOperator_mem_doublyAntiperiodicL2`: the orbit-torus operator maps
  doubly twisted maps to doubly twisted targets.
* `TauCeti.doublyAntiperiodicTorusOperator_zero_apply_smul`,
  `TauCeti.exists_restrictScalars_eq_doublyAntiperiodicTorusOperator_zero`: the reference
  operator `∂s + J₀ ∂t` is complex linear.
* `TauCeti.continuous_doublyAntiperiodicTorusOperator`,
  `TauCeti.continuousOn_doublyAntiperiodicTorusOperator`: continuous dependence on the loop.
* `TauCeti.isInvertible_doublyAntiperiodicTorusOperator`: invertibility for every infinitesimally
  symplectic loop invariant under the rotation by `T / 2`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* D. Salamon, *Lectures on Floer homology*, in Symplectic Geometry and Topology,
  IAS/Park City Math. Ser. 7 (1999), Section 2, for the operator `∂s + A` with `A` self-adjoint.
-/

public section

noncomputable section

open Complex
open scoped Real lp

namespace TauCeti

open CircleSobolev

/-- The product of the two mode spaces carrying `TauCeti.torusModeSobolev`. -/
local notation "𝕏[" F "]" => ℓ²(ℕ, WithLp 2 (CircleSobolev 1 F × CircleSobolev 1 F)) ×
  ℓ²(ℕ, WithLp 2 (CircleSobolev 0 F × CircleSobolev 0 F))

/-- The `L²` space of mode sequences, the target of `TauCeti.torusModeOperator`. -/
local notation "𝕐[" F "]" => ℓ²(ℕ, WithLp 2 (CircleSobolev 0 F × CircleSobolev 0 F))

section Space

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- For continuous mode maps `φ k`, the set of `x` all of whose modes `φ k x` are pairs of
antiperiodic loops is closed, as an intersection of preimages of the closed subspaces of
antiperiodic loops. -/
private theorem isClosed_setOf_forall_mem_antiperiodic {X : Type*} [TopologicalSpace X] (s : ℝ)
    {φ : ℕ → X → WithLp 2 (CircleSobolev s F × CircleSobolev s F)} (hφ : ∀ k, Continuous (φ k)) :
    IsClosed {x | ∀ k, (φ k x).fst ∈ antiperiodic s F ∧ (φ k x).snd ∈ antiperiodic s F} := by
  simp only [Set.ofPred_forall, Set.ofPred_and]
  exact isClosed_iInter fun k ↦
    (isClosed_antiperiodic.preimage (continuous_fst.comp ((WithLp.prod_continuous_ofLp 2 _ _).comp
      (hφ k)))).inter
    (isClosed_antiperiodic.preimage (continuous_snd.comp ((WithLp.prod_continuous_ofLp 2 _ _).comp
      (hφ k))))

variable (F) in
/-- The Sobolev space `H¹` of maps `u(s, t)` antiperiodic of antiperiod `ℓ` in `s` and antiperiodic
of antiperiod `T / 2` in `t`, for any period `T` of the modes: the elements of
`TauCeti.torusModeSobolev F ω` with the antiperiodic frequencies `ωₖ = (2k + 1)π/ℓ` all of whose
modes `aₖ, bₖ` are antiperiodic loops (`TauCeti.CircleSobolev.antiperiodic`). It is a subspace of
the ambient space of pairs of mode sequences, contained in `TauCeti.torusModeSobolev F ω`
(`TauCeti.doublyAntiperiodicSobolev_le_torusModeSobolev`). -/
def doublyAntiperiodicSobolev (ℓ : ℝ) : Submodule ℂ 𝕏[F] where
  carrier := {x | x ∈ torusModeSobolev F (fun k : ℕ ↦ (2 * k + 1) * π / ℓ) ∧
    ∀ k, (x.1 k).fst ∈ antiperiodic 1 F ∧ (x.1 k).snd ∈ antiperiodic 1 F}
  add_mem' hx hy := ⟨add_mem hx.1 hy.1,
    fun k ↦ ⟨add_mem (hx.2 k).1 (hy.2 k).1, add_mem (hx.2 k).2 (hy.2 k).2⟩⟩
  zero_mem' := ⟨zero_mem _, fun _ ↦ ⟨zero_mem _, zero_mem _⟩⟩
  smul_mem' c _ hx := ⟨Submodule.smul_mem _ c hx.1,
    fun k ↦ ⟨Submodule.smul_mem _ c (hx.2 k).1, Submodule.smul_mem _ c (hx.2 k).2⟩⟩

theorem mem_doublyAntiperiodicSobolev_iff {ℓ : ℝ} {x : 𝕏[F]} :
    x ∈ doublyAntiperiodicSobolev F ℓ ↔
      x ∈ torusModeSobolev F (fun k : ℕ ↦ (2 * k + 1) * π / ℓ) ∧
        ∀ k, (x.1 k).fst ∈ antiperiodic 1 F ∧ (x.1 k).snd ∈ antiperiodic 1 F :=
  Iff.rfl

theorem doublyAntiperiodicSobolev_le_torusModeSobolev (ℓ : ℝ) :
    doublyAntiperiodicSobolev F ℓ ≤ torusModeSobolev F fun k : ℕ ↦ (2 * k + 1) * π / ℓ :=
  fun _ hx ↦ hx.1

/-- `TauCeti.doublyAntiperiodicSobolev` is closed: it is the intersection of the closed subspace
`TauCeti.torusModeSobolev F ω` with preimages of the closed subspaces of antiperiodic loops. -/
theorem isClosed_doublyAntiperiodicSobolev (ℓ : ℝ) :
    IsClosed (doublyAntiperiodicSobolev F ℓ : Set 𝕏[F]) :=
  (isClosed_torusModeSobolev _).inter <| isClosed_setOf_forall_mem_antiperiodic 1 fun k ↦
    (lp.evalCLM ℂ _ 2 k).continuous.comp continuous_fst

/-- The Sobolev space `H¹` of maps antiperiodic in both factors is complete. -/
instance [CompleteSpace F] (ℓ : ℝ) : CompleteSpace (doublyAntiperiodicSobolev F ℓ) :=
  (isClosed_doublyAntiperiodicSobolev ℓ).completeSpace_coe

variable (F) in
/-- The `L²` space of maps antiperiodic in both factors, in modes: the mode sequences in `H⁰(F)²`
all of whose modes are antiperiodic loops (`TauCeti.CircleSobolev.antiperiodic`). It is the target
of `TauCeti.doublyAntiperiodicTorusOperator`. -/
def doublyAntiperiodicL2 : Submodule ℂ 𝕐[F] where
  carrier := {y | ∀ k, (y k).fst ∈ antiperiodic 0 F ∧ (y k).snd ∈ antiperiodic 0 F}
  add_mem' hx hy k := ⟨add_mem (hx k).1 (hy k).1, add_mem (hx k).2 (hy k).2⟩
  zero_mem' _ := ⟨zero_mem _, zero_mem _⟩
  smul_mem' c _ hx k := ⟨Submodule.smul_mem _ c (hx k).1, Submodule.smul_mem _ c (hx k).2⟩

theorem mem_doublyAntiperiodicL2_iff {y : 𝕐[F]} :
    y ∈ doublyAntiperiodicL2 F ↔
      ∀ k, (y k).fst ∈ antiperiodic 0 F ∧ (y k).snd ∈ antiperiodic 0 F :=
  Iff.rfl

/-- `TauCeti.doublyAntiperiodicL2` is closed, as an intersection of preimages of the closed
subspaces of antiperiodic loops. -/
theorem isClosed_doublyAntiperiodicL2 : IsClosed (doublyAntiperiodicL2 F : Set 𝕐[F]) :=
  isClosed_setOf_forall_mem_antiperiodic 0 fun k ↦ (lp.evalCLM ℂ _ 2 k).continuous

/-- The `L²` space of maps antiperiodic in both factors is complete. -/
instance [CompleteSpace F] : CompleteSpace (doublyAntiperiodicL2 F) :=
  isClosed_doublyAntiperiodicL2.completeSpace_coe

end Space

section Operator

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpaceDoublyAntiperiodic : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-- The inclusion of the maps antiperiodic in both factors into the maps antiperiodic in `s`,
`TauCeti.doublyAntiperiodicSobolev F ℓ ≤ TauCeti.torusModeSobolev F ω`. -/
private def inclusionTorusModeSobolev (ℓ : ℝ) :
    doublyAntiperiodicSobolev F ℓ →L[ℂ] torusModeSobolev F fun k : ℕ ↦ (2 * k + 1) * π / ℓ :=
  (doublyAntiperiodicSobolev F ℓ).subtypeL.codRestrict _ fun x ↦
    doublyAntiperiodicSobolev_le_torusModeSobolev ℓ x.property

omit [FiniteDimensional ℂ F] in
@[simp]
private theorem inclusionTorusModeSobolev_apply (ℓ : ℝ) (x : doublyAntiperiodicSobolev F ℓ) :
    inclusionTorusModeSobolev ℓ x =
      Submodule.inclusion (doublyAntiperiodicSobolev_le_torusModeSobolev ℓ) x :=
  (rfl)

/-- For a loop `S` invariant under the rotation by `T / 2`, the orbit-torus operator `∂s + A` maps
maps antiperiodic in both factors to targets antiperiodic in both factors. -/
theorem torusModeOperator_mem_doublyAntiperiodicL2 {ℓ : ℝ}
    {S : C(AddCircle T, F →L[ℝ] F)} (hS : ∀ t, S (t + (T / 2 : ℝ)) = S t)
    {x : torusModeSobolev F fun k : ℕ ↦ (2 * k + 1) * π / ℓ}
    (hx : (x : 𝕏[F]) ∈ doublyAntiperiodicSobolev F ℓ) :
    torusModeOperator T (fun k : ℕ ↦ (2 * k + 1) * π / ℓ) S x ∈ doublyAntiperiodicL2 F := fun k ↦ by
  rw [torusModeOperator_apply_apply_eq]
  exact ⟨add_mem (Submodule.smul_mem _ I (loopOperator_mem_antiperiodic hS (hx.2 k).1))
      (Submodule.smul_of_tower_mem _ _ ((inclusion_mem_supported_iff _).2 (hx.2 k).2)),
    sub_mem (Submodule.smul_mem _ I (loopOperator_mem_antiperiodic hS (hx.2 k).2))
      (Submodule.smul_of_tower_mem _ _ ((inclusion_mem_supported_iff _).2 (hx.2 k).1))⟩

/-- The orbit-torus operator `∂s + A`, `A ζ = J₀ (ζ' - S ζ)`, on maps antiperiodic of antiperiod
`ℓ` in `s` and of antiperiod `T / 2` in `t`, for a loop `S` of period `T` invariant under the
rotation by `T / 2`: the restriction of `TauCeti.torusModeOperator T ω S`, `ωₖ = (2k + 1)π/ℓ`, to
`TauCeti.doublyAntiperiodicSobolev F ℓ`, with values in `TauCeti.doublyAntiperiodicL2 F`. -/
def doublyAntiperiodicTorusOperator (ℓ : ℝ) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t, S (t + (T / 2 : ℝ)) = S t) :
    doublyAntiperiodicSobolev F ℓ →L[ℝ] doublyAntiperiodicL2 F :=
  (torusModeOperator T (fun k : ℕ ↦ (2 * k + 1) * π / ℓ) S ∘L
    (inclusionTorusModeSobolev ℓ).restrictScalars ℝ).codRestrictOfTower fun x ↦ by
      simpa using torusModeOperator_mem_doublyAntiperiodicL2 T hS
        (x := Submodule.inclusion (doublyAntiperiodicSobolev_le_torusModeSobolev ℓ) x) (by simp)

@[simp]
theorem coe_doublyAntiperiodicTorusOperator_apply (ℓ : ℝ) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t, S (t + (T / 2 : ℝ)) = S t) (x : doublyAntiperiodicSobolev F ℓ) :
    (doublyAntiperiodicTorusOperator T ℓ S hS x : 𝕐[F]) =
      torusModeOperator T (fun k : ℕ ↦ (2 * k + 1) * π / ℓ) S
        (Submodule.inclusion (doublyAntiperiodicSobolev_le_torusModeSobolev ℓ) x) := by
  rw [doublyAntiperiodicTorusOperator, ContinuousLinearMap.coe_codRestrictOfTower_apply]
  simp

/-- **The reference operator is complex linear.** For `S = 0` the operator `∂s + J₀ ∂t` on maps
antiperiodic in both factors commutes with multiplication by complex scalars, the complex
structure acting by `J₀`. -/
theorem doublyAntiperiodicTorusOperator_zero_apply_smul (ℓ : ℝ) (c : ℂ)
    (x : doublyAntiperiodicSobolev F ℓ) :
    doublyAntiperiodicTorusOperator T ℓ 0 (fun _ ↦ rfl) (c • x) =
      c • doublyAntiperiodicTorusOperator T ℓ 0 (fun _ ↦ rfl) x :=
  Subtype.ext <| by
    have h := coe_doublyAntiperiodicTorusOperator_apply (F := F) T ℓ 0 fun _ ↦ rfl
    rw [Submodule.coe_smul, h, h, map_smul, torusModeOperator_zero_apply_smul]

/-- **The reference operator as a complex-linear map.** For `S = 0` the operator `∂s + J₀ ∂t` on
maps antiperiodic in both factors is the restriction of scalars of a bounded complex-linear map,
for the complex structures given by `J₀`. -/
theorem exists_restrictScalars_eq_doublyAntiperiodicTorusOperator_zero (ℓ : ℝ) :
    ∃ L : doublyAntiperiodicSobolev F ℓ →L[ℂ] doublyAntiperiodicL2 F,
      L.restrictScalars ℝ = doublyAntiperiodicTorusOperator T ℓ 0 fun _ ↦ rfl :=
  ⟨{ toFun := doublyAntiperiodicTorusOperator T ℓ 0 fun _ ↦ rfl
     map_add' := map_add _
     map_smul' := doublyAntiperiodicTorusOperator_zero_apply_smul T ℓ
     cont := (doublyAntiperiodicTorusOperator T ℓ 0 fun _ ↦ rfl).continuous }, rfl⟩

/-- **Continuous dependence on the loop.** The orbit-torus operator on maps antiperiodic in both
factors depends continuously, in operator norm, on the loop `S`, with its uniform norm, among the
loops invariant under the rotation by `T / 2`. -/
theorem continuous_doublyAntiperiodicTorusOperator (ℓ : ℝ) :
    Continuous fun S : {S : C(AddCircle T, F →L[ℝ] F) // ∀ t, S (t + (T / 2 : ℝ)) = S t} ↦
      doublyAntiperiodicTorusOperator T ℓ S.val S.property := by
  -- Composed with the inclusion of the target into `L²`, which induces the topology of the
  -- operators, the operator is `∂s + A` composed with the inclusion of the domain.
  refine (ContinuousLinearMap.isInducing_postcomp (E := doublyAntiperiodicSobolev F ℓ)
    (σ := RingHom.id ℝ) ((doublyAntiperiodicL2 F).subtypeL.restrictScalars ℝ)
    Topology.IsInducing.subtypeVal).continuous_iff.2 ?_
  have h : (fun S : {S : C(AddCircle T, F →L[ℝ] F) // ∀ t, S (t + (T / 2 : ℝ)) = S t} ↦
      ((doublyAntiperiodicL2 F).subtypeL.restrictScalars ℝ).comp
        (doublyAntiperiodicTorusOperator T ℓ S.val S.property)) = fun S ↦
      (torusModeOperator T (fun k : ℕ ↦ (2 * k + 1) * π / ℓ) S.val).comp
        ((inclusionTorusModeSobolev ℓ).restrictScalars ℝ) :=
    funext fun S ↦ ContinuousLinearMap.ext fun x ↦ by
      simp [coe_doublyAntiperiodicTorusOperator_apply]
  rw [Function.comp_def, h]
  exact (ContinuousLinearMap.precomp _
    ((inclusionTorusModeSobolev ℓ).restrictScalars ℝ)).continuous.comp
      ((continuous_torusModeOperator T _).comp continuous_subtypeVal)

/-- Along a family of loops `M x` invariant under the rotation by `T / 2`, continuous on `s` in the
uniform norm, the orbit-torus operators on maps antiperiodic in both factors are continuous on `s`
in operator norm. -/
theorem continuousOn_doublyAntiperiodicTorusOperator {X : Type*} [TopologicalSpace X] (ℓ : ℝ)
    {M : X → C(AddCircle T, F →L[ℝ] F)} {s : Set X} (hM : ContinuousOn M s)
    (hM' : ∀ x t, M x (t + (T / 2 : ℝ)) = M x t) :
    ContinuousOn (fun x ↦ doublyAntiperiodicTorusOperator T ℓ (M x) (hM' x)) s := by
  refine (continuous_doublyAntiperiodicTorusOperator T ℓ).comp_continuousOn
    (f := fun x ↦ ⟨M x, hM' x⟩) ?_
  exact (Topology.IsInducing.subtypeVal (t := {S : C(AddCircle T, F →L[ℝ] F) |
    ∀ t, S (t + (T / 2 : ℝ)) = S t})).continuousOn_iff.2 hM

/-! ### The half rotation -/

/-- The rotation by half the period of both loops of a mode. -/
private def halfRotatePair (s : ℝ) :
    WithLp 2 (CircleSobolev s F × CircleSobolev s F) →L[ℂ]
      WithLp 2 (CircleSobolev s F × CircleSobolev s F) :=
  let r : CircleSobolev s F →L[ℂ] CircleSobolev s F :=
    (rotate ((T / 2 : ℝ) : AddCircle T)).toLinearIsometry.toContinuousLinearMap
  r.withLpProdMap 2 r

omit hT [FiniteDimensional ℂ F] in
@[simp]
private theorem halfRotatePair_apply (s : ℝ)
    (y : WithLp 2 (CircleSobolev s F × CircleSobolev s F)) :
    halfRotatePair T s y = WithLp.toLp 2 (rotate ((T / 2 : ℝ) : AddCircle T) y.fst,
      rotate ((T / 2 : ℝ) : AddCircle T) y.snd) := by
  simp [halfRotatePair]

omit hT [FiniteDimensional ℂ F] in
/-- The half rotation of every mode of an element of `TauCeti.torusModeSobolev F ω`. -/
private def halfRotate {ω : ℕ → ℝ} (x : torusModeSobolev F ω) : torusModeSobolev F ω :=
  ⟨(lp.ampliation ℕ 2 (halfRotatePair T 1) (x : 𝕏[F]).1,
      lp.ampliation ℕ 2 (halfRotatePair T 0) (x : 𝕏[F]).2), mem_torusModeSobolev_iff.2 fun k ↦ by
    rw [lp.ampliation_apply_apply, lp.ampliation_apply_apply,
      mem_torusModeSobolev_iff.1 x.property k]
    refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_) <;>
      simp [← Complex.coe_smul, map_smul]⟩

/-- For a loop `S` invariant under the rotation by `T / 2`, the orbit-torus operator commutes with
the half rotation of every mode. -/
private theorem torusModeOperator_halfRotate {ω : ℕ → ℝ} {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t, S (t + (T / 2 : ℝ)) = S t) (x : torusModeSobolev F ω) (k : ℕ) :
    torusModeOperator T ω S (halfRotate T x) k =
      halfRotatePair T 0 (torusModeOperator T ω S x k) := by
  rw [torusModeOperator_apply_apply_eq, torusModeOperator_apply_apply_eq]
  refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_) <;>
    simp [halfRotate, ← Complex.coe_smul, loopOperator_rotate_of_invariant T hS]

end Operator

section Inner

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpaceDoublyAntiperiodicInner : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-- If the orbit-torus operator maps `x` to a target antiperiodic in `t`, then `x` is antiperiodic
in `t`: the half rotation `R x` has image `R (D x) = -D x`, so `R x = -x` by injectivity. -/
private theorem mem_doublyAntiperiodicSobolev_of_mem {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hS' : ∀ t, S (t + (T / 2 : ℝ)) = S t) {x : torusModeSobolev F fun k : ℕ ↦ (2 * k + 1) * π / ℓ}
    (hx : torusModeOperator T (fun k : ℕ ↦ (2 * k + 1) * π / ℓ) S x ∈ doublyAntiperiodicL2 F) :
    (x : 𝕏[F]) ∈ doublyAntiperiodicSobolev F ℓ := by
  have hT : T ≠ 0 := hT.out.ne'
  have hrot : halfRotate T x = -x := by
    refine (isInvertible_torusModeOperator_antiperiodic T hℓ S hS).injective
      (lp.ext (funext fun k ↦ ?_))
    rw [torusModeOperator_halfRotate T hS', map_neg]
    refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)
    · simpa using (rotate_half_period_eq_neg_iff hT).2 (hx k).1
    · simpa using (rotate_half_period_eq_neg_iff hT).2 (hx k).2
  refine ⟨x.property, fun k ↦ ?_⟩
  have hk := congrArg
    (fun z : torusModeSobolev F (fun k : ℕ ↦ (2 * k + 1) * π / ℓ) ↦ (z : 𝕏[F]).1 k) hrot
  simp only [halfRotate, lp.ampliation_apply_apply, halfRotatePair_apply] at hk
  exact ⟨(rotate_half_period_eq_neg_iff hT).1 (by simpa using congrArg WithLp.fst hk),
    (rotate_half_period_eq_neg_iff hT).1 (by simpa using congrArg WithLp.snd hk)⟩

/-- **Invertibility along the homotopy to the complex-linear reference.** For every
infinitesimally symplectic loop `S` invariant under the rotation by `T / 2`, the orbit-torus
operator `∂s + A`, `A ζ = J₀ (ζ' - S ζ)`, is invertible from the Sobolev space `H¹` of maps
antiperiodic in both factors onto the corresponding `L²` space. Since `τ • S` satisfies the same
hypotheses, every operator of the path `τ ↦ ∂s + J₀ (∂t - τ S)`, `τ ∈ [0, 1]`, is invertible, and
the path starts at the complex-linear operator `∂s + J₀ ∂t`
(`TauCeti.doublyAntiperiodicTorusOperator_zero_apply_smul`). -/
theorem isInvertible_doublyAntiperiodicTorusOperator {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hS' : ∀ t, S (t + (T / 2 : ℝ)) = S t) :
    (doublyAntiperiodicTorusOperator T ℓ S hS').IsInvertible :=
  -- The inverse of `D` maps doubly antiperiodic targets to doubly antiperiodic maps.
  (isInvertible_torusModeOperator_antiperiodic T hℓ S hS).codRestrictOfTower_comp (fun _ ↦ rfl) _
    fun _ hx ↦ mem_doublyAntiperiodicSobolev_of_mem T hℓ hS hS' hx

end Inner

end TauCeti
