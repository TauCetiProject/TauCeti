/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Bounded bilinear maps and bounded scalar actions over a normed ring

Over a seminormed commutative ring `R`, which need not be a field, an `R`-bilinear map `β` with
`‖β x y‖ ≤ C * ‖x‖ * ‖y‖` is jointly continuous (`LinearMap.continuous₂_of_bound`), and so is a
scalar action with `‖r • m‖ ≤ C * ‖r‖ * ‖m‖` (`TauCeti.continuousSMul_of_norm_smul_le`). For an
`R`-algebra `S`, such a bound on the action makes the structure map bounded
(`TauCeti.exists_norm_algebraMap_le_of_norm_smul_le`).
The evaluation action of bounded operators on a seminormed space is bounded
(`ContinuousLinearMap.isBoundedSMul_apply`) and hence jointly continuous
(`IsBoundedSMul.continuousSMul`), as is every submonoid such as the unitary group.
Likewise, a commuting normed-field scalar action on the codomain induces a bounded scalar action on
continuous semilinear maps (`ContinuousLinearMap.instIsBoundedSMul`), a scalar-tower action induces
a jointly continuous scalar action in the bounded-convergence topology
(`ContinuousLinearMap.instContinuousSMulOfIsScalarTower`), bounded linear endomorphisms form a
topological ring directly (`ContinuousLinearMap.instIsTopologicalRing`), and a compatible
normed-field action on a seminormed space makes its continuous linear endomorphisms a normed algebra
(`ContinuousLinearMap.instNormedAlgebraOfSMulCommClass`) matching
`ContinuousLinearMap.toNormedSpace` and `ContinuousLinearMap.algebra`.

A fibrewise linear change of coordinates `(x, v) ↦ (x, e x v)`, with `e` continuous at `a`, tends
to `(a, 0)` at `(a, 0)` (`ContinuousAt.tendsto_prodMk_clm_apply`).

Bounded operators act jointly continuously on their domain for the operator norm topology
(`IsBoundedSMul.continuousSMul`), and so does every submonoid of them, such as a
unitary group.
-/

public section

open Filter Topology
open scoped NNReal

variable {R : Type*} [SeminormedCommRing R]

/-- An `R`-bilinear map bounded by `C * ‖x‖ * ‖y‖` is jointly continuous. -/
theorem LinearMap.continuous₂_of_bound {X Y Z : Type*} [SeminormedAddCommGroup X]
    [Module R X] [SeminormedAddCommGroup Y] [Module R Y] [SeminormedAddCommGroup Z] [Module R Z]
    (β : X →ₗ[R] Y →ₗ[R] Z) (C : ℝ) (hβ : ∀ x y, ‖β x y‖ ≤ C * ‖x‖ * ‖y‖) :
    Continuous fun p : X × Y ↦ β p.1 p.2 :=
  IsBoundedBilinearMap.continuous (𝕜 := R)
    { add_left := fun x₁ x₂ y ↦ by simp
      smul_left := fun c x y ↦ by simp
      add_right := fun x y₁ y₂ ↦ by simp
      smul_right := fun c x y ↦ by simp
      bound := ⟨max C 1, by positivity, fun x y ↦
        (hβ x y).trans (by gcongr; exact le_max_left _ _)⟩ }

/-- A scalar action bounded by `C * ‖r‖ * ‖m‖` is continuous. -/
theorem TauCeti.continuousSMul_of_norm_smul_le {M : Type*} [SeminormedAddCommGroup M]
    [Module R M]
    (h : ∃ C : ℝ≥0, ∀ (r : R) (m : M), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖) : ContinuousSMul R M :=
  h.elim fun C hC ↦ ⟨(LinearMap.lsmul R M).continuous₂_of_bound C hC⟩

/-- The action of bounded operators on a seminormed space by evaluation is bounded:
`‖f v‖ ≤ ‖f‖ * ‖v‖`. In particular it is jointly continuous, and so are the actions of the units
and of submonoids such as the unitary group. -/
instance ContinuousLinearMap.isBoundedSMul_apply {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] : IsBoundedSMul (V →L[𝕜] V) V :=
  .of_norm_smul_le ContinuousLinearMap.le_opNorm

namespace ContinuousLinearMap

/-- A commuting normed-field scalar action on the codomain induces a bounded scalar action on
continuous semilinear maps. -/
instance (priority := 950) instIsBoundedSMul
    {𝕜 𝕜₂ 𝕜' E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
    [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass 𝕜₂ 𝕜' F] :
    IsBoundedSMul 𝕜' (E →SL[σ₁₂] F) :=
  .of_norm_smul_le opNorm_smul_le

/-- A scalar action factoring continuously through the codomain scalar field `𝕜₂` acts jointly
continuously on `E →SL[σ] F` in the bounded-convergence topology. -/
instance (priority := 950) instContinuousSMulOfIsScalarTower
    {𝕜₁ 𝕜₂ S E F : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂}
    [RingHomSurjective σ] [RingHomIsometric σ]
    [AddCommGroup E] [Module 𝕜₁ E] [TopologicalSpace E]
    [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜₂ F]
    [Monoid S] [TopologicalSpace S] [DistribMulAction S F] [SMulCommClass 𝕜₂ S F]
    [ContinuousConstSMul S F] [SMul S 𝕜₂] [IsScalarTower S 𝕜₂ F] [ContinuousSMul S 𝕜₂] :
    ContinuousSMul S (E →SL[σ] F) where
  continuous_smul := by
    have h : (fun p : S × (E →SL[σ] F) ↦ p.1 • p.2) = fun p ↦ (p.1 • (1 : 𝕜₂)) • p.2 := by
      ext p x; exact (smul_one_smul 𝕜₂ p.1 (p.2 x)).symm
    rw [h]
    exact continuous_smul.comp (((continuous_fst.smul continuous_const).prodMk continuous_snd :
      Continuous fun p : S × (E →SL[σ] F) ↦ (p.1 • (1 : 𝕜₂), p.2)))

/-- Continuous linear endomorphisms of a seminormed space form a topological ring for the
bounded-convergence / operator-norm topology without unfolding the seminormed-ring coercion
chain. -/
instance (priority := 950) instIsTopologicalRing
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    IsTopologicalRing (E →L[𝕜] E) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

/-- Continuous `𝕜`-linear endomorphisms of a seminormed space `E` form a normed `𝕜'`-algebra for
any normed field `𝕜'` acting compatibly on `E`, with underlying `NormedSpace` and `Algebra`
structures `ContinuousLinearMap.toNormedSpace` and `ContinuousLinearMap.algebra`. -/
noncomputable instance (priority := 950) instNormedAlgebraOfSMulCommClass
    {𝕜 𝕜' E : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedField 𝕜'] [NormedSpace 𝕜' E] [SMulCommClass 𝕜 𝕜' E] [SMul 𝕜' 𝕜]
    [IsScalarTower 𝕜' 𝕜 E] :
    NormedAlgebra 𝕜' (E →L[𝕜] E) :=
  { toNormedSpace, algebra with }

end ContinuousLinearMap

/-- If the action of `R` on an `R`-algebra `S` is bounded, `‖r • s‖ ≤ C * ‖r‖ * ‖s‖`, then so is
the structure map: `‖algebraMap R S r‖ ≤ C * ‖1‖ * ‖r‖`. -/
theorem TauCeti.exists_norm_algebraMap_le_of_norm_smul_le {S : Type*} [SeminormedRing S]
    [Algebra R S] (h : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖) :
    ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖ :=
  h.elim fun C hC ↦ ⟨C * ‖(1 : S)‖₊, fun r ↦ by
    simpa [Algebra.algebraMap_eq_smul_one, mul_right_comm] using hC r 1⟩

/-- A fibrewise linear change of coordinates `(x, v) ↦ (x, e x v)`, with `e` continuous at `a`,
tends to `(a, 0)` at `(a, 0)`. -/
theorem ContinuousAt.tendsto_prodMk_clm_apply {𝕜 X E F : Type*} [NontriviallyNormedField 𝕜]
    [TopologicalSpace X] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 F] {e : X → E →L[𝕜] F} {a : X} (he : ContinuousAt e a) :
    Tendsto (fun z : X × E ↦ (z.1, e z.1 z.2)) (𝓝 (a, 0)) (𝓝 (a, 0)) := by
  have h : ContinuousAt (fun z : X × E ↦ e z.1 z.2) (a, 0) :=
    (he.comp (f := Prod.fst) (x := (a, (0 : E))) continuousAt_fst).clm_apply continuousAt_snd
  simpa using continuousAt_fst.tendsto.prodMk_nhds h.tendsto

end
