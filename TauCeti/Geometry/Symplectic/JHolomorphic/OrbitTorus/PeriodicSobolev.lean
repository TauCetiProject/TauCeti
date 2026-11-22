/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Analysis.Sobolev.Circle.LinearODE.DeterminantLine
public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.ModeSobolev
import Mathlib.Analysis.Normed.Operator.Prod
import TauCeti.Data.SignType.Basic
import TauCeti.LinearAlgebra.LinearMap.RegularRestriction

/-!
# The orbit-torus operator on maps periodic along the circle factor

Let `γ` be a closed orbit of the suspension flow of a surface diffeomorphism and `C = S¹ × γ` its
orbit torus in `S¹ × Y_φ`. In a unitary trivialization of the normal bundle, the normal operator of
`C` is independent of the circle coordinate `s`,

`D u = ∂s u + A u`,  `A ζ = J₀ (ζ' - S ζ)`,

where the asymptotic operator `A` acts on loops in the coordinate `t` of period `T`, `J₀` is the
complex structure of the fibre `F` (multiplication by `I`) and `S` is a loop of real-linear maps,
infinitesimally symplectic for `Im ⟪·, ·⟫`. Of the four real sign characters of the torus, the two
untwisted along the circle factor make `D` act on maps periodic of period `ℓ` in `s`. This file
realizes the one untwisted along `γ` as well, acting on maps periodic in `t`, on Sobolev spaces,
and reduces it to the loop operator `L_S ζ = ζ' - S ζ` of
`TauCeti.Analysis.Sobolev.Circle.LinearODE.DeterminantLine`, so to the return map `P = Ψ(T)` of
`w' = S w`. In the geometric application `P` is conjugate to the linearized return map of the orbit
(`TauCeti.comp_dysonSeriesLeft_frameConnection`), and the result is the comparison of the
untwisted orbit-torus operator with `det (1 - P)`.

**The splitting.** A map periodic in `s` is the sum of its `s`-independent mode `a₀(t)` and of its
modes `cos (ωₖ s) aₖ + sin (ωₖ s) bₖ` of frequencies `ωₖ = 2(k + 1)π/ℓ`. The operator preserves this
splitting: on the `s`-independent mode it is the asymptotic operator `A`, and on the others it is
`TauCeti.torusModeOperator`. So `D = A ⊕ D'` (`TauCeti.periodicTorusOperator`), as a bounded
real-linear map from `H¹(F) × H¹_{≠0}` to `H⁰(F) × L²_{≠0}`, and `D'` is invertible for every
infinitesimally symplectic loop (`TauCeti.isInvertible_torusModeOperator_periodic`).

**The comparison.** Including the `s`-independent mode, `a ↦ (a, 0)` on the domains and
`w ↦ (J₀ w, 0)` on the targets, intertwines `L_S` with `D`. Since `D'` is bijective, these
inclusions induce isomorphisms of kernels and cokernels
(`LinearMap.kerEquivOfRegular`, `LinearMap.cokerEquivOfRegular`):

* `TauCeti.kerPeriodicTorusOperatorEquiv`: `ker D ≃ ker L_S`, `x ↦ x₀`;
* `TauCeti.quotientRangePeriodicTorusOperatorEquiv`: `coker D ≃ coker L_S`, `[z] ↦ [-J₀ z₀]`.

Composed with `TauCeti.CircleSobolev.kerLoopOperatorEquiv` and
`TauCeti.CircleSobolev.quotientRangeLoopOperatorEquiv`, they identify the determinant line of `D`
with that of `1 - P` (`TauCeti.detLinePeriodicTorusOperatorEquiv`). Consequently `D` is Fredholm
of index zero (`TauCeti.isFredholm_periodicTorusOperator`, `TauCeti.index_periodicTorusOperator`),
it is invertible exactly when `det (1 - P) ≠ 0`
(`TauCeti.isInvertible_periodicTorusOperator_iff_det_ne_zero`), and then the orientation of its
determinant line induced by `1 - P` and the one given by bijectivity differ by the sign of
`det (1 - P)` (`TauCeti.sign_detLineEndEquiv_detLinePeriodicTorusOperatorEquiv`). For `S = 0` the
operator `∂s + J₀ ∂t` is complex linear (`TauCeti.periodicTorusOperator_zero_apply_smul`).

The twist along `γ` by the sign `-1`, whose loop operator acts on maps antiperiodic in `t`, and
finite covers of the torus are not treated here.

## Main definitions

* `TauCeti.periodicTorusOperator T ℓ S`: the operator `∂s + J₀ (∂t - S)` on maps periodic in `s`.
* `TauCeti.kerPeriodicTorusOperatorEquiv`, `TauCeti.quotientRangePeriodicTorusOperatorEquiv`: its
  kernel and cokernel are those of `L_S`.
* `TauCeti.detLinePeriodicTorusOperatorEquiv`: its determinant line is that of `1 - Ψ(T)`.

## Main results

* `TauCeti.isFredholm_periodicTorusOperator`, `TauCeti.index_periodicTorusOperator`: it is
  Fredholm of index zero.
* `TauCeti.isInvertible_periodicTorusOperator_iff_det_ne_zero`: it is invertible exactly when
  `det (1 - Ψ(T)) ≠ 0`.
* `TauCeti.detLineEndEquiv_detLinePeriodicTorusOperatorEquiv`,
  `TauCeti.sign_detLineEndEquiv_detLinePeriodicTorusOperatorEquiv`: for bijective `D`, the two
  orientations of its determinant line differ by the sign of `det (1 - Ψ(T))`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893 (the twisted normal operators of tori and their
  determinant signs).
* D. Salamon, *Lectures on Floer homology*, in Symplectic Geometry and Topology,
  IAS/Park City Math. Ser. 7 (1999), Lecture 2 (the operator `J₀ ∂t + S` and the return map).
-/

public section

noncomputable section

open Complex
open LinearMap (ker range)
open scoped Real ENNReal lp

namespace TauCeti

open CircleSobolev

/-- The `L²` space of mode sequences, the target of `TauCeti.torusModeOperator`. -/
local notation "𝕐[" F "]" => ℓ²(ℕ, WithLp 2 (CircleSobolev 0 F × CircleSobolev 0 F))

section Operator

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpacePeriodicTorusOperator : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-- The orbit-torus operator `∂s + A` on maps periodic of period `ℓ` in `s`, for the asymptotic
operator `A ζ = J₀ (ζ' - S ζ)` of a loop `S`. A map periodic in `s` is a pair `(a₀, x)` of its
`s`-independent mode `a₀ ∈ H¹(F)` and its modes of frequencies `2(k + 1)π/ℓ`
(`TauCeti.torusModeSobolev`); the operator is `A` on the first and `TauCeti.torusModeOperator` on
the second. -/
def periodicTorusOperator (ℓ : ℝ) (S : C(AddCircle T, F →L[ℝ] F)) :
    CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →L[ℝ]
      CircleSobolev 0 F × 𝕐[F] :=
  (I • loopOperator T S).prodMap (torusModeOperator T _ S)

@[simp]
theorem periodicTorusOperator_apply (ℓ : ℝ) (S : C(AddCircle T, F →L[ℝ] F))
    (x : CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ)) :
    periodicTorusOperator T ℓ S x = (I • loopOperator T S x.1, torusModeOperator T _ S x.2) :=
  (rfl)

/-- **The reference operator is complex linear.** For `S = 0` the operator `∂s + J₀ ∂t` on maps
periodic in `s` commutes with multiplication by complex scalars, the complex structure of the
Sobolev spaces acting by `J₀`. -/
theorem periodicTorusOperator_zero_apply_smul (ℓ : ℝ) (c : ℂ)
    (x : CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ)) :
    periodicTorusOperator T ℓ 0 (c • x) = c • periodicTorusOperator T ℓ 0 x := by
  refine Prod.ext ?_ (torusModeOperator_zero_apply_smul T _ c x.2)
  simp [smul_comm c I]

/-- **Continuous dependence on the loop.** The operator `∂s + A` on maps periodic in `s` depends
continuously, in operator norm, on the loop `S` with its uniform norm. -/
theorem continuous_periodicTorusOperator (ℓ : ℝ) :
    Continuous (periodicTorusOperator (F := F) T ℓ) :=
  ((continuous_loopOperator T).const_smul I).prod_mapL ℝ (continuous_torusModeOperator T _)

end Operator

section Inner

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F] {ℓ : ℝ}

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpacePeriodicSobolev : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-- The inclusion `a ↦ (a, 0)` of the `s`-independent mode into the domain of
`TauCeti.periodicTorusOperator`. -/
private abbrev constModeDomain (ℓ : ℝ) :
    CircleSobolev 1 F →ₗ[ℝ]
      CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) :=
  LinearMap.inl ℝ _ _

/-- The inclusion `w ↦ (J₀ w, 0)` of the `s`-independent mode into the target of
`TauCeti.periodicTorusOperator`. -/
private abbrev constModeTarget : CircleSobolev 0 F →ₗ[ℝ] CircleSobolev 0 F × 𝕐[F] :=
  LinearMap.inl ℝ _ _ ∘ₗ (I • LinearMap.id)

/-- The inclusions of the `s`-independent mode intertwine `L_S` with
`TauCeti.periodicTorusOperator`. -/
private theorem constModeTarget_comp_loopOperator (S : C(AddCircle T, F →L[ℝ] F)) :
    constModeTarget ∘ₗ (loopOperator T S : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 0 F) =
      (periodicTorusOperator T ℓ S).toLinearMap ∘ₗ constModeDomain ℓ := by
  ext a <;> simp

omit [FiniteDimensional ℂ F] in
private theorem injective_constModeTarget : Function.Injective (constModeTarget (F := F)) :=
  fun _ _ h ↦ smul_right_injective _ I_ne_zero (congrArg Prod.fst h)

/-- An element whose image under `TauCeti.periodicTorusOperator` is `s`-independent is itself
`s`-independent, since the operator is injective on the other modes. -/
private theorem mem_range_constModeDomain (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (x : CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ))
    (hx : (periodicTorusOperator T ℓ S).toLinearMap x ∈ range constModeTarget) :
    x ∈ range (constModeDomain ℓ) := by
  obtain ⟨w, hw⟩ := hx
  have h2 : torusModeOperator T _ S x.2 = 0 := by simpa using (congrArg Prod.snd hw).symm
  refine ⟨x.1, Prod.ext rfl ?_⟩
  exact (map_eq_zero_iff _ (isInvertible_torusModeOperator_periodic T hℓ S hS).injective).1
    h2 |>.symm

/-- The target of `TauCeti.periodicTorusOperator` is spanned by its range and the `s`-independent
mode, since the operator is onto the other modes. -/
private theorem range_constModeTarget_sup_range (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    range constModeTarget ⊔ range (periodicTorusOperator T ℓ S).toLinearMap = ⊤ := by
  refine eq_top_iff.2 fun z _ ↦ ?_
  obtain ⟨b, hb⟩ := (isInvertible_torusModeOperator_periodic T hℓ S hS).surjective z.2
  refine Submodule.mem_sup.2
    ⟨(z.1, 0), ⟨(-I) • z.1, by simp [smul_smul]⟩, (0, z.2), ⟨(0, b), by simp [hb]⟩, by simp⟩

/-- **The kernel of the periodic orbit-torus operator.** For `ℓ ≠ 0` and an infinitesimally
symplectic loop `S`, taking the `s`-independent mode is a linear equivalence from the kernel of
`∂s + A` on maps periodic in `s` (`TauCeti.periodicTorusOperator`) onto the kernel of
`L_S ζ = ζ' - S ζ` (`TauCeti.coe_kerPeriodicTorusOperatorEquiv_apply`); the kernel elements are
`s`-independent. -/
def kerPeriodicTorusOperatorEquiv (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    ker (periodicTorusOperator T ℓ S).toLinearMap ≃ₗ[ℝ]
      ker (loopOperator T S : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 0 F) :=
  (LinearMap.kerEquivOfRegular (constModeTarget_comp_loopOperator T S)
    LinearMap.inl_injective injective_constModeTarget
    (mem_range_constModeDomain T hℓ S hS)).symm

/-- The kernel elements of `TauCeti.periodicTorusOperator` are `s`-independent: the inverse of
`TauCeti.kerPeriodicTorusOperatorEquiv` sends `a` to the map `(a, 0)` with no other modes. -/
@[simp]
theorem kerPeriodicTorusOperatorEquiv_symm_apply (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (a : ker (loopOperator T S : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 0 F)) :
    ((kerPeriodicTorusOperatorEquiv T hℓ S hS).symm a :
      CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ)) =
        ((a : CircleSobolev 1 F), 0) := by
  simp [kerPeriodicTorusOperatorEquiv]

@[simp]
theorem coe_kerPeriodicTorusOperatorEquiv_apply (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (x : ker (periodicTorusOperator T ℓ S).toLinearMap) :
    (kerPeriodicTorusOperatorEquiv T hℓ S hS x : CircleSobolev 1 F) = x.val.1 := by
  conv_rhs => rw [← (kerPeriodicTorusOperatorEquiv T hℓ S hS).symm_apply_apply x,
    kerPeriodicTorusOperatorEquiv_symm_apply]

/-- **The cokernel of the periodic orbit-torus operator.** For `ℓ ≠ 0` and an infinitesimally
symplectic loop `S`, `z ↦ -J₀ z₀` on the `s`-independent mode induces a linear equivalence from the
cokernel of `∂s + A` on maps periodic in `s` (`TauCeti.periodicTorusOperator`) onto the cokernel
of `L_S ζ = ζ' - S ζ` (`TauCeti.quotientRangePeriodicTorusOperatorEquiv_mk`). -/
def quotientRangePeriodicTorusOperatorEquiv (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    ((CircleSobolev 0 F × 𝕐[F]) ⧸ range (periodicTorusOperator T ℓ S).toLinearMap) ≃ₗ[ℝ]
      CircleSobolev 0 F ⧸ range (loopOperator T S : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 0 F) :=
  (LinearMap.cokerEquivOfRegular (constModeTarget_comp_loopOperator T S)
    injective_constModeTarget (mem_range_constModeDomain T hℓ S hS)
    (range_constModeTarget_sup_range T hℓ S hS)).symm

/-- On the class of `z`, `TauCeti.quotientRangePeriodicTorusOperatorEquiv` is the class of
`-J₀ z₀`, where `z₀` is the `s`-independent mode of `z`. -/
@[simp]
theorem quotientRangePeriodicTorusOperatorEquiv_mk (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (z : CircleSobolev 0 F × 𝕐[F]) :
    quotientRangePeriodicTorusOperatorEquiv T hℓ S hS (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((-I) • z.1) := by
  -- The other modes of `z` lie in the range, since the operator is onto them.
  obtain ⟨b, hb⟩ := (isInvertible_torusModeOperator_periodic T hℓ S hS).surjective z.2
  have hz : (Submodule.Quotient.mk z :
      (CircleSobolev 0 F × 𝕐[F]) ⧸ range (periodicTorusOperator T ℓ S).toLinearMap) =
      Submodule.Quotient.mk (constModeTarget ((-I) • z.1)) := by
    rw [Submodule.Quotient.eq]
    exact ⟨(0, b), Prod.ext (by simp [smul_smul]) (by simp [hb])⟩
  rw [hz]
  exact LinearMap.cokerEquivOfRegular_symm_mk _ _ _ _ _

/-- **The determinant line of the periodic orbit-torus operator.** For `ℓ ≠ 0` and an
infinitesimally symplectic loop `S`, the isomorphisms of kernels and cokernels with those of
`L_S ζ = ζ' - S ζ` (`TauCeti.kerPeriodicTorusOperatorEquiv`,
`TauCeti.quotientRangePeriodicTorusOperatorEquiv`), followed by those of `L_S` with `1 - Ψ(T)`
(`TauCeti.CircleSobolev.kerLoopOperatorEquiv`,
`TauCeti.CircleSobolev.quotientRangeLoopOperatorEquiv`), identify the determinant line of `∂s + A`
on maps periodic in `s` with the determinant line of `1 - Ψ(T)`, where
`Ψ = TauCeti.dysonSeriesLeft S`. -/
def detLinePeriodicTorusOperatorEquiv (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (periodicTorusOperator T ℓ S).toLinearMap.detLine ≃ₗ[ℝ]
      (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F)).detLine :=
  LinearMap.detLineCongrKerCoker
    ((kerPeriodicTorusOperatorEquiv T hℓ S hS).trans (kerLoopOperatorEquiv T S))
    ((quotientRangePeriodicTorusOperatorEquiv T hℓ S hS).trans
      (quotientRangeLoopOperatorEquiv T S))

/-- **The periodic orbit-torus operator is Fredholm.** It is the direct sum of the Fredholm
operator `J₀ L_S` and an invertible operator. -/
theorem isFredholm_periodicTorusOperator (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (periodicTorusOperator T ℓ S).IsFredholm := by
  have hI : I • loopOperator T S = (ContinuousLinearEquiv.smulLeft (R₁ := ℝ)
      (M₁ := CircleSobolev 0 F) (Units.mk0 I I_ne_zero) : _ →L[ℝ] _) ∘L loopOperator T S := by
    ext a
    simp [Units.smul_def]
  refine ContinuousLinearMap.IsFredholm.prodMap ?_
    (isInvertible_torusModeOperator_periodic T hℓ S hS).isFredholm
  rw [hI, ContinuousLinearMap.isFredholm_equiv_comp]
  exact isFredholm_loopOperator T S

/-- **The periodic orbit-torus operator has index zero**, as `L_S`, whose kernel and cokernel it
shares. -/
@[simp]
theorem index_periodicTorusOperator (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (periodicTorusOperator T ℓ S).index = 0 := by
  rw [ContinuousLinearMap.index_eq_finrank_sub,
    (kerPeriodicTorusOperatorEquiv T hℓ S hS).finrank_eq,
    (quotientRangePeriodicTorusOperatorEquiv T hℓ S hS).finrank_eq,
    ← ContinuousLinearMap.index_eq_finrank_sub, index_loopOperator]

/-- The periodic orbit-torus operator is injective exactly when `L_S` is. -/
private theorem injective_periodicTorusOperator_iff (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    Function.Injective (periodicTorusOperator T ℓ S) ↔ Function.Injective (loopOperator T S) := by
  rw [← ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.coe_coe (loopOperator T S),
    ← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot,
    ← Submodule.subsingleton_iff_eq_bot,
    (kerPeriodicTorusOperatorEquiv T hℓ S hS).subsingleton_congr]

/-- **The Fredholm alternative for the periodic orbit-torus operator.** For `ℓ ≠ 0` and an
infinitesimally symplectic loop `S`, the operator `∂s + A` on maps periodic in `s` is invertible
exactly when `det (1 - Ψ(T)) ≠ 0`, where `Ψ = TauCeti.dysonSeriesLeft S`. In the geometric
application, the untwisted normal operator of an orbit torus is invertible exactly when the
linearized return map of the orbit does not have `1` as an eigenvalue. -/
theorem isInvertible_periodicTorusOperator_iff_det_ne_zero (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (periodicTorusOperator T ℓ S).IsInvertible ↔
      LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F)) ≠ 0 := by
  rw [← isInvertible_loopOperator_iff_det_ne_zero]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (isFredholm_loopOperator T S).isInvertible_of_injective_of_index_eq_zero
      ((injective_periodicTorusOperator_iff T hℓ S hS).1 h.injective) (index_loopOperator T S)
  · exact (isFredholm_periodicTorusOperator T hℓ S hS).isInvertible_of_injective_of_index_eq_zero
      ((injective_periodicTorusOperator_iff T hℓ S hS).2 h.injective)
      (index_periodicTorusOperator T hℓ S hS)

/-- **The determinant line of a nondegenerate periodic orbit-torus operator.** Let `∂s + A` on maps
periodic in `s` be bijective, equivalently `det (1 - Ψ(T)) ≠ 0`. Transporting its determinant line
to that of `1 - Ψ(T)` (`TauCeti.detLinePeriodicTorusOperatorEquiv`) and applying the canonical
trivialization of the determinant line of an endomorphism (`LinearMap.detLineEndEquiv`) gives
`(det (1 - Ψ(T)))⁻¹` times the trivialization of the determinant line of the bijective operator
(`LinearMap.detLineEquivOfBijective`). -/
theorem detLineEndEquiv_detLinePeriodicTorusOperatorEquiv (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hD : Function.Bijective (periodicTorusOperator T ℓ S).toLinearMap)
    (x : (periodicTorusOperator T ℓ S).toLinearMap.detLine) :
    LinearMap.detLineEndEquiv (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F))
        (detLinePeriodicTorusOperatorEquiv T hℓ S hS x) =
      (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F)))⁻¹ *
        (periodicTorusOperator T ℓ S).toLinearMap.detLineEquivOfBijective hD x := by
  have hinj := (injective_loopOperator_iff T S).1
    ((injective_periodicTorusOperator_iff T hℓ S hS).1 hD.1)
  have hP := And.intro hinj (LinearMap.injective_iff_surjective.1 hinj)
  -- The two steps are composed as terms: `rw` times out on the large operator types here.
  refine (LinearMap.detLineEndEquiv_eq_inv_det_mul _ hP _).trans ?_
  exact congrArg (_ * ·) (LinearMap.detLineEquivOfBijective_detLineCongrKerCoker hD hP _ _ x)

/-- **The orientation sign of a nondegenerate periodic orbit-torus operator.** In the situation of
`TauCeti.detLineEndEquiv_detLinePeriodicTorusOperatorEquiv`, the orientation of the determinant
line of `∂s + A` on maps periodic in `s` induced by the canonical trivialization for `1 - Ψ(T)` and
the orientation given by bijectivity differ by the sign of `det (1 - Ψ(T))`. -/
theorem sign_detLineEndEquiv_detLinePeriodicTorusOperatorEquiv (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hD : Function.Bijective (periodicTorusOperator T ℓ S).toLinearMap)
    (x : (periodicTorusOperator T ℓ S).toLinearMap.detLine) :
    SignType.sign (LinearMap.detLineEndEquiv
          (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F))
          (detLinePeriodicTorusOperatorEquiv T hℓ S hS x)) =
      SignType.sign (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F))) *
        SignType.sign
          ((periodicTorusOperator T ℓ S).toLinearMap.detLineEquivOfBijective hD x) := by
  have h (a b : ℝ) : SignType.sign (a⁻¹ * b) = SignType.sign a * SignType.sign b := by
    rw [sign_mul, TauCeti.sign_inv]
  exact (congrArg SignType.sign
    (detLineEndEquiv_detLinePeriodicTorusOperatorEquiv T hℓ S hS hD x)).trans (h _ _)

end Inner

end TauCeti
