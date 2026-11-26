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
import TauCeti.Topology.Algebra.Module.ComplexSmulI
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

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

**The comparison.** It uses only that `D'` is invertible, so it is proved once for
`(J₀ L_S) ⊕ B` with any invertible `B` (`TauCeti.kerProdMapLoopOperatorEquiv`,
`TauCeti.quotientRangeProdMapLoopOperatorEquiv`, `TauCeti.detLineProdMapLoopOperatorEquiv`,
`TauCeti.isInvertible_prodMap_loopOperator_iff_det_ne_zero` and the lemmas beside them); the
operators on finite covers of the torus are of this form too. Including the first factor,
`a ↦ (a, 0)` on the domains and `w ↦ (J₀ w, 0)` on the targets, intertwines `L_S` with
`(J₀ L_S) ⊕ B`. Since `B` is bijective, these inclusions induce isomorphisms of kernels and
cokernels (`LinearMap.kerEquivOfRegular`, `LinearMap.cokerEquivOfRegular`). For `D`:

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
operator `∂s + J₀ ∂t` is complex linear (`TauCeti.periodicTorusOperator_zero_apply_smul`), and so
is the operator of every loop whose loop operator is complex linear
(`TauCeti.periodicTorusOperator_apply_smul`).

The twist along `γ` by the sign `-1`, whose loop operator acts on maps antiperiodic in `t`, is the
operator of the loop `TauCeti.CircleSobolev.antiperiodicGaugeLoop T S`; its comparison with
`det (1 + P)` is in `TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.OrbitTwistSobolev`.
Finite covers of the torus are treated in
`TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.Cover` and
`TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.SkewCover`.

## Main definitions

* `TauCeti.kerProdMapLoopOperatorEquiv`, `TauCeti.quotientRangeProdMapLoopOperatorEquiv`,
  `TauCeti.detLineProdMapLoopOperatorEquiv`: the kernel, cokernel and determinant line of
  `(J₀ L_S) ⊕ B`, for an invertible `B`, are those of `L_S` and of `1 - Ψ(T)`.
* `TauCeti.periodicTorusOperator T ℓ S`: the operator `∂s + J₀ (∂t - S)` on maps periodic in `s`.
* `TauCeti.kerPeriodicTorusOperatorEquiv`, `TauCeti.quotientRangePeriodicTorusOperatorEquiv`: its
  kernel and cokernel are those of `L_S`.
* `TauCeti.detLinePeriodicTorusOperatorEquiv`: its determinant line is that of `1 - Ψ(T)`.

## Main results

* `TauCeti.isInvertible_prodMap_loopOperator_iff_det_ne_zero`,
  `TauCeti.sign_detLineEndEquiv_detLineProdMapLoopOperatorEquiv`: the Fredholm alternative and the
  comparison of orientations for `(J₀ L_S) ⊕ B`.
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

/-! ### The asymptotic operator beside an invertible operator -/

section ProdMap

variable (T : ℝ) [hT : Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ F] {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] (S : C(AddCircle T, F →L[ℝ] F))
  {B : E →L[ℝ] E'}

/-- A finite-dimensional complex space is complete, as the Sobolev spaces below need. -/
local instance instCompleteSpaceProdMapLoopOperator : CompleteSpace F :=
  FiniteDimensional.completeSpace ℂ F

/-- The inclusion `a ↦ (a, 0)` of the domain of `L_S` into that of `(J₀ L_S) ⊕ B`. -/
private abbrev constModeDomain : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 1 F × E :=
  LinearMap.inl ℝ _ _

/-- The inclusion `w ↦ (J₀ w, 0)` of the target of `L_S` into that of `(J₀ L_S) ⊕ B`. -/
private abbrev constModeTarget : CircleSobolev 0 F →ₗ[ℝ] CircleSobolev 0 F × E' :=
  LinearMap.inl ℝ _ _ ∘ₗ (I • LinearMap.id)

/-- The inclusions of the first factor intertwine `L_S` with `(J₀ L_S) ⊕ B`. -/
private theorem constModeTarget_comp_loopOperator (B : E →L[ℝ] E') :
    constModeTarget (E' := E') ∘ₗ
        (loopOperator T S : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 0 F) =
      ((I • loopOperator T S).prodMap B).toLinearMap ∘ₗ constModeDomain := by
  ext a <;> simp

omit [FiniteDimensional ℂ F] in
private theorem injective_constModeTarget :
    Function.Injective (constModeTarget (F := F) (E' := E')) :=
  fun _ _ h ↦ smul_right_injective _ I_ne_zero (congrArg Prod.fst h)

/-- An element whose image under `(J₀ L_S) ⊕ B` lies in the first factor lies itself in the first
factor, since `B` is injective. -/
private theorem mem_range_constModeDomain (hB : B.IsInvertible) (x : CircleSobolev 1 F × E)
    (hx : ((I • loopOperator T S).prodMap B).toLinearMap x ∈ range constModeTarget) :
    x ∈ range constModeDomain := by
  obtain ⟨w, hw⟩ := hx
  have h2 : B x.2 = 0 := by simpa using (congrArg Prod.snd hw).symm
  exact ⟨x.1, Prod.ext rfl ((map_eq_zero_iff _ hB.injective).1 h2).symm⟩

/-- The target of `(J₀ L_S) ⊕ B` is spanned by its range and the first factor, since `B` is
surjective. -/
private theorem range_constModeTarget_sup_range (hB : B.IsInvertible) :
    range constModeTarget ⊔ range ((I • loopOperator T S).prodMap B).toLinearMap = ⊤ := by
  refine eq_top_iff.2 fun z _ ↦ ?_
  obtain ⟨b, hb⟩ := hB.surjective z.2
  refine Submodule.mem_sup.2
    ⟨(z.1, 0), ⟨(-I) • z.1, by simp [smul_smul]⟩, (0, z.2), ⟨(0, b), by simp [hb]⟩, by simp⟩

/-- **The kernel of the asymptotic operator beside an invertible operator.** For an invertible
`B`, taking the first component is a linear equivalence from the kernel of `(J₀ L_S) ⊕ B` onto the
kernel of `L_S ζ = ζ' - S ζ` (`TauCeti.coe_kerProdMapLoopOperatorEquiv_apply`); the kernel elements
have no second component. -/
def kerProdMapLoopOperatorEquiv (hB : B.IsInvertible) :
    ker ((I • loopOperator T S).prodMap B).toLinearMap ≃ₗ[ℝ]
      ker (loopOperator T S : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 0 F) :=
  (LinearMap.kerEquivOfRegular (constModeTarget_comp_loopOperator T S B)
    LinearMap.inl_injective injective_constModeTarget (mem_range_constModeDomain T S hB)).symm

/-- The kernel elements of `(J₀ L_S) ⊕ B` have no second component: the inverse of
`TauCeti.kerProdMapLoopOperatorEquiv` sends `a` to `(a, 0)`. -/
theorem kerProdMapLoopOperatorEquiv_symm_apply (hB : B.IsInvertible)
    (a : ker (loopOperator T S : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 0 F)) :
    ((kerProdMapLoopOperatorEquiv T S hB).symm a : CircleSobolev 1 F × E) =
      ((a : CircleSobolev 1 F), 0) := by
  rw [kerProdMapLoopOperatorEquiv, LinearEquiv.symm_symm, LinearMap.coe_kerEquivOfRegular_apply]
  rfl

theorem coe_kerProdMapLoopOperatorEquiv_apply (hB : B.IsInvertible)
    (x : ker ((I • loopOperator T S).prodMap B).toLinearMap) :
    (kerProdMapLoopOperatorEquiv T S hB x : CircleSobolev 1 F) = x.val.1 := by
  conv_rhs => rw [← (kerProdMapLoopOperatorEquiv T S hB).symm_apply_apply x,
    kerProdMapLoopOperatorEquiv_symm_apply]

/-- **The cokernel of the asymptotic operator beside an invertible operator.** For an invertible
`B`, `z ↦ -J₀ z₁` on the first component induces a linear equivalence from the cokernel of
`(J₀ L_S) ⊕ B` onto the cokernel of `L_S ζ = ζ' - S ζ`
(`TauCeti.quotientRangeProdMapLoopOperatorEquiv_mk`). -/
def quotientRangeProdMapLoopOperatorEquiv (hB : B.IsInvertible) :
    ((CircleSobolev 0 F × E') ⧸ range ((I • loopOperator T S).prodMap B).toLinearMap) ≃ₗ[ℝ]
      CircleSobolev 0 F ⧸ range (loopOperator T S : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 0 F) :=
  (LinearMap.cokerEquivOfRegular (constModeTarget_comp_loopOperator T S B)
    injective_constModeTarget (mem_range_constModeDomain T S hB)
    (range_constModeTarget_sup_range T S hB)).symm

/-- On the class of `z`, `TauCeti.quotientRangeProdMapLoopOperatorEquiv` is the class of
`-J₀ z₁`, where `z₁` is the first component of `z`. -/
theorem quotientRangeProdMapLoopOperatorEquiv_mk (hB : B.IsInvertible)
    (z : CircleSobolev 0 F × E') :
    quotientRangeProdMapLoopOperatorEquiv T S hB (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((-I) • z.1) := by
  -- The second component of `z` lies in the range, since `B` is surjective.
  obtain ⟨b, hb⟩ := hB.surjective z.2
  have hz : (Submodule.Quotient.mk z :
      (CircleSobolev 0 F × E') ⧸ range ((I • loopOperator T S).prodMap B).toLinearMap) =
      Submodule.Quotient.mk (constModeTarget ((-I) • z.1)) := by
    rw [Submodule.Quotient.eq]
    exact ⟨(0, b), Prod.ext (by simp [smul_smul]) (by simp [hb])⟩
  rw [hz]
  exact LinearMap.cokerEquivOfRegular_symm_mk _ _ _ _ _

/-- **The determinant line of the asymptotic operator beside an invertible operator.** For an
invertible `B`, the isomorphisms of kernels and cokernels of `(J₀ L_S) ⊕ B` with those of
`L_S ζ = ζ' - S ζ` (`TauCeti.kerProdMapLoopOperatorEquiv`,
`TauCeti.quotientRangeProdMapLoopOperatorEquiv`), followed by those of `L_S` with `1 - Ψ(T)`
(`TauCeti.CircleSobolev.kerLoopOperatorEquiv`,
`TauCeti.CircleSobolev.quotientRangeLoopOperatorEquiv`), identify the determinant line of
`(J₀ L_S) ⊕ B` with the determinant line of `1 - Ψ(T)`, where `Ψ = TauCeti.dysonSeriesLeft S`. -/
def detLineProdMapLoopOperatorEquiv (hB : B.IsInvertible) :
    ((I • loopOperator T S).prodMap B).toLinearMap.detLine ≃ₗ[ℝ]
      (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F)).detLine :=
  LinearMap.detLineCongrKerCoker
    ((kerProdMapLoopOperatorEquiv T S hB).trans (kerLoopOperatorEquiv T S))
    ((quotientRangeProdMapLoopOperatorEquiv T S hB).trans (quotientRangeLoopOperatorEquiv T S))

/-- `TauCeti.detLineProdMapLoopOperatorEquiv` is the isomorphism of determinant lines induced by
the isomorphisms of kernels and cokernels with those of `1 - Ψ(T)`. -/
theorem detLineProdMapLoopOperatorEquiv_def (hB : B.IsInvertible) :
    detLineProdMapLoopOperatorEquiv T S hB =
      LinearMap.detLineCongrKerCoker
        ((kerProdMapLoopOperatorEquiv T S hB).trans (kerLoopOperatorEquiv T S))
        ((quotientRangeProdMapLoopOperatorEquiv T S hB).trans
          (quotientRangeLoopOperatorEquiv T S)) :=
  (rfl)

/-- `TauCeti.detLineProdMapLoopOperatorEquiv` is the transport along the isomorphisms of kernels
and cokernels with those of `L_S` (`TauCeti.kerProdMapLoopOperatorEquiv`,
`TauCeti.quotientRangeProdMapLoopOperatorEquiv`), followed by the identification of the
determinant line of `L_S` with that of `1 - Ψ(T)`
(`TauCeti.CircleSobolev.detLineLoopOperatorEquiv`). -/
theorem detLineProdMapLoopOperatorEquiv_eq_trans (hB : B.IsInvertible) :
    detLineProdMapLoopOperatorEquiv T S hB =
      (LinearMap.detLineCongrKerCoker (kerProdMapLoopOperatorEquiv T S hB)
        (quotientRangeProdMapLoopOperatorEquiv T S hB)).trans
        (detLineLoopOperatorEquiv T S) := by
  rw [detLineLoopOperatorEquiv_def, ← LinearMap.detLineCongrKerCoker_trans]
  rfl

/-- **The asymptotic operator beside an invertible operator is Fredholm.** It is the direct sum of
the Fredholm operator `J₀ L_S` and an invertible operator. -/
theorem isFredholm_prodMap_loopOperator (hB : B.IsInvertible) :
    ((I • loopOperator T S).prodMap B).IsFredholm :=
  (isFredholm_I_smul_loopOperator T S).prodMap hB.isFredholm

/-- **The asymptotic operator beside an invertible operator has index zero**: the index is additive
under `prodMap`, `J₀ L_S` has the index zero of `L_S`, and the invertible `B` has index zero. -/
@[simp]
theorem index_prodMap_loopOperator (hB : B.IsInvertible) :
    ((I • loopOperator T S).prodMap B).index = 0 := by
  have hL := isFredholm_I_smul_loopOperator T S
  have := hL.finite_ker
  have := hL.finite_coker
  have := hB.isFredholm.finite_ker
  have := hB.isFredholm.finite_coker
  rw [ContinuousLinearMap.index_prodMap, B.index_eq_zero_of_bijective hB.bijective, add_zero,
    index_I_smul_loopOperator]

/-- For an invertible `B`, `(J₀ L_S) ⊕ B` is injective exactly when `L_S` is. -/
theorem injective_prodMap_loopOperator_iff (hB : B.IsInvertible) :
    Function.Injective ((I • loopOperator T S).prodMap B) ↔
      Function.Injective (loopOperator T S) := by
  rw [ContinuousLinearMap.coe_prodMap', Prod.map_injective, and_iff_left hB.injective,
    ← smulIEquiv_comp, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe]
  exact (ContinuousLinearEquiv.injective _).of_comp_iff _

/-- **The Fredholm alternative for the asymptotic operator beside an invertible operator.** For an
invertible `B`, `(J₀ L_S) ⊕ B` is invertible exactly when `det (1 - Ψ(T)) ≠ 0`, where
`Ψ = TauCeti.dysonSeriesLeft S`. -/
theorem isInvertible_prodMap_loopOperator_iff_det_ne_zero (hB : B.IsInvertible) :
    ((I • loopOperator T S).prodMap B).IsInvertible ↔
      LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F)) ≠ 0 := by
  rw [ContinuousLinearMap.isInvertible_prodMap_iff, and_iff_left hB,
    ContinuousLinearMap.isInvertible_I_smul_iff, isInvertible_loopOperator_iff_det_ne_zero]

/-- **The determinant line of a nondegenerate asymptotic operator beside an invertible operator.**
Let `(J₀ L_S) ⊕ B` be bijective, equivalently `det (1 - Ψ(T)) ≠ 0`. Transporting its determinant
line to that of `1 - Ψ(T)` (`TauCeti.detLineProdMapLoopOperatorEquiv`) and applying the canonical
trivialization of the determinant line of an endomorphism (`LinearMap.detLineEndEquiv`) gives
`(det (1 - Ψ(T)))⁻¹` times the trivialization of the determinant line of the bijective operator
(`LinearMap.detLineEquivOfBijective`). -/
theorem detLineEndEquiv_detLineProdMapLoopOperatorEquiv (hB : B.IsInvertible)
    (hD : Function.Bijective ((I • loopOperator T S).prodMap B).toLinearMap)
    (x : ((I • loopOperator T S).prodMap B).toLinearMap.detLine) :
    LinearMap.detLineEndEquiv (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F))
        (detLineProdMapLoopOperatorEquiv T S hB x) =
      (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F)))⁻¹ *
        ((I • loopOperator T S).prodMap B).toLinearMap.detLineEquivOfBijective hD x := by
  have hinj := (injective_loopOperator_iff T S).1
    ((injective_prodMap_loopOperator_iff T S hB).1 hD.1)
  have hP := And.intro hinj (LinearMap.injective_iff_surjective.1 hinj)
  -- The two steps are composed as terms: `rw` times out on the large operator types here.
  refine (LinearMap.detLineEndEquiv_eq_inv_det_mul _ hP _).trans ?_
  exact congrArg (_ * ·) (LinearMap.detLineEquivOfBijective_detLineCongrKerCoker hD hP _ _ x)

/-- **The orientation sign of a nondegenerate asymptotic operator beside an invertible operator.**
In the situation of `TauCeti.detLineEndEquiv_detLineProdMapLoopOperatorEquiv`, the orientation of
the determinant line of `(J₀ L_S) ⊕ B` induced by the canonical trivialization for `1 - Ψ(T)` and
the orientation given by bijectivity differ by the sign of `det (1 - Ψ(T))`. -/
theorem sign_detLineEndEquiv_detLineProdMapLoopOperatorEquiv (hB : B.IsInvertible)
    (hD : Function.Bijective ((I • loopOperator T S).prodMap B).toLinearMap)
    (x : ((I • loopOperator T S).prodMap B).toLinearMap.detLine) :
    SignType.sign (LinearMap.detLineEndEquiv
          (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F))
          (detLineProdMapLoopOperatorEquiv T S hB x)) =
      SignType.sign (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F))) *
        SignType.sign
          (((I • loopOperator T S).prodMap B).toLinearMap.detLineEquivOfBijective hD x) := by
  have h (a b : ℝ) : SignType.sign (a⁻¹ * b) = SignType.sign a * SignType.sign b := by
    rw [sign_mul, TauCeti.sign_inv]
  exact (congrArg SignType.sign
    (detLineEndEquiv_detLineProdMapLoopOperatorEquiv T S hB hD x)).trans (h _ _)

end ProdMap

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
-- Exposed: `PeriodicOrientation.lean` uses the determinant lines of this operator as those of
-- `(J₀ L_S) ⊕ B`, which needs `periodicTorusOperator_eq_prodMap` to hold definitionally there.
@[expose]
def periodicTorusOperator (ℓ : ℝ) (S : C(AddCircle T, F →L[ℝ] F)) :
    CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ) →L[ℝ]
      CircleSobolev 0 F × 𝕐[F] :=
  (I • loopOperator T S).prodMap (torusModeOperator T _ S)

/-- `TauCeti.periodicTorusOperator` is `J₀ L_S` on the `s`-independent mode and
`TauCeti.torusModeOperator` on the others. -/
theorem periodicTorusOperator_eq_prodMap (ℓ : ℝ) (S : C(AddCircle T, F →L[ℝ] F)) :
    periodicTorusOperator T ℓ S = (I • loopOperator T S).prodMap (torusModeOperator T _ S) :=
  (rfl)

@[simp]
theorem periodicTorusOperator_apply (ℓ : ℝ) (S : C(AddCircle T, F →L[ℝ] F))
    (x : CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ)) :
    periodicTorusOperator T ℓ S x = (I • loopOperator T S x.1, torusModeOperator T _ S x.2) :=
  (rfl)

/-- **Complex linearity.** If the loop operator `L_S` commutes with multiplication by complex
scalars, as for a constant complex scalar loop, so does the operator `∂s + A` on maps periodic in
`s`, the complex structure of the Sobolev spaces acting by `J₀`. -/
theorem periodicTorusOperator_apply_smul (ℓ : ℝ) {S : C(AddCircle T, F →L[ℝ] F)}
    (hS : ∀ (c : ℂ) (a : CircleSobolev 1 F), loopOperator T S (c • a) = c • loopOperator T S a)
    (c : ℂ) (x : CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ)) :
    periodicTorusOperator T ℓ S (c • x) = c • periodicTorusOperator T ℓ S x := by
  refine Prod.ext ?_ (torusModeOperator_apply_smul T _ hS c x.2)
  simp [hS, smul_comm c I]

/-- **The reference operator is complex linear.** For `S = 0` the operator `∂s + J₀ ∂t` on maps
periodic in `s` commutes with multiplication by complex scalars, the complex structure of the
Sobolev spaces acting by `J₀`. -/
theorem periodicTorusOperator_zero_apply_smul (ℓ : ℝ) (c : ℂ)
    (x : CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ)) :
    periodicTorusOperator T ℓ 0 (c • x) = c • periodicTorusOperator T ℓ 0 x :=
  periodicTorusOperator_apply_smul T ℓ (fun c a ↦ by simp) c x

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

/-- **The kernel of the periodic orbit-torus operator.** For `ℓ ≠ 0` and an infinitesimally
symplectic loop `S`, taking the `s`-independent mode is a linear equivalence from the kernel of
`∂s + A` on maps periodic in `s` (`TauCeti.periodicTorusOperator`) onto the kernel of
`L_S ζ = ζ' - S ζ` (`TauCeti.coe_kerPeriodicTorusOperatorEquiv_apply`); the kernel elements are
`s`-independent. It is `TauCeti.kerProdMapLoopOperatorEquiv` for the invertible operator on the
other modes. -/
def kerPeriodicTorusOperatorEquiv (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    ker (periodicTorusOperator T ℓ S).toLinearMap ≃ₗ[ℝ]
      ker (loopOperator T S : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 0 F) :=
  kerProdMapLoopOperatorEquiv T S (isInvertible_torusModeOperator_periodic T hℓ S hS)

/-- The kernel elements of `TauCeti.periodicTorusOperator` are `s`-independent: the inverse of
`TauCeti.kerPeriodicTorusOperatorEquiv` sends `a` to the map `(a, 0)` with no other modes. -/
@[simp]
theorem kerPeriodicTorusOperatorEquiv_symm_apply (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (a : ker (loopOperator T S : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 0 F)) :
    ((kerPeriodicTorusOperatorEquiv T hℓ S hS).symm a :
      CircleSobolev 1 F × torusModeSobolev F (fun k : ℕ ↦ 2 * (k + 1) * π / ℓ)) =
        ((a : CircleSobolev 1 F), 0) :=
  kerProdMapLoopOperatorEquiv_symm_apply T S _ a

@[simp]
theorem coe_kerPeriodicTorusOperatorEquiv_apply (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (x : ker (periodicTorusOperator T ℓ S).toLinearMap) :
    (kerPeriodicTorusOperatorEquiv T hℓ S hS x : CircleSobolev 1 F) = x.val.1 :=
  coe_kerProdMapLoopOperatorEquiv_apply T S _ x

/-- **The cokernel of the periodic orbit-torus operator.** For `ℓ ≠ 0` and an infinitesimally
symplectic loop `S`, `z ↦ -J₀ z₀` on the `s`-independent mode induces a linear equivalence from the
cokernel of `∂s + A` on maps periodic in `s` (`TauCeti.periodicTorusOperator`) onto the cokernel
of `L_S ζ = ζ' - S ζ` (`TauCeti.quotientRangePeriodicTorusOperatorEquiv_mk`). It is
`TauCeti.quotientRangeProdMapLoopOperatorEquiv` for the invertible operator on the other modes. -/
def quotientRangePeriodicTorusOperatorEquiv (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    ((CircleSobolev 0 F × 𝕐[F]) ⧸ range (periodicTorusOperator T ℓ S).toLinearMap) ≃ₗ[ℝ]
      CircleSobolev 0 F ⧸ range (loopOperator T S : CircleSobolev 1 F →ₗ[ℝ] CircleSobolev 0 F) :=
  quotientRangeProdMapLoopOperatorEquiv T S (isInvertible_torusModeOperator_periodic T hℓ S hS)

/-- On the class of `z`, `TauCeti.quotientRangePeriodicTorusOperatorEquiv` is the class of
`-J₀ z₀`, where `z₀` is the `s`-independent mode of `z`. -/
@[simp]
theorem quotientRangePeriodicTorusOperatorEquiv_mk (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (z : CircleSobolev 0 F × 𝕐[F]) :
    quotientRangePeriodicTorusOperatorEquiv T hℓ S hS (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((-I) • z.1) :=
  quotientRangeProdMapLoopOperatorEquiv_mk T S _ z

/-- **The determinant line of the periodic orbit-torus operator.** For `ℓ ≠ 0` and an
infinitesimally symplectic loop `S`, the isomorphisms of kernels and cokernels with those of
`L_S ζ = ζ' - S ζ` (`TauCeti.kerPeriodicTorusOperatorEquiv`,
`TauCeti.quotientRangePeriodicTorusOperatorEquiv`), followed by those of `L_S` with `1 - Ψ(T)`
(`TauCeti.CircleSobolev.kerLoopOperatorEquiv`,
`TauCeti.CircleSobolev.quotientRangeLoopOperatorEquiv`), identify the determinant line of `∂s + A`
on maps periodic in `s` with the determinant line of `1 - Ψ(T)`, where
`Ψ = TauCeti.dysonSeriesLeft S`. -/
-- Exposed: the periodic corollaries in `PeriodicOrientation.lean` apply the results stated with
-- `detLineProdMapLoopOperatorEquiv` by unfolding this definition. An equation lemma to rewrite
-- with instead equates terms whose types agree only after unfolding `periodicTorusOperator` and
-- the normed and plain product instances; the `checkType` linter times out on its statement.
@[expose]
def detLinePeriodicTorusOperatorEquiv (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (periodicTorusOperator T ℓ S).toLinearMap.detLine ≃ₗ[ℝ]
      (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F)).detLine :=
  detLineProdMapLoopOperatorEquiv T S (isInvertible_torusModeOperator_periodic T hℓ S hS)

/-- `TauCeti.detLinePeriodicTorusOperatorEquiv` is the isomorphism of determinant lines induced by
the isomorphisms of kernels and cokernels with those of `1 - Ψ(T)`. -/
theorem detLinePeriodicTorusOperatorEquiv_def (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    detLinePeriodicTorusOperatorEquiv T hℓ S hS =
      LinearMap.detLineCongrKerCoker
        ((kerPeriodicTorusOperatorEquiv T hℓ S hS).trans (kerLoopOperatorEquiv T S))
        ((quotientRangePeriodicTorusOperatorEquiv T hℓ S hS).trans
          (quotientRangeLoopOperatorEquiv T S)) :=
  (rfl)

/-- `TauCeti.detLinePeriodicTorusOperatorEquiv` is the transport along the isomorphisms of kernels
and cokernels with those of `L_S` (`TauCeti.kerPeriodicTorusOperatorEquiv`,
`TauCeti.quotientRangePeriodicTorusOperatorEquiv`), followed by the identification of the
determinant line of `L_S` with that of `1 - Ψ(T)`
(`TauCeti.CircleSobolev.detLineLoopOperatorEquiv`). -/
theorem detLinePeriodicTorusOperatorEquiv_eq_trans (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    detLinePeriodicTorusOperatorEquiv T hℓ S hS =
      (LinearMap.detLineCongrKerCoker (kerPeriodicTorusOperatorEquiv T hℓ S hS)
        (quotientRangePeriodicTorusOperatorEquiv T hℓ S hS)).trans
        (detLineLoopOperatorEquiv T S) :=
  detLineProdMapLoopOperatorEquiv_eq_trans T S _

/-- **The periodic orbit-torus operator is Fredholm.** It is the direct sum of the Fredholm
operator `J₀ L_S` and an invertible operator. -/
theorem isFredholm_periodicTorusOperator (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (periodicTorusOperator T ℓ S).IsFredholm :=
  isFredholm_prodMap_loopOperator T S (isInvertible_torusModeOperator_periodic T hℓ S hS)

/-- **The periodic orbit-torus operator has index zero**, as `L_S`, whose kernel and cokernel it
shares. -/
@[simp]
theorem index_periodicTorusOperator (hℓ : ℓ ≠ 0) (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (periodicTorusOperator T ℓ S).index = 0 :=
  index_prodMap_loopOperator T S (isInvertible_torusModeOperator_periodic T hℓ S hS)

/-- **The Fredholm alternative for the periodic orbit-torus operator.** For `ℓ ≠ 0` and an
infinitesimally symplectic loop `S`, the operator `∂s + A` on maps periodic in `s` is invertible
exactly when `det (1 - Ψ(T)) ≠ 0`, where `Ψ = TauCeti.dysonSeriesLeft S`. In the geometric
application, the untwisted normal operator of an orbit torus is invertible exactly when the
linearized return map of the orbit does not have `1` as an eigenvalue. -/
theorem isInvertible_periodicTorusOperator_iff_det_ne_zero (hℓ : ℓ ≠ 0)
    (S : C(AddCircle T, F →L[ℝ] F))
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0) :
    (periodicTorusOperator T ℓ S).IsInvertible ↔
      LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : F →ₗ[ℝ] F)) ≠ 0 :=
  isInvertible_prodMap_loopOperator_iff_det_ne_zero T S
    (isInvertible_torusModeOperator_periodic T hℓ S hS)

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
        (periodicTorusOperator T ℓ S).toLinearMap.detLineEquivOfBijective hD x :=
  detLineEndEquiv_detLineProdMapLoopOperatorEquiv T S _ hD x

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
          ((periodicTorusOperator T ℓ S).toLinearMap.detLineEquivOfBijective hD x) :=
  sign_detLineEndEquiv_detLineProdMapLoopOperatorEquiv T S _ hD x

end Inner

end TauCeti
