/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Endomorphism
public import TauCeti.Analysis.ODE.Periodic
public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Basic
public import TauCeti.LinearAlgebra.Determinant.Endomorphism
public import TauCeti.Topology.Instances.AddCircle.Coe
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Data.SignType.Basic
import TauCeti.LinearAlgebra.LinearMap.RegularRestriction
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The determinant line of a periodic loop operator and the return map

Let `E` be a finite-dimensional complex normed space, `S : AddCircle T → (E →L[ℝ] E)` a continuous
loop of real-linear maps, and `L_S ζ = ζ' - S ζ` the Fredholm operator `H¹(E) → H⁰(E)` of index
zero on the circle Sobolev spaces (`TauCeti.CircleSobolev.loopOperator`). Write
`Ψ = TauCeti.dysonSeriesLeft S` for the propagator of `w' = S w`, so that `P = Ψ(T)` is the
return map. This file identifies the kernel, the cokernel and the determinant line of `L_S` with
those of the finite-dimensional endomorphism `1 - P` of `E`:

* evaluation at `0` of the continuous representative is a linear equivalence from the kernel of
  `L_S` onto the kernel of `1 - P` (`TauCeti.CircleSobolev.kerLoopOperatorEquiv`);
* the endpoint map `f ↦ Ψ(T) (∫₀ᵀ Ψ(s)⁻¹ f(s) ds)` on continuous loops induces a linear
  equivalence from the cokernel of `L_S` onto the cokernel of `1 - P`
  (`TauCeti.CircleSobolev.quotientRangeLoopOperatorEquiv`);
* together they identify the determinant line `det (ker L_S) ⊗ (det (coker L_S))^*` with the
  determinant line of `1 - P` (`TauCeti.CircleSobolev.detLineLoopOperatorEquiv`). When `L_S` is
  invertible, equivalently when `det (1 - P) ≠ 0`
  (`TauCeti.CircleSobolev.isInvertible_loopOperator_iff_det_ne_zero`), the canonical
  trivialization of the determinant line of `1 - P` and the trivialization of the determinant line
  of the bijective operator `L_S` differ by `det (1 - P)`, so the two orientations of `det L_S`
  differ by the sign of `det (1 - P)`
  (`TauCeti.CircleSobolev.sign_detLineEndEquiv_detLineLoopOperatorEquiv`).

The same statements for the operator `w ↦ w' - S w` from `C¹` periodic maps to continuous periodic
maps are `TauCeti.kerTwistedLinearOperatorEquiv`, `TauCeti.quotientRangeTwistedLinearOperatorEquiv`
and `TauCeti.detLineTwistedLinearOperatorEquiv`. This file transfers them to the Sobolev
realization, a Fredholm operator between Banach spaces, whose determinant line is the fibre at
`L_S` of the determinant line bundle over Fredholm operators. The two realizations are compared by
regularity: an element of `H¹` whose image under `L_S` is a continuous loop has a `C¹` continuous
representative, since a continuous weak derivative is a classical derivative
(`TauCeti.CircleSobolev.hasDerivAt_toContinuousMap_of_derivative_eq`). So the kernels agree and the
map of cokernels is injective (`LinearMap.kerEquivOfRegular`,
`LinearMap.injective_mapQ_of_regular`). It is onto because `L_S` has index zero, as has the
operator on `C¹` maps, so both cokernels have the dimension of the common kernel
(`LinearMap.sup_range_eq_top_of_finrank_le`).

These identifications are coherent in families. For a continuous family `M x` of coefficient loops,
transporting the normalized generator of the determinant line of `1 - Ψ_x(T)`
(`LinearMap.detLineEndGenerator`) to the determinant line of `L_{M x}` gives a continuous
orientation of the determinant line bundle of the family
(`TauCeti.CircleSobolev.isDetLineCoherentOn_detLineLoopOperatorEquiv_symm`), although kernels and
cokernels jump. So orientation transport along a path of loop operators follows the return maps
(`TauCeti.CircleSobolev.detLineOrientationTransport_rayOfNeZero_detLineLoopOperatorEquiv_symm`),
and the finite-dimensional sign laws for paths of endomorphisms `1 - Ψ_t(T)`
(`TauCeti.detLineOrientationTransport_detLineEquivOfBijective_of_pos`,
`TauCeti.detLineOrientationTransport_detLineEquivOfBijective_of_neg`) apply to the loop operators.
The proof compares kernel charts: continuous loops `r l` lifting a right inverse of the endpoint map
stabilize `L_S`, with kernel coordinate the value at `0`, and correspond to the stabilizer
`l ↦ E (r l)` of `1 - Ψ(T)`; evaluation at `0` identifies the two stabilized kernels
(`ContinuousLinearMap.detLineChartEquiv_detLineCongrKerCoker`).

Between bijective endpoints, transport along a path of loop operators therefore preserves the
orientations given by bijectivity when `det (1 - P_a) * det (1 - P_b) > 0`
(`TauCeti.CircleSobolev.detLineOrientationTransport_detLineEquivOfBijective_loopOperator_of_pos`)
and reverses them when `det (1 - P_a) * det (1 - P_b) < 0`
(`TauCeti.CircleSobolev.detLineOrientationTransport_detLineEquivOfBijective_loopOperator_of_neg`),
since at a bijective `L_S` the transported normalized generator is `det (1 - P)` times the
generator given by bijectivity
(`TauCeti.CircleSobolev.detLineLoopOperatorEquiv_symm_detLineEndGenerator_eq_det_smul`).

The operators `∂t - J₀ S(t)` on loops along a closed orbit, which govern the periodic twists of the
normal operator `∂s + J₀ ∂t + S(t)` of an orbit torus, are of this form, with `P` the linearized
return map. For them the orientation comparison above is expressed by the sign of `det (1 - P)`,
and, along a path of such operators with bijective endpoints, transport carries the orientation
given by bijectivity at one end to the orientation given by bijectivity at the other when the
product of the determinants at the two ends is positive, and to its opposite when it is negative.

## Main definitions

* `TauCeti.CircleSobolev.kerLoopOperatorEquiv T S`: `ker L_S ≃ ker (1 - Ψ(T))`.
* `TauCeti.CircleSobolev.quotientRangeLoopOperatorEquiv T S`: `coker L_S ≃ coker (1 - Ψ(T))`.
* `TauCeti.CircleSobolev.detLineLoopOperatorEquiv T S`: `det L_S ≃ det (1 - Ψ(T))`.

## Main results

* `TauCeti.CircleSobolev.injective_loopOperator_iff`: `L_S` is injective exactly when `1 - Ψ(T)`
  is.
* `TauCeti.CircleSobolev.isInvertible_loopOperator_iff_det_ne_zero`: `L_S` is invertible exactly
  when `det (1 - Ψ(T)) ≠ 0`.
* `TauCeti.CircleSobolev.detLineEndEquiv_detLineLoopOperatorEquiv`,
  `TauCeti.CircleSobolev.sign_detLineEndEquiv_detLineLoopOperatorEquiv`: for bijective `L_S`, the
  trivialization of `det L_S` through `1 - Ψ(T)` is `(det (1 - Ψ(T)))⁻¹` times the trivialization
  given by bijectivity, so the two orientations differ by the sign of `det (1 - Ψ(T))`.
* `TauCeti.CircleSobolev.isDetLineCoherentOn_detLineLoopOperatorEquiv_symm`: for a continuous family
  of coefficient loops, the transported normalized generators form a coherent family.
* `TauCeti.CircleSobolev.detLineOrientationTransport_rayOfNeZero_detLineLoopOperatorEquiv_symm`:
  orientation transport along a path of loop operators carries transported normalized generators to
  transported normalized generators.
* `TauCeti.CircleSobolev.detLineOrientationTransport_detLineEquivOfBijective_loopOperator_of_pos`,
  `TauCeti.CircleSobolev.detLineOrientationTransport_detLineEquivOfBijective_loopOperator_of_neg`:
  along a path between bijective loop operators, transport preserves or reverses the orientations
  given by bijectivity according to the sign of `det (1 - Ψ_a(T)) * det (1 - Ψ_b(T))`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (the operator `J₀ ∂_t + S` on `W^{1,2}(S¹)` and the return map).
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893 (the determinant signs of the twisted normal operators of tori).
-/

public section

noncomputable section

open LinearMap (ker range)

namespace TauCeti

namespace CircleSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (T : ℝ) (S : C(AddCircle T, E →L[ℝ] E))

/-! ### Comparison with the operator on `C¹` periodic maps -/

variable [hT : Fact (0 < T)] [FiniteDimensional ℂ E]

/-- A finite-dimensional complex space is complete, as needed for continuous representatives and
for the propagator. -/
local instance instCompleteSpaceLoopOperatorDetLine : CompleteSpace E :=
  FiniteDimensional.completeSpace ℂ E

variable (E) in
/-- A continuous `T`-periodic map, as an element of `H⁰(E)`. -/
private def toH0 : twistedContinuous E T 1 →ₗ[ℝ] CircleSobolev 0 E :=
  ((ofContinuousMap (E := E) T).restrictScalars ℝ).toLinearMap ∘ₗ
    (twistedContinuousOneEquiv E T).toLinearMap

private theorem toH0_apply (f : twistedContinuous E T 1) :
    toH0 E T f = ofContinuousMap T (twistedContinuousOneEquiv E T f) :=
  (rfl)

private theorem toH0_injective : Function.Injective (toH0 E T) :=
  (ofContinuousMap_injective T).comp (twistedContinuousOneEquiv E T).injective

/-- A `C¹` periodic map is the continuous representative of an element of `H¹(E)` whose derivative
is the class of its classical derivative. -/
private theorem exists_toContinuousMap_eq (w : twistedContDiff E T 1) :
    ∃ a : CircleSobolev 1 E,
      toContinuousMap T (by norm_num) a =
          twistedContinuousOneEquiv E T
            (Submodule.inclusion twistedContDiff_le_twistedContinuous w) ∧
        derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) a =
          ofContinuousMap T (twistedContinuousOneEquiv E T ⟨_, deriv_mem_twistedContinuous w⟩) :=
  exists_toContinuousMap_eq_and_derivative_eq T _ _ fun x ↦ by
    simp only [twistedContinuousOneEquiv_apply, Submodule.coe_inclusion]
    exact ((mem_twistedContDiff.1 w.property).1.differentiable one_ne_zero x).hasDerivAt

variable (E) in
/-- A `C¹` periodic map, as an element of `H¹(E)`. -/
private def toH1 : twistedContDiff E T 1 →ₗ[ℝ] CircleSobolev 1 E where
  toFun w := (exists_toContinuousMap_eq T w).choose
  map_add' w v := toContinuousMap_injective T (by norm_num) <| by
    have h (w : twistedContDiff E T 1) := (exists_toContinuousMap_eq T w).choose_spec.1
    rw [h]
    simp only [map_add]
    rw [h, h]
  map_smul' c w := toContinuousMap_injective T (by norm_num) <| by
    have h (w : twistedContDiff E T 1) := (exists_toContinuousMap_eq T w).choose_spec.1
    rw [RingHom.id_apply, ContinuousLinearMap.map_smul_of_tower, h, h, map_smul, map_smul]

private theorem toContinuousMap_toH1 (w : twistedContDiff E T 1) :
    toContinuousMap T (by norm_num) (toH1 E T w) =
      twistedContinuousOneEquiv E T (Submodule.inclusion twistedContDiff_le_twistedContinuous w) :=
  (exists_toContinuousMap_eq T w).choose_spec.1

private theorem derivative_toH1 (w : twistedContDiff E T 1) :
    derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) (toH1 E T w) =
      ofContinuousMap T (twistedContinuousOneEquiv E T ⟨_, deriv_mem_twistedContinuous w⟩) :=
  (exists_toContinuousMap_eq T w).choose_spec.2

private theorem toH1_injective : Function.Injective (toH1 E T) := fun w v h ↦ by
  have h' := congrArg (toContinuousMap T (by norm_num)) h
  rw [toContinuousMap_toH1, toContinuousMap_toH1] at h'
  exact Submodule.inclusion_injective _ ((twistedContinuousOneEquiv E T).injective h')

/-- The square comparing `w ↦ w' - S w` on `C¹` periodic maps with `L_S` commutes. -/
private theorem toH0_comp_twistedLinearOperator :
    toH0 E T ∘ₗ
        twistedLinearOperator (AddCircle.continuous_comp_coe S) (AddCircle.periodic_comp_coe S) 1 =
      (loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E) ∘ₗ toH1 E T := by
  ext w : 1
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, loopOperator_apply,
    mulLoop_apply, toH0_apply, derivative_toH1, toContinuousMap_toH1, ← map_sub]
  congr 1
  refine AddCircle.continuousMap_ext_coe fun t ↦ ?_
  simp only [ContinuousMap.sub_apply, twistedContinuousOneEquiv_apply,
    ContinuousMap.applyContinuousLinearMap_apply, twistedLinearOperator_apply,
    Submodule.coe_inclusion]

/-- **Regularity.** An element of `H¹(E)` whose image under `L_S` is a continuous loop comes from
a `C¹` periodic map. -/
private theorem mem_range_toH1 (a : CircleSobolev 1 E)
    (ha : loopOperator T S a ∈ range (toH0 E T)) : a ∈ range (toH1 E T) := by
  obtain ⟨f, hf⟩ := ha
  set u := toContinuousMap T (show (1 : ℝ) / 2 < 1 by norm_num) a
  -- The weak derivative of `a` is the continuous loop `S u + f`.
  have hder : derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) a =
      ofContinuousMap T
        (ContinuousMap.applyContinuousLinearMap S u + twistedContinuousOneEquiv E T f) := by
    rw [map_add, ← toH0_apply, hf, loopOperator_apply, mulLoop_apply]
    abel
  have hd (x : ℝ) := hasDerivAt_toContinuousMap_of_derivative_eq T a _ hder x
  have hu : (fun y : ℝ ↦ u y) ∈ twistedContDiff E T 1 := by
    refine mem_twistedContDiff.2
      ⟨contDiff_one_iff_deriv.2 ⟨fun x ↦ (hd x).differentiableAt, ?_⟩, fun t ↦ ?_⟩
    · rw [funext fun x ↦ (hd x).deriv]
      exact AddCircle.continuous_comp_coe
        (ContinuousMap.applyContinuousLinearMap S u + twistedContinuousOneEquiv E T f)
    · exact (mem_twistedContinuous.1 (coe_continuousMap_mem_twistedContinuous u)).2 t
  refine ⟨⟨_, hu⟩, toContinuousMap_injective T (by norm_num) ?_⟩
  rw [toContinuousMap_toH1]
  refine AddCircle.continuousMap_ext_coe fun t ↦ ?_
  simp only [twistedContinuousOneEquiv_apply, Submodule.coe_inclusion, u]

private theorem finrank_quotient_range_loopOperator_le :
    Module.finrank ℝ
        (CircleSobolev 0 E ⧸ range (loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E)) ≤
      Module.finrank ℝ (twistedContinuous E T 1 ⧸
        range (twistedLinearOperator (AddCircle.continuous_comp_coe S)
          (AddCircle.periodic_comp_coe S) 1)) := by
  have hindex := index_loopOperator T S
  rw [ContinuousLinearMap.index_eq_finrank_sub, sub_eq_zero, Nat.cast_inj] at hindex
  rw [← hindex, ← finrank_ker_twistedLinearOperator_eq_finrank_quotient_range _ _ hT.out
    one_ne_zero, (LinearMap.kerEquivOfRegular (toH0_comp_twistedLinearOperator T S)
      (toH1_injective T) (toH0_injective T) (mem_range_toH1 T S)).finrank_eq]

private theorem sup_range_eq_top :
    range (toH0 E T) ⊔ range (loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E) =
      ⊤ :=
  have : FiniteDimensional ℝ (CircleSobolev 0 E ⧸
      range (loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E)) :=
    (isFredholm_loopOperator T S).finite_coker
  LinearMap.sup_range_eq_top_of_finrank_le (toH0_comp_twistedLinearOperator T S)
    (toH0_injective T) (mem_range_toH1 T S) (finrank_quotient_range_loopOperator_le T S)

/-! ### Kernel, cokernel and determinant line -/

/-- **The kernel of `L_S` is the kernel of `1 - Ψ(T)`.** Evaluation at `0` of the continuous
representative is a linear equivalence from the kernel of `ζ ↦ ζ' - S ζ`, `H¹(E) → H⁰(E)`, onto the
kernel of `1 - Ψ(T)`, where `Ψ = TauCeti.dysonSeriesLeft S` is the propagator of `w' = S w`
(`TauCeti.CircleSobolev.coe_kerLoopOperatorEquiv_apply`). -/
def kerLoopOperatorEquiv :
    ker (loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E) ≃ₗ[ℝ]
      ker (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)) :=
  ((LinearMap.kerEquivOfRegular (toH0_comp_twistedLinearOperator T S) (toH1_injective T)
      (toH0_injective T) (mem_range_toH1 T S)).symm.trans
    (kerTwistedLinearOperatorEquiv (AddCircle.continuous_comp_coe S)
      (AddCircle.periodic_comp_coe S) 1)).trans
    (LinearEquiv.ofEq _ _ (by rw [one_smul]))

@[simp]
theorem coe_kerLoopOperatorEquiv_apply
    (a : ker (loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E)) :
    (kerLoopOperatorEquiv T S a : E) = toContinuousMap T (by norm_num) a.val 0 := by
  obtain ⟨b, rfl⟩ := (LinearMap.kerEquivOfRegular (toH0_comp_twistedLinearOperator T S)
    (toH1_injective T) (toH0_injective T) (mem_range_toH1 T S)).surjective a
  have h0 (f : twistedContinuous E T 1) : twistedContinuousOneEquiv E T f 0 = (f : ℝ → E) 0 := by
    rw [← AddCircle.coe_zero, twistedContinuousOneEquiv_apply]
  simp [kerLoopOperatorEquiv, toContinuousMap_toH1, h0]

/-- The inverse of `TauCeti.CircleSobolev.kerLoopOperatorEquiv` sends `x` to the element of `H¹(E)`
whose continuous representative is the solution `t ↦ Ψ(t) x` of `w' = S w`. -/
@[simp]
theorem toContinuousMap_kerLoopOperatorEquiv_symm_apply
    (x : ker (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E))) (t : ℝ) :
    toContinuousMap T (by norm_num) ((kerLoopOperatorEquiv T S).symm x).val t =
      dysonSeriesLeft (fun t : ℝ ↦ S t) t x := by
  set a := (kerLoopOperatorEquiv T S).symm x
  have h0 : toContinuousMap T (by norm_num) a.val 0 = x := by
    rw [← coe_kerLoopOperatorEquiv_apply, LinearEquiv.apply_symm_apply]
  rw [eq_dysonSeriesLeft_apply (AddCircle.continuous_comp_coe S)
    ((loopOperator_eq_zero_iff T S a.val).1 a.property) t]
  exact congrArg _ h0

/-- **The cokernel of `L_S` is the cokernel of `1 - Ψ(T)`.** The endpoint map
`f ↦ Ψ(T) (∫₀ᵀ Ψ(s)⁻¹ f(s) ds)` on continuous loops induces a linear equivalence from the cokernel
of `ζ ↦ ζ' - S ζ`, `H¹(E) → H⁰(E)`, onto the cokernel of `1 - Ψ(T)`, where
`Ψ = TauCeti.dysonSeriesLeft S` (`TauCeti.CircleSobolev.quotientRangeLoopOperatorEquiv_mk`). -/
def quotientRangeLoopOperatorEquiv :
    (CircleSobolev 0 E ⧸ range (loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E)) ≃ₗ[ℝ]
      E ⧸ range (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)) :=
  ((LinearMap.cokerEquivOfRegular (toH0_comp_twistedLinearOperator T S) (toH0_injective T)
      (mem_range_toH1 T S) (sup_range_eq_top T S)).symm.trans
    (quotientRangeTwistedLinearOperatorEquiv (AddCircle.continuous_comp_coe S)
      (AddCircle.periodic_comp_coe S)
      hT.out one_ne_zero)).trans
    (Submodule.quotEquivOfEq _ _ (by rw [one_smul]))

/-- On the class of a continuous loop `f`, `TauCeti.CircleSobolev.quotientRangeLoopOperatorEquiv`
is the class of the endpoint value `Ψ(T) (∫₀ᵀ Ψ(s)⁻¹ f(s) ds)`, with `Ψ(s)⁻¹ = dysonSeries (-S) s`.
-/
@[simp]
theorem quotientRangeLoopOperatorEquiv_mk (f : C(AddCircle T, E)) :
    quotientRangeLoopOperatorEquiv T S (Submodule.Quotient.mk (ofContinuousMap T f)) =
      Submodule.Quotient.mk (dysonSeriesLeft (fun t : ℝ ↦ S t) T
        (∫ s in 0..T, dysonSeries (-fun t : ℝ ↦ S t) s (f s))) := by
  have hj : ofContinuousMap T f = toH0 E T ((twistedContinuousOneEquiv E T).symm f) := by
    rw [toH0_apply, LinearEquiv.apply_symm_apply]
  rw [hj]
  simp [quotientRangeLoopOperatorEquiv]

/-- **The determinant line of `L_S` is that of `1 - Ψ(T)`.** Evaluation at `0` on the kernel
(`TauCeti.CircleSobolev.kerLoopOperatorEquiv`) and the endpoint map on the cokernel
(`TauCeti.CircleSobolev.quotientRangeLoopOperatorEquiv`) identify the determinant line
`det (ker L_S) ⊗ (det (coker L_S))^*` of `L_S ζ = ζ' - S ζ`, `H¹(E) → H⁰(E)`, with the determinant
line of `1 - Ψ(T)`, where `Ψ = TauCeti.dysonSeriesLeft S`. -/
def detLineLoopOperatorEquiv :
    (loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E).detLine ≃ₗ[ℝ]
      (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)).detLine :=
  LinearMap.detLineCongrKerCoker (kerLoopOperatorEquiv T S) (quotientRangeLoopOperatorEquiv T S)

/-- `TauCeti.CircleSobolev.detLineLoopOperatorEquiv` is the isomorphism of determinant lines
induced by `TauCeti.CircleSobolev.kerLoopOperatorEquiv` on kernels and
`TauCeti.CircleSobolev.quotientRangeLoopOperatorEquiv` on cokernels. -/
theorem detLineLoopOperatorEquiv_def :
    detLineLoopOperatorEquiv T S =
      LinearMap.detLineCongrKerCoker (kerLoopOperatorEquiv T S)
        (quotientRangeLoopOperatorEquiv T S) :=
  (rfl)

open TensorProduct in
/-- On pure tensors, `TauCeti.CircleSobolev.detLineLoopOperatorEquiv` transports the kernel factor
along evaluation at `0` and the cokernel functional along the inverse of the endpoint map. -/
@[simp]
theorem detLineLoopOperatorEquiv_tmul
    (x : detLine ℝ (ker (loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E)))
    (φ : Module.Dual ℝ (detLine ℝ (CircleSobolev 0 E ⧸
      range (loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E)))) :
    detLineLoopOperatorEquiv T S (x ⊗ₜ φ) =
      LinearEquiv.detLineCongr (kerLoopOperatorEquiv T S) x ⊗ₜ
        (φ ∘ₗ (LinearEquiv.detLineCongr (quotientRangeLoopOperatorEquiv T S)).symm.toLinearMap) :=
  LinearMap.detLineCongrKerCoker_tmul _ _ x φ

/-- The operator `ζ ↦ ζ' - S ζ`, `H¹(E) → H⁰(E)`, is injective exactly when `1 - Ψ(T)` is, where
`Ψ = TauCeti.dysonSeriesLeft S`. -/
theorem injective_loopOperator_iff :
    Function.Injective (loopOperator T S) ↔
      Function.Injective ⇑(1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)) := by
  rw [← ContinuousLinearMap.coe_coe, ← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot,
    ← Submodule.subsingleton_iff_eq_bot, ← Submodule.subsingleton_iff_eq_bot,
    (kerLoopOperatorEquiv T S).subsingleton_congr]

/-- **The Fredholm alternative for `L_S`.** The operator `ζ ↦ ζ' - S ζ`, `H¹(E) → H⁰(E)`, is
invertible exactly when `det (1 - Ψ(T)) ≠ 0`, where `Ψ = TauCeti.dysonSeriesLeft S`. -/
theorem isInvertible_loopOperator_iff_det_ne_zero :
    (loopOperator T S).IsInvertible ↔
      LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)) ≠ 0 := by
  rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot,
    ← injective_loopOperator_iff]
  exact ⟨fun h ↦ h.injective, fun h ↦
    (isFredholm_loopOperator T S).isInvertible_of_injective_of_index_eq_zero h
      (index_loopOperator T S)⟩

/-- **The determinant line of a nondegenerate loop operator.** Let `L_S ζ = ζ' - S ζ`,
`H¹(E) → H⁰(E)`, be bijective, equivalently `det (1 - Ψ(T)) ≠ 0`. Transporting the determinant line
of `L_S` to that of `1 - Ψ(T)` and applying the canonical trivialization of the determinant line of
an endomorphism (`LinearMap.detLineEndEquiv`) gives `(det (1 - Ψ(T)))⁻¹` times the trivialization
of the determinant line of the bijective operator `L_S` (`LinearMap.detLineEquivOfBijective`). -/
theorem detLineEndEquiv_detLineLoopOperatorEquiv (hL : Function.Bijective (loopOperator T S))
    (x : (loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E).detLine) :
    LinearMap.detLineEndEquiv (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E))
        (detLineLoopOperatorEquiv T S x) =
      (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)))⁻¹ *
        (loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E).detLineEquivOfBijective
          hL x := by
  have hinj := (injective_loopOperator_iff T S).1 hL.1
  have hP := And.intro hinj (LinearMap.injective_iff_surjective.1 hinj)
  rw [LinearMap.detLineEndEquiv_eq_inv_det_mul _ hP, detLineLoopOperatorEquiv,
    LinearMap.detLineEquivOfBijective_detLineCongrKerCoker hL hP]

/-- **The orientation sign of a nondegenerate loop operator.** In the situation of
`TauCeti.CircleSobolev.detLineEndEquiv_detLineLoopOperatorEquiv`, the orientation of the
determinant line of `L_S` induced by the canonical trivialization for `1 - Ψ(T)` and the orientation
given by bijectivity of `L_S` differ by the sign of `det (1 - Ψ(T))`. -/
theorem sign_detLineEndEquiv_detLineLoopOperatorEquiv
    (hL : Function.Bijective (loopOperator T S))
    (x : (loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E).detLine) :
    SignType.sign (LinearMap.detLineEndEquiv
          (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E))
          (detLineLoopOperatorEquiv T S x)) =
      SignType.sign (LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E))) *
        SignType.sign
          ((loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E).detLineEquivOfBijective
            hL x) := by
  rw [detLineEndEquiv_detLineLoopOperatorEquiv T S hL, sign_mul, TauCeti.sign_inv]

/-- At a bijective `L_S`, the element of its determinant line corresponding to the normalized
generator of the determinant line of `1 - Ψ(T)` is `det (1 - Ψ(T))` times the generator of the
trivialization given by bijectivity. -/
theorem detLineLoopOperatorEquiv_symm_detLineEndGenerator_eq_det_smul
    (hL : Function.Bijective (loopOperator T S)) :
    (detLineLoopOperatorEquiv T S).symm
        (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)).detLineEndGenerator =
      LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)) •
        ((loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E).detLineEquivOfBijective
          hL).symm 1 := by
  have hinj := (injective_loopOperator_iff T S).1 hL.1
  have hP := And.intro hinj (LinearMap.injective_iff_surjective.1 hinj)
  rw [LinearMap.detLineEndGenerator_eq_det_smul _ hP, LinearEquiv.map_smul]
  congr 1
  rw [LinearEquiv.symm_apply_eq]
  refine (LinearMap.detLineEquivOfBijective hP).injective ?_
  rw [LinearEquiv.apply_symm_apply]
  exact ((LinearMap.detLineEquivOfBijective_detLineCongrKerCoker hL hP _ _ _).trans
    (LinearEquiv.apply_symm_apply _ _)).symm

/-! ### Coherence along families -/

/-- A solution `a` of `L_S a + f = 0`, for a continuous loop `f`, satisfies
`(1 - Ψ(T)) (a 0) + E f = 0`, where `E f = Ψ(T) (∫₀ᵀ Ψ(s)⁻¹ f(s) ds)` is the endpoint map. -/
private theorem one_sub_apply_add_twistedEndpoint_eq_zero {a : CircleSobolev 1 E}
    {f : twistedContinuous E T 1} (ha : loopOperator T S a + toH0 E T f = 0) :
    (1 - dysonSeriesLeft (fun t : ℝ ↦ S t) T) (toContinuousMap T (by norm_num) a 0) +
      twistedEndpoint (AddCircle.continuous_comp_coe S) T 1 f = 0 := by
  have hL : loopOperator T S a = toH0 E T (-f) := by
    rw [map_neg, eq_neg_iff_add_eq_zero, ha]
  obtain ⟨w, rfl⟩ := mem_range_toH1 T S a ⟨-f, hL.symm⟩
  have hw : twistedLinearOperator (AddCircle.continuous_comp_coe S)
      (AddCircle.periodic_comp_coe S) 1 w = -f := by
    refine toH0_injective T ?_
    rw [← hL]
    exact LinearMap.congr_fun (toH0_comp_twistedLinearOperator T S) w
  have key := (forall_add_eq_smul_iff_smul_one_sub_apply_eq (AddCircle.continuous_comp_coe S)
    (AddCircle.periodic_comp_coe S) (mem_twistedContinuous.1 (-f).property).1
    (mem_twistedContinuous.1 (-f).property).2 ((twistedLinearOperator_eq_iff _ _ w (-f)).1 hw)).1
    (mem_twistedContDiff.1 w.property).2
  rw [one_smul] at key
  have h0 : toContinuousMap T (by norm_num) (toH1 E T w) 0 = (w : ℝ → E) 0 := by
    rw [toContinuousMap_toH1, ← AddCircle.coe_zero, twistedContinuousOneEquiv_apply,
      Submodule.coe_inclusion]
  rw [h0, key, twistedEndpoint_apply, ← map_add]
  simp [intervalIntegral.integral_neg]

variable (r : E →ₗ[ℝ] twistedContinuous E T 1)

/-- The stabilizer of `L_S` by the continuous loops `r l`, `l ∈ E`. -/
private def loopStab : E →L[ℝ] CircleSobolev 0 E :=
  LinearMap.toContinuousLinearMap (toH0 E T ∘ₗ r)

/-- The kernel coordinate `(a, l) ↦ a 0` of the stabilized loop operator. -/
private def evalZero : CircleSobolev 1 E × E →L[ℝ] E :=
  (ContinuousMap.evalCLM ℝ (0 : AddCircle T) ∘L
    (toContinuousMap T (show (1 : ℝ) / 2 < 1 by norm_num)).restrictScalars ℝ) ∘L
    ContinuousLinearMap.fst ℝ _ _

private theorem evalZero_apply (y : CircleSobolev 1 E × E) :
    evalZero T y = toContinuousMap T (by norm_num) y.1 0 :=
  (rfl)

/-- The stabilizer `l ↦ E (r l)` of `1 - Ψ(T)` matching `TauCeti.CircleSobolev.loopStab`. -/
private def endpointStab : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap (twistedEndpoint (AddCircle.continuous_comp_coe S) T 1 ∘ₗ r)

/-- Evaluation at zero in the first factor: the comparison map between the stabilized kernels. -/
private def evalZeroProd : CircleSobolev 1 E × E →ₗ[ℝ] E × E :=
  ((evalZero T : CircleSobolev 1 E × E →L[ℝ] E) : CircleSobolev 1 E × E →ₗ[ℝ] E).prod
    (LinearMap.snd ℝ _ _)

private theorem evalZeroProd_snd (y : CircleSobolev 1 E × E) : (evalZeroProd T y).2 = y.2 :=
  (rfl)

private theorem fst_evalZeroProd (y : CircleSobolev 1 E × E) :
    ContinuousLinearMap.fst ℝ E E (evalZeroProd T y) = evalZero T y :=
  (rfl)

/-- The endomorphism `1 - Ψ(T)` of `E`, as a continuous linear map whose underlying linear map is
literally the map `1 - Ψ(T)` of `TauCeti.CircleSobolev.detLineLoopOperatorEquiv`. -/
private def returnEnd : E →L[ℝ] E :=
  ⟨1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E),
    LinearMap.continuous_of_finiteDimensional _⟩

omit hT in
private theorem returnEnd_eq : returnEnd T S = 1 - dysonSeriesLeft (fun t : ℝ ↦ S t) T :=
  ContinuousLinearMap.ext fun e ↦ by simp [returnEnd]

private theorem evalZeroProd_ker (y : CircleSobolev 1 E × E)
    (hy : (loopOperator T S).coprod (loopStab T r) y = 0) :
    (returnEnd T S).coprod (endpointStab T S r) (evalZeroProd T y) = 0 := by
  obtain ⟨a, l⟩ := y
  simp only [ContinuousLinearMap.coprod_apply, loopStab, LinearMap.coe_toContinuousLinearMap',
    LinearMap.comp_apply] at hy
  have h1 := fst_evalZeroProd T (a, l)
  rw [ContinuousLinearMap.coe_fst', evalZero_apply] at h1
  rw [ContinuousLinearMap.coprod_apply, h1, evalZeroProd_snd, returnEnd_eq, endpointStab,
    LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply]
  exact one_sub_apply_add_twistedEndpoint_eq_zero T S hy

private theorem evalZeroProd_inl
    (u : ker (loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E)) :
    evalZeroProd T ((u : CircleSobolev 1 E), 0) = ((kerLoopOperatorEquiv T S u : E), 0) := by
  simp [evalZeroProd, evalZero_apply]

private theorem quotientRangeLoopOperatorEquiv_mkQ_loopStab (l : E) :
    quotientRangeLoopOperatorEquiv T S
        ((loopOperator T S : CircleSobolev 1 E →ₗ[ℝ] CircleSobolev 0 E).range.mkQ
          (loopStab T r l)) =
      (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)).range.mkQ
        (endpointStab T S r l) := by
  simp [loopStab, endpointStab, toH0_apply]

/-- Where the kernel chart `(E (r ·), fst)` of `1 - Ψ(T)` is valid, so is the kernel chart
`(r ·, a ↦ a 0)` of `L_S`, and the two charts read the normalized generator of the determinant line
of `1 - Ψ(T)` and its transport to the determinant line of `L_S` in the same way. -/
private theorem exists_detLineChartEquiv_detLineLoopOperatorEquiv_symm
    (h' : (((returnEnd T S).coprod (endpointStab T S r)).prod
      (ContinuousLinearMap.fst ℝ E E)).IsInvertible) :
    ∃ h : (((loopOperator T S).coprod (loopStab T r)).prod (evalZero T)).IsInvertible,
      ContinuousLinearMap.detLineChartEquiv (loopOperator T S) (loopStab T r) (evalZero T) h
          ((detLineLoopOperatorEquiv T S).symm
            (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)).detLineEndGenerator) =
        ContinuousLinearMap.detLineChartEquiv (returnEnd T S) (endpointStab T S r)
          (ContinuousLinearMap.fst ℝ E E) h'
          ((returnEnd T S : E →ₗ[ℝ] E)).detLineEndGenerator := by
  have hΦ := evalZeroProd_ker T S r
  have hK := evalZeroProd_inl T S
  have hC := quotientRangeLoopOperatorEquiv_mkQ_loopStab T S r
  have h := ContinuousLinearMap.isInvertible_prod_coprod_of_kerCokerEquiv
    (eΛ := LinearEquiv.refl ℝ E) hΦ hK (fun y _ ↦ evalZeroProd_snd T y) hC (LinearEquiv.refl ℝ E)
    (fun y _ ↦ (fst_evalZeroProd T y).trans (LinearEquiv.refl_apply _).symm) h'
  refine ⟨h, ?_⟩
  have := ContinuousLinearMap.detLineChartEquiv_detLineCongrKerCoker
    (eΛ := LinearEquiv.refl ℝ E) hΦ hK (fun y _ ↦ evalZeroProd_snd T y) hC (LinearEquiv.refl ℝ E)
    (fun y _ ↦ (fst_evalZeroProd T y).trans (LinearEquiv.refl_apply _).symm) h h'
    ((detLineLoopOperatorEquiv T S).symm
      (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)).detLineEndGenerator)
  have hid : ∀ z, TensorProduct.congr (LinearEquiv.refl ℝ E).detLineCongr
      (LinearEquiv.refl ℝ E).detLineCongr.symm.dualMap z = z := fun z ↦ by
    simp [LinearEquiv.detLineCongr_refl]
  have hx : LinearMap.detLineCongrKerCoker (kerLoopOperatorEquiv T S)
      (quotientRangeLoopOperatorEquiv T S) ((detLineLoopOperatorEquiv T S).symm
        (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)).detLineEndGenerator) =
      (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ S t) T) : E →ₗ[ℝ] E)).detLineEndGenerator := by
    rw [← detLineLoopOperatorEquiv_def, LinearEquiv.apply_symm_apply]
  -- `hx` is stated for `1 - Ψ(T)`, and `this` for `returnEnd T S`, whose underlying linear map is
  -- that endomorphism by construction (see `TauCeti.CircleSobolev.returnEnd`).
  exact ((hid _).symm.trans this.symm).trans (congrArg _ hx)

variable {X : Type*} [TopologicalSpace X] {M : X → C(AddCircle T, E →L[ℝ] E)}

omit hT [FiniteDimensional ℂ E] in
/-- The coefficients of a continuous family of loops are jointly continuous in the parameter and
the time. -/
private theorem continuous_uncurry_apply_coe (hM : Continuous M) :
    Continuous (Function.uncurry fun (x : X) (t : ℝ) ↦ M x t) :=
  continuous_eval.comp ((hM.comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' T).comp continuous_snd))

omit hT in
private theorem continuous_returnEnd (hM : Continuous M) :
    Continuous fun x ↦ returnEnd T (M x) := by
  simp only [returnEnd_eq]
  exact continuous_const.sub ((continuous_parametric_dysonSeriesLeft
    (continuous_uncurry_apply_coe T hM)).comp (continuous_id.prodMk continuous_const))

omit hT in
private theorem continuous_endpointStab (hM : Continuous M) :
    Continuous fun x ↦ endpointStab T (M x) r := by
  refine continuous_clm_apply.2 fun l ↦ ?_
  have hMt := continuous_uncurry_apply_coe T hM
  have hint : Continuous (Function.uncurry fun (x : X) (u : ℝ) ↦
      dysonSeries (-fun t : ℝ ↦ M x t) u ((r l : ℝ → E) u)) :=
    (continuous_parametric_dysonSeries (p := fun x t ↦ -M x t) hMt.neg).clm_apply
      ((mem_twistedContinuous.1 (r l).property).1.comp continuous_snd)
  simp only [endpointStab, LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply,
    twistedEndpoint_apply]
  exact ((continuous_parametric_dysonSeriesLeft hMt).comp
    (continuous_id.prodMk continuous_const)).clm_apply
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hint 0 T)

variable (M) in
/-- **The determinant lines of a family of loop operators and of its return maps are coherently
identified.** Let `M` be a family of continuous loops of real-linear maps of `E`, continuous on a
parameter set `s`, with loop operators `L_x ζ = ζ' - M x ζ`, `H¹(E) → H⁰(E)`, and return maps
`P_x = Ψ_x(T)` of `w' = M x w`. Transporting the normalized generator of the determinant line of
the endomorphism `1 - P_x` (`LinearMap.detLineEndGenerator`) to the determinant line of `L_x` along
`TauCeti.CircleSobolev.detLineLoopOperatorEquiv` gives a coherent family on `s`
(`TauCeti.IsDetLineCoherentOn`): a continuous orientation of the determinant line bundle of the
family `L_x` over `s`, although the kernels and cokernels of `L_x` jump. -/
theorem isDetLineCoherentOn_detLineLoopOperatorEquiv_symm (s : Set X) (hM : ContinuousOn M s) :
    IsDetLineCoherentOn (fun x ↦ loopOperator T (M x))
      (fun x ↦ (detLineLoopOperatorEquiv T (M x)).symm
        (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M x t) T) : E →ₗ[ℝ] E)).detLineEndGenerator) s := by
  refine isDetLineCoherentOn_iff.2 fun x₀ hx₀ ↦ ?_
  -- A right inverse of the endpoint map at `x₀` gives the stabilizers.
  obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective
    (twistedEndpoint (AddCircle.continuous_comp_coe (M x₀)) T 1)
    (LinearMap.range_eq_top.2 (twistedEndpoint_surjective _ hT.out one_ne_zero))
  -- The chart data are continuous on `s`: restrict the family to the subtype `s`.
  have hA : ContinuousOn (fun x ↦ returnEnd T (M x)) s :=
    continuousOn_iff_continuous_domRestrict.2
      (continuous_returnEnd T (M := s.domRestrict M) hM.domRestrict)
  have hK : ContinuousOn (fun x ↦ endpointStab T (M x) r) s :=
    continuousOn_iff_continuous_domRestrict.2
      (continuous_endpointStab T r (M := s.domRestrict M) hM.domRestrict)
  -- At `x₀` the stabilizer of `1 - Ψ(T)` is the identity, so its kernel chart is valid there.
  have h₀ : (((returnEnd T (M x₀)).coprod (endpointStab T (M x₀) r)).prod
      (ContinuousLinearMap.fst ℝ E E)).IsInvertible := by
    have hK₀ : endpointStab T (M x₀) r = ContinuousLinearMap.id ℝ E := by
      ext l
      simpa [endpointStab] using LinearMap.congr_fun hr l
    rw [hK₀]
    exact ContinuousLinearMap.isInvertible_coprod_id_prod_fst _
  obtain ⟨h₁, hc₀⟩ := exists_detLineChartEquiv_detLineLoopOperatorEquiv_symm T (M x₀) r h₀
  refine isDetLineCoherentWithinAt_of_eventually_sameRay
    ((continuous_loopOperator T).comp_continuousOn hM x₀ hx₀) (isFredholm_loopOperator T (M x₀))
    ((LinearEquiv.map_ne_zero_iff _).2 (LinearMap.detLineEndGenerator_ne_zero _)) h₁ ?_
  -- Near `x₀`, the chart of `1 - Ψ(T)` with moving stabilizer is a positive multiple of the frozen
  -- one, which reads the coherent normalized generators on the ray of their reading at `x₀`.
  have ev₁ := (isDetLineCoherentOn_iff.1
    (isDetLineCoherentOn_detLineEndGenerator (fun x ↦ returnEnd T (M x)) s) x₀
      hx₀).eventually_sameRay (hA x₀ hx₀) h₀
  have ev₂ := ContinuousLinearMap.eventually_detLineChartEquiv_eq_smul
    (q := fun _ ↦ ContinuousLinearMap.fst ℝ E E) (hA x₀ hx₀) (hK x₀ hx₀)
    continuousWithinAt_const h₀
  filter_upwards [ev₁, ev₂] with x hx₁ hx₂
  obtain ⟨h₃, hsr⟩ := hx₁
  obtain ⟨h₂, h₄, c, hc, hcu⟩ := hx₂
  obtain ⟨h, hx⟩ := exists_detLineChartEquiv_detLineLoopOperatorEquiv_symm T (M x) r h₂
  refine ⟨h, ?_⟩
  -- The equalities are transported under `SameRay` by `congrArg₂`; `rw` is very slow here.
  exact (congrArg₂ (SameRay ℝ) hx hc₀).mpr
    ((congrArg₂ (SameRay ℝ) (hcu _) rfl).mpr (hsr.pos_smul_left hc))

/-- **Orientation transport along loop operators follows the return maps.** Along a path `M` of
coefficient loops, continuous on `[a, b]`, transport of orientations of the determinant lines of
the loop operators `L_t ζ = ζ' - M t ζ` carries the orientation of the transported normalized
generator of `1 - Ψ_a(T)` to that of `1 - Ψ_b(T)`. -/
theorem detLineOrientationTransport_rayOfNeZero_detLineLoopOperatorEquiv_symm
    {M : ℝ → C(AddCircle T, E →L[ℝ] E)} {a b : ℝ} (hM : ContinuousOn M (Set.uIcc a b)) :
    detLineOrientationTransport a b ((continuous_loopOperator T).comp_continuousOn hM)
        (fun t _ ↦ isFredholm_loopOperator T (M t))
        (rayOfNeZero ℝ _ ((LinearEquiv.map_ne_zero_iff _).2 (LinearMap.detLineEndGenerator_ne_zero
          (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M a t) T) : E →ₗ[ℝ] E))) :
          (detLineLoopOperatorEquiv T (M a)).symm _ ≠ 0)) =
      rayOfNeZero ℝ _ ((LinearEquiv.map_ne_zero_iff _).2 (LinearMap.detLineEndGenerator_ne_zero
          (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : E →ₗ[ℝ] E))) :
          (detLineLoopOperatorEquiv T (M b)).symm _ ≠ 0) :=
  detLineOrientationTransport_rayOfNeZero _ _
    (isDetLineCoherentOn_detLineLoopOperatorEquiv_symm T M _ hM)

/-- **Transport preserves the orientations of invertibility when the determinants have the same
sign.** Along a continuous path `M` of coefficient loops from a bijective `L_{M a}` to a bijective
`L_{M b}` with `det (1 - Ψ_a(T)) * det (1 - Ψ_b(T)) > 0`, transport of orientations carries the
orientation of the determinant line of `L_{M a}` given by bijectivity
(`LinearMap.detLineEquivOfBijective`) to the one of `L_{M b}` given by bijectivity. -/
theorem detLineOrientationTransport_detLineEquivOfBijective_loopOperator_of_pos
    {M : ℝ → C(AddCircle T, E →L[ℝ] E)} {a b : ℝ}
    (hM : ContinuousOn M (Set.uIcc a b)) (ha : Function.Bijective (loopOperator T (M a)))
    (hb : Function.Bijective (loopOperator T (M b)))
    (h : 0 < LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M a t) T) : E →ₗ[ℝ] E)) *
      LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : E →ₗ[ℝ] E))) :
    detLineOrientationTransport a b ((continuous_loopOperator T).comp_continuousOn hM)
        (fun t _ ↦ isFredholm_loopOperator T (M t))
        (rayOfNeZero ℝ _ ((LinearMap.detLineEquivOfBijective ha).symm.map_ne_zero_iff.2
          one_ne_zero)) =
      rayOfNeZero ℝ _ ((LinearMap.detLineEquivOfBijective hb).symm.map_ne_zero_iff.2
        one_ne_zero) :=
  detLineOrientationTransport_rayOfNeZero_of_mul_pos _ _
    (isDetLineCoherentOn_detLineLoopOperatorEquiv_symm T M _ hM)
    (detLineLoopOperatorEquiv_symm_detLineEndGenerator_eq_det_smul T (M a) ha)
    (detLineLoopOperatorEquiv_symm_detLineEndGenerator_eq_det_smul T (M b) hb) _ _ h

/-- **Transport reverses the orientations of invertibility when the determinants have opposite
signs.** Along a continuous path `M` of coefficient loops from a bijective `L_{M a}` to a bijective
`L_{M b}` with `det (1 - Ψ_a(T)) * det (1 - Ψ_b(T)) < 0`, transport of orientations carries the
orientation of the determinant line of `L_{M a}` given by bijectivity
(`LinearMap.detLineEquivOfBijective`) to the opposite of the one of `L_{M b}` given by
bijectivity. -/
theorem detLineOrientationTransport_detLineEquivOfBijective_loopOperator_of_neg
    {M : ℝ → C(AddCircle T, E →L[ℝ] E)} {a b : ℝ}
    (hM : ContinuousOn M (Set.uIcc a b)) (ha : Function.Bijective (loopOperator T (M a)))
    (hb : Function.Bijective (loopOperator T (M b)))
    (h : LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M a t) T) : E →ₗ[ℝ] E)) *
      LinearMap.det (1 - (↑(dysonSeriesLeft (fun t : ℝ ↦ M b t) T) : E →ₗ[ℝ] E)) < 0) :
    detLineOrientationTransport a b ((continuous_loopOperator T).comp_continuousOn hM)
        (fun t _ ↦ isFredholm_loopOperator T (M t))
        (rayOfNeZero ℝ _ ((LinearMap.detLineEquivOfBijective ha).symm.map_ne_zero_iff.2
          one_ne_zero)) =
      -rayOfNeZero ℝ _ ((LinearMap.detLineEquivOfBijective hb).symm.map_ne_zero_iff.2
        one_ne_zero) :=
  detLineOrientationTransport_rayOfNeZero_of_mul_neg _ _
    (isDetLineCoherentOn_detLineLoopOperatorEquiv_symm T M _ hM)
    (detLineLoopOperatorEquiv_symm_detLineEndGenerator_eq_det_smul T (M a) ha)
    (detLineLoopOperatorEquiv_symm_detLineEndGenerator_eq_det_smul T (M b) hb) _ _ h

end CircleSobolev

end TauCeti
