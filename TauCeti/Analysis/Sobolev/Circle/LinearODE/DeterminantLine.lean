/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Periodic
public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Basic
public import TauCeti.LinearAlgebra.Determinant.Endomorphism
public import TauCeti.Topology.Instances.AddCircle.Coe
import TauCeti.Data.SignType.Basic
import TauCeti.LinearAlgebra.LinearMap.RegularRestriction

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

The operators `∂t - J₀ S(t)` on loops along a closed orbit, which govern the periodic twists of the
normal operator `∂s + J₀ ∂t + S(t)` of an orbit torus, are of this form, with `P` the linearized
return map. For them the orientation comparison above is expressed by the sign of `det (1 - P)`.

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

end CircleSobolev

end TauCeti
