/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContinuousMap.Basic
public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Analysis.Sobolev.Circle.OfContinuousMap
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

/-!
# Periodic linear differential operators on the circle Sobolev spaces

Let `E` be a finite-dimensional complex normed space and `S : AddCircle T → (E →L[ℝ] E)` a
continuous loop of *real*-linear maps. The first-order operator

`L_S ζ = ζ' - S ζ`

acts on `E`-valued loops of period `T`. This file realizes it as a bounded real-linear operator
`H¹(E) → H⁰(E)` between the Fourier-coefficient Sobolev spaces of
`TauCeti/Analysis/Sobolev/Circle/Basic.lean` (`TauCeti.CircleSobolev.loopOperator`) and proves
that it is a Fredholm operator of index zero whose kernel consists of the classical periodic
solutions of `ζ' = S ζ`. Consequently it is invertible exactly when the equation `ζ' = S ζ` has
no nonzero periodic solution.

Real-linear coefficients are what the linearized Hamiltonian equation along a periodic orbit
produces: in a complex vector space `E` with its standard complex structure, the linearized
Hamiltonian vector field `S_t` is real-linear, not complex-linear. The zero-order term is therefore
not a Fourier multiplier. It is defined through continuous representatives: an element of `H¹` is
a continuous loop, it is multiplied pointwise by `S`, and the result returns to `H⁰` by its
Fourier coefficients (`TauCeti.CircleSobolev.ofContinuousMap`). This only uses that `S` is
continuous.

The Fredholm property is a compact perturbation argument. The operator `ζ ↦ ζ' + ζ` is a
bijection `H^(s + 1) → H^s` for every order `s`, since it multiplies the `n`-th Fourier
coefficient by `1 + 2πin/T`, which is nonzero and has modulus comparable to `1 + |n|`
(`TauCeti.CircleSobolev.bijective_derivative_add_inclusion`). The difference between `L_S` and
this isomorphism is `ζ ↦ -(ζ + S ζ)`, which factors through the compact inclusion
`H¹ → H^(3/4)` (Rellich's theorem, `TauCeti.CircleSobolev.isCompactOperator_inclusion`) followed
by the bounded map `H^(3/4) → C → H⁰`. Hence `L_S` is Fredholm of index zero, so it is invertible
as soon as it is injective. Its kernel is identified with the periodic solutions of `ζ' = S ζ` by
comparing weak and classical derivatives
(`TauCeti.CircleSobolev.hasDerivAt_toContinuousMap_of_derivative_eq`).

## Main definitions

* `TauCeti.CircleSobolev.mulLoop T hs S`: for `s > 1/2`, the bounded real-linear map
  `H^s(E) → H⁰(E)` multiplying the continuous representative pointwise by `S`.
* `TauCeti.CircleSobolev.loopOperator T S`: the operator `ζ ↦ ζ' - S ζ`, `H¹(E) → H⁰(E)`.

## Main statements

* `TauCeti.CircleSobolev.mulLoop_sub`, `TauCeti.CircleSobolev.mulLoop_smul`,
  `TauCeti.CircleSobolev.loopOperator_sub`: the zero-order term and `L_S` depend linearly on the
  coefficient loop `S`.
* `TauCeti.CircleSobolev.mulLoop_const_smul_id`: multiplication by a constant complex scalar loop
  is multiplication by that scalar.
* `TauCeti.CircleSobolev.isCompactOperator_mulLoop`: the zero-order term is compact.
* `TauCeti.CircleSobolev.isFredholm_loopOperator`, `TauCeti.CircleSobolev.index_loopOperator`:
  `L_S` is a Fredholm operator of index zero.
* `TauCeti.CircleSobolev.loopOperator_eq_zero_iff`: the kernel of `L_S` consists of the elements
  whose continuous representative solves `ζ' = S ζ` classically.
* `TauCeti.CircleSobolev.isInvertible_loopOperator_iff`: `L_S` is invertible exactly when
  `ζ' = S ζ` has no nonzero continuous periodic solution.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (the operator `J₀ ∂_t + S` on `W^{1,2}(S¹)` and its invertibility
  at nondegenerate orbits).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.1
  (compact perturbations of Fredholm operators).
-/

public section

noncomputable section

open Complex
open ContinuousMap (applyContinuousLinearMap applyContinuousLinearMap_apply)
open scoped Real

namespace TauCeti

namespace CircleSobolev

variable {s t : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (T : ℝ) [hT : Fact (0 < T)] [FiniteDimensional ℂ E]

/-- A finite-dimensional complex space is complete, as needed for continuous representatives. -/
local instance instCompleteSpaceLinearODE : CompleteSpace E := FiniteDimensional.completeSpace ℂ E

/-- For `s > 1/2`, multiplication by a continuous loop `S` of real-linear maps, as a bounded
real-linear map `H^s(E) → H⁰(E)`: the continuous representative of `a` is multiplied pointwise by
`S`, and the resulting continuous loop is sent to `H⁰(E)` by its Fourier coefficients. -/
def mulLoop (hs : 1 / 2 < s) (S : C(AddCircle T, E →L[ℝ] E)) :
    CircleSobolev s E →L[ℝ] CircleSobolev 0 E :=
  (ofContinuousMap T).restrictScalars ℝ ∘L applyContinuousLinearMap S ∘L
    (toContinuousMap T hs).restrictScalars ℝ

theorem mulLoop_apply (hs : 1 / 2 < s) (S : C(AddCircle T, E →L[ℝ] E)) (a : CircleSobolev s E) :
    mulLoop T hs S a =
      ofContinuousMap T (applyContinuousLinearMap S (toContinuousMap T hs a)) :=
  (rfl)

/-- The zero-order multiplication operator depends continuously in operator norm on its
coefficient loop, with the uniform norm on coefficients. -/
@[fun_prop]
theorem continuous_mulLoop (hs : 1 / 2 < s) :
    Continuous (mulLoop (E := E) T hs) := by
  exact continuous_const.clm_comp
    (ContinuousMap.applyContinuousLinearMap.continuous.clm_comp continuous_const)

/-- Multiplication by `S` only depends on the continuous representative, so it commutes with the
inclusions between the spaces `H^s`, `s > 1/2`. -/
@[simp]
theorem mulLoop_inclusion (ht : 1 / 2 < t) (h : t ≤ s) (S : C(AddCircle T, E →L[ℝ] E))
    (a : CircleSobolev s E) :
    mulLoop T ht S (inclusion h a) = mulLoop T (ht.trans_le h) S a := by
  simp only [mulLoop_apply, toContinuousMap_inclusion]

/-- Multiplication by a loop is additive in the loop. -/
theorem mulLoop_sub (hs : 1 / 2 < s) (S₁ S₂ : C(AddCircle T, E →L[ℝ] E)) :
    mulLoop T hs (S₁ - S₂) = mulLoop T hs S₁ - mulLoop T hs S₂ := by
  ext a : 1
  simp only [mulLoop_apply, map_sub, sub_apply]

/-- Multiplication by a loop is real-homogeneous in the loop. -/
theorem mulLoop_smul (hs : 1 / 2 < s) (c : ℝ) (S : C(AddCircle T, E →L[ℝ] E)) :
    mulLoop T hs (c • S) = c • mulLoop T hs S := by
  ext a : 1
  simp only [mulLoop_apply, map_smul, smul_apply]
  exact (ofContinuousMap T).map_smul_of_tower c _

/-- Multiplication by the constant loop `z • id`, for a complex scalar `z`, is multiplication by
`z` after the inclusion `H^s ⊆ H⁰`. -/
theorem mulLoop_const_smul_id (hs : 1 / 2 < s) (z : ℂ) (a : CircleSobolev s E) :
    mulLoop T hs (ContinuousMap.const _ (z • ContinuousLinearMap.id ℝ E)) a =
      z • inclusion (by linarith) a := by
  rw [← ofContinuousMap_toContinuousMap T hs, ← map_smul, mulLoop_apply]
  congr 1
  ext x
  simp

/-- **The zero-order term is compact.** For `s > 1/2`, multiplication by a continuous loop `S` is
a compact operator `H^s(E) → H⁰(E)`: it factors through the compact inclusion into `H^t` for any
`1/2 < t < s`. -/
theorem isCompactOperator_mulLoop (hs : 1 / 2 < s) (S : C(AddCircle T, E →L[ℝ] E)) :
    IsCompactOperator (mulLoop T hs S) := by
  obtain ⟨t, ht, hts⟩ := exists_between hs
  have hfac : ⇑(mulLoop T hs S) = mulLoop T ht S ∘ inclusion (E := E) hts.le := by
    funext a
    exact (mulLoop_inclusion T ht hts.le S a).symm
  rw [hfac]
  exact (isCompactOperator_inclusion hts).clm_comp (mulLoop T ht S)

/-- The periodic first-order operator `ζ ↦ ζ' - S ζ`, as a bounded real-linear map
`H¹(E) → H⁰(E)`, for a continuous loop `S` of real-linear maps of `E`. -/
def loopOperator (S : C(AddCircle T, E →L[ℝ] E)) : CircleSobolev 1 E →L[ℝ] CircleSobolev 0 E :=
  (derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num)).restrictScalars ℝ -
    mulLoop T (by norm_num) S

theorem loopOperator_apply (S : C(AddCircle T, E →L[ℝ] E)) (a : CircleSobolev 1 E) :
    loopOperator T S a =
      derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) a - mulLoop T (by norm_num) S a :=
  (rfl)

/-- Subtracting `S₂` from the coefficient loop adds multiplication by `S₂` to `L_S`. -/
theorem loopOperator_sub (S₁ S₂ : C(AddCircle T, E →L[ℝ] E)) :
    loopOperator T (S₁ - S₂) = loopOperator T S₁ + mulLoop T (by norm_num) S₂ := by
  rw [loopOperator, loopOperator, mulLoop_sub]
  abel

/-- The periodic first-order operator depends continuously in operator norm on its
coefficient loop, with the uniform norm on coefficients. -/
@[fun_prop]
theorem continuous_loopOperator : Continuous (loopOperator (E := E) T) :=
  continuous_const.sub (continuous_mulLoop T (by norm_num))

/-- `L_S` differs from the isomorphism `ζ ↦ ζ' + ζ` by a compact operator. -/
private theorem loopOperator_eq_add (S : C(AddCircle T, E →L[ℝ] E)) :
    loopOperator T S =
      (derivativeAddInclusionEquiv (E := E) T (show (0 : ℝ) + 1 = 1 by norm_num) :
        CircleSobolev 1 E →L[ℂ] CircleSobolev 0 E).restrictScalars ℝ +
      -((inclusion (show (0 : ℝ) ≤ 1 by norm_num)).restrictScalars ℝ +
        mulLoop T (by norm_num) S) := by
  ext a : 1
  simp only [loopOperator_apply, add_apply, neg_apply, coe_derivativeAddInclusionEquiv,
    ContinuousLinearMap.coe_restrictScalars']
  abel

private theorem isCompactOperator_inclusion_add_mulLoop (S : C(AddCircle T, E →L[ℝ] E)) :
    IsCompactOperator
      (-((inclusion (show (0 : ℝ) ≤ 1 by norm_num)).restrictScalars ℝ + mulLoop T (by norm_num) S :
        CircleSobolev 1 E →L[ℝ] CircleSobolev 0 E)) := by
  rw [FunLike.coe_neg, FunLike.coe_add, ContinuousLinearMap.coe_restrictScalars']
  exact ((isCompactOperator_inclusion (by norm_num)).add (isCompactOperator_mulLoop T _ S)).neg

/-- **`L_S` is a Fredholm operator.** -/
theorem isFredholm_loopOperator (S : C(AddCircle T, E →L[ℝ] E)) :
    (loopOperator T S).IsFredholm := by
  rw [loopOperator_eq_add]
  exact ((derivativeAddInclusionEquiv (E := E) T _).isFredholm.restrictScalars ℝ)
    |>.add_of_isCompactOperator (isCompactOperator_inclusion_add_mulLoop T S)

/-- **`L_S` has index zero.** -/
@[simp]
theorem index_loopOperator (S : C(AddCircle T, E →L[ℝ] E)) : (loopOperator T S).index = 0 := by
  rw [loopOperator_eq_add, ContinuousLinearMap.index_add_of_isCompactOperator
    ((derivativeAddInclusionEquiv (E := E) T _).isFredholm.restrictScalars ℝ)
    (isCompactOperator_inclusion_add_mulLoop T S), ContinuousLinearMap.index_restrictScalars_real,
    ContinuousLinearEquiv.index_eq_zero, mul_zero]

/-- **The kernel of `L_S`.** An element `a ∈ H¹(E)` lies in the kernel of `ζ ↦ ζ' - S ζ` exactly
when its continuous representative `ζ` solves `ζ' = S ζ` classically. -/
theorem loopOperator_eq_zero_iff (S : C(AddCircle T, E →L[ℝ] E)) (a : CircleSobolev 1 E) :
    loopOperator T S a = 0 ↔ ∀ x : ℝ,
      HasDerivAt (fun y : ℝ ↦ toContinuousMap T (by norm_num) a y)
        (S x (toContinuousMap T (by norm_num) a x)) x := by
  rw [loopOperator_apply, sub_eq_zero, mulLoop_apply]
  refine ⟨fun h x ↦ by
    simpa only [applyContinuousLinearMap_apply] using
      hasDerivAt_toContinuousMap_of_derivative_eq T a _ h x, fun h ↦ ?_⟩
  obtain ⟨b, hb, hdb⟩ := exists_toContinuousMap_eq_and_derivative_eq T
    (toContinuousMap T (by norm_num) a)
    (applyContinuousLinearMap S (toContinuousMap T (by norm_num) a))
    fun x ↦ by simpa only [applyContinuousLinearMap_apply] using h x
  rwa [toContinuousMap_injective T _ hb] at hdb

/-- **`L_S` is invertible exactly when `ζ' = S ζ` has no nonzero periodic solution.** Since `L_S`
is Fredholm of index zero, it is invertible as soon as it is injective, and its kernel consists of
the periodic solutions of `ζ' = S ζ`. -/
theorem isInvertible_loopOperator_iff (S : C(AddCircle T, E →L[ℝ] E)) :
    (loopOperator T S).IsInvertible ↔
      ∀ ζ : C(AddCircle T, E), (∀ x : ℝ, HasDerivAt (fun y : ℝ ↦ ζ y) (S x (ζ x)) x) → ζ = 0 := by
  refine ⟨fun h ζ hζ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨a, ha, -⟩ :=
      exists_toContinuousMap_eq_and_derivative_eq T ζ (applyContinuousLinearMap S ζ)
        fun x ↦ by simpa only [applyContinuousLinearMap_apply] using hζ x
    have ha0 : loopOperator T S a = 0 :=
      (loopOperator_eq_zero_iff T S a).2 fun x ↦ by rw [ha]; exact hζ x
    rw [← ha, h.injective (ha0.trans (map_zero _).symm), map_zero]
  · have hinj : Function.Injective (loopOperator T S) :=
      (injective_iff_map_eq_zero _).2 fun a ha ↦ toContinuousMap_injective T (by norm_num)
        ((h _ ((loopOperator_eq_zero_iff T S a).1 ha)).trans (map_zero _).symm)
    exact (isFredholm_loopOperator T S).isInvertible_of_injective_of_index_eq_zero hinj
      (index_loopOperator T S)

end CircleSobolev

end TauCeti
