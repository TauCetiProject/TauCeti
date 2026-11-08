/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

* `TauCeti.CircleSobolev.bijective_derivative_add_inclusion`: `ζ ↦ ζ' + ζ` is a bijection
  `H^(s + 1) → H^s`; `TauCeti.CircleSobolev.derivativeAddInclusionEquiv` is the resulting
  continuous linear equivalence.
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
open scoped Real

namespace TauCeti

namespace CircleSobolev

variable {s t : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (T : ℝ)

/-- The Fourier multiplier `1 + 2πin/T` of `ζ ↦ ζ' + ζ` does not vanish: its real part is `1`. -/
private theorem one_add_derivFactor_ne_zero (n : ℤ) : (1 + 2 * π * I * n / T : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [Complex.div_re] at this

/-- The Fourier multiplier `1 + 2πin/T` has modulus at least `1`. -/
private theorem one_le_norm_one_add_derivFactor (n : ℤ) : 1 ≤ ‖(1 + 2 * π * I * n / T : ℂ)‖ := by
  refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
  simp [Complex.div_re]

variable [hT : Fact (0 < T)]

/-- **`ζ ↦ ζ' + ζ` is a bijection `H^(s + 1) → H^s`.** It multiplies the `n`-th Fourier
coefficient by `1 + 2πin/T`, which never vanishes. -/
theorem bijective_derivative_add_inclusion (h : s + 1 = t) :
    Function.Bijective
      (derivative T h.le + inclusion (by linarith) :
        CircleSobolev t E →L[ℂ] CircleSobolev s E) := by
  subst h
  refine ⟨fun a b hab ↦ CircleSobolev.ext (funext fun n ↦ ?_), fun b ↦ ?_⟩
  · have hn := congrArg (fun c : CircleSobolev s E ↦ c.coeff n) hab
    simp only [add_apply, coeff_add, Pi.add_apply, coeff_derivative, coeff_inclusion] at hn
    refine smul_right_injective E (one_add_derivFactor_ne_zero T n) ?_
    simp only [add_smul, one_smul]
    rw [add_comm (a.coeff n), hn, add_comm]
  · -- Divide the coefficients of `b` by `1 + 2πin/T`, then recover one order of regularity.
    set c : ℤ → ℂ := fun n ↦ (1 + 2 * π * I * n / T : ℂ)⁻¹
    have hc (n : ℤ) : ‖c n‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (one_le_norm_one_add_derivFactor T n)
    let a : CircleSobolev s E := ⟨fun n ↦ c n • b.coeff n, memℓp_of_forall_le (C := 1) fun n ↦ by
      rw [norm_smul, one_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) (hc n))
        (weight_nonneg s n)⟩
    obtain ⟨d, hda, hdb⟩ := exists_inclusion_eq_and_derivative_eq T a (b - a) fun n ↦ by
      have hne := one_add_derivFactor_ne_zero T n
      simp only [coeff_sub, Pi.sub_apply, a, c, smul_smul]
      have key : (1 : ℂ) - (1 + 2 * π * I * n / T)⁻¹ =
          2 * π * I * n / T * (1 + 2 * π * I * n / T)⁻¹ := by
        field_simp
        ring
      rw [← key, sub_smul, one_smul]
    refine ⟨d, ?_⟩
    rw [add_apply, hdb, hda, sub_add_cancel]

variable [CompleteSpace E]

/-- `ζ ↦ ζ' + ζ`, as a continuous linear equivalence `H^(s + 1) ≃ H^s`. -/
def derivativeAddInclusionEquiv (h : s + 1 = t) : CircleSobolev t E ≃L[ℂ] CircleSobolev s E :=
  ContinuousLinearEquiv.ofBijective (derivative T h.le + inclusion (by linarith))
    (LinearMap.ker_eq_bot.2 (bijective_derivative_add_inclusion T h).injective)
    (LinearMap.range_eq_top.2 (bijective_derivative_add_inclusion T h).surjective)

@[simp]
theorem coe_derivativeAddInclusionEquiv (h : s + 1 = t) :
    (derivativeAddInclusionEquiv (E := E) T h : CircleSobolev t E →L[ℂ] CircleSobolev s E) =
      derivative T h.le + inclusion (by linarith) :=
  ContinuousLinearEquiv.coe_ofBijective _ _ _

variable [FiniteDimensional ℂ E]

/-- For `s > 1/2`, multiplication by a continuous loop `S` of real-linear maps, as a bounded
real-linear map `H^s(E) → H⁰(E)`: the continuous representative of `a` is multiplied pointwise by
`S`, and the resulting continuous loop is sent to `H⁰(E)` by its Fourier coefficients. -/
def mulLoop (hs : 1 / 2 < s) (S : C(AddCircle T, E →L[ℝ] E)) :
    CircleSobolev s E →L[ℝ] CircleSobolev 0 E :=
  LinearMap.mkContinuous
    { toFun a := ofContinuousMap T ⟨fun x ↦ S x (toContinuousMap T hs a x),
        S.continuous.clm_apply (map_continuous _)⟩
      map_add' a b := by
        rw [← map_add]
        congr 1
        ext x
        simp
      map_smul' r a := by
        rw [RingHom.id_apply, ← ContinuousLinearMap.map_smul_of_tower]
        congr 1
        ext x
        simp }
    (‖(ofContinuousMap T : C(AddCircle T, E) →L[ℂ] CircleSobolev 0 E)‖ * ‖S‖ *
      ‖(toContinuousMap T hs : CircleSobolev s E →L[ℂ] C(AddCircle T, E))‖) fun a ↦ by
    refine ((ofContinuousMap (E := E) T).le_opNorm _).trans ?_
    rw [mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun x ↦ ?_
    refine ((S x).le_opNorm _).trans ?_
    exact mul_le_mul (S.norm_coe_le_norm x)
      (((toContinuousMap T hs a).norm_coe_le_norm x).trans ((toContinuousMap T hs).le_opNorm a))
      (norm_nonneg _) (norm_nonneg S)

theorem mulLoop_apply (hs : 1 / 2 < s) (S : C(AddCircle T, E →L[ℝ] E)) (a : CircleSobolev s E) :
    mulLoop T hs S a = ofContinuousMap T ⟨fun x ↦ S x (toContinuousMap T hs a x),
      S.continuous.clm_apply (map_continuous _)⟩ :=
  (rfl)

/-- Multiplication by `S` only depends on the continuous representative, so it commutes with the
inclusions between the spaces `H^s`, `s > 1/2`. -/
@[simp]
theorem mulLoop_inclusion (ht : 1 / 2 < t) (h : t ≤ s) (S : C(AddCircle T, E →L[ℝ] E))
    (a : CircleSobolev s E) :
    mulLoop T ht S (inclusion h a) = mulLoop T (ht.trans_le h) S a := by
  simp only [mulLoop_apply, toContinuousMap_inclusion]

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
  refine ⟨fun h x ↦ hasDerivAt_toContinuousMap_of_derivative_eq T a _ h x, fun h ↦ ?_⟩
  obtain ⟨b, hb, hdb⟩ := exists_toContinuousMap_eq_and_derivative_eq T
    (toContinuousMap T (by norm_num) a)
    ⟨fun x ↦ S x (toContinuousMap T (by norm_num) a x), S.continuous.clm_apply (map_continuous _)⟩ h
  rwa [toContinuousMap_injective T _ hb] at hdb

/-- **`L_S` is invertible exactly when `ζ' = S ζ` has no nonzero periodic solution.** Since `L_S`
is Fredholm of index zero, it is invertible as soon as it is injective, and its kernel consists of
the periodic solutions of `ζ' = S ζ`. -/
theorem isInvertible_loopOperator_iff (S : C(AddCircle T, E →L[ℝ] E)) :
    (loopOperator T S).IsInvertible ↔
      ∀ ζ : C(AddCircle T, E), (∀ x : ℝ, HasDerivAt (fun y : ℝ ↦ ζ y) (S x (ζ x)) x) → ζ = 0 := by
  refine ⟨fun h ζ hζ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨a, ha, -⟩ := exists_toContinuousMap_eq_and_derivative_eq T ζ
      ⟨fun x ↦ S x (ζ x), S.continuous.clm_apply ζ.continuous⟩ hζ
    have ha0 : loopOperator T S a = 0 :=
      (loopOperator_eq_zero_iff T S a).2 fun x ↦ by rw [ha]; exact hζ x
    rw [← ha, h.injective (ha0.trans (map_zero _).symm), map_zero]
  · have hinj : Function.Injective (loopOperator T S) :=
      (injective_iff_map_eq_zero _).2 fun a ha ↦ toContinuousMap_injective T (by norm_num)
        ((h _ ((loopOperator_eq_zero_iff T S a).1 ha)).trans (map_zero _).symm)
    have hfred := isFredholm_loopOperator T S
    have := hfred.finite_coker
    have hidx := (loopOperator T S).index_of_injective hinj
    rw [index_loopOperator] at hidx
    have h0 : Module.finrank ℝ (CircleSobolev 0 E ⧸ (loopOperator T S).range) = 0 := by omega
    have hrange : (loopOperator T S).range = ⊤ :=
      Submodule.Quotient.subsingleton_iff.mp (Module.finrank_zero_iff.mp h0)
    exact ContinuousLinearMap.isInvertible_iff_isFredholm_and_bijective.2
      ⟨hfred, hinj, LinearMap.range_eq_top.1 hrange⟩

end CircleSobolev

end TauCeti
