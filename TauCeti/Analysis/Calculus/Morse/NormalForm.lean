/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import TauCeti.Analysis.Calculus.Hadamard
public import TauCeti.Analysis.Calculus.Morse.Basic
public import TauCeti.Analysis.Normed.Algebra.SquareRoot

/-!
# The Morse lemma

Near a nondegenerate critical point a `C^{n+2}` function, with `1 ≤ n ≤ ∞`, is, in suitable
`C^n` coordinates, exactly its Hessian quadratic form. This file proves that for a real-valued
function on a Banach space, in the form
`TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart`: there is a chart `ψ` at the critical
point `x`, carrying `x` to `0`, with both coordinate maps `C^n` on their domains, and with

`f y = f x + 2⁻¹ * fderiv ℝ (fderiv ℝ f) x (ψ y) (ψ y)`

on the whole of its source.  Nondegeneracy is the one from
`TauCeti.Analysis.Calculus.Morse.Basic`: the second derivative, read as a map from the space to
its dual, is a linear homeomorphism.  In finite dimensions that is the classical condition that
the Hessian be a nondegenerate bilinear form, so this is the classical Morse lemma; in infinite
dimensions it is the strong nondegeneracy of Morse theory on Banach and Hilbert manifolds, and
the statement is the Morse--Palais lemma of Palais (1969).

The proof is Palais's.  Write `f (x + v) - f x - fderiv ℝ f x v = 2⁻¹ * B v v v`, where `B v` is
the **averaged Hessian** `TauCeti.hessianAverage f x v`, the average of the second derivative
along the segment from `x` to `x + v`, weighted so that `B 0` is the Hessian itself.  Then `B` is
a `C^n` family of symmetric continuous bilinear forms with `B 0` invertible, so
`TauCeti.exists_congruence_of_symmetric_family` produces a `C^n` family of operators `R v`,
equal to the identity at `v = 0`, with `B v w w' = B 0 (R v w) (R v w')`.  Taking `w = w' = v`
turns the second-order term into the Hessian evaluated at `φ v = R v v`, and `φ` has derivative
the identity at `0`, so it is a chart by the inverse function theorem.

The weight `2 * (1 - t)` is what makes `B 0` the Hessian on the nose.  Iterating the smooth
Hadamard factorisation of `TauCeti.Analysis.Calculus.Hadamard` twice would also produce a smooth
family with `f (x + v) - f x = B v v v` at a critical point, but its value at `0` is then the
derivative of a parametrised integral rather than the Hessian, and it is not symmetric; both are
needed here.  The averaged Hessian and its Taylor formula are stated for a map into an arbitrary
Banach space, nothing in them being special to real-valued functions; only the congruence and the
Morse lemma itself need `f` real-valued.

The family `R` is manufactured from a square root, the **Palais congruence**
`TauCeti.palaisCongruence`: the operator `C v = (B 0)⁻¹ ∘ B v` is close to the identity for `v`
close to `0`, so it has a unique square root there (`TauCeti.sqrtNearOne`), and that square root
is automatically self-adjoint for the pairing `B 0`, because the adjoint of a square root is a
square root of the adjoint and the two are close to the identity.  Self-adjointness is exactly
what turns `R v * R v = C v` into the congruence identity.

The Palais congruence `TauCeti.palaisCongruence B₀ B = sqrtNearOne (B₀⁻¹ ∘ B)` is a function of
the pair of forms, defined without any choice. It is smooth near every pair `(B₀, B₀)` with `B₀`
invertible, so the reference form may vary as well, and it is natural: pulling both forms back
by an invertible map `L` conjugates it by `L`. Naturality is what lets constructions built from it
in local coordinates agree under changes of linear coordinates, such as the transition maps of a
vector bundle.

The Morse lemma supplies the local model of a Morse function: the index of the critical point,
the local handle structure, and the local form of the gradient flow are all read off it.  The
averaged Hessian of a `C^{n+2}` function is `C^n`, and the congruence construction preserves the
regularity of the family. The Morse lemma therefore gives a `C^n` chart for a `C^{n+2}`
function when `1 ≤ n ≤ ∞`; taking `n = ∞` recovers the smooth Morse lemma.

The varying-reference variant `TauCeti.exists_parametric_congruence_of_symmetric_family`
compares a jointly smooth family `B (b, v)` to `B (b, 0)` by jointly smooth invertible
operators `R (b, v)`, with `R (b, 0) = 1` throughout a base neighbourhood and jointly smooth
inverses. This is the linear normalization needed for a parameter-dependent Morse change of
coordinates fixing the zero section, with its Hessian as the reference quadratic form.
The construction uses `TauCeti.exists_congruence_of_symmetric_family` to compare all forms
to `B (a, 0)`, then divides by the resulting operator on the zero section. Inversion is smooth
on a product neighbourhood of invertible operators. This preserves the differentiability
order, including order zero.

## Main declarations

* `TauCeti.hessianAverage`: the averaged Hessian along a segment, normalised so that
  `TauCeti.hessianAverage_zero` identifies its value at `0` with the Hessian.
* `TauCeti.map_add_eq_add_hessianAverage`: the second-order Taylor formula it satisfies.
* `TauCeti.palaisCongruence`: the Palais congruence `sqrtNearOne (B₀⁻¹ ∘ B)` of two forms.
* `TauCeti.eventually_contDiffAt_palaisCongruence`: it is smooth in both forms near `(B₀, B₀)`.
* `TauCeti.eventually_palaisCongruence_apply_apply`: for symmetric forms near `(B₀, B₀)` it is a
  congruence, `B₁ (R w) (R w') = B w w'`.
* `TauCeti.eventually_palaisCongruence_bilinearComp`: it is natural under pulling both forms back
  by an invertible map.
* `TauCeti.hessianAverage_comp_clm`: the averaged Hessian of a composite with a continuous linear
  map.
* `TauCeti.exists_congruence_of_symmetric_family`: a `C^n` family of symmetric continuous
  bilinear forms whose value at a basepoint is invertible is, near that point, the congruence of
  that value by a `C^n` family of operators equal to the identity at the basepoint.
* `TauCeti.exists_parametric_congruence_of_symmetric_family`: congruence to the varying
  reference `B (b, 0)`, with identity operators on the zero section and jointly `C^n` inverses.
* `TauCeti.IsNondegenerateCriticalPoint.exists_normal_form`: **the Morse lemma**, in the form of a
  `C^n` map `φ` fixing `0` with derivative the identity there.
* `TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart`: the Morse lemma as a chart at the
  critical point.

## References

* R. S. Palais, *The Morse lemma for Banach spaces*, Bull. Amer. Math. Soc. **75** (1969),
  968--971, for the statement proved here: the theorem below asks only that `E` be a Banach
  space, which is that note's setting rather than the Hilbert one.
* R. S. Palais, *Morse theory on Hilbert manifolds*, Topology **2** (1963), 299--340, Section 2,
  for the proof by an operator square root used here.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, 1963, Lemma 2.2, for the classical
  finite-dimensional statement.
* M. Audin, M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014, Chapter 1.
-/

public section

noncomputable section

open Filter MeasureTheory Topology

open scoped ContDiff

namespace TauCeti

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {x : E}

section HessianAverage

variable [CompleteSpace F] {f : E → F}

/-- The **averaged Hessian** of `f` at `x` in the direction `v`: the average of the second
derivative of `f` along the segment from `x` to `x + v`, against the weight `2 * (1 - t)`.  The
weight is normalised so that the value at `v = 0` is the Hessian at `x` itself
(`TauCeti.hessianAverage_zero`), while `TauCeti.map_add_eq_add_hessianAverage` says that
`f (x + v)` differs from its first-order Taylor polynomial by `2⁻¹ • hessianAverage f x v v v`. -/
def hessianAverage (f : E → F) (x v : E) : E →L[ℝ] E →L[ℝ] F :=
  segmentAverage (fun t ↦ 2 * (1 - t)) (fderiv ℝ (fderiv ℝ f)) x v

omit [CompleteSpace F] in
/-- The averaged Hessian as an integral over the compact unit interval, the shape in which the
regularity theorem for parametrised integrals applies to it. -/
theorem hessianAverage_eq_integral_Icc (f : E → F) (x : E) :
    hessianAverage f x = fun v ↦ ∫ t in Set.Icc (0 : ℝ) 1,
      (2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (x + t • v) := by
  exact segmentAverage_eq_integral_Icc _ _ _

/-- At the basepoint the averaged Hessian is the Hessian: the weight `2 * (1 - t)` has integral
`1` over the unit interval. -/
@[simp]
theorem hessianAverage_zero (f : E → F) (x : E) :
    hessianAverage f x 0 = fderiv ℝ (fderiv ℝ f) x := by
  rw [hessianAverage, segmentAverage_zero]
  have hI : (∫ t in (0 : ℝ)..1, 2 * (1 - t)) = 1 := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    norm_num [integral_id]
  rw [hI, one_smul]

omit [CompleteSpace F] in
/-- The averaged fiber Hessian of a jointly `C^{n+2}` family is jointly `C^n` in the parameter
and the fiber displacement. -/
theorem contDiff_hessianAverage_param
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {n : ℕ∞} {g : P × E → F} (hg : ContDiff ℝ (n + 2) g) (x : E) :
    ContDiff ℝ n (fun p : P × E ↦ hessianAverage (fun y ↦ g (p.1, y)) x p.2) := by
  have hD : ContDiff ℝ (n + 1)
      (fun p : P × E ↦ fderiv ℝ (fun y ↦ g (p.1, y)) p.2) := by
    apply ContDiff.fderiv (f := fun p : P × E ↦ fun y : E ↦ g (p.1, y))
    · exact hg.comp (by fun_prop)
    · fun_prop
    · norm_num [add_assoc]
  have hDD : ContDiff ℝ n
      (fun p : P × E ↦ fderiv ℝ (fderiv ℝ (fun y ↦ g (p.1, y))) p.2) := by
    apply ContDiff.fderiv
      (f := fun p : P × E ↦ fderiv ℝ (fun y ↦ g (p.1, y)))
    · exact hD.comp (by fun_prop :
        ContDiff ℝ (n + 1) (fun p : (P × E) × E ↦ (p.1.1, p.2)))
    · fun_prop
    · exact le_rfl
  exact hDD.contDiff_segmentAverage_param
    ((by fun_prop : Continuous fun t : ℝ ↦ 2 * (1 - t)).intervalIntegrable 0 1) x

omit [CompleteSpace F] in
/-- The averaged Hessian of a `C^{n+2}` function is `C^n` in the direction. -/
theorem contDiff_hessianAverage {n : ℕ∞} (hf : ContDiff ℝ (n + 2) f) (x : E) :
    ContDiff ℝ n (hessianAverage f x) := by
  exact (contDiff_hessianAverage_param (hf.comp contDiff_snd) x).comp
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ n (fun v : E ↦ ((0 : E), v)))

omit [CompleteSpace F] in
private theorem continuous_hessianAverage_integrand (hf : ContDiff ℝ 2 f) (x v : E) :
    Continuous fun t : ℝ ↦ (2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (x + t • v) := by
  -- The scalar action on iterated continuous linear maps is definitionally equal to the
  -- normed-space action, but instance search does not identify the two instances.
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] F) :=
    @NormedSpace.toIsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] F) _ _ _
  have hd : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
  exact (by fun_prop : Continuous fun t : ℝ ↦ 2 * (1 - t)).smul (hd.comp (by fun_prop))

/-- Evaluating the averaged Hessian on a pair of vectors commutes with the integral. -/
theorem hessianAverage_apply (hf : ContDiff ℝ 2 f) (x v w w' : E) :
    hessianAverage f x v w w'
      = ∫ t in (0 : ℝ)..1, (2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (x + t • v) w w' := by
  have h1 := continuous_hessianAverage_integrand hf x v
  have h2 : Continuous fun t : ℝ ↦ ((2 * (1 - t)) • fderiv ℝ (fderiv ℝ f) (x + t • v)) w :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] F) w).continuous.comp h1
  have hApply := ContinuousLinearMap.segmentAverage_apply
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] F) w) (fun t ↦ 2 * (1 - t))
      (fderiv ℝ (fderiv ℝ f)) x v (h1.intervalIntegrable 0 1)
  simp only [ContinuousLinearMap.apply_apply] at hApply
  rw [hessianAverage, hApply,
    ContinuousLinearMap.intervalIntegral_apply (h2.intervalIntegrable 0 1) w']
  simp

/-- The averaged Hessian is a symmetric bilinear form, since each second derivative along the
segment is. -/
theorem hessianAverage_symm (hf : ContDiff ℝ 2 f) (x v w w' : E) :
    hessianAverage f x v w w' = hessianAverage f x v w' w := by
  rw [hessianAverage_apply hf, hessianAverage_apply hf]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [(hf.contDiffAt.isSymmSndFDerivAt (by norm_num) :
    IsSymmSndFDerivAt ℝ f (x + t • v)) w w']

/-- **Taylor's formula to second order**, with the remainder written as the averaged Hessian
evaluated twice on the increment. -/
theorem map_add_eq_add_hessianAverage (hf : ContDiff ℝ 2 f) (x v : E) :
    f (x + v) = f x + fderiv ℝ f x v + (2 : ℝ)⁻¹ • hessianAverage f x v v v := by
  have h := map_add_eq_sum_add_integral_iteratedFDeriv (n := 1) (x := x) (y := v)
    (fun _ _ ↦ hf.contDiffAt)
  norm_num [Finset.sum_range_succ] at h
  -- `iteratedFDeriv_two_apply` is stated with the numeral `2`, while Taylor's theorem leaves the
  -- order as `1 + 1`; expose that definitional equality before rewriting.
  rw [show (1 : ℕ) + 1 = 2 from rfl] at h
  simp only [iteratedFDeriv_two_apply] at h
  rw [h, hessianAverage_apply hf, ← intervalIntegral.integral_smul]
  refine congrArg (fun z ↦ f x + fderiv ℝ f x v + z) ?_
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [smul_smul]
  congr 1
  ring

/-- The averaged Hessian of a composite with a continuous linear map `L` is the averaged Hessian
of the outer function along the image segment, with both arguments moved by `L`. -/
theorem hessianAverage_comp_clm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : G → F} (hg : ContDiff ℝ 2 g) (L : E →L[ℝ] G) (x v : E) :
    hessianAverage (g ∘ L) x v = (hessianAverage g (L x) (L v)).bilinearComp L L := by
  ext w w'
  rw [hessianAverage_apply (hg.comp L.contDiff), ContinuousLinearMap.bilinearComp_apply,
    hessianAverage_apply hg]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  have h := congrArg (fun m ↦ m ![w, w'])
    (L.iteratedFDeriv_comp_right hg (x + t • v) (i := 2) (by norm_num))
  simp only [iteratedFDeriv_two_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [h, map_add, map_smul]

end HessianAverage

section Congruence

open Set

variable [CompleteSpace E]

/-! ### The Palais congruence -/

/-- The **Palais congruence** of a bilinear form `B` with respect to a reference form `B₀`: the
square root near the identity (`TauCeti.sqrtNearOne`) of the operator `B₀⁻¹ ∘ B`, where `B₀` is
read as a map from `E` to its dual. For symmetric forms, with `B₀` invertible and `B` close to
`B₀`, it is a congruence: `B₀ (R w) (R w') = B w w'`
(`TauCeti.eventually_palaisCongruence_apply_apply`). It is defined without any choice, so it is
natural under linear changes of coordinates (`TauCeti.eventually_palaisCongruence_bilinearComp`).
-/
def palaisCongruence (B₀ B : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E :=
  sqrtNearOne (E →L[ℝ] E) (B₀.inverse ∘L B)

/-- The Palais congruence of an invertible form with respect to itself is the identity. -/
@[simp]
theorem palaisCongruence_self {B₀ : E →L[ℝ] E →L[ℝ] ℝ} (hB₀ : B₀.IsInvertible) :
    palaisCongruence B₀ B₀ = 1 := by
  rw [palaisCongruence, hB₀.inverse_comp_self, ← ContinuousLinearMap.one_def, sqrtNearOne_one]

variable {B₀ : E →L[ℝ] E →L[ℝ] ℝ}

/-- The comparison operator `B₀⁻¹ ∘ B` tends to the identity as both forms tend to an invertible
form. -/
private theorem tendsto_inverse_comp (hB₀ : B₀.IsInvertible) :
    Tendsto (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦ p.1.inverse ∘L p.2)
      (𝓝 (B₀, B₀)) (𝓝 1) := by
  have h : ContDiffAt ℝ 0
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦ p.1.inverse ∘L p.2) (B₀, B₀) :=
    (ContDiffAt.comp (g := ContinuousLinearMap.inverse) (B₀, B₀) hB₀.contDiffAt_map_inverse
      contDiffAt_fst).clm_comp contDiffAt_snd
  rw [← hB₀.inverse_comp_self.trans ContinuousLinearMap.one_def.symm]
  exact h.continuousAt.tendsto

/-- **The Palais congruence is smooth**, jointly in the reference form and the compared form, on a
neighbourhood of `(B₀, B₀)` for every invertible `B₀`. -/
theorem eventually_contDiffAt_palaisCongruence {n : ℕ∞ω} (hB₀ : B₀.IsInvertible) :
    ∀ᶠ p in 𝓝 (B₀, B₀), ContDiffAt ℝ n
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦ palaisCongruence p.1 p.2) p := by
  filter_upwards [(continuous_fst.tendsto (B₀, B₀)).eventually hB₀.eventually_nhds,
    (tendsto_inverse_comp hB₀).eventually
      ((isOpen_analyticAt ℝ (sqrtNearOne (E →L[ℝ] E))).mem_nhds analyticAt_sqrtNearOne)]
    with p hp hA
  exact hA.contDiffAt.comp p
    (((ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse hp).comp p contDiffAt_fst).clm_comp
      contDiffAt_snd)

/-- The adjoint of an operator `T` for the pairing given by a form `B`. When `B` is invertible it
is characterized by `B (adj T w) w' = B w (T w')`. -/
private def pairingAdjoint (B : E →L[ℝ] E →L[ℝ] ℝ) (T : E →L[ℝ] E) : E →L[ℝ] E :=
  B.inverse ∘L ((ContinuousLinearMap.compL ℝ E E ℝ).flip T ∘L B)

omit [CompleteSpace E] in
private theorem apply_pairingAdjoint_apply {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : B.IsInvertible)
    (T : E →L[ℝ] E) (w w' : E) : B (pairingAdjoint B T w) w' = B w (T w') := by
  simp [pairingAdjoint, hB.self_apply_inverse]

omit [CompleteSpace E] in
/-- An operator is determined by the pairing of its values against an invertible form. -/
private theorem ext_of_apply_apply {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : B.IsInvertible)
    {T₁ T₂ : E →L[ℝ] E} (h : ∀ w w', B (T₁ w) w' = B (T₂ w) w') : T₁ = T₂ :=
  ContinuousLinearMap.ext fun w ↦ hB.injective (ContinuousLinearMap.ext (h w))

/-- **The Palais congruence is a congruence.** Near `(B₀, B₀)`, for an invertible `B₀`, any two
symmetric forms `B₁` and `B` satisfy `B₁ (R w) (R w') = B w w'`, where `R` is their Palais
congruence: `R` squares to `B₁⁻¹ ∘ B`, and it is self-adjoint for the pairing `B₁` because its
adjoint is another square root of the self-adjoint operator `B₁⁻¹ ∘ B` close to the identity. -/
theorem eventually_palaisCongruence_apply_apply (hB₀ : B₀.IsInvertible) :
    ∀ᶠ p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) in 𝓝 (B₀, B₀),
      (∀ w w', p.1 w w' = p.1 w' w) → (∀ w w', p.2 w w' = p.2 w' w) →
        ∀ w w', p.1 (palaisCongruence p.1 p.2 w) (palaisCongruence p.1 p.2 w') = p.2 w w' := by
  have hR : ContDiffAt ℝ 0
      (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦ palaisCongruence p.1 p.2) (B₀, B₀) :=
    (eventually_contDiffAt_palaisCongruence hB₀).self_of_nhds
  -- The adjoint of the Palais congruence for the pairing `p.1` tends to the identity.
  have hadj : Tendsto (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦
      pairingAdjoint p.1 (palaisCongruence p.1 p.2)) (𝓝 (B₀, B₀)) (𝓝 1) := by
    have h : ContinuousAt (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦
        pairingAdjoint p.1 (palaisCongruence p.1 p.2)) (B₀, B₀) := by
      simp only [pairingAdjoint]
      exact ((hB₀.contDiffAt_map_inverse.comp _ contDiffAt_fst).clm_comp
          (((ContinuousLinearMap.compL ℝ E E ℝ).flip.contDiff.contDiffAt.comp _ hR).clm_comp
            contDiffAt_fst)).continuousAt
    have h1 : pairingAdjoint B₀ (palaisCongruence B₀ B₀) = 1 :=
      ext_of_apply_apply hB₀ fun w w' ↦ by
        rw [apply_pairingAdjoint_apply hB₀, palaisCongruence_self hB₀]
        simp
    simpa [h1] using h.tendsto
  filter_upwards [(continuous_fst.tendsto (B₀, B₀)).eventually hB₀.eventually_nhds,
    (tendsto_inverse_comp hB₀).eventually eventually_mul_self_sqrtNearOne,
    hadj.eventually eventually_sqrtNearOne_mul_self] with p hp hRR hadjR hs₁ hs w w'
  set R := palaisCongruence p.1 p.2 with hRdef
  set C := p.1.inverse ∘L p.2
  have hRR' : R * R = C := by rw [hRdef, palaisCongruence]; exact hRR
  have hC (w w' : E) : p.1 (C w) w' = p.2 w w' := by simp [C, hp.self_apply_inverse]
  -- `C` is self-adjoint for `p.1`, and the adjoint reverses products.
  have hCadj : pairingAdjoint p.1 C = C := ext_of_apply_apply hp fun w w' ↦ by
    rw [apply_pairingAdjoint_apply hp, hs₁, hC, hs, hC]
  have hmul : pairingAdjoint p.1 R * pairingAdjoint p.1 R = pairingAdjoint p.1 (R * R) :=
    ext_of_apply_apply hp fun w w' ↦ by
      simp only [mul_apply_eq_comp, apply_pairingAdjoint_apply hp]
  -- So the adjoint of `R` is a square root of `C` close to the identity, hence equals `R`.
  have hfix : pairingAdjoint p.1 R = R := by
    rw [← hadjR, hmul, hRR', hCadj, hRdef, palaisCongruence]
  calc p.1 (R w) (R w') = p.1 (pairingAdjoint p.1 R w) (R w') := by rw [hfix]
    _ = p.1 w ((R * R) w') := by rw [apply_pairingAdjoint_apply hp, mul_apply_eq_comp]
    _ = p.2 w w' := by rw [hRR', hs₁, hC, hs]

omit [CompleteSpace E] in
/-- The comparison operator of two forms pulled back by an invertible map `L` is the comparison
operator of the forms, conjugated by `L`. -/
private theorem inverse_bilinearComp_comp_bilinearComp
    {B₀ B : F →L[ℝ] F →L[ℝ] ℝ} (hB₀ : B₀.IsInvertible) {L : E →L[ℝ] F} (hL : L.IsInvertible) :
    (B₀.bilinearComp L L).inverse ∘L B.bilinearComp L L = L.inverse ∘L (B₀.inverse ∘L B) ∘L L := by
  obtain ⟨e, rfl⟩ := hL
  obtain ⟨D, rfl⟩ := hB₀
  -- The pulled-back reference form is the continuous linear equivalence `D'`.
  let D' : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
    e.trans (D.trans (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)))
  have hD' : ((D : F →L[ℝ] F →L[ℝ] ℝ).bilinearComp (e : E →L[ℝ] F) (e : E →L[ℝ] F)) =
      (D' : E →L[ℝ] E →L[ℝ] ℝ) := by
    ext w w'
    simp [D']
  rw [hD', ContinuousLinearMap.inverse_equiv, ContinuousLinearMap.inverse_equiv,
    ContinuousLinearMap.inverse_equiv]
  ext w : 1
  apply D'.injective
  ext w'
  simp [D']

/-- **The Palais congruence is natural.** For forms `B₁`, `B` on `F` close to an invertible `B₀`
and a map `L : E → F` close to an invertible `L₀`, the Palais congruence of the pulled-back forms
`B₁ (L ·) (L ·)` and `B (L ·) (L ·)` is that of `B₁` and `B`, conjugated by `L`. This is the
compatibility of the Palais congruence with changes of linear coordinates. -/
theorem eventually_palaisCongruence_bilinearComp [CompleteSpace F] {L₀ : E →L[ℝ] F}
    (hL₀ : L₀.IsInvertible) {B₀ : F →L[ℝ] F →L[ℝ] ℝ} (hB₀ : B₀.IsInvertible) :
    ∀ᶠ q : (E →L[ℝ] F) × (F →L[ℝ] F →L[ℝ] ℝ) × (F →L[ℝ] F →L[ℝ] ℝ) in 𝓝 (L₀, B₀, B₀),
      palaisCongruence (q.2.1.bilinearComp q.1 q.1) (q.2.2.bilinearComp q.1 q.1) =
        q.1.inverse ∘L palaisCongruence q.2.1 q.2.2 ∘L q.1 := by
  have hsnd : Tendsto (fun q : (E →L[ℝ] F) × (F →L[ℝ] F →L[ℝ] ℝ) × (F →L[ℝ] F →L[ℝ] ℝ) ↦ q.2)
      (𝓝 (L₀, B₀, B₀)) (𝓝 (B₀, B₀)) := continuous_snd.tendsto _
  have hR : ContDiffAt ℝ 0 (fun q : (E →L[ℝ] F) × (F →L[ℝ] F →L[ℝ] ℝ) × (F →L[ℝ] F →L[ℝ] ℝ) ↦
      palaisCongruence q.2.1 q.2.2) (L₀, B₀, B₀) :=
    ContDiffAt.comp (f := Prod.snd) (L₀, B₀, B₀)
      (eventually_contDiffAt_palaisCongruence hB₀).self_of_nhds contDiffAt_snd
  -- The conjugated congruence tends to the identity.
  have hy : Tendsto (fun q : (E →L[ℝ] F) × (F →L[ℝ] F →L[ℝ] ℝ) × (F →L[ℝ] F →L[ℝ] ℝ) ↦
      q.1.inverse ∘L palaisCongruence q.2.1 q.2.2 ∘L q.1) (𝓝 (L₀, B₀, B₀)) (𝓝 1) := by
    have h : ContinuousAt (fun q : (E →L[ℝ] F) × (F →L[ℝ] F →L[ℝ] ℝ) × (F →L[ℝ] F →L[ℝ] ℝ) ↦
        q.1.inverse ∘L palaisCongruence q.2.1 q.2.2 ∘L q.1) (L₀, B₀, B₀) :=
      ((ContDiffAt.comp (g := ContinuousLinearMap.inverse) (L₀, B₀, B₀)
        hL₀.contDiffAt_map_inverse contDiffAt_fst).clm_comp
          (hR.clm_comp contDiffAt_fst)).continuousAt
    have h1 : L₀.inverse ∘L palaisCongruence B₀ B₀ ∘L L₀ = 1 := by
      rw [palaisCongruence_self hB₀]
      ext w
      simp [hL₀.inverse_apply_self]
    rw [← h1]
    exact h.tendsto
  filter_upwards [(continuous_fst.tendsto (L₀, B₀, B₀)).eventually hL₀.eventually_nhds,
    (hsnd.eventually ((continuous_fst.tendsto (B₀, B₀)).eventually hB₀.eventually_nhds)),
    hsnd.eventually ((tendsto_inverse_comp hB₀).eventually eventually_mul_self_sqrtNearOne),
    hy.eventually eventually_sqrtNearOne_mul_self] with q hL hB hRR hy'
  rw [palaisCongruence, inverse_bilinearComp_comp_bilinearComp hB hL, ← hy']
  congr 1
  ext w
  have hRR' := congrArg (fun T : F →L[ℝ] F ↦ T (q.1 w)) hRR
  simp only [mul_apply_eq_comp] at hRR'
  simp [palaisCongruence, hL.self_apply_inverse, hRR']

/-- A `C^n` family `B` of symmetric continuous bilinear forms on a Banach space whose value at
`a` is invertible is, near `a`, the congruence of that value by a `C^n` family of continuous
linear operators equal to the identity at `a`: there is `R` with `R a = 1` and
`B₀ (R v w) (R v w') = B v w w'`. The parameter space `F` is independent of the Banach
space `E` on which the forms act. In particular, continuity of the family suffices to obtain
continuous congruences. The family `R` is the Palais congruence `TauCeti.palaisCongruence` of
`B v` with respect to `B₀`. -/
theorem exists_congruence_of_symmetric_family
    {n : ℕ∞ω} {a : F} {B : F → E →L[ℝ] E →L[ℝ] ℝ} (hB : ContDiff ℝ n B)
    (hsymm : ∀ v w w', B v w w' = B v w' w)
    (B₀ : E ≃L[ℝ] (E →L[ℝ] ℝ)) (hB₀ : (B₀ : E →L[ℝ] E →L[ℝ] ℝ) = B a) :
    ∃ (R : F → (E →L[ℝ] E)) (U : Set F), IsOpen U ∧ a ∈ U ∧ R a = 1 ∧
      ContDiffOn ℝ n R U ∧ ∀ v ∈ U, ∀ w w', B₀ (R v w) (R v w') = B v w w' := by
  have hinv : (B₀ : E →L[ℝ] E →L[ℝ] ℝ).IsInvertible := ⟨B₀, rfl⟩
  have hten : Tendsto (fun v ↦ ((B₀ : E →L[ℝ] E →L[ℝ] ℝ), B v)) (𝓝 a)
      (𝓝 ((B₀ : E →L[ℝ] E →L[ℝ] ℝ), (B₀ : E →L[ℝ] E →L[ℝ] ℝ))) := by
    rw [hB₀]
    exact tendsto_const_nhds.prodMk_nhds (hB.continuous.tendsto a)
  obtain ⟨W, hWsub, hWopen, haW⟩ := mem_nhds_iff.1 (hten.eventually
    ((eventually_palaisCongruence_apply_apply hinv).and
      (eventually_contDiffAt_palaisCongruence (n := n) hinv)))
  refine ⟨fun v ↦ palaisCongruence B₀ (B v), W, hWopen, haW, by simp [← hB₀, hinv],
    fun v hv ↦ ?_, fun v hv w w' ↦ ?_⟩
  · exact (ContDiffAt.comp (g := fun p : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦
      palaisCongruence p.1 p.2) v (hWsub hv).2
        (contDiffAt_const.prodMk hB.contDiffAt)).contDiffWithinAt
  · simpa using (hWsub hv).1 (fun w w' ↦ by simpa [hB₀] using hsymm a w w') (hsymm v) w w'

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- **Congruence with a varying reference form.** A jointly `C^n` symmetric family `B (b, v)`
whose value at `(a, 0)` is invertible is, on a product neighbourhood, congruent to `B (b, 0)`
by jointly `C^n` invertible operators. The operators are the identity on the entire zero
section in that neighbourhood, and their inverses are jointly `C^n` there as well.

The parameter spaces `P` and `F` need not be complete or finite-dimensional. No definiteness
or constant-signature hypothesis is required. -/
theorem exists_parametric_congruence_of_symmetric_family
    {n : ℕ∞ω} {a : P} {B : P × F → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiff ℝ n B) (hsymm : ∀ z w w', B z w w' = B z w' w)
    (hBa : (B (a, 0)).IsInvertible) :
    ∃ (R : P × F → E →L[ℝ] E) (U : Set P) (V : Set F),
      IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ (0 : F) ∈ V ∧
      (∀ b ∈ U, R (b, 0) = 1) ∧ ContDiffOn ℝ n R (U ×ˢ V) ∧
      ContDiffOn ℝ n (fun z ↦ (R z).inverse) (U ×ˢ V) ∧
      (∀ z ∈ U ×ˢ V, (R z).IsInvertible) ∧
      ∀ z ∈ U ×ˢ V, ∀ w w', B (z.1, 0) (R z w) (R z w') = B z w w' := by
  obtain ⟨A, hA⟩ := hBa
  obtain ⟨T, W, hW, haW, hTa, hT, hspec⟩ :=
    exists_congruence_of_symmetric_family hB hsymm A hA
  -- Shrink to a product neighbourhood where the fixed-reference operators are invertible.
  have hTa_inv : (T (a, 0)).IsInvertible := by
    rw [hTa]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  have hnear : ∀ᶠ z in 𝓝 (a, (0 : F)), (T z).IsInvertible :=
    (hT.continuousOn.continuousAt (hW.mem_nhds haW)).eventually hTa_inv.eventually_nhds
  obtain ⟨U, V, hU, haU, hV, h0V, hUV⟩ :=
    mem_nhds_prod_iff'.mp (Filter.inter_mem (hW.mem_nhds haW) hnear)
  have hsub : U ×ˢ V ⊆ W := fun z hz ↦ (hUV hz).1
  have hTi (z : P × F) (hz : z ∈ U ×ˢ V) : (T z).IsInvertible := (hUV hz).2
  let S : P × F → E →L[ℝ] E := fun z ↦ T (z.1, 0)
  have hS : ContDiffOn ℝ n S (U ×ˢ V) :=
    hT.comp (contDiffOn_fst.prodMk contDiffOn_const)
      (fun z hz ↦ hsub ⟨hz.1, h0V⟩)
  have hSi (z : P × F) (hz : z ∈ U ×ˢ V) : (S z).IsInvertible :=
    hTi (z.1, 0) ⟨hz.1, h0V⟩
  have hSinv : ContDiffOn ℝ n (fun z ↦ (S z).inverse) (U ×ˢ V) := by
    intro z hz
    exact (hSi z hz).contDiffAt_map_inverse.comp_contDiffWithinAt z (hS z hz)
  let R : P × F → E →L[ℝ] E := fun z ↦ (S z).inverse.comp (T z)
  have hR : ContDiffOn ℝ n R (U ×ˢ V) := hSinv.clm_comp (hT.mono hsub)
  have hRi (z : P × F) (hz : z ∈ U ×ˢ V) : (R z).IsInvertible :=
    (hSi z hz).inverse.comp (hTi z hz)
  refine ⟨R, U, V, hU, hV, haU, h0V, ?_, hR, ?_, hRi, ?_⟩
  · intro b hb
    exact (hTi (b, 0) ⟨hb, h0V⟩).inverse_comp_self
  · intro z hz
    exact (hRi z hz).contDiffAt_map_inverse.comp_contDiffWithinAt z (hR z hz)
  · intro z hz w w'
    -- Divide by the zero-section operator on both arguments of the reference form.
    calc
      B (z.1, 0) (R z w) (R z w') =
          A (S z (R z w)) (S z (R z w')) :=
        (hspec (z.1, 0) (hsub ⟨hz.1, h0V⟩) _ _).symm
      _ = A (T z w) (T z w') := by
        simp only [R, ContinuousLinearMap.comp_apply, (hSi z hz).self_apply_inverse]
      _ = B z w w' := hspec z (hsub hz) w w'

end Congruence

section MorseLemma

variable [CompleteSpace E] {f : E → ℝ} {n : ℕ∞}

/-- **The Morse lemma.** Near a nondegenerate critical point `x` of a `C^{n+2}` function `f`,
with `1 ≤ n ≤ ∞`, there is a `C^n` map `φ`, fixing `0` and with derivative the identity there,
in terms of which `f` is exactly its Hessian quadratic form:
`f (x + v) = f x + 2⁻¹ * fderiv ℝ (fderiv ℝ f) x (φ v) (φ v)` for `v` near `0`.

`TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart` repackages this as a chart at
`x`. -/
theorem IsNondegenerateCriticalPoint.exists_normal_form (hf : ContDiff ℝ (n + 2) f)
    (h : IsNondegenerateCriticalPoint f x) (hn : n ≠ 0) :
    ∃ (φ : E → E) (U : Set E), IsOpen U ∧ 0 ∈ U ∧ φ 0 = 0 ∧ ContDiffOn ℝ n φ U ∧
      HasFDerivAt φ (ContinuousLinearMap.id ℝ E) 0 ∧ ∀ v ∈ U,
      f (x + v) = f x + (2 : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ f) x (φ v) (φ v) := by
  have hf₂ : ContDiff ℝ 2 f := hf.of_le le_add_self
  obtain ⟨B₀, hB₀⟩ := h.isInvertible
  obtain ⟨R, U, hUopen, h0U, hR0, hRsmooth, hRspec⟩ :=
    exists_congruence_of_symmetric_family (a := (0 : E)) (B := hessianAverage f x)
      (contDiff_hessianAverage hf x)
      (fun v w w' ↦ hessianAverage_symm hf₂ x v w w') B₀
      (by rw [hB₀, hessianAverage_zero])
  have hRsmoothAt : ContDiffAt ℝ n R 0 :=
    (hRsmooth 0 h0U).contDiffAt (hUopen.mem_nhds h0U)
  have hφsmooth : ContDiffOn ℝ n (fun v ↦ R v v) U :=
    hRsmooth.clm_apply contDiffOn_id
  refine ⟨fun v ↦ R v v, U, hUopen, h0U, by simp [hR0], hφsmooth, ?_, ?_⟩
  · have hd : HasFDerivAt (fun v ↦ R v v)
        ((R 0).comp (ContinuousLinearMap.id ℝ E) + (fderiv ℝ R 0).flip 0) 0 :=
      ((hRsmoothAt.differentiableAt (by simpa using hn)).hasFDerivAt).clm_apply
        (hasFDerivAt_id (𝕜 := ℝ) (0 : E))
    have he : (R 0).comp (ContinuousLinearMap.id ℝ E) + (fderiv ℝ R 0).flip 0
        = ContinuousLinearMap.id ℝ E := by
      rw [hR0]
      ext w
      simp
    rw [← he]
    exact hd
  · intro v hv
    rw [map_add_eq_add_hessianAverage hf₂, ← hRspec v hv v v, ← hB₀]
    simp [h.fderiv_eq_zero]

/-- **The Morse lemma, as a chart.** At a nondegenerate critical point `x` of a `C^{n+2}`
function `f`, with `1 ≤ n ≤ ∞`, there is a chart `ψ` sending `x` to `0`, `C^n` in both
directions, on whose whole source `f` is its Hessian quadratic form read in that chart. -/
theorem IsNondegenerateCriticalPoint.exists_morse_chart (hf : ContDiff ℝ (n + 2) f)
    (h : IsNondegenerateCriticalPoint f x) (hn : n ≠ 0) :
    ∃ ψ : OpenPartialHomeomorph E E, x ∈ ψ.source ∧ ψ x = 0 ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      ∀ y ∈ ψ.source, f y = f x + (2 : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ f) x (ψ y) (ψ y) := by
  obtain ⟨φ, U, hUopen, h0U, hφ0, hφsmooth, hφderiv, hφeq⟩ := h.exists_normal_form hf hn
  have hn' : (n : ℕ∞ω) ≠ 0 := by simpa using hn
  let V : Set E := (fun y ↦ y - x) ⁻¹' U
  have hVopen : IsOpen V := hUopen.preimage (by fun_prop)
  have hxV : x ∈ V := by simp [V, h0U]
  have hΦsmoothOn : ContDiffOn ℝ n (φ ∘ fun y : E ↦ y - x) V :=
    hφsmooth.comp (by fun_prop) fun _ hy ↦ hy
  have hΦsmoothAt {y : E} (hy : y ∈ V) : ContDiffAt ℝ n (φ ∘ fun y : E ↦ y - x) y :=
    (hΦsmoothOn y hy).contDiffAt (hVopen.mem_nhds hy)
  have hΦderiv : HasFDerivAt (φ ∘ fun y : E ↦ y - x)
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) x := by
    simpa using HasFDerivAt.comp x (by simpa using hφderiv) (hasFDerivAt_sub_const (𝕜 := ℝ) x)
  have hgood : {y | y ∈ V ∧ ∃ e : E ≃L[ℝ] E,
      (e : E →L[ℝ] E) = fderiv ℝ (φ ∘ fun y : E ↦ y - x) y} ∈ 𝓝 x := by
    have ht := ((hΦsmoothAt hxV).continuousAt_fderiv hn').tendsto
    rw [hΦderiv.fderiv] at ht
    exact Filter.inter_mem (hVopen.mem_nhds hxV)
      (ht.eventually (ContinuousLinearEquiv.refl ℝ E).nhds)
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.1 hgood
  let p := (hΦsmoothAt hxV).toOpenPartialHomeomorph _ hΦderiv hn'
  let ψ := p.restrOpen W hWopen
  have hψsrc : ψ.source = p.source ∩ W := p.restrOpen_source W hWopen
  have hψ : ⇑ψ = φ ∘ fun y : E ↦ y - x := by
    rw [OpenPartialHomeomorph.coe_restrOpen, ContDiffAt.toOpenPartialHomeomorph_coe]
  refine ⟨ψ, hψsrc ▸ ⟨(hΦsmoothAt hxV).mem_toOpenPartialHomeomorph_source hΦderiv hn', hxW⟩,
    by simp [hψ, hφ0], ?_, fun z hz ↦ ?_, ?_⟩
  · rw [hψ, hψsrc]
    exact hΦsmoothOn.mono fun z hz ↦ (hWsub hz.2).1
  · obtain ⟨hyV, e, he⟩ := hWsub (hψsrc ▸ ψ.map_target hz).2
    refine (ψ.contDiffAt_symm hz (f₀' := e) ?_ (hψ ▸ hΦsmoothAt hyV)).contDiffWithinAt
    rw [hψ, he]
    exact ((hΦsmoothAt hyV).differentiableAt hn').hasFDerivAt
  · rw [hψsrc, hψ]
    exact fun y hy ↦ by simpa using hφeq (y - x) (hWsub hy.2).1

end MorseLemma

end TauCeti
