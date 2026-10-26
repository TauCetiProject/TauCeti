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

The family `R` is manufactured from a square root: the operator `C v = (B 0)⁻¹ ∘ B v` is close to
the identity for `v` close to `0`, so it has a unique square root there
(`TauCeti.sqrtNearOne`), and that square root is automatically self-adjoint for the pairing
`B 0`, because the adjoint of a square root is a square root of the adjoint and the two are close
to the identity.  Self-adjointness is exactly what turns `R v * R v = C v` into the congruence
identity.

The Morse lemma supplies the local model of a Morse function: the index of the critical point,
the local handle structure, and the local form of the gradient flow are all read off it.  The
averaged Hessian of a `C^{n+2}` function is `C^n`, and the congruence construction preserves the
regularity of the family. The Morse lemma therefore gives a `C^n` chart for a `C^{n+2}`
function when `1 ≤ n ≤ ∞`; taking `n = ∞` recovers the smooth Morse lemma.

## Main declarations

* `TauCeti.hessianAverage`: the averaged Hessian along a segment, normalised so that
  `TauCeti.hessianAverage_zero` identifies its value at `0` with the Hessian.
* `TauCeti.map_add_eq_add_hessianAverage`: the second-order Taylor formula it satisfies.
* `TauCeti.exists_congruence_of_symmetric_family`: a `C^n` family of symmetric continuous
  bilinear forms whose value at a basepoint is invertible is, near that point, the congruence of
  that value by a `C^n` family of operators equal to the identity at the basepoint.
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
/-- The averaged Hessian of a `C^{n+2}` function is `C^n` in the direction. -/
theorem contDiff_hessianAverage {n : ℕ∞} (hf : ContDiff ℝ (n + 2) f) (x : E) :
    ContDiff ℝ n (hessianAverage f x) := by
  have hd : ContDiff ℝ n (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := n + 1) (by norm_num [add_assoc])).fderiv_right (m := n) (by simp)
  exact hd.contDiff_segmentAverage
    ((by fun_prop : Continuous fun t : ℝ ↦ 2 * (1 - t)).intervalIntegrable 0 1) x

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

end HessianAverage

section Congruence

variable [CompleteSpace E]

/-- A `C^n` family `B` of symmetric continuous bilinear forms on a Banach space whose value at
`a` is invertible is, near `a`, the congruence of that value by a `C^n` family of continuous
linear operators equal to the identity at `a`: there is `R` with `R a = 1` and
`B₀ (R v w) (R v w') = B v w w'`. The parameter space `F` is independent of the Banach
space `E` on which the forms act. In particular, continuity of the family suffices to obtain
continuous congruences. -/
theorem exists_congruence_of_symmetric_family
    {n : ℕ∞ω} {a : F} {B : F → E →L[ℝ] E →L[ℝ] ℝ} (hB : ContDiff ℝ n B)
    (hsymm : ∀ v w w', B v w w' = B v w' w)
    (B₀ : E ≃L[ℝ] (E →L[ℝ] ℝ)) (hB₀ : (B₀ : E →L[ℝ] E →L[ℝ] ℝ) = B a) :
    ∃ (R : F → (E →L[ℝ] E)) (U : Set F), IsOpen U ∧ a ∈ U ∧ R a = 1 ∧
      ContDiffOn ℝ n R U ∧ ∀ v ∈ U, ∀ w w', B₀ (R v w) (R v w') = B v w w' := by
  -- the adjoint of an operator for the pairing given by `B₀`
  set adj : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E (B₀.symm : (E →L[ℝ] ℝ) →L[ℝ] E)).comp
      (((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) (E →L[ℝ] ℝ)).flip
          (G' := E →L[ℝ] E →L[ℝ] ℝ) (B₀ : E →L[ℝ] E →L[ℝ] ℝ)).comp
        ((ContinuousLinearMap.compL ℝ E E ℝ).flip)) with hadjdef
  have adj_spec : ∀ (T : E →L[ℝ] E) (w w' : E), B₀ (adj T w) w' = B₀ w (T w') := by
    intro T w w'
    simp [hadjdef]
  have hdet : ∀ T₁ T₂ : E →L[ℝ] E, (∀ w w', B₀ (T₁ w) w' = B₀ (T₂ w) w') → T₁ = T₂ := by
    intro T₁ T₂ h
    ext w
    refine B₀.injective ?_
    ext w'
    exact h w w'
  have adj_one : adj 1 = 1 := by
    refine hdet _ _ fun w w' ↦ ?_
    rw [adj_spec]
    simp
  have adj_mul : ∀ S T : E →L[ℝ] E, adj (S * T) = adj T * adj S := by
    intro S T
    refine hdet _ _ fun w w' ↦ ?_
    rw [adj_spec, mul_apply_eq_comp, mul_apply_eq_comp, adj_spec, adj_spec]
  have hB₀symm : ∀ w w' : E, B₀ w w' = B₀ w' w := by
    intro w w'
    have h := hsymm a w w'
    rw [← hB₀] at h
    simpa using h
  -- the comparison operator `B₀⁻¹ ∘ B v`
  set C : F → (E →L[ℝ] E) := fun v ↦ (B₀.symm : (E →L[ℝ] ℝ) →L[ℝ] E).comp (B v) with hCdef
  have hCapply : ∀ (v : F) (w w' : E), B₀ (C v w) w' = B v w w' := by
    intro v w w'
    simp [hCdef]
  have hCa : C a = 1 := by
    refine hdet _ _ fun w w' ↦ ?_
    rw [hCapply, ← hB₀]
    simp
  have hCsmooth : ContDiff ℝ n C := by
    have h := (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
      (B₀.symm : (E →L[ℝ] ℝ) →L[ℝ] E)).contDiff.comp hB
    exact h
  have hCadj : ∀ v, adj (C v) = C v := by
    intro v
    refine hdet _ _ fun w w' ↦ ?_
    rw [adj_spec, hCapply, hB₀symm, hCapply, hsymm]
  let R : F → (E →L[ℝ] E) := fun v ↦ sqrtNearOne (E →L[ℝ] E) (C v)
  have hRa : R a = 1 := by simp [R, hCa]
  have hten : Filter.Tendsto C (𝓝 (a : F)) (𝓝 1) :=
    hCa ▸ hCsmooth.continuous.continuousAt
  have e1 := hten.eventually (eventually_mul_self_sqrtNearOne (A := E →L[ℝ] E))
  have e2 := hten.eventually
    (eventually_sqrtNearOne_fixed adj.continuous.continuousAt adj_one adj_mul)
  have hspec : ∀ᶠ v in 𝓝 (a : F), ∀ w w', B₀ (R v w) (R v w') = B v w w' := by
    filter_upwards [e1, e2] with v h1 h2
    have h4 : sqrtNearOne (E →L[ℝ] E) (C v) = adj (sqrtNearOne (E →L[ℝ] E) (C v)) :=
      (h2 (hCadj v)).symm
    have hself : ∀ w w' : E, B₀ (sqrtNearOne (E →L[ℝ] E) (C v) w) w'
        = B₀ w (sqrtNearOne (E →L[ℝ] E) (C v) w') := by
      intro w w'
      conv_lhs => rw [h4]
      exact adj_spec _ w w'
    intro w w'
    calc B₀ (sqrtNearOne (E →L[ℝ] E) (C v) w) (sqrtNearOne (E →L[ℝ] E) (C v) w')
        = B₀ w (sqrtNearOne (E →L[ℝ] E) (C v) (sqrtNearOne (E →L[ℝ] E) (C v) w')) :=
          hself w _
      _ = B₀ w ((sqrtNearOne (E →L[ℝ] E) (C v) * sqrtNearOne (E →L[ℝ] E) (C v)) w') := by
          rw [mul_apply_eq_comp]
      _ = B₀ w (C v w') := by rw [h1]
      _ = B v w w' := by
          rw [hB₀symm w (C v w'), hCapply v w' w]
          exact hsymm v w' w
  obtain ⟨W, hWsub, hWopen, haW⟩ := mem_nhds_iff.1 hspec
  let S : Set (E →L[ℝ] E) := {a | AnalyticAt ℝ (sqrtNearOne (E →L[ℝ] E)) a}
  have hSopen : IsOpen S := isOpen_analyticAt ℝ (sqrtNearOne (E →L[ℝ] E))
  have h1S : (1 : E →L[ℝ] E) ∈ S := analyticAt_sqrtNearOne
  let U : Set F := W ∩ C ⁻¹' S
  have hUopen : IsOpen U := hWopen.inter (hSopen.preimage hCsmooth.continuous)
  have haU : (a : F) ∈ U := ⟨haW, by simpa [hCa] using h1S⟩
  refine ⟨R, U, hUopen, haU, hRa, ?_, ?_⟩
  · intro v hv
    have hsqrt : ContDiffAt ℝ n (sqrtNearOne (E →L[ℝ] E)) (C v) := hv.2.contDiffAt
    have hcomp := (hsqrt.comp v hCsmooth.contDiffAt).contDiffWithinAt (s := U)
    rwa [Function.comp_def] at hcomp
  · intro v hv
    exact hWsub hv.1

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
  have hsub : HasFDerivAt (fun y : E ↦ y - x) (ContinuousLinearMap.id ℝ E) x := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) x).sub_const x
  have hΨderiv : HasFDerivAt (φ ∘ fun y : E ↦ y - x)
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) x := by
    have hc : HasFDerivAt (φ ∘ fun y : E ↦ y - x)
        ((ContinuousLinearMap.id ℝ E).comp (ContinuousLinearMap.id ℝ E)) x :=
      HasFDerivAt.comp x (by simpa using hφderiv) hsub
    simpa using hc
  let V : Set E := {y | y - x ∈ U}
  have hVopen : IsOpen V := hUopen.preimage (by fun_prop)
  have hxV : x ∈ V := by simp [V, h0U]
  have hΨsmoothOn : ContDiffOn ℝ n (φ ∘ fun y : E ↦ y - x) V := by
    intro y hy
    have hφAt : ContDiffAt ℝ n φ (y - x) :=
      (hφsmooth (y - x) hy).contDiffAt (hUopen.mem_nhds hy)
    exact (hφAt.comp y (by fun_prop)).contDiffWithinAt
  have hΨsmooth : ContDiffAt ℝ n (φ ∘ fun y : E ↦ y - x) x :=
    (hΨsmoothOn x hxV).contDiffAt (hVopen.mem_nhds hxV)
  have hΨx : (φ ∘ fun y : E ↦ y - x) x = 0 := by simp [hφ0]
  have hΨeq : ∀ y ∈ V, f y = f x + (2 : ℝ)⁻¹ *
      fderiv ℝ (fderiv ℝ f) x ((φ ∘ fun y : E ↦ y - x) y)
        ((φ ∘ fun y : E ↦ y - x) y) := by
    intro y hy
    simpa using hφeq (y - x) hy
  have hderivInvertible : ∀ᶠ y in 𝓝 x, ∃ e : E ≃L[ℝ] E,
      (e : E →L[ℝ] E) = fderiv ℝ (φ ∘ fun y : E ↦ y - x) y := by
    have ht := (hΨsmooth.continuousAt_fderiv (by simpa using hn)).tendsto
    rw [hΨderiv.fderiv] at ht
    exact ht.eventually (ContinuousLinearEquiv.refl ℝ E).nhds
  have hgood : {y | y ∈ V ∧ ∃ e : E ≃L[ℝ] E,
      (e : E →L[ℝ] E) = fderiv ℝ (φ ∘ fun y : E ↦ y - x) y} ∈ 𝓝 x :=
    Filter.inter_mem (hVopen.mem_nhds hxV) hderivInvertible
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.1 hgood
  let p := hΨsmooth.toOpenPartialHomeomorph _ hΨderiv (by simpa using hn)
  let ψ := p.restrOpen W hWopen
  have hxsource : x ∈ ψ.source := by
    simp only [ψ, OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hΨsmooth.mem_toOpenPartialHomeomorph_source hΨderiv (by simpa using hn), hxW⟩
  refine ⟨ψ, hxsource, ?_, ?_, ?_, ?_⟩
  · simpa [ψ, p] using hΨx
  · intro y hy
    simp only [ψ, OpenPartialHomeomorph.restrOpen_source] at hy
    have hyV := (hWsub hy.2).1
    have hsmooth := hΨsmoothOn y hyV
    apply hsmooth.mono
    intro z hz
    simp only [ψ, OpenPartialHomeomorph.restrOpen_source] at hz
    exact (hWsub hz.2).1
  · intro z hz
    have hy : ψ.symm z ∈ ψ.source := ψ.map_target hz
    have hy' := hy
    simp only [ψ, OpenPartialHomeomorph.restrOpen_source] at hy'
    obtain ⟨e, he⟩ := (hWsub hy'.2).2
    have hyV := (hWsub hy'.2).1
    have hforwardAt : ContDiffAt ℝ n (φ ∘ fun y : E ↦ y - x) (ψ.symm z) :=
      (hΨsmoothOn (ψ.symm z) hyV).contDiffAt (hVopen.mem_nhds hyV)
    have hforwardDeriv : HasFDerivAt ψ (e : E →L[ℝ] E) (ψ.symm z) := by
      have hd : HasFDerivAt (φ ∘ fun y : E ↦ y - x) (e : E →L[ℝ] E) (ψ.symm z) := by
        rw [he]
        exact hforwardAt.differentiableAt (by simpa using hn) |>.hasFDerivAt
      simpa [ψ, p] using hd
    exact (ψ.contDiffAt_symm hz hforwardDeriv (by simpa [ψ, p] using hforwardAt)).contDiffWithinAt
  · simp only [ψ, OpenPartialHomeomorph.restrOpen_source]
    intro y hy
    simpa [ψ, p] using hΨeq y (hWsub hy.2).1

end MorseLemma

end TauCeti
