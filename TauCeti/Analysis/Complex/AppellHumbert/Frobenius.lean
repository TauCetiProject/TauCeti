/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.AppellHumbert.PoincareSeries
public import TauCeti.Analysis.Complex.AppellHumbert.Translation
public import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Central.End
import Mathlib.Analysis.Complex.Liouville
import Mathlib.GroupTheory.OrderOfElement
import TauCeti.Algebra.Module.ZLattice.BilinFormDual
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.MulLeftRight
import TauCeti.LinearAlgebra.LinearIndependent.SpanEq
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import TauCeti.Algebra.Module.Lattice
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.Torus.Periodic

/-!
# Frobenius' dimension formula for theta functions

Let `D = (B, χ)` be an Appell–Humbert datum for a full lattice `L` in a finite-dimensional complex
normed space `V`, with positive Riemann form `E` (`TauCeti.AppellHumbertData.IsPositive`), and let
`Θ = Θ (B, χ)` be its space of theta functions. Let `L^⊥ = {v : E (v, l) ∈ ℤ for all l ∈ L}` be the
dual of `L` for `E` (`D.riemannForm.dualSubmodule L`). The twisted translations `U_a` by `a ∈ L^⊥`
preserve `Θ` (`TauCeti.AppellHumbertData.twistedTranslateEnd`). This file proves:

* `Θ` is finite-dimensional and not zero
  (`TauCeti.AppellHumbertData.IsPositive.finiteDimensional_thetaSpace`,
  `TauCeti.AppellHumbertData.IsPositive.finrank_thetaSpace_pos`);
* for any nondegenerate Riemann form, `L` has finite index in `L^⊥`
  (`TauCeti.AppellHumbertData.finite_dualQuotient`); this and the double duality `L = (L^⊥)^⊥`
  used below are the general facts
  `LinearMap.BilinForm.finite_quotient_dualSubmodule` and
  `LinearMap.BilinForm.dualSubmodule_flip_dualSubmodule_of_isZLattice` for the Riemann form;
* the restrictions of the `U_a`, `a ∈ L^⊥`, span `End_ℂ (Θ)`, and those attached to representatives
  of `L^⊥ / L` are linearly independent
  (`TauCeti.AppellHumbertData.IsPositive.span_range_twistedTranslateEnd_eq_top`,
  `TauCeti.AppellHumbertData.IsPositive.linearIndependent_twistedTranslateEnd_out`);
* **Frobenius' dimension formula** `(dim Θ)² = [L^⊥ : L]`
  (`TauCeti.AppellHumbertData.IsPositive.finrank_thetaSpace_sq`);
* **irreducibility**: a space of functions that contains the translates `U_a f`, `a ∈ L^⊥`, of one
  nonzero theta function contains `Θ`, and an endomorphism of `Θ` that commutes with all `U_a` is a
  scalar (`TauCeti.AppellHumbertData.IsPositive.thetaSpace_le_of_twistedTranslate_mem`,
  `TauCeti.AppellHumbertData.IsPositive.exists_eq_smul_one_of_commute`);
* some `N ≥ 1`, for example `[L^⊥ : L]`, has `N L^⊥ ⊆ L`, again for any nondegenerate Riemann form
  (`TauCeti.AppellHumbertData.relIndex_ne_zero_and_nsmul_relIndex_mem`).

No symplectic basis of `L` enters the statements or the proofs.

## Method

The upper bound comes from a pairing. For theta functions `f, g` and `b ∈ V`, the function
`x ↦ exp (-B₁ (b, b) / 2) conj ((U_x f) (0)) (U_x g) (b)`, with `B₁` the complex bilinear part of
`B`, is `L`-periodic in `x`; let `m (f, g, b)` be its mean over the torus `V ⧸ L`, computed in the
coordinates of a basis of `L`. It is holomorphic in `b`, and `m (g, f, -b) = conj (m (f, g, b))`.
For tuples `s`, `t` of theta functions, `m (s, t, 0) = 0` therefore forces `m (t, s, ·) = 0` by
Liouville's theorem applied to `exp (-|m (t, s, b)|²)`. If moreover `m (U_a s, t, 0) = 0` for every
`a ∈ L^⊥`, the Fourier coefficients of `x ↦ ∑ᵢ conj ((U_x tᵢ) (0)) (U_x sᵢ) (b)` all vanish, so this
function does too, and evaluating gives `∑ᵢ conj (tᵢ (y)) sᵢ = 0`. For a basis `s` of `Θ` this
shows that `t ↦ (q ↦ m (U_q s, t, 0))` embeds `Θⁿ`, `n = dim Θ`, in the functions on `L^⊥ / L`;
so `n² ≤ [L^⊥ : L]`.

The lower bound: conjugation by `U_y`, `y ∈ L^⊥`, multiplies `U_a` by the character
`exp (2πi E (y, a))` of `y`, and distinct classes of `L^⊥ / L` give distinct characters, as `L` is
the dual of `L^⊥`. Eigenvectors for distinct characters are linearly independent
(`linearIndependent_of_forall_mul_mul_eq_smul`), so
`[L^⊥ : L] ≤ dim End (Θ) = n²`. Equality makes the translations a basis of `End (Θ)`, which gives
the spanning statement, irreducibility and Schur's lemma.

## Provenance

The results and the method are adapted from `New.IsAppellHumbert.finrank_sq_eq_relIndex`,
`New.IsAppellHumbert.exists_injective_to_dual_quotient`, `New.IsAppellHumbert.finite_thetaSpace`,
`New.IsAppellHumbert.linearIndependent_thetaShiftEnd_out`,
`New.IsAppellHumbert.relIndex_dualLattice_eq_finrank_end`,
`New.IsAppellHumbert.span_range_thetaShiftEnd_eq_top`, `New.IsAppellHumbert.finrank_thetaSpace_sq`,
`New.IsAppellHumbert.thetaSpace_le_of_thetaShift_mem`, `New.IsAppellHumbert.schur_lemma`,
`New.IsAppellHumbert.exists_nsmul_mem_of_mem_dualLattice` and the private pairing lemmas of the file
`src/Lib/Shimura/ComplexTheta/DimensionFormula.lean`, and from `New.IsPosRiemann.isDualFamily`
(file `src/Lib/Shimura/ComplexTheta/AppellHumbertData.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, commit `72fead1`, Apache 2.0, Copyright 2026 Anthropic, PBC).
The source takes means over `V ⧸ L` with its Haar probability measure and Fourier uniqueness from
its own Stone–Weierstrass argument; here the means are integrals over the unit cube in the
coordinates of a basis of `L`, and Fourier uniqueness is that of Mathlib's `mFourierBasis`
(`TauCeti.UnitAddTorus.eq_zero_of_forall_setIntegral_mFourier_mul_eq_zero`). The holomorphy of the
mean is `TauCeti.analyticAt_integral_smul`.

## References

* G. Frobenius, *Über die Grundlagen der Theorie der Jacobischen Functionen*, J. Reine Angew. Math.
  97 (1884), 16–48.
* C. Birkenhake, H. Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Springer, 2004,
  3.2.7, 4.1.5 and 6.4.
* D. Bump, A. Pekker, *On the dimension of theta functions*, Proc. Amer. Math. Soc. 130 (2002),
  3473–3481.
-/

public section

open Complex MeasureTheory Set Module Filter
open scoped Real ComplexConjugate

namespace TauCeti.AppellHumbertData

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : Submodule ℤ V}
  (D : AppellHumbertData L)

/-! ### The pairing integrand -/

/-- The integrand `exp (-B₁ (b, b) / 2) conj ((U_x f) (0)) (U_x g) (b)` of the pairing of `f` and
`g` at `b`, as a function of `x`. -/
private noncomputable def pairingIntegrand (f g : V → ℂ) (b x : V) : ℂ :=
  exp (-(D.symmetricPart b b / 2)) *
    (conj (D.twistedTranslate x f 0) * D.twistedTranslate x g b)

variable {D}

/-- The pairing integrand of theta functions is periodic in `x`: translating `x` by `l ∈ L`
multiplies both translates by the same scalar of modulus one. -/
private theorem pairingIntegrand_add {f g : V → ℂ} (hf : f ∈ D.thetaSpace) (hg : g ∈ D.thetaSpace)
    (b x : V) (l : L) :
    D.pairingIntegrand f g b (x + l) = D.pairingIntegrand f g b x := by
  have hc : ‖exp (π * I * D.riemannForm x l) * D.semichar l‖ = 1 := by
    simp only [norm_mul, Circle.norm_coe, mul_one, norm_exp, mul_re, ofReal_re, I_re,
      mul_zero, ofReal_im, I_im, sub_self, zero_mul, Real.exp_zero]
  have key (A B' : ℂ) : conj ((exp (π * I * D.riemannForm x l) * D.semichar l) * A) *
      ((exp (π * I * D.riemannForm x l) * D.semichar l) * B') = conj A * B' := by
    rw [map_mul, mul_mul_mul_comm, conj_mul', hc]
    simp
  simp only [pairingIntegrand, twistedTranslate_add_eq_smul_of_mem_thetaSpace hf,
    twistedTranslate_add_eq_smul_of_mem_thetaSpace hg, Pi.smul_apply, smul_eq_mul, key]

/-- The pairing integrand of continuous functions is continuous in `x`. -/
private theorem continuous_pairingIntegrand {f g : V → ℂ} (hf : Continuous f) (hg : Continuous g)
    (b : V) : Continuous (D.pairingIntegrand f g b) := by
  have h : D.pairingIntegrand f g b = fun x ↦ exp (-(D.symmetricPart b b / 2)) *
      (conj (exp (-(D.form x 0 + D.form x x / 2)) * f (0 + x)) *
        (exp (-(D.form x b + D.form x x / 2)) * g (b + x))) := by
    funext x
    simp [pairingIntegrand, twistedTranslate_apply]
  rw [h]
  fun_prop

/-- **Conjugate symmetry of the pairing integrand**: exchanging `f` and `g` and replacing `b` by
`-b` conjugates the integrand, translated by `b`. -/
private theorem pairingIntegrand_neg_add (f g : V → ℂ) (b x : V) :
    D.pairingIntegrand g f (-b) (x + b) = conj (D.pairingIntegrand f g b x) := by
  -- The exponents agree: their difference is `i (2 Im (B₁ (b, b)) / 2 - Im B (b, b))` = 0.
  have h_exp : -(D.symmetricPart (-b) (-b) / 2) +
      (conj (-(D.form (x + b) 0 + D.form (x + b) (x + b) / 2)) +
        -(D.form (x + b) (-b) + D.form (x + b) (x + b) / 2)) =
      conj (-(D.symmetricPart b b / 2)) + (-(D.form x 0 + D.form x x / 2) +
        conj (-(D.form x b + D.form x x / 2))) := by
    apply Complex.ext
    · simp only [map_neg, map_add, _root_.neg_apply, neg_neg, neg_re, add_re,
        div_ofNat_re, conj_re, _root_.add_apply, map_zero, zero_re]
      linarith [D.re_form_comm x b]
    · simp only [map_neg, map_add, _root_.neg_apply, neg_neg, neg_im, add_im,
        div_ofNat_im, conj_im, _root_.add_apply, map_zero, zero_im, D.im_symmetricPart_self]
      ring
  simp only [pairingIntegrand, twistedTranslate_apply, map_mul, conj_conj, ← exp_conj]
  rw [show (0 : V) + (x + b) = x + b by simp, show -b + (x + b) = 0 + x by abel,
    show b + x = x + b by abel]
  calc _ = exp (-(D.symmetricPart (-b) (-b) / 2) +
        (conj (-(D.form (x + b) 0 + D.form (x + b) (x + b) / 2)) +
        -(D.form (x + b) (-b) + D.form (x + b) (x + b) / 2))) *
          (conj (g (x + b)) * f (0 + x)) := by
        rw [exp_add, exp_add]
        ring
    _ = _ := by
        rw [h_exp, exp_add, exp_add]
        ring

/-- Scaling the first function of the pairing integrand conjugates the scalar. -/
private theorem pairingIntegrand_smul_left (c : ℂ) (f g : V → ℂ) (b : V) :
    D.pairingIntegrand (c • f) g b = fun x ↦ conj c * D.pairingIntegrand f g b x := by
  funext x
  simp only [pairingIntegrand, map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

/-- The pairing integrand is additive in the second function. -/
private theorem pairingIntegrand_add_right (f g g' : V → ℂ) (b : V) :
    D.pairingIntegrand f (g + g') b =
      fun x ↦ D.pairingIntegrand f g b x + D.pairingIntegrand f g' b x := by
  funext x
  simp only [pairingIntegrand, map_add, Pi.add_apply]
  ring

/-- The pairing integrand is linear in the second function. -/
private theorem pairingIntegrand_smul_right (c : ℂ) (f g : V → ℂ) (b : V) :
    D.pairingIntegrand f (c • g) b = fun x ↦ c * D.pairingIntegrand f g b x := by
  funext x
  simp only [pairingIntegrand, map_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- Translating the second function by `a` and moving `b` to `b - a` multiplies the pairing
integrand by the character `exp (2πi E (a, x))`, up to a constant that does not depend on the
functions. -/
private theorem exists_pairingIntegrand_twistedTranslate_right (a b : V) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (f g : V → ℂ) (x : V),
      D.pairingIntegrand f (D.twistedTranslate a g) (b - a) x =
        κ * (exp (2 * π * I * D.riemannForm a x) * D.pairingIntegrand f g b x) := by
  refine ⟨exp (-(D.symmetricPart (b - a) (b - a) / 2)) *
      exp (-(D.form a (b - a) + D.form a a / 2)) / exp (-(D.symmetricPart b b / 2)),
    by simp [exp_ne_zero], fun f g x ↦ ?_⟩
  have h := D.twistedTranslate_twistedTranslate_eq_smul_swap x a g
  simp only [pairingIntegrand, h, Pi.smul_apply, smul_eq_mul, Circle.coe_exp,
    twistedTranslate_apply (a := a), sub_add_cancel]
  push_cast
  field_simp

/-- At `b = z - y` and `x = y`, the pairing integrand is `conj (f y) g z` up to a constant that does
not depend on the functions. -/
private theorem exists_pairingIntegrand_sub_self (y z : V) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ f g : V → ℂ,
      D.pairingIntegrand f g (z - y) y = κ * (conj (f y) * g z) := by
  refine ⟨exp (-(D.symmetricPart (z - y) (z - y) / 2)) * conj (exp (-(D.form y y / 2))) *
      exp (-(D.form y (z - y) + D.form y y / 2)), by simp [exp_ne_zero], fun f g ↦ ?_⟩
  simp only [pairingIntegrand, twistedTranslate_apply, map_zero, zero_add, sub_add_cancel,
    map_mul]
  ring

/-! ### Means over the torus in lattice coordinates -/

section Torus

variable [FiniteDimensional ℂ V] [DiscreteTopology L] [IsZLattice ℝ L]

variable (L) in
/-- The real basis of `V` given by a `ℤ`-basis of the full lattice `L`. -/
private noncomputable def latticeBasis : Basis (Free.ChooseBasisIndex ℤ L) ℝ V :=
  (Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L

variable (L) in
/-- The mean of a function `G` on `V` over the torus `V ⧸ L`, as the integral over the unit cube in
the coordinates of `latticeBasis L`. -/
private noncomputable def torusMean (G : V → ℂ) : ℂ :=
  ∫ φ in univ.pi fun _ : Free.ChooseBasisIndex ℤ L ↦ Icc (0 : ℝ) 1,
    G ((latticeBasis L).equivFun.symm φ)

private theorem continuous_latticeBasis_equivFun_symm :
    Continuous (latticeBasis L).equivFun.symm :=
  LinearMap.continuous_of_finiteDimensional (latticeBasis L).equivFun.symm.toLinearMap

/-- A continuous function is integrable over the unit cube in lattice coordinates. -/
private theorem integrable_comp_latticeBasis {G : V → ℂ} (hG : Continuous G) :
    Integrable (fun φ ↦ G ((latticeBasis L).equivFun.symm φ))
      ((volume : Measure (Free.ChooseBasisIndex ℤ L → ℝ)).restrict
        (univ.pi fun _ ↦ Icc (0 : ℝ) 1)) :=
  (hG.comp continuous_latticeBasis_equivFun_symm).continuousOn.integrableOn_compact
    (isCompact_univ_pi fun _ ↦ isCompact_Icc)

/-- An `L`-periodic function, read in lattice coordinates, is periodic under `ℤ^ι`. -/
private theorem periodic_comp_latticeBasis {G : V → ℂ} (hG : ∀ (x : V) (l : L), G (x + l) = G x)
    (φ : Free.ChooseBasisIndex ℤ L → ℝ) (n : Free.ChooseBasisIndex ℤ L → ℤ) :
    G ((latticeBasis L).equivFun.symm (φ + fun i ↦ (n i : ℝ))) =
      G ((latticeBasis L).equivFun.symm φ) := by
  have h : (latticeBasis L).equivFun.symm (fun i ↦ (n i : ℝ)) =
      ((∑ i, n i • Free.chooseBasis ℤ L i : L) : V) := by
    simp [latticeBasis, Basis.equivFun_symm_apply, Basis.ofZLatticeBasis_apply,
      Int.cast_smul_eq_zsmul]
  rw [map_add, h, hG]

/-- **Translation invariance** of the mean of an `L`-periodic function. -/
private theorem torusMean_comp_add_right {G : V → ℂ} (hG : ∀ (x : V) (l : L), G (x + l) = G x)
    (v : V) : torusMean L (fun x ↦ G (x + v)) = torusMean L G := by
  have h (φ : Free.ChooseBasisIndex ℤ L → ℝ) : (latticeBasis L).equivFun.symm φ + v =
      (latticeBasis L).equivFun.symm (φ + (latticeBasis L).equivFun v) := by
    rw [map_add, LinearEquiv.symm_apply_apply]
  simp only [torusMean, h]
  exact UnitAddTorus.setIntegral_unitCube_comp_add_right
    (g := fun φ ↦ G ((latticeBasis L).equivFun.symm φ)) (periodic_comp_latticeBasis hG) _

/-- The mean is additive on continuous functions. -/
private theorem torusMean_add {G G' : V → ℂ} (hG : Continuous G) (hG' : Continuous G') :
    torusMean L (fun x ↦ G x + G' x) = torusMean L G + torusMean L G' :=
  integral_add (integrable_comp_latticeBasis hG) (integrable_comp_latticeBasis hG')

/-- The mean of a finite sum of continuous functions is the sum of the means. -/
private theorem torusMean_sum {κ : Type*} {s : Finset κ} {G : κ → V → ℂ}
    (hG : ∀ i, Continuous (G i)) :
    torusMean L (fun x ↦ ∑ i ∈ s, G i x) = ∑ i ∈ s, torusMean L (G i) :=
  integral_finsetSum s fun i _ ↦ integrable_comp_latticeBasis (hG i)

/-- The mean is homogeneous. -/
private theorem torusMean_const_mul (c : ℂ) (G : V → ℂ) :
    torusMean L (fun x ↦ c * G x) = c * torusMean L G :=
  integral_const_mul c _

/-- **Fourier uniqueness on the torus.** For a positive datum, a continuous `L`-periodic function
all of whose Fourier coefficients `∫ exp (2πi E (a, x)) G (x)`, `a ∈ L^⊥`, vanish is zero. -/
private theorem IsPositive.eq_zero_of_forall_torusMean_eq_zero (hD : D.IsPositive) {G : V → ℂ}
    (hc : Continuous G) (hG : ∀ (x : V) (l : L), G (x + l) = G x)
    (h : ∀ a ∈ D.riemannForm.dualSubmodule L,
      torusMean L (fun x ↦ exp (2 * π * I * D.riemannForm a x) * G x) = 0) :
    G = 0 := by
  classical
  set e := D.riemannForm.dualBasis hD.nondegenerate (latticeBasis L)
  have h_zero : (fun φ ↦ G ((latticeBasis L).equivFun.symm φ)) = 0 := by
    refine UnitAddTorus.eq_zero_of_forall_setIntegral_mFourier_mul_eq_zero
      (hc.comp continuous_latticeBasis_equivFun_symm) (periodic_comp_latticeBasis hG) fun n ↦ ?_
    -- The character of `a = -∑ⱼ nⱼ eⱼ` is the monomial `mFourier (-n)`.
    set a : V := ∑ j, ((-n j : ℤ) : ℝ) • e j
    have ha : a ∈ D.riemannForm.dualSubmodule L := by
      rw [D.riemannForm.dualSubmodule_eq_span_dualBasis_ofZLatticeBasis hD.nondegenerate L
        (Free.chooseBasis ℤ L)]
      exact Submodule.sum_mem _ fun j _ ↦ by
        rw [Int.cast_smul_eq_zsmul]
        exact zsmul_mem (Submodule.subset_span (mem_range_self j)) _
    have hE (j i : Free.ChooseBasisIndex ℤ L) :
        D.riemannForm (e j) (latticeBasis L i) = if i = j then 1 else 0 :=
      LinearMap.BilinForm.apply_dualBasis_left _ _ _ _
    have hn (i : Free.ChooseBasisIndex ℤ L) : D.riemannForm a (latticeBasis L i) = (-n) i := by
      simp only [a, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hE,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Pi.neg_apply]
    have h_char (φ : Free.ChooseBasisIndex ℤ L → ℝ) :=
      UnitAddTorus.exp_two_pi_I_mul_equivFun_symm_eq_mFourier (latticeBasis L) (D.riemannForm a)
        hn φ
    have := h a ha
    simp only [torusMean, h_char] at this
    exact this
  funext x
  have := congrFun h_zero ((latticeBasis L).equivFun x)
  rwa [LinearEquiv.symm_apply_apply] at this

end Torus

/-! ### The pairing of tuples of theta functions -/

section Pairing

variable [FiniteDimensional ℂ V] [DiscreteTopology L] [IsZLattice ℝ L]

/-- The pairing mean of theta functions is holomorphic in `b`: it is the integral of a weight
against a function that is jointly holomorphic in `b` and in parameters depending continuously on
the point of the cube. -/
private theorem differentiable_torusMean_pairingIntegrand {f g : V → ℂ} (hf : f ∈ D.thetaSpace)
    (hg : g ∈ D.thetaSpace) :
    Differentiable ℂ fun b ↦ torusMean L (D.pairingIntegrand f g b) := by
  set Q : Set (Free.ChooseBasisIndex ℤ L → ℝ) := univ.pi fun _ ↦ Icc (0 : ℝ) 1
  set X : (Free.ChooseBasisIndex ℤ L → ℝ) → V := fun φ ↦ (latticeBasis L).equivFun.symm φ
  have hX : Continuous X := continuous_latticeBasis_equivFun_symm
  -- Clamp the coordinates to the cube, so that the parameters stay in a compact set.
  set clamp : (Free.ChooseBasisIndex ℤ L → ℝ) → Free.ChooseBasisIndex ℤ L → ℝ :=
    fun φ i ↦ projIcc (0 : ℝ) 1 zero_le_one (φ i)
  have hclamp : Continuous clamp := continuous_pi fun i ↦
    continuous_subtypeVal.comp (continuous_projIcc.comp (continuous_apply i))
  have hclampQ (φ : Free.ChooseBasisIndex ℤ L → ℝ) : clamp φ ∈ Q := fun i _ ↦
    (projIcc (0 : ℝ) 1 zero_le_one (φ i)).property
  have hclamp_eq {φ} (hφ : φ ∈ Q) : clamp φ = φ :=
    funext fun i ↦ by simp [clamp, projIcc_of_mem _ (hφ i (mem_univ i))]
  set ψ : (Free.ChooseBasisIndex ℤ L → ℝ) → (V →L[ℂ] ℂ) × V := fun φ ↦ (-D.form (X φ), X φ)
  have hψ : Continuous ψ := by
    refine (Continuous.neg ?_).prodMk hX
    exact D.form.continuous.comp hX
  set w : (Free.ChooseBasisIndex ℤ L → ℝ) → ℂ := fun φ ↦
    conj (D.twistedTranslate (X (clamp φ)) f 0) * exp (-(D.form (X (clamp φ)) (X (clamp φ)) / 2))
  have hw : Continuous w := by
    have hf' := (differentiable_of_mem_thetaSpace hf).continuous
    simp only [w, twistedTranslate_apply]
    fun_prop
  set F : V × ((V →L[ℂ] ℂ) × V) → ℂ := fun p ↦
    exp (-(D.symmetricPart p.1 p.1 / 2) + p.2.1 p.1) * g (p.1 + p.2.2)
  have hF : Differentiable ℂ F := by
    have hg' := differentiable_of_mem_thetaSpace hg
    have hB₁ := D.symmetricPart.differentiable_apply_self
    have h1 : Differentiable ℂ fun p : V × ((V →L[ℂ] ℂ) × V) ↦ D.symmetricPart p.1 p.1 :=
      hB₁.comp differentiable_fst
    have h2 : Differentiable ℂ fun p : V × ((V →L[ℂ] ℂ) × V) ↦ p.2.1 p.1 :=
      (differentiable_fst.comp differentiable_snd).clm_apply differentiable_fst
    simp only [F]
    fun_prop
  have h_eq (b : V) : torusMean L (D.pairingIntegrand f g b) =
      ∫ φ in Q, w φ • F (b, ψ (clamp φ)) := by
    refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc) fun φ hφ ↦ ?_
    simp only [w, F, ψ, hclamp_eq hφ, pairingIntegrand, twistedTranslate_apply, smul_eq_mul,
      _root_.neg_apply, exp_add]
    rw [show -(D.form (X φ) b + D.form (X φ) (X φ) / 2) =
      -(D.form (X φ) (X φ) / 2) + -(D.form (X φ) b) by ring, exp_add]
    ring
  intro b
  rw [show (fun b ↦ torusMean L (D.pairingIntegrand f g b)) =
    fun b ↦ ∫ φ in Q, w φ • F (b, ψ (clamp φ)) from funext h_eq]
  have hint : Integrable w ((volume : Measure (Free.ChooseBasisIndex ℤ L → ℝ)).restrict Q) :=
    hw.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ ↦ isCompact_Icc)
  exact (analyticAt_integral_smul ((isCompact_univ_pi fun _ ↦ isCompact_Icc).image hψ)
    (hψ.comp hclamp) (fun φ ↦ mem_image_of_mem ψ (hclampQ φ))
    (fun y _ ↦ hF.differentiableOn.analyticAt_of_finiteDimensional univ_mem) hint).differentiableAt

/-- **Conjugate symmetry of the pairing mean.** -/
private theorem torusMean_pairingIntegrand_neg {f g : V → ℂ} (hf : f ∈ D.thetaSpace)
    (hg : g ∈ D.thetaSpace) (b : V) :
    torusMean L (D.pairingIntegrand g f (-b)) = conj (torusMean L (D.pairingIntegrand f g b)) := by
  rw [← torusMean_comp_add_right (pairingIntegrand_add hg hf (-b)) b]
  simp only [pairingIntegrand_neg_add, torusMean]
  exact integral_conj

/-- The pairing mean `∑ᵢ m (sᵢ, tᵢ, b)` of two tuples of functions. -/
private noncomputable def tupleMean {κ : Type*} [Fintype κ] (s t : κ → V → ℂ) (b : V) : ℂ :=
  ∑ i, torusMean L (D.pairingIntegrand (s i) (t i) b)

variable {κ : Type*} [Fintype κ]

/-- **Liouville's theorem for the pairing mean**: if `m (s, t, 0) = 0`, then `m (t, s, ·)`
vanishes identically, since `exp (-|m (t, s, b)|²)` is entire and bounded. -/
private theorem tupleMean_eq_zero_of_eq_zero {s t : κ → V → ℂ} (hs : ∀ i, s i ∈ D.thetaSpace)
    (ht : ∀ i, t i ∈ D.thetaSpace) (h0 : D.tupleMean s t 0 = 0) (b : V) :
    D.tupleMean t s b = 0 := by
  have h_conj (c : V) : D.tupleMean s t (-c) = conj (D.tupleMean t s c) := by
    simp only [tupleMean, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ torusMean_pairingIntegrand_neg (ht i) (hs i) c
  have h_diff (u v : κ → V → ℂ) (hu : ∀ i, u i ∈ D.thetaSpace) (hv : ∀ i, v i ∈ D.thetaSpace) :
      Differentiable ℂ (D.tupleMean u v) :=
    Differentiable.fun_sum fun i _ ↦ differentiable_torusMean_pairingIntegrand (hu i) (hv i)
  set h : V → ℂ := fun c ↦ exp (-(D.tupleMean s t (-c) * D.tupleMean t s c))
  have hh : Differentiable ℂ h :=
    (((h_diff s t hs ht).comp differentiable_id.neg).mul (h_diff t s ht hs)).neg.cexp
  have h_norm (c : V) : ‖h c‖ = Real.exp (-‖D.tupleMean t s c‖ ^ 2) := by
    simp only [h, h_conj, norm_exp, conj_mul', neg_re]
    norm_cast
  have h_bdd : Bornology.IsBounded (range h) :=
    isBounded_iff_forall_norm_le.mpr ⟨1, forall_mem_range.mpr fun c ↦ by
      rw [h_norm]
      exact Real.exp_le_one_iff.mpr (by nlinarith [norm_nonneg (D.tupleMean t s c)])⟩
  have h_const := hh.apply_eq_apply_of_bounded h_bdd b 0
  have h0' : D.tupleMean t s 0 = 0 := by
    have := h_conj 0
    rw [neg_zero, h0] at this
    simpa using this.symm
  have := congrArg norm h_const
  rw [h_norm, h_norm, h0', norm_zero] at this
  simpa using this

/-- **The key vanishing statement.** For a positive datum and tuples `s`, `t` of theta functions, if
`m (U_a s, t, 0) = 0` for every `a ∈ L^⊥`, then `∑ᵢ conj (tᵢ y) sᵢ = 0` for every `y`. -/
private theorem IsPositive.sum_conj_smul_eq_zero (hD : D.IsPositive) {s t : κ → V → ℂ}
    (hs : ∀ i, s i ∈ D.thetaSpace) (ht : ∀ i, t i ∈ D.thetaSpace)
    (h : ∀ a ∈ D.riemannForm.dualSubmodule L,
      D.tupleMean (fun i ↦ D.twistedTranslate a (s i)) t 0 = 0) (y : V) :
    ∑ i, conj (t i y) • s i = 0 := by
  -- For each `b`, the function `x ↦ ∑ᵢ J (tᵢ, sᵢ, b) (x)` has vanishing Fourier coefficients.
  have h_zero (b : V) : (fun x ↦ ∑ i, D.pairingIntegrand (t i) (s i) b x) = 0 := by
    have hcont (i : κ) : Continuous (D.pairingIntegrand (t i) (s i) b) :=
      continuous_pairingIntegrand (differentiable_of_mem_thetaSpace (ht i)).continuous
        (differentiable_of_mem_thetaSpace (hs i)).continuous b
    refine hD.eq_zero_of_forall_torusMean_eq_zero (continuous_finsetSum _ fun i _ ↦ hcont i)
      (fun x l ↦ Finset.sum_congr rfl fun i _ ↦ pairingIntegrand_add (ht i) (hs i) b x l)
      fun a ha ↦ ?_
    obtain ⟨κ₀, hκ₀, hκ⟩ := D.exists_pairingIntegrand_twistedTranslate_right a b
    have hchar : Continuous fun x ↦ exp (2 * π * I * D.riemannForm a x) := by
      simp only [riemannForm_apply]
      fun_prop
    have hfun (i : κ) : D.pairingIntegrand (t i) (D.twistedTranslate a (s i)) (b - a) =
        fun x ↦ κ₀ * (exp (2 * π * I * D.riemannForm a x) * D.pairingIntegrand (t i) (s i) b x) :=
      funext (hκ (t i) (s i))
    have h_liouville := D.tupleMean_eq_zero_of_eq_zero
      (fun i ↦ twistedTranslate_mem_thetaSpace_of_mem_dualSubmodule ha (hs i)) ht (h a ha) (b - a)
    simp only [tupleMean, hfun, torusMean_const_mul, ← Finset.mul_sum] at h_liouville
    rw [← torusMean_sum (G := fun i x ↦ exp (2 * π * I * D.riemannForm a x) *
      D.pairingIntegrand (t i) (s i) b x) fun i ↦ hchar.mul (hcont i)] at h_liouville
    simp only [← Finset.mul_sum] at h_liouville
    exact (mul_eq_zero.mp h_liouville).resolve_left hκ₀
  -- Evaluate at `x = y`, `b = z - y`.
  funext z
  obtain ⟨κ₀, hκ₀, hκ⟩ := D.exists_pairingIntegrand_sub_self (L := L) y z
  have := congrFun (h_zero (z - y)) y
  simp only [hκ, ← Finset.mul_sum, Pi.zero_apply, mul_eq_zero, hκ₀, false_or] at this
  simpa [Finset.sum_apply] using this

end Pairing

/-! ### Frobenius' dimension formula -/

section Dimension

variable [FiniteDimensional ℂ V] [DiscreteTopology L] [IsZLattice ℝ L]

variable (D) in
/-- The quotient `L^⊥ / L` of the dual of `L` for the Riemann form by `L`. -/
abbrev DualQuotient : Type _ :=
  D.riemannForm.dualSubmodule L ⧸ (L.submoduleOf (D.riemannForm.dualSubmodule L)).toAddSubgroup

/-- For a nondegenerate Riemann form, `L` has finite index in its dual `L^⊥`. -/
theorem finite_dualQuotient (hE : D.riemannForm.Nondegenerate) : Finite D.DualQuotient :=
  D.riemannForm.finite_quotient_dualSubmodule hE L D.le_dualSubmodule

/-- The map `t ↦ (q ↦ m (U_q s, t, 0))` from tuples of theta functions to the functions on
`L^⊥ / L`, for a tuple `s` of theta functions. -/
private noncomputable def dualPairing {κ : Type*} [Fintype κ] (s : κ → D.thetaSpace) :
    (κ → D.thetaSpace) →ₗ[ℂ] (D.DualQuotient → ℂ) where
  toFun t q := D.tupleMean (fun i ↦ D.twistedTranslate (q.out : V) (s i)) (fun i ↦ t i) 0
  map_add' t t' := by
    funext q
    have hc (f : D.thetaSpace) : Continuous (f : V → ℂ) :=
      (differentiable_of_mem_thetaSpace f.property).continuous
    have hT (i) : Continuous (D.twistedTranslate (q.out : V) (s i)) :=
      hc ⟨_, twistedTranslate_mem_thetaSpace_of_mem_dualSubmodule q.out.property (s i).property⟩
    simp only [tupleMean, Pi.add_apply, Submodule.coe_add, pairingIntegrand_add_right,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ torusMean_add
      (continuous_pairingIntegrand (hT i) (hc _) 0) (continuous_pairingIntegrand (hT i) (hc _) 0)
  map_smul' c t := by
    funext q
    simp only [tupleMean, Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, smul_eq_mul,
      Finset.mul_sum, pairingIntegrand_smul_right, torusMean_const_mul]

/-- For a positive datum and a linearly independent tuple `s` of theta functions, the map
`t ↦ (q ↦ m (U_q s, t, 0))` is injective. -/
private theorem IsPositive.injective_dualPairing (hD : D.IsPositive) {κ : Type*} [Fintype κ]
    {s : κ → D.thetaSpace} (hs : LinearIndependent ℂ s) : Function.Injective (dualPairing s) := by
  refine (injective_iff_map_eq_zero _).mpr fun t ht ↦ ?_
  -- First `m (U_a s, t, 0) = 0` for every `a ∈ L^⊥`, not only for the representatives.
  have h (a : V) (ha : a ∈ D.riemannForm.dualSubmodule L) :
      D.tupleMean (fun i ↦ D.twistedTranslate a (s i)) (fun i ↦ t i) 0 = 0 := by
    obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_add
      (L.submoduleOf (D.riemannForm.dualSubmodule L)).toAddSubgroup ⟨a, ha⟩
    have h0 := congrFun ht (QuotientAddGroup.mk ⟨a, ha⟩)
    set l' : L := ⟨((l : D.riemannForm.dualSubmodule L) : V), l.property⟩
    have h_out (i : κ) : D.twistedTranslate
        ((QuotientAddGroup.mk ⟨a, ha⟩ : D.DualQuotient).out : V) (s i) =
          (exp (π * I * D.riemannForm a l') * D.semichar l') • D.twistedTranslate a (s i) := by
      rw [hl, Submodule.coe_add]
      exact twistedTranslate_add_eq_smul_of_mem_thetaSpace (s i).property a l'
    simp only [dualPairing, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, tupleMean, h_out,
      pairingIntegrand_smul_left, torusMean_const_mul, ← Finset.mul_sum] at h0
    refine (mul_eq_zero.mp h0).resolve_left ?_
    simp [exp_ne_zero]
  -- Hence `∑ᵢ conj (tᵢ y) sᵢ = 0`, and `t = 0` by independence.
  ext i y
  have h_sum := hD.sum_conj_smul_eq_zero (fun i ↦ (s i).property) (fun i ↦ (t i).property) h y
  have h_sum' : ∑ i, conj ((t i : V → ℂ) y) • s i = 0 :=
    Subtype.ext (by simpa using h_sum)
  simpa using Fintype.linearIndependent_iff.mp hs _ h_sum' i

/-- **Finiteness**: the theta functions of a positive datum form a finite-dimensional space. -/
theorem IsPositive.finiteDimensional_thetaSpace (hD : D.IsPositive) :
    FiniteDimensional ℂ D.thetaSpace := by
  obtain ⟨f, hf, hf_ne⟩ := hD.exists_mem_thetaSpace_ne_zero
  have := finite_dualQuotient hD.nondegenerate
  have h_ind : LinearIndependent ℂ ![(⟨f, hf⟩ : D.thetaSpace)] := by
    simpa [LinearIndependent.pair_iff] using hf_ne
  have := Module.Finite.of_injective _ (hD.injective_dualPairing h_ind)
  exact Module.Finite.pi_iff.mp this 0

/-- The theta functions of a positive datum form a space of positive dimension. -/
theorem IsPositive.finrank_thetaSpace_pos (hD : D.IsPositive) : 0 < finrank ℂ D.thetaSpace := by
  obtain ⟨f, hf, hf_ne⟩ := hD.exists_mem_thetaSpace_ne_zero
  have := hD.finiteDimensional_thetaSpace
  exact finrank_pos_iff_exists_ne_zero.mpr ⟨⟨f, hf⟩, by simpa using hf_ne⟩

/-- **Independence of the translations.** For a positive datum, the twisted translations by
representatives of the classes of `L^⊥ / L` are linearly independent endomorphisms of the space of
theta functions. -/
theorem IsPositive.linearIndependent_twistedTranslateEnd_out (hD : D.IsPositive) :
    LinearIndependent ℂ fun q : D.DualQuotient ↦ D.twistedTranslateEnd q.out := by
  -- `U_q` is an eigenvector of conjugation `A ↦ U_(-y) A U_y` by `U_y`, `y ∈ L^⊥`, for the
  -- character `y ↦ exp (2πi E (y, q))`, and distinct classes give distinct characters.
  let e (q : D.DualQuotient) (y : D.riemannForm.dualSubmodule L) : ℂ :=
    exp (2 * π * I * D.riemannForm y q.out)
  have e_inj : e.Injective := by
    intro q q' h_eq
    -- `E (y, q' - q) ∈ ℤ` for every `y ∈ L^⊥`, so `q' - q` lies in the dual of `L^⊥`, which is `L`.
    have h_mem : ((q'.out : V) - q.out) ∈ L := by
      refine (D.riemannForm.dualSubmodule_flip_dualSubmodule_of_isZLattice hD.nondegenerate L).le
        fun y hy ↦ ?_
      obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.mp (congrFun h_eq ⟨y, hy⟩)
      have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      have hk' : ((D.riemannForm y q.out : ℝ) : ℂ) = (D.riemannForm y q'.out : ℝ) + k :=
        mul_left_cancel₀ h2 (by linear_combination hk)
      have hk'' : D.riemannForm y q.out = D.riemannForm y q'.out + k := by exact_mod_cast hk'
      refine Submodule.mem_one.mpr ⟨-k, ?_⟩
      rw [algebraMap_int_eq, eq_intCast, LinearMap.BilinForm.flip_apply, map_sub, Int.cast_neg,
        hk'']
      ring
    refine Quotient.out_equiv_out.mp (QuotientAddGroup.leftRel_apply.mpr
      ((Submodule.mem_submoduleOf_toAddSubgroup _).mpr ?_))
    simpa [neg_add_eq_sub] using h_mem
  have h_eigen (q : D.DualQuotient) (y : D.riemannForm.dualSubmodule L) :
      D.twistedTranslateEnd (-y) * D.twistedTranslateEnd q.out * D.twistedTranslateEnd y =
        e q y • D.twistedTranslateEnd q.out := by
    rw [twistedTranslateEnd_mul, smul_mul_assoc, twistedTranslateEnd_mul, smul_smul,
      neg_add_cancel_comm]
    congr 1
    simp only [e, ← exp_add, Submodule.coe_neg, Submodule.coe_add, map_neg, map_add,
      LinearMap.neg_apply, LinearMap.add_apply, riemannForm_self, D.riemannForm_swap (q.out : V)]
    congr 1
    push_cast
    ring
  have h_ne (q : D.DualQuotient) : D.twistedTranslateEnd q.out ≠ 0 := by
    obtain ⟨f, hf, hf_ne⟩ := hD.exists_mem_thetaSpace_ne_zero
    obtain ⟨w, hw⟩ := Function.ne_iff.mp hf_ne
    intro h_zero
    have h1 := congrArg (fun A : Module.End ℂ D.thetaSpace ↦ (A ⟨f, hf⟩ : V → ℂ) (w - q.out))
      h_zero
    simp only [coe_twistedTranslateEnd_apply, twistedTranslate_apply, sub_add_cancel,
      LinearMap.zero_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at h1
    exact hw ((mul_eq_zero.mp h1).resolve_left (exp_ne_zero _))
  exact linearIndependent_of_forall_mul_mul_eq_smul e_inj h_ne h_eigen

/-- For a positive datum, the index of `L` in its dual is the dimension of the endomorphisms of the
space of theta functions. -/
theorem IsPositive.relIndex_eq_finrank_end (hD : D.IsPositive) :
    L.toAddSubgroup.relIndex (D.riemannForm.dualSubmodule L).toAddSubgroup =
      finrank ℂ (Module.End ℂ D.thetaSpace) := by
  have := finite_dualQuotient hD.nondegenerate
  have := hD.finiteDimensional_thetaSpace
  have : Fintype D.DualQuotient := Fintype.ofFinite _
  have card_le : Fintype.card D.DualQuotient ≤ finrank ℂ (Module.End ℂ D.thetaSpace) :=
    hD.linearIndependent_twistedTranslateEnd_out.fintype_card_le_finrank
  have h_embed := LinearMap.finrank_le_finrank_of_injective
    (hD.injective_dualPairing (Module.finBasis ℂ D.thetaSpace).linearIndependent)
  have le_card : finrank ℂ (Module.End ℂ D.thetaSpace) ≤ Fintype.card D.DualQuotient := by
    simpa [Module.finrank_linearMap, Module.finrank_pi_fintype,
      Module.finrank_fintype_fun_eq_card] using h_embed
  rw [← Submodule.natCard_quotient_submoduleOf, Nat.card_eq_fintype_card]
  exact card_le.antisymm le_card

/-- **The translations span the endomorphisms.** For a positive datum, the twisted translations
by the dual lattice span the endomorphisms of the space of theta functions. -/
theorem IsPositive.span_range_twistedTranslateEnd_eq_top (hD : D.IsPositive) :
    Submodule.span ℂ (range D.twistedTranslateEnd) = ⊤ := by
  have := finite_dualQuotient hD.nondegenerate
  have := hD.finiteDimensional_thetaSpace
  have : Fintype D.DualQuotient := Fintype.ofFinite _
  have card_eq : Fintype.card D.DualQuotient = finrank ℂ (Module.End ℂ D.thetaSpace) := by
    rw [← Nat.card_eq_fintype_card]
    exact hD.relIndex_eq_finrank_end
  -- Naming the space `End Θ` lets its additive group be synthesized before unification.
  exact LinearIndependent.span_range_eq_top_of_comp (V := Module.End ℂ D.thetaSpace)
    (A := D.twistedTranslateEnd) (r := fun q : D.DualQuotient ↦ q.out)
    hD.linearIndependent_twistedTranslateEnd_out card_eq

/-- **Frobenius' dimension formula.** For an Appell–Humbert datum with positive Riemann form, the
square of the dimension of the space of theta functions is the index of `L` in its dual for the
Riemann form: `(dim Θ)² = [L^⊥ : L]`. -/
theorem IsPositive.finrank_thetaSpace_sq (hD : D.IsPositive) :
    finrank ℂ D.thetaSpace ^ 2 =
      L.toAddSubgroup.relIndex (D.riemannForm.dualSubmodule L).toAddSubgroup := by
  have := hD.finiteDimensional_thetaSpace
  rw [hD.relIndex_eq_finrank_end, Module.finrank_linearMap, sq]

/-- **Irreducibility.** For a positive datum, a complex space of functions that contains the
twisted translates `U_a f`, `a ∈ L^⊥`, of one nonzero theta function `f` contains every theta
function. -/
theorem IsPositive.thetaSpace_le_of_twistedTranslate_mem (hD : D.IsPositive) {f : V → ℂ}
    (hf : f ∈ D.thetaSpace) (hf_ne : f ≠ 0) (S : Submodule ℂ (V → ℂ))
    (hS : ∀ a ∈ D.riemannForm.dualSubmodule L, D.twistedTranslate a f ∈ S) :
    D.thetaSpace ≤ S := by
  -- The endomorphism `g ⊗ ℓ` with `ℓ f = 1` maps `f` to `g`, and lies in the span of the
  -- translations, which map `f` into `S`.
  intro g hg
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual ℂ (V → ℂ), ℓ f = 1 :=
    Module.Projective.exists_dual_eq_one ℂ hf_ne
  let A : Module.End ℂ D.thetaSpace := (ℓ.domRestrict D.thetaSpace).smulRight ⟨g, hg⟩
  have hA : A ⟨f, hf⟩ = ⟨g, hg⟩ := by simp [A, hℓ]
  let W : Submodule ℂ (Module.End ℂ D.thetaSpace) :=
    (S.submoduleOf D.thetaSpace).comap (LinearMap.applyₗ ⟨f, hf⟩)
  have hW (B : Module.End ℂ D.thetaSpace) : B ∈ W ↔ ((B ⟨f, hf⟩ : D.thetaSpace) : V → ℂ) ∈ S := by
    rw [Submodule.mem_comap, LinearMap.applyₗ_apply_apply, Submodule.submoduleOf,
      Submodule.mem_comap, Submodule.subtype_apply]
  have hA_mem : A ∈ W := Submodule.mem_span.mp (hD.span_range_twistedTranslateEnd_eq_top.ge
    Submodule.mem_top) W (range_subset_iff.mpr fun a ↦ (hW _).mpr (by
      rw [coe_twistedTranslateEnd_apply]
      exact hS a a.property))
  rwa [hW, hA] at hA_mem

/-- **Schur's lemma.** For a positive datum, an endomorphism of the space of theta functions that
commutes with the twisted translations by the dual lattice is a scalar. -/
theorem IsPositive.exists_eq_smul_one_of_commute (hD : D.IsPositive)
    {T : Module.End ℂ D.thetaSpace}
    (hT : ∀ a : D.riemannForm.dualSubmodule L, Commute (D.twistedTranslateEnd a) T) :
    ∃ c : ℂ, T = c • 1 := by
  have central (A : Module.End ℂ D.thetaSpace) : Commute A T :=
    Commute.span_left (forall_mem_range.mpr hT) A
      (hD.span_range_twistedTranslateEnd_eq_top.ge Submodule.mem_top)
  exact (Algebra.IsCentral.mem_center_iff ℂ).mp
    (Subalgebra.mem_center_iff.mpr fun A ↦ (central A).eq)

/-- For a nondegenerate Riemann form, the index `N = [L^⊥ : L]` is positive and `N L^⊥ ⊆ L`. -/
theorem relIndex_ne_zero_and_nsmul_relIndex_mem (hE : D.riemannForm.Nondegenerate) :
    L.toAddSubgroup.relIndex (D.riemannForm.dualSubmodule L).toAddSubgroup ≠ 0 ∧
      ∀ a ∈ D.riemannForm.dualSubmodule L,
        L.toAddSubgroup.relIndex (D.riemannForm.dualSubmodule L).toAddSubgroup • a ∈ L :=
  ⟨D.riemannForm.relIndex_dualSubmodule_ne_zero hE L D.le_dualSubmodule,
    fun _ ha ↦ L.toAddSubgroup.nsmul_relIndex_mem ha⟩

end Dimension

end TauCeti.AppellHumbertData
