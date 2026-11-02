/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import TauCeti.Analysis.Polynomial.SymmetricPower
import Mathlib.Analysis.Analytic.Constructions

/-!
# Adjoining a fixed root in elementary-symmetric coordinates

Adjoining `a` to an unordered root tuple multiplies its monic polynomial by `X - C a`.
In lower-coefficient coordinates, this is an affine map from `n`-space to `(n + 1)`-space.
It is analytic and its derivative is injective everywhere, including at tuples already
containing `a`. These are the model-space calculations for the basepoint divisor in the
symmetric power of a complex curve.

The analytic left inverse is synthetic division by the fixed monic factor, followed by reading
the lower coefficients. It uses Mathlib's `Polynomial.divByMonicHom`; both multiplication and
division are linear in the polynomial, so their action on monic lower coefficients is analytic
by `TauCeti.Polynomial.analyticAt_linearMap_monicOfCoeff`.

## Main declarations

* `TauCeti.Sym.analyticAt_coeffEquiv_cons_coeffEquiv_symm`: insertion is analytic in coefficients.
* `TauCeti.Sym.fderiv_coeffEquiv_cons_coeffEquiv_symm_injective`: its differential is injective.
-/

public section

open Polynomial

namespace TauCeti.Sym

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsAlgClosed 𝕜] {n : ℕ}

/-- Adjoining a fixed root is analytic in elementary-symmetric coordinates, including at tuples
where the added point is already present: on monic polynomials it is multiplication by `X - C a`,
which is linear in the polynomial and affine in its lower coefficients. -/
theorem analyticAt_coeffEquiv_cons_coeffEquiv_symm (a : 𝕜) (c₀ : Fin n → 𝕜) :
    AnalyticAt 𝕜 (fun c => coeffEquiv 𝕜 (n + 1) (Sym.cons a ((coeffEquiv 𝕜 n).symm c))) c₀ := by
  refine AnalyticAt.pi fun i => ?_
  simpa only [coeffEquiv_apply_eq_coeff, toMonic_cons, toMonic_coeffEquiv_symm,
    LinearMap.comp_apply, Polynomial.lcoeff_apply, LinearMap.mulLeft_apply] using
    Polynomial.analyticAt_linearMap_monicOfCoeff
      ((Polynomial.lcoeff 𝕜 i).comp (LinearMap.mulLeft 𝕜 (X - C a))) c₀

/-- The derivative of fixed-root insertion in coefficient coordinates is injective everywhere,
even at repeated roots. Polynomial division by the monic factor `X - C a` provides an analytic
left inverse on the whole coefficient space. -/
theorem fderiv_coeffEquiv_cons_coeffEquiv_symm_injective (a : 𝕜) (c₀ : Fin n → 𝕜) :
    Function.Injective (fderiv 𝕜
      (fun c => coeffEquiv 𝕜 (n + 1) (Sym.cons a ((coeffEquiv 𝕜 n).symm c))) c₀) := by
  let F : (Fin n → 𝕜) → (Fin (n + 1) → 𝕜) :=
    fun c => coeffEquiv 𝕜 (n + 1) (Sym.cons a ((coeffEquiv 𝕜 n).symm c))
  let R : (Fin (n + 1) → 𝕜) → (Fin n → 𝕜) :=
    fun d i => ((Polynomial.monicOfCoeff d) /ₘ (X - C a)).coeff i
  have hR (d : Fin (n + 1) → 𝕜) : AnalyticAt 𝕜 R d := by
    refine AnalyticAt.pi fun i => ?_
    simpa only [R, LinearMap.comp_apply, Polynomial.lcoeff_apply,
      Polynomial.divByMonicHom_apply] using
      Polynomial.analyticAt_linearMap_monicOfCoeff
        ((Polynomial.lcoeff 𝕜 i).comp (Polynomial.divByMonicHom (X - C a))) d
  have hRF : R ∘ F = id := by
    funext c i
    simp only [Function.comp_apply, R, F]
    rw [← toMonic_coeffEquiv_symm, Equiv.symm_apply_apply, toMonic_cons,
      Polynomial.mul_divByMonic_cancel_left _ (monic_X_sub_C a),
      toMonic_coeffEquiv_symm, Polynomial.coeff_monicOfCoeff]
    rfl
  have hderiv := ((hR (F c₀)).differentiableAt.hasFDerivAt.comp c₀
    (analyticAt_coeffEquiv_cons_coeffEquiv_symm a c₀).differentiableAt.hasFDerivAt).fderiv
  rw [hRF, fderiv_id] at hderiv
  exact Function.LeftInverse.injective fun v =>
    (congrArg (fun L => L v) hderiv).symm

end TauCeti.Sym
