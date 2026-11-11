/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Polynomial.Basic

/-!
# Joint polynomial models from finite linear presentations

A polynomial function space need not be presented in monomial coordinates. Given a linear
map `T` from a finite coordinate space to tuples of input polynomials, and parameter
polynomials `Q` for those coordinates, `polynomialFromLinearPresentation Q T` assembles a
jointly polynomial model. Specializing and extracting its input polynomials recovers
`T (fun i => eval w (Q i))`, including when specialization cancels terms.

`exists_polynomialRealization_of_linear_coordinates` applies this to a coefficient map into
any module supplied with finite linear coordinates and a linear polynomial presentation.
It gives both the realization equation and the extraction round trip. Neither injectivity
of the presentation nor an infinite scalar field is needed for assembly. When evaluation
of the presentation is faithful, the image and fibre comparisons in
`TauCeti.Geometry.Neuromanifold.Basic` apply to the resulting realization equation.

The finite coefficient-space viewpoint follows Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3.1.
The construction uses Mathlib's polynomial renaming and finite-coordinate linear expansion
`LinearMap.pi_apply_eq_sum_univ`.
-/

public section

noncomputable section

namespace TauCeti.Neuromanifold

open MvPolynomial

variable {K W X J I : Type*} [CommSemiring K] [Fintype I]

/-- Assemble a joint polynomial tuple from polynomial parameter coordinates in a finite
linear presentation of input polynomials. The presentation may have a kernel. -/
def polynomialFromLinearPresentation (Q : I → MvPolynomial W K)
    (T : (I → K) →ₗ[K] (J → MvPolynomial X K)) :
    J → MvPolynomial (W ⊕ X) K := by
  classical
  exact fun j => ∑ i, rename Sum.inl (Q i) * rename Sum.inr (T (Pi.single i 1) j)

open scoped Classical in
/-- Each output is the linear combination of the presentation's coordinate polynomials,
with the parameter polynomials as coefficients. -/
theorem polynomialFromLinearPresentation_apply (Q : I → MvPolynomial W K)
    (T : (I → K) →ₗ[K] (J → MvPolynomial X K)) (j : J) :
    polynomialFromLinearPresentation Q T j =
      ∑ i, rename Sum.inl (Q i) * rename Sum.inr (T (Pi.single i 1) j) := (rfl)

/-- Specializing the collected input polynomial recovers the supplied linear presentation
of the evaluated parameter coordinates. -/
theorem map_inputPolynomial_polynomialFromLinearPresentation (Q : I → MvPolynomial W K)
    (T : (I → K) →ₗ[K] (J → MvPolynomial X K)) (w : W → K) (j : J) :
    map (eval w) (inputPolynomial (polynomialFromLinearPresentation Q T) j) =
      T (fun i => eval w (Q i)) j := by
  classical
  have hinr (q : MvPolynomial W K) :
      sumAlgEquiv K X W (rename Sum.inr q) = C q :=
    AlgHom.congr_fun (sumAlgEquiv_comp_rename_inr K X W) q
  have hinl (q : MvPolynomial X K) :
      sumAlgEquiv K X W (rename Sum.inl q) = map C q :=
    AlgHom.congr_fun (sumAlgEquiv_comp_rename_inl K X W) q
  have hC : (eval w).comp (C : K →+* MvPolynomial W K) = RingHom.id K := by
    ext
    simp
  rw [LinearMap.pi_apply_eq_sum_univ T]
  simp [inputPolynomial_def, polynomialFromLinearPresentation_apply, rename_rename,
    Function.comp_def, hinr, hinl, map_map, hC, MvPolynomial.map_id,
    ← Pi.single_apply, Pi.single_comm, Algebra.smul_def]

/-- The assembled tuple realizes evaluation of the supplied linear polynomial presentation. -/
theorem polynomialRealization_polynomialFromLinearPresentation (Q : I → MvPolynomial W K)
    (T : (I → K) →ₗ[K] (J → MvPolynomial X K)) :
    polynomialRealization (polynomialFromLinearPresentation Q T) =
      fun w x j => eval x (T (fun i => eval w (Q i)) j) := by
  funext w x j
  rw [← eval₂_inputPolynomial, ← eval_map,
    map_inputPolynomial_polynomialFromLinearPresentation]

/-- Extraction after assembly returns the presented input polynomials. Only the inferred
degree bound is forgotten; no coefficients are discarded. -/
theorem polynomialCoefficientMap_polynomialFromLinearPresentation_coe [Fintype J]
    (Q : I → MvPolynomial W K) (T : (I → K) →ₗ[K] (J → MvPolynomial X K))
    (w : W → K) (j : J) :
    (polynomialCoefficientMap (polynomialFromLinearPresentation Q T) w j : MvPolynomial X K) =
      T (fun i => eval w (Q i)) j := by
  rw [polynomialCoefficientMap_coe, map_inputPolynomial_polynomialFromLinearPresentation]

omit [Fintype I] in
/-- A coefficient map polynomial in any supplied finite linear coordinates admits a joint
polynomial model. Evaluation realizes the supplied map, and extraction recovers its original
polynomial presentation, not merely the same function on inputs. -/
theorem exists_polynomialRealization_of_linear_coordinates [Finite I] [Fintype J]
    {V : Type*} [AddCommMonoid V] [Module K V]
    (c : (W → K) → V) (e : V ≃ₗ[K] (I → K))
    (T : V →ₗ[K] (J → MvPolynomial X K)) (Q : I → MvPolynomial W K)
    (hQ : ∀ w i, eval w (Q i) = e (c w) i) :
    ∃ P : J → MvPolynomial (W ⊕ X) K,
      polynomialRealization P = (fun v x j => eval x (T v j)) ∘ c ∧
        ∀ w j, (polynomialCoefficientMap P w j : MvPolynomial X K) = T (c w) j := by
  let := Fintype.ofFinite I
  have hcoords (w : W → K) : (fun i => eval w (Q i)) = e (c w) := funext (hQ w)
  refine ⟨polynomialFromLinearPresentation Q (T.comp e.symm.toLinearMap), ?_, ?_⟩
  · rw [polynomialRealization_polynomialFromLinearPresentation]
    funext w x j
    simp [hcoords]
  · intro w j
    rw [polynomialCoefficientMap_polynomialFromLinearPresentation_coe]
    simp [hcoords]

end TauCeti.Neuromanifold
