/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MvPolynomial
public import TauCeti.Geometry.RealAlgebraic.Projection.Collins
public import TauCeti.Geometry.RealAlgebraic.Stack.Delineation
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Collins delineability

Let `F` be a finite family of polynomials in one distinguished variable over a commutative ring
`R`, and let `φ x : R →+* ℝ` be a family of specializations parametrized by a preconnected space
`X`. If the elements of the Collins projection `F.collinsProjection` depend continuously on `x`
after specialization, and the set of those that vanish does not depend on `x`, then the
specialized family `p.map (φ x)`, `p ∈ F`, has a delineation over `X`: a common stack of
continuous, strictly ordered root functions on whose sections and sectors every member is
sign-invariant (`TauCeti.Delineation`).

The main case is `R = MvPolynomial (Fin n) A` for a coefficient map `φ : A →+* ℝ`, specialized at
the points `x` of a preconnected set `S ⊆ ℝⁿ` by `MvPolynomial.eval₂Hom φ x`. This is Collins'
delineability theorem: if every element of the projection is sign-invariant on `S`, the family is
delineable over `S`. Taking `A = ℝ` and `φ = RingHom.id ℝ` gives real families; taking `A = ℤ`
and `φ = Int.castRingHom ℝ` gives integer families whose projection is computed over `ℤ`.
Nothing is assumed about the formal leading coefficients, which may vanish on `S`, nor are
nullified members excluded: the reducta in the projection account for both. No semialgebraicity of
`S` is needed.
Only the zero pattern of the projection is used, not its signs.

## Main results

* `TauCeti.nonempty_delineation_of_collinsProjection`: a family of specializations along which the
  Collins projection is continuous and has a constant zero pattern delineates the family.
* `TauCeti.nonempty_delineation_of_signInvariant_collinsProjection`: **Collins delineability**
  over a preconnected subset of `ℝⁿ` on which the projection is sign-invariant.
* `TauCeti.nonempty_delineation_image_finSuccEquiv_map_of_signInvariant_collinsProjection`:
  delineability after mapping the coefficients of a multivariate family injectively into `ℝ`.

## References

* G. E. Collins, *Quantifier elimination for real closed fields by cylindrical algebraic
  decomposition*, Lecture Notes in Computer Science 33 (1975), 134–183.
* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Section 5.1 (Theorem 5.16) and Chapter 11.
* D. Jovanović, *Solving Non-Linear Arithmetic*, dissertation, New York University, 2012,
  Definition 2.5 and Theorem 2.6.
-/

public section

open Polynomial

namespace TauCeti

section General

variable {R X : Type*} [CommRing R] [TopologicalSpace X] [PreconnectedSpace X] {F : Finset R[X]}

/-- **Delineability from the Collins projection.** Let `φ x : R →+* ℝ` be specializations
parametrized by a preconnected space `X`. If every element of the Collins projection of `F`
specializes continuously in `x`, and whether it specializes to zero does not depend on `x`, then
the specialized family `p.map (φ x)`, `p ∈ F`, has a delineation over `X`. -/
theorem nonempty_delineation_of_collinsProjection (φ : X → R →+* ℝ)
    (hcont : ∀ a ∈ F.collinsProjection, Continuous fun x ↦ φ x a)
    (hzero : ∀ a ∈ F.collinsProjection, ∀ x y, φ x a = 0 ↔ φ y a = 0) :
    Nonempty (Delineation fun (p : F) x ↦ p.1.map (φ x)) := by
  refine nonempty_delineation (fun p i ↦ ?_) (fun p ↦ ?_)
    (fun p x y ↦ Finset.natDegree_map_eq_of_collinsProjection (fun a ha ↦ hzero a ha x y) p.2)
    (fun p x y ↦ ?_)
    fun p q _ x y ↦
      Finset.natDegree_gcd_map_eq_of_collinsProjection (fun a ha ↦ hzero a ha x y) p.2 q.2
  · -- the coefficients up to the degree are elements of the projection, the others vanish
    simp only [coeff_map]
    rcases le_or_gt i p.1.natDegree with hi | hi
    · exact hcont _ (Finset.coeff_mem_collinsProjection p.2 p.1.self_mem_reducta hi)
    · simpa [coeff_eq_zero_of_natDegree_lt hi] using continuous_const
  · by_cases h : ∃ x, p.1.map (φ x) = 0
    · obtain ⟨x, hx⟩ := h
      exact .inl fun y ↦
        (Finset.map_eq_zero_iff_of_collinsProjection (fun a ha ↦ hzero a ha x y) p.2).1 hx
    · exact .inr fun x hx ↦ h ⟨x, hx⟩
  · -- count distinct complex roots after composing with the injective map `ℝ → ℂ`
    have hzero' (a) (ha : a ∈ F.collinsProjection) :
        (algebraMap ℝ ℂ).comp (φ x) a = 0 ↔ (algebraMap ℝ ℂ).comp (φ y) a = 0 := by
      simpa using hzero a ha x y
    simpa only [aroots, map_map] using
      Finset.card_roots_toFinset_map_eq_of_collinsProjection hzero' p.2

end General

section MvPolynomial

variable {A : Type*} [CommRing A] {n : ℕ} {φ : A →+* ℝ}
  {F : Finset (MvPolynomial (Fin n) A)[X]} {S : Set (Fin n → ℝ)}

/-- **Collins delineability.** Let `F` be a finite family of polynomials in one distinguished
variable whose coefficients are polynomials over `A` in the base coordinates, and let
`φ : A →+* ℝ`. If every element of the Collins projection of `F` is sign-invariant, after
evaluation along `φ`, on a preconnected set `S ⊆ ℝⁿ`, then the family of fibers
`p.map (MvPolynomial.eval₂Hom φ x)`, `p ∈ F`, `x ∈ S`, has a delineation over `S`.

Only the zero pattern of the projection on `S` is used; see
`TauCeti.nonempty_delineation_of_collinsProjection`. -/
theorem nonempty_delineation_of_signInvariant_collinsProjection (hS : IsPreconnected S)
    (h : ∀ q ∈ F.collinsProjection, SignInvariant (fun x ↦ MvPolynomial.eval₂ φ x q) S) :
    Nonempty (Delineation fun (p : F) (x : S) ↦ p.1.map (MvPolynomial.eval₂Hom φ x.1)) := by
  have := isPreconnected_iff_preconnectedSpace.1 hS
  refine nonempty_delineation_of_collinsProjection (fun x : S ↦ MvPolynomial.eval₂Hom φ x.1)
    (fun q _ ↦ ?_) fun q hq x y ↦ ?_
  · simp only [MvPolynomial.coe_eval₂Hom, ← MvPolynomial.eval_map]
    exact (MvPolynomial.continuous_eval _).comp continuous_subtype_val
  · simpa only [MvPolynomial.coe_eval₂Hom, sign_eq_zero_iff] using
      (congrArg (· = 0) (signInvariant_def.1 (h q hq) x x.2 y y.2)).to_iff

/-- **Delineability of families mapped to `ℝ`.** Let `P` be a finite family of polynomials in
the variables `X 0, …, X n` over `A`, and let `φ : A →+* ℝ` be injective. If every element of the
Collins projection computed over `A`, with `X 0` singled out, is sign-invariant after evaluation
along `φ` on a preconnected set `S ⊆ ℝⁿ`, then the family obtained by mapping `P` to `ℝ` and
singling out `X 0` has a delineation over `S`. -/
theorem nonempty_delineation_image_finSuccEquiv_map_of_signInvariant_collinsProjection
    [DecidableEq (MvPolynomial (Fin n) A)[X]] [DecidableEq (MvPolynomial (Fin n) ℝ)[X]]
    (hφ : Function.Injective φ) {P : Finset (MvPolynomial (Fin (n + 1)) A)}
    (hS : IsPreconnected S)
    (h : ∀ q ∈ (P.image (MvPolynomial.finSuccEquiv A n)).collinsProjection,
      SignInvariant (fun x ↦ MvPolynomial.eval₂ φ x q) S) :
    Nonempty (Delineation fun (p : P.image fun f ↦ MvPolynomial.finSuccEquiv ℝ n (f.map φ))
      (x : S) ↦ p.1.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) x.1)) := by
  classical
  refine nonempty_delineation_of_signInvariant_collinsProjection hS fun q hq ↦ ?_
  rw [Finset.collinsProjection_image_finSuccEquiv_map hφ] at hq
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
  simpa only [MvPolynomial.eval₂_id, MvPolynomial.eval_map] using h r hr

end MvPolynomial

end TauCeti
