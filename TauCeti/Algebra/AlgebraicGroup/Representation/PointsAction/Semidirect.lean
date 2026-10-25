/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
public import Mathlib.GroupTheory.SemidirectProduct
public import TauCeti.RepresentationTheory.ToMultiplicative

/-!
# The semidirect product of points with a comodule

Let `V` be a comodule over a Hopf algebra `H`, so that the group `G(A)` of `A`-points of `H`
acts linearly on the scalar extension `A ⊗[R] V` (`TauCeti.Comodule.pointsRepresentation`).
The `A`-points of the semidirect product `V_a ⋊ G` of the vector group of `V` by `G` are the
ordinary semidirect product of the additive group `A ⊗[R] V` by `G(A)`. Through
`Representation.toMulAut` this is Mathlib's `SemidirectProduct` of `Multiplicative (A ⊗[R] V)`
by `G(A)`.

A tensor `b : V ⊗[R] H` is a regular one-cochain of `G` with values in `V`: its value at an
`A`-point `g` is obtained by pushing the `H`-factor through `g`
(`TauCeti.Comodule.pointCochain`). It defines the set-theoretic section `g ↦ (b(g), g)` of the
projection onto `G(A)` (`TauCeti.Comodule.pointSection`). This section is multiplicative exactly
when `b` satisfies the cocycle identity `b(gh) = b(g) + g • b(h)` at `A`-points, and it is the
conjugate of the standard section by the normal-factor element `x` exactly when
`b(g) = x - g • x`.

## Main declarations

* `TauCeti.Comodule.pointSection`: the section of the points semidirect product defined by a
  regular one-cochain.
* `TauCeti.Comodule.pointSection_mul_eq_iff`: multiplicativity of the section is the cocycle
  identity.
* `TauCeti.Comodule.pointSection_eq_conj_iff`: conjugacy of the section to the standard one is
  the coboundary identity.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part I, Chapter 4.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.Comodule

variable {R H V A : Type*} [CommSemiring R]


variable [Semiring H] [HopfAlgebra R H] [AddCommGroup V] [Module R V] [Comodule R H V]
  [CommRing A] [Algebra R A]

section Section

open SemidirectProduct

variable (V A) in
/-- The set-theoretic section `g ↦ (b(g), g)` of the projection of the points semidirect product
`(A ⊗[R] V) ⋊ G(A)` onto `G(A)`, attached to a regular one-cochain `b : V ⊗[R] H`. -/
noncomputable def pointSection (b : V ⊗[R] H) (g : WithConv (H →ₐ[R] A)) :
    Multiplicative (A ⊗[R] V) ⋊[(pointsRepresentation V).toMulAut] WithConv (H →ₐ[R] A) :=
  ⟨Multiplicative.ofAdd (pointCochain V g.ofConv b), g⟩

@[simp]
theorem toAdd_pointSection_left (b : V ⊗[R] H) (g : WithConv (H →ₐ[R] A)) :
    (pointSection V A b g).left.toAdd = pointCochain V g.ofConv b :=
  (rfl)

@[simp]
theorem pointSection_right (b : V ⊗[R] H) (g : WithConv (H →ₐ[R] A)) :
    (pointSection V A b g).right = g :=
  (rfl)

/-- The section attached to a cochain is a section of the projection onto the points. -/
@[simp]
theorem rightHom_pointSection (b : V ⊗[R] H) (g : WithConv (H →ₐ[R] A)) :
    rightHom (pointSection V A b g) = g :=
  (rfl)

/-- The section attached to a cochain is multiplicative at a pair of points exactly when the
cochain satisfies the cocycle identity `b(gh) = b(g) + g • b(h)` there. -/
theorem pointSection_mul_eq_iff (b : V ⊗[R] H) (g h : WithConv (H →ₐ[R] A)) :
    pointSection V A b (g * h) = pointSection V A b g * pointSection V A b h ↔
      pointCochain V (g * h).ofConv b =
        pointCochain V g.ofConv b + endOfPoint V g.ofConv (pointCochain V h.ofConv b) := by
  constructor
  · intro hgh
    have := congrArg (fun x ↦ x.left.toAdd) hgh
    simpa [mul_left] using this
  · intro hgh
    refine SemidirectProduct.ext ?_ (by simp)
    apply Multiplicative.toAdd.injective
    simp [mul_left, hgh]

/-- Conjugating the standard section by the normal-factor element `x` gives the section of the
cochain `g ↦ x - g • x`. -/
theorem inl_mul_inr_mul_inv_inl (x : A ⊗[R] V) (g : WithConv (H →ₐ[R] A)) :
    (inl (Multiplicative.ofAdd x) * inr g * (inl (Multiplicative.ofAdd x))⁻¹ :
        Multiplicative (A ⊗[R] V) ⋊[(pointsRepresentation V).toMulAut] WithConv (H →ₐ[R] A)) =
      ⟨Multiplicative.ofAdd (x - endOfPoint V g.ofConv x), g⟩ := by
  refine SemidirectProduct.ext ?_ (by simp)
  apply Multiplicative.toAdd.injective
  simp [mul_left, ← map_inv, sub_eq_add_neg]

/-- The section attached to a cochain agrees at `g` with the conjugate of the standard section
by the normal-factor element `x` exactly when `b(g) = x - g • x`. -/
theorem pointSection_eq_conj_iff (b : V ⊗[R] H) (x : A ⊗[R] V) (g : WithConv (H →ₐ[R] A)) :
    pointSection V A b g =
        inl (Multiplicative.ofAdd x) * inr g * (inl (Multiplicative.ofAdd x))⁻¹ ↔
      pointCochain V g.ofConv b = x - endOfPoint V g.ofConv x := by
  rw [inl_mul_inr_mul_inv_inl, SemidirectProduct.ext_iff]
  simp only [pointSection, and_true]
  exact Multiplicative.ofAdd.injective.eq_iff

end Section

end TauCeti.Comodule
