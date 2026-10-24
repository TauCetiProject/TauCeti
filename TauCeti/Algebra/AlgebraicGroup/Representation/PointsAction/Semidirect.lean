/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
public import Mathlib.GroupTheory.GroupExtension.Defs
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

The points semidirect products form a functor of the value algebra
(`TauCeti.Comodule.pointSemidirectMap`). By the Yoneda lemma, a family of sections natural in the
value algebra is the section of a single regular one-cochain: its value at the universal point
`id : H →ₐ[R] H` (`TauCeti.Comodule.eq_pointSection_of_naturality`). Thus sections of
`V_a ⋊ G → G` defined on the functor of points, such as those coming from closed subgroups
complementary to `V_a`, are the sections of regular cochains.

## Main declarations

* `TauCeti.Comodule.pointSection`: the section of the points semidirect product defined by a
  regular one-cochain.
* `TauCeti.Comodule.pointSection_mul_eq_iff`: multiplicativity of the section is the cocycle
  identity.
* `TauCeti.Comodule.pointSection_eq_conj_iff`: conjugacy of the section to the standard one is
  the coboundary identity.
* `TauCeti.Comodule.pointSemidirectMap`: functoriality of the points semidirect product in the
  value algebra.
* `TauCeti.Comodule.eq_pointSection_of_naturality`: sections natural in the value algebra are the
  sections of regular cochains.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part I, Chapter 4.
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.Comodule

section Points

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

section Functoriality

open SemidirectProduct

variable {B C : Type*} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

variable (V) in
/-- Functoriality of the points semidirect product `(A ⊗[R] V) ⋊ G(A)` in the value algebra: an
algebra map `φ : A →ₐ[R] B` acts by `φ ⊗ id` on the normal factor and by postcomposition on the
points of `G`. -/
noncomputable def pointSemidirectMap (φ : A →ₐ[R] B) :
    Multiplicative (A ⊗[R] V) ⋊[(pointsRepresentation V).toMulAut] WithConv (H →ₐ[R] A) →*
      Multiplicative (B ⊗[R] V) ⋊[(pointsRepresentation V).toMulAut] WithConv (H →ₐ[R] B) :=
  map (AddMonoidHom.toMultiplicative (LinearMap.rTensor V φ.toLinearMap).toAddMonoidHom)
    (AlgHom.mapValue φ) fun g ↦ by
      ext x
      exact congrArg Multiplicative.ofAdd <| by
        simpa [Representation.toMulAut_apply] using
          LinearMap.congr_fun (rTensor_comp_endOfPoint V φ g.ofConv) x

@[simp]
theorem toAdd_pointSemidirectMap_left (φ : A →ₐ[R] B)
    (x : Multiplicative (A ⊗[R] V) ⋊[(pointsRepresentation V).toMulAut] WithConv (H →ₐ[R] A)) :
    (pointSemidirectMap V φ x).left.toAdd = LinearMap.rTensor V φ.toLinearMap x.left.toAdd :=
  (rfl)

@[simp]
theorem pointSemidirectMap_right (φ : A →ₐ[R] B)
    (x : Multiplicative (A ⊗[R] V) ⋊[(pointsRepresentation V).toMulAut] WithConv (H →ₐ[R] A)) :
    (pointSemidirectMap V φ x).right = AlgHom.mapValue φ x.right :=
  (rfl)

@[simp]
theorem pointSemidirectMap_inl (φ : A →ₐ[R] B) (x : A ⊗[R] V) :
    pointSemidirectMap V φ (inl (Multiplicative.ofAdd x) :
        Multiplicative (A ⊗[R] V) ⋊[(pointsRepresentation V).toMulAut] WithConv (H →ₐ[R] A)) =
      inl (Multiplicative.ofAdd (LinearMap.rTensor V φ.toLinearMap x)) :=
  map_inl _ _ _ _

@[simp]
theorem pointSemidirectMap_inr (φ : A →ₐ[R] B) (g : WithConv (H →ₐ[R] A)) :
    pointSemidirectMap V φ (inr g) = inr (AlgHom.mapValue φ g) :=
  map_inr _ _ _ _

variable (V) in
/-- The identity of the value algebra induces the identity of the points semidirect product. -/
@[simp]
theorem pointSemidirectMap_id :
    pointSemidirectMap V (AlgHom.id R A) (H := H) = MonoidHom.id _ := by
  ext x
  · simp
  · simp

variable (V) in
/-- The points semidirect product is functorial in the value algebra. -/
theorem pointSemidirectMap_comp (ψ : B →ₐ[R] C) (φ : A →ₐ[R] B) :
    pointSemidirectMap V (ψ.comp φ) (H := H) =
      (pointSemidirectMap V ψ).comp (pointSemidirectMap V φ) := by
  ext x
  · simp [← LinearMap.rTensor_comp_apply]
  · simp [AlgHom.mapValue_comp]

/-- The section of a regular cochain is natural in the value algebra. -/
@[simp]
theorem pointSemidirectMap_pointSection (φ : A →ₐ[R] B) (b : V ⊗[R] H)
    (g : WithConv (H →ₐ[R] A)) :
    pointSemidirectMap V φ (pointSection V A b g) = pointSection V B b (AlgHom.mapValue φ g) := by
  refine SemidirectProduct.ext ?_ (by simp)
  apply Multiplicative.toAdd.injective
  simp

end Functoriality

end Points

section Naturality

open SemidirectProduct

universe w

variable {R : Type*} [CommSemiring R] {H : Type w} [CommRing H] [HopfAlgebra R H]
  {V : Type*} [AddCommGroup V] [Module R V] [Comodule R H V]

/-- **Natural sections are sections of regular cochains.** Let `s` be a family of sections of the
projections `(A ⊗[R] V) ⋊ G(A) → G(A)`, natural in the commutative `R`-algebra `A`. Then `s` is the
section `g ↦ (b(g), g)` of the regular cochain `b : V ⊗[R] H` read off from the value of `s` at
the universal point `id : H →ₐ[R] H`. -/
theorem eq_pointSection_of_naturality
    (s : ∀ (A : Type w) [CommRing A] [Algebra R A],
      (toGroupExtension (pointsRepresentation (R := R) (H := H) (A := A) V).toMulAut).Section)
    (hs : ∀ (A B : Type w) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
      (φ : A →ₐ[R] B) (g : WithConv (H →ₐ[R] A)),
      pointSemidirectMap V φ (s A g) = s B (AlgHom.mapValue φ g))
    (A : Type w) [CommRing A] [Algebra R A] (g : WithConv (H →ₐ[R] A)) :
    s A g = pointSection V A
      (TensorProduct.comm R H V (s H (toConv (AlgHom.id R H))).left.toAdd) g := by
  have h := hs H A g.ofConv (toConv (AlgHom.id R H))
  rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_id, toConv_ofConv] at h
  refine SemidirectProduct.ext ?_ ?_
  · rw [← h]
    apply Multiplicative.toAdd.injective
    simp
  · exact (s A).rightHom_section g

end Naturality

end TauCeti.Comodule
