/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Semidirect
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.OneCocycle
public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import TauCeti.Algebra.Coalgebra.Convolution

/-!
# Sections of vector-group semidirect products by a diagonalizable group

Let `D = D(G)` be the diagonalizable group with coordinate Hopf algebra `R[G]` and let `V` be a
comodule over `R[G]`, so that `D` acts linearly on the vector group of `V`. On `A`-points the
semidirect product `V_a ⋊ D` is the ordinary semidirect product of the additive group
`A ⊗[R] V` by `D(A)`, acting through `TauCeti.Comodule.pointsRepresentation`.

A regular one-cocycle `b : V ⊗[R] R[G]` (`TauCeti.Comodule.IsRegularCocycle₁`) defines a section
`g ↦ (b(g), g)` of the projection `V_a ⋊ D → D` on the points over every commutative `R`-algebra
`A`, and this section is a group homomorphism. Since `b` is the coboundary of a vector `v : V`
(`TauCeti.Comodule.eq_regularCoboundary_tensorComponent_monoidCoeff_one`), that splitting is the
conjugate of the standard splitting `g ↦ (0, g)` by the element `1 ⊗ v` of the normal factor.
The conjugating vector is a single vector of `V`, independent of `A`. Conversely, when `R` is a
ring and `G` is commutative, a regular cochain satisfying the cocycle identity on all points is
a regular cocycle; when moreover `G` is a group, this says that the sections are multiplicative
on all points. Both follow from the universal pair of points of `R[G] ⊗[R] R[G]`.

This is the vector-group step in the conjugacy of maximal tori in a connected solvable group:
two tori complementary to a normal vector subgroup on which they act linearly are images of two
splittings, which are then conjugate by a rational point of the vector subgroup.

## Main declarations

* `TauCeti.Comodule.IsRegularCocycle₁.pointCochain_eq`: on every point, a regular cocycle is the
  coboundary of its identity-character coefficient.
* `TauCeti.Comodule.IsRegularCocycle₁.pointCochain_mul`: a regular cocycle satisfies the cocycle
  identity on points.
* `TauCeti.Comodule.isRegularCocycle₁_iff_forall_pointCochain_mul`: conversely, the cocycle
  identity on points characterizes regular cocycles.
* `TauCeti.Comodule.IsRegularCocycle₁.pointSplitting`: the splitting of the points semidirect
  product defined by a regular cocycle.
* `TauCeti.Comodule.IsRegularCocycle₁.pointSplitting_apply`: this splitting is the conjugate of
  the standard splitting by a vector independent of the value algebra.
* `TauCeti.Comodule.IsRegularCocycle₁.isConj_pointSplitting`: it is conjugate to the standard
  splitting by an element of the normal factor.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §10.6.
* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., Part I, Chapter 4.
-/

public section

open scoped TensorProduct
open WithConv SemidirectProduct

namespace TauCeti.Comodule

universe u v w x

section Monoid

variable {R : Type u} [CommSemiring R] {G : Type v} [Monoid G]
  {V : Type w} [AddCommGroup V] [Module R V] [Comodule R (MonoidAlgebra R G) V]
  {A : Type x} [CommRing A] [Algebra R A]

/-- The value of a regular coboundary at a point `g` is `1 ⊗ v - g • (1 ⊗ v)`. -/
@[simp]
theorem pointCochain_regularCoboundary (g : MonoidAlgebra R G →ₐ[R] A) (v : V) :
    pointCochain V g (regularCoboundary (R := R) (G := G) v) =
      1 ⊗ₜ[R] v - endOfPoint V g (1 ⊗ₜ[R] v) := by
  rw [regularCoboundary_apply]
  simp [← MonoidAlgebra.one_def, endOfPoint_tmul, pointCochain_apply]

namespace IsRegularCocycle₁

variable {b : V ⊗[R] MonoidAlgebra R G}

/-- On the points over every commutative `R`-algebra, a regular cocycle is the coboundary
`g ↦ 1 ⊗ v - g • (1 ⊗ v)` of its identity-character coefficient `v`. -/
theorem pointCochain_eq (hb : IsRegularCocycle₁ b) (g : MonoidAlgebra R G →ₐ[R] A) :
    pointCochain V g b =
      1 ⊗ₜ[R] LinearMap.tensorComponent (monoidCoeff R G 1) b -
        endOfPoint V g (1 ⊗ₜ[R] LinearMap.tensorComponent (monoidCoeff R G 1) b) := by
  conv_lhs => rw [eq_regularCoboundary_tensorComponent_monoidCoeff_one hb]
  exact pointCochain_regularCoboundary g _

/-- A regular cocycle satisfies the cocycle identity `b(gh) = b(g) + g • b(h)` on the points
over every commutative `R`-algebra. -/
theorem pointCochain_mul (hb : IsRegularCocycle₁ b)
    (g h : WithConv (MonoidAlgebra R G →ₐ[R] A)) :
    pointCochain V (g * h).ofConv b =
      pointCochain V g.ofConv b + endOfPoint V g.ofConv (pointCochain V h.ofConv b) := by
  simp only [hb.pointCochain_eq, endOfPoint_convMul, LinearMap.comp_apply, map_sub]
  abel

end IsRegularCocycle₁

end Monoid

section Group

variable {R : Type u} [CommSemiring R] {G : Type v} [Group G]
  {V : Type w} [AddCommGroup V] [Module R V] [Comodule R (MonoidAlgebra R G) V]
  {A : Type x} [CommRing A] [Algebra R A]

namespace IsRegularCocycle₁

variable {b : V ⊗[R] MonoidAlgebra R G}

variable (A) in
/-- The splitting of the points semidirect product `(A ⊗[R] V) ⋊ D(A)` defined by a regular
cocycle: the section `g ↦ (b(g), g)` as a group homomorphism. -/
noncomputable def pointSplitting (hb : IsRegularCocycle₁ b) :
    (toGroupExtension
      (pointsRepresentation (R := R) (H := MonoidAlgebra R G) (A := A) V).toMulAut).Splitting where
  toFun := pointSection V A b
  map_one' := by
    rw [← mul_left_cancel_iff (a := pointSection V A b 1), ← (pointSection_mul_eq_iff b 1 1).2
      (hb.pointCochain_mul 1 1), mul_one, mul_one]
  map_mul' g h := (pointSection_mul_eq_iff b g h).2 (hb.pointCochain_mul g h)
  rightInverse_rightHom := rightHom_pointSection b

variable (A) in
@[simp]
theorem coe_pointSplitting (hb : IsRegularCocycle₁ b) :
    ⇑(hb.pointSplitting A) = pointSection V A b :=
  (rfl)

/-- **Splittings by regular cocycles are conjugate to the standard splitting.** On the points
over every commutative `R`-algebra `A`, the splitting defined by a regular cocycle `b` is the
conjugate of the standard splitting `g ↦ (0, g)` by `1 ⊗ v`, where `v` is the
identity-character coefficient of `b`. The vector `v` does not depend on `A`. -/
theorem pointSplitting_apply (hb : IsRegularCocycle₁ b)
    (g : WithConv (MonoidAlgebra R G →ₐ[R] A)) :
    hb.pointSplitting A g =
      inl (Multiplicative.ofAdd (1 ⊗ₜ[R] LinearMap.tensorComponent (monoidCoeff R G 1) b)) *
        inr g *
        (inl (Multiplicative.ofAdd (1 ⊗ₜ[R] LinearMap.tensorComponent (monoidCoeff R G 1) b)))⁻¹ :=
  (pointSection_eq_conj_iff b _ g).2 (hb.pointCochain_eq g.ofConv)

variable (A) in
/-- On the points over every commutative `R`-algebra, the splitting defined by a regular cocycle
is conjugate to the standard splitting by an element of the normal factor. -/
theorem isConj_pointSplitting (hb : IsRegularCocycle₁ b) :
    (toGroupExtension
      (pointsRepresentation (R := R) (H := MonoidAlgebra R G) (A := A) V).toMulAut).IsConj
        (hb.pointSplitting A) (inr_splitting _) :=
  ⟨_, funext hb.pointSplitting_apply⟩

end IsRegularCocycle₁

end Group

section CommMonoid

variable {R : Type u} [CommRing R] {G : Type v} [CommMonoid G]
  {V : Type w} [AddCommGroup V] [Module R V] [Comodule R (MonoidAlgebra R G) V]

/-- **The cocycle identity on points characterizes regular cocycles.** A regular cochain
satisfies the regular cocycle identity exactly when it satisfies `b(gh) = b(g) + g • b(h)` on the
points over every commutative `R`-algebra. It suffices to test the universal pair of points of
`R[G] ⊗[R] R[G]`. -/
theorem isRegularCocycle₁_iff_forall_pointCochain_mul (b : V ⊗[R] MonoidAlgebra R G) :
    IsRegularCocycle₁ b ↔
      ∀ (A : Type (max u v)) [CommRing A] [Algebra R A]
        (g h : WithConv (MonoidAlgebra R G →ₐ[R] A)),
        pointCochain V (g * h).ofConv b =
          pointCochain V g.ofConv b + endOfPoint V g.ofConv (pointCochain V h.ofConv b) := by
  refine ⟨fun hb A _ _ g h ↦ hb.pointCochain_mul g h, fun H ↦ ?_⟩
  have h := H (MonoidAlgebra R G ⊗[R] MonoidAlgebra R G)
    (toConv Algebra.TensorProduct.includeLeft) (toConv Algebra.TensorProduct.includeRight)
  rw [← TauCeti.Bialgebra.comulPoint_eq_include_mul] at h
  simp only [endOfPoint_includeLeft_pointCochain_includeRight,
    pointCochain_includeLeft] at h
  have htransport :
      TensorProduct.comm R V _ (Coalgebra.comul.lTensor V b) =
        TensorProduct.comm R V _ (TensorProduct.assoc R V (MonoidAlgebra R G)
          (MonoidAlgebra R G) ((coact (R := R) (C := MonoidAlgebra R G) (M := V)).rTensor _ b +
            b ⊗ₜ[R] 1)) := by
    simpa only [pointCochain_apply, Bialgebra.toLinearMap_comulAlgHom, map_add, add_comm] using h
  rw [isRegularCocycle₁_iff, ← MonoidAlgebra.one_def]
  exact (TensorProduct.comm R V _).injective htransport

end CommMonoid

section CommGroup

variable {R : Type u} [CommRing R] {G : Type v} [CommGroup G]
  {V : Type w} [AddCommGroup V] [Module R V] [Comodule R (MonoidAlgebra R G) V]

/-- A regular cochain is a regular cocycle exactly when its sections of the points semidirect
products `(A ⊗[R] V) ⋊ D(A)` are multiplicative for every commutative `R`-algebra `A`. -/
theorem isRegularCocycle₁_iff_forall_pointSection_mul (b : V ⊗[R] MonoidAlgebra R G) :
    IsRegularCocycle₁ b ↔
      ∀ (A : Type (max u v)) [CommRing A] [Algebra R A]
        (g h : WithConv (MonoidAlgebra R G →ₐ[R] A)),
        pointSection V A b (g * h) = pointSection V A b g * pointSection V A b h := by
  simp only [pointSection_mul_eq_iff]
  exact isRegularCocycle₁_iff_forall_pointCochain_mul b

end CommGroup

end TauCeti.Comodule
