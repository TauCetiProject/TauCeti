/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.SectionMatrix
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Ideal

/-!
# The polynomial ring of a section through a node

Let `A` be a commutative ring, `γ δ s t : A` and `q(x, y) = x ^ 2 + γ * x * y + δ * y ^ 2` the
binary quadratic node form `TauCeti.BinaryQuadraticForm.nodeForm γ δ`. The ring
`R = A[Y][X] ⧸ (q(X, Y) - q(s, t))` is the polynomial model of a nodal curve near a section
`(s, t)` which may pass through the singular point. It is the local algebra on which Knudsen
builds the expansion of a pointed stable curve along an extra section.

We realize `R` as `AdjoinRoot F` for the monic quadratic
`F = X ^ 2 + C (γ * Y) * X + C (δ * Y ^ 2 - q(s, t))` in `X` over `A[Y]`. Monicity holds over
every base, including the zero ring, so `F` is a non-zero-divisor in `A[Y][X]`. The coordinates
`u = [X]` and `v = [Y]` satisfy `q(u, v) = q(s, t)`, and `R` is the universal `A`-algebra with
such a pair. Evaluation at the section is the `A`-algebra map `R → A` sending `u ↦ s` and
`v ↦ t`. Its kernel is the section ideal `J = (u - s, v - t)`, so `A → R → A` splits
`0 → J → R → A → 0` as `A`-modules.

On `R` the node-section matrix `Φ` (`TauCeti.BinaryQuadraticForm.sectionMatrix`) at `(u, v)` and
`(s, t)` has determinant zero, so `Φ` and its adjugate `Ψ` compose to zero in both orders. This is
the matrix factorization through which Knudsen presents `J` and its dual `Hom_R(J, R)` as
cokernels; those presentations are not proved here.

No Noetherian, nontriviality or discriminant hypothesis is made, except that the degree of `F`
is two only over a nontrivial ring.

## Main declarations

* `TauCeti.pointedNodePolynomial`: the defining monic quadratic `F`.
* `TauCeti.monic_pointedNodePolynomial`, `TauCeti.isRegular_pointedNodePolynomial`.
* `TauCeti.PointedNodeRing`: the ring `R = AdjoinRoot F`.
* `TauCeti.PointedNodeRing.coordX`, `TauCeti.PointedNodeRing.coordY`: the coordinates `u`, `v`.
* `TauCeti.PointedNodeRing.lift`, `TauCeti.PointedNodeRing.algHom_ext`: the universal property.
* `TauCeti.PointedNodeRing.sectionEval`: evaluation at the section `(s, t)`.
* `TauCeti.PointedNodeRing.sectionIdeal`: the section ideal `J = (u - s, v - t)`.
* `TauCeti.PointedNodeRing.ker_sectionEval`: the kernel of section evaluation is `J`.
* `TauCeti.PointedNodeRing.sectionMatrix_mul_adjugate`,
  `TauCeti.PointedNodeRing.adjugate_mul_sectionMatrix`: `Φ * Ψ = Ψ * Φ = 0` on `R`.

## References

* F. F. Knudsen, *A closer look at the stacks of stable pointed curves*, arXiv:1106.1588v2
  (2012), §3, Key Example and the proof of Proposition 3.1.
-/

public section

noncomputable section

namespace TauCeti

open Polynomial
open BinaryQuadraticForm (nodeForm eval_nodeForm eval_nodeForm_map)

variable {A : Type*} [CommRing A] (γ δ s t : A)

/-- The defining polynomial `F = X ^ 2 + C (γ * Y) * X + C (δ * Y ^ 2 - q(s, t))` of a section
`(s, t)` through the node `q(X, Y) = q(s, t)`, as a polynomial in the outer variable `X` over
`A[Y]`; here `q = BinaryQuadraticForm.nodeForm γ δ`. -/
def pointedNodePolynomial : A[X][X] :=
  X ^ 2 + C (C γ * X) * X + C (C δ * X ^ 2 - C ((nodeForm γ δ).eval s t))

theorem pointedNodePolynomial_def :
    pointedNodePolynomial γ δ s t =
      X ^ 2 + C (C γ * X) * X + C (C δ * X ^ 2 - C ((nodeForm γ δ).eval s t)) :=
  (rfl)

/-- The defining polynomial is `q(X, Y) - q(s, t)`, with `X` the outer and `Y` the inner
variable. -/
theorem pointedNodePolynomial_eq_eval_sub :
    pointedNodePolynomial γ δ s t =
      (nodeForm (C (C γ)) (C (C δ))).eval X (C X) - C (C ((nodeForm γ δ).eval s t)) := by
  simp only [pointedNodePolynomial_def, eval_nodeForm, C_mul, C_pow, C_sub]
  ring

/-- The defining polynomial is monic in `X`, over every commutative ring including the zero
ring. -/
theorem monic_pointedNodePolynomial : (pointedNodePolynomial γ δ s t).Monic := by
  rw [pointedNodePolynomial_def, add_assoc]
  exact monic_X_pow_add degree_linear_lt

/-- Over a nontrivial ring the defining polynomial has degree two in `X`. -/
theorem natDegree_pointedNodePolynomial [Nontrivial A] :
    (pointedNodePolynomial γ δ s t).natDegree = 2 := by
  rw [pointedNodePolynomial_def, add_assoc, natDegree_add_eq_left_of_degree_lt] <;>
    simp only [natDegree_X_pow, degree_X_pow]
  exact degree_linear_lt

/-- Multiplication by the defining polynomial is injective on `A[Y][X]` (on either side). -/
theorem isRegular_pointedNodePolynomial : IsRegular (pointedNodePolynomial γ δ s t) :=
  (monic_pointedNodePolynomial γ δ s t).isRegular

/-- Evaluating the defining polynomial at `X = x`, `Y = y` gives `q(x, y) - q(s, t)`. -/
theorem eval_eval_pointedNodePolynomial (x y : A) :
    ((pointedNodePolynomial γ δ s t).eval (C x)).eval y =
      (nodeForm γ δ).eval x y - (nodeForm γ δ).eval s t := by
  simp [pointedNodePolynomial_def]
  ring

/-- The polynomial ring `A[Y][X] ⧸ (q(X, Y) - q(s, t))` of a section `(s, t)` on the curve
`q(X, Y) = q(s, t)`, where `q = BinaryQuadraticForm.nodeForm γ δ`, realized as `AdjoinRoot` of the
monic quadratic `pointedNodePolynomial γ δ s t`. -/
abbrev PointedNodeRing : Type _ :=
  AdjoinRoot (pointedNodePolynomial γ δ s t)

namespace PointedNodeRing

/-- The coordinate `u = [X]` of the pointed node ring, the adjoined root. -/
def coordX : PointedNodeRing γ δ s t :=
  AdjoinRoot.root _

/-- The coordinate `v = [Y]` of the pointed node ring, the image of the inner variable. -/
def coordY : PointedNodeRing γ δ s t :=
  AdjoinRoot.of _ X

@[simp]
theorem root_eq_coordX : AdjoinRoot.root (pointedNodePolynomial γ δ s t) = coordX γ δ s t :=
  (rfl)

@[simp]
theorem of_X_eq_coordY : AdjoinRoot.of (pointedNodePolynomial γ δ s t) X = coordY γ δ s t :=
  (rfl)

theorem mk_X : AdjoinRoot.mk (pointedNodePolynomial γ δ s t) X = coordX γ δ s t :=
  AdjoinRoot.mk_X

theorem mk_C_X : AdjoinRoot.mk (pointedNodePolynomial γ δ s t) (C X) = coordY γ δ s t :=
  AdjoinRoot.mk_C X

/-- The coefficient map `A → R` is the composite `A → A[Y] → R` of the two coefficient
inclusions. -/
theorem algebraMap_eq :
    algebraMap A (PointedNodeRing γ δ s t) =
      (AdjoinRoot.of (pointedNodePolynomial γ δ s t)).comp C := by
  rw [AdjoinRoot.algebraMap_eq', Polynomial.algebraMap_eq]

@[simp]
theorem of_C (a : A) :
    AdjoinRoot.of (pointedNodePolynomial γ δ s t) (C a) =
      algebraMap A (PointedNodeRing γ δ s t) a := by
  rw [algebraMap_eq, RingHom.comp_apply]

theorem mk_C_C (a : A) :
    AdjoinRoot.mk (pointedNodePolynomial γ δ s t) (C (C a)) =
      algebraMap A (PointedNodeRing γ δ s t) a := by
  rw [AdjoinRoot.mk_C, of_C]

/-- The coordinates of the pointed node ring satisfy `q(u, v) = q(s, t)`. -/
theorem eval_coordX_coordY :
    (nodeForm (algebraMap A (PointedNodeRing γ δ s t) γ) (algebraMap A _ δ)).eval
        (coordX γ δ s t) (coordY γ δ s t) =
      algebraMap A _ ((nodeForm γ δ).eval s t) := by
  have h := AdjoinRoot.mk_self (f := pointedNodePolynomial γ δ s t)
  simp only [pointedNodePolynomial_def, map_add, map_sub, map_mul, map_pow, mk_X, mk_C_X,
    mk_C_C] at h
  rw [eval_nodeForm]
  linear_combination h

section Lift

variable {B : Type*} [CommRing B] [Algebra A B]

/-- The universal property of the pointed node ring: a pair `(x, y)` in an `A`-algebra `B`
with `q(x, y) = q(s, t)` determines the `A`-algebra map `R → B` sending `u ↦ x` and `v ↦ y`. -/
def lift (x y : B)
    (h : (nodeForm (algebraMap A B γ) (algebraMap A B δ)).eval x y =
      algebraMap A B ((nodeForm γ δ).eval s t)) :
    PointedNodeRing γ δ s t →ₐ[A] B :=
  AdjoinRoot.liftAlgHom _ (aeval y) x <| by
    rw [pointedNodePolynomial_eq_eval_sub, ← sub_eq_zero.mpr h]
    simp [eval₂_pow]

variable (x y : B)
  (h : (nodeForm (algebraMap A B γ) (algebraMap A B δ)).eval x y =
    algebraMap A B ((nodeForm γ δ).eval s t))

@[simp]
theorem lift_coordX : lift γ δ s t x y h (coordX γ δ s t) = x :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp]
theorem lift_coordY : lift γ δ s t x y h (coordY γ δ s t) = y := by
  rw [← of_X_eq_coordY, lift, AdjoinRoot.liftAlgHom_of, aeval_X]

/-- `lift` on the class of a polynomial `P(X, Y)` evaluates it at `X = x`, `Y = y`. -/
@[simp]
theorem lift_mk (P : A[X][X]) :
    lift γ δ s t x y h (AdjoinRoot.mk _ P) = P.eval₂ (aeval y).toRingHom x :=
  AdjoinRoot.liftAlgHom_mk _ _ _ _ P

/-- Two `A`-algebra maps out of the pointed node ring agree once they agree on both
coordinates. -/
theorem algHom_ext {f g : PointedNodeRing γ δ s t →ₐ[A] B}
    (hX : f (coordX γ δ s t) = g (coordX γ δ s t))
    (hY : f (coordY γ δ s t) = g (coordY γ δ s t)) : f = g :=
  AdjoinRoot.algHom_ext' (Polynomial.algHom_ext <| by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AdjoinRoot.coe_ofAlgHom, of_X_eq_coordY]
    exact hY) hX

end Lift

/-- Evaluation at the section: the `A`-algebra map `R → A` sending `u ↦ s` and `v ↦ t`. -/
def sectionEval : PointedNodeRing γ δ s t →ₐ[A] A :=
  lift γ δ s t s t (by simp)

@[simp]
theorem sectionEval_coordX : sectionEval γ δ s t (coordX γ δ s t) = s :=
  lift_coordX ..

@[simp]
theorem sectionEval_coordY : sectionEval γ δ s t (coordY γ δ s t) = t :=
  lift_coordY ..

/-- Section evaluation on the class of a polynomial `P(X, Y)` is `P(s, t)`. -/
@[simp]
theorem sectionEval_mk (P : A[X][X]) :
    sectionEval γ δ s t (AdjoinRoot.mk _ P) = (P.eval (C s)).eval t := by
  rw [sectionEval, lift_mk]
  induction P using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [eval₂_add, hp, hq, eval_add, eval_add]
  | monomial n a _ => simp

/-- The section ideal `J = (u - s, v - t)` of the pointed node ring. -/
def sectionIdeal : Ideal (PointedNodeRing γ δ s t) :=
  Ideal.span {coordX γ δ s t - algebraMap A _ s, coordY γ δ s t - algebraMap A _ t}

theorem sectionIdeal_def :
    sectionIdeal γ δ s t =
      Ideal.span {coordX γ δ s t - algebraMap A _ s, coordY γ δ s t - algebraMap A _ t} :=
  (rfl)

theorem coordX_sub_mem_sectionIdeal :
    coordX γ δ s t - algebraMap A _ s ∈ sectionIdeal γ δ s t :=
  Ideal.subset_span (by simp)

theorem coordY_sub_mem_sectionIdeal :
    coordY γ δ s t - algebraMap A _ t ∈ sectionIdeal γ δ s t :=
  Ideal.subset_span (by simp)

/-- The kernel of evaluation at the section is the section ideal `J = (u - s, v - t)`. Since
section evaluation is an `A`-algebra map, it is a retraction of the coefficient map `A → R`, so
`0 → J → R → A → 0` is split by the coefficient map. -/
theorem ker_sectionEval : RingHom.ker (sectionEval γ δ s t) = sectionIdeal γ δ s t := by
  refine le_antisymm (fun r hr ↦ ?_) (Ideal.span_le.mpr ?_)
  · induction r using AdjoinRoot.induction_on with | ih P => ?_
    rw [RingHom.mem_ker, sectionEval_mk,
      ← mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero] at hr
    have := Ideal.mem_map_of_mem (AdjoinRoot.mk (pointedNodePolynomial γ δ s t)) hr
    rw [Ideal.map_span, Set.image_pair, Set.pair_comm] at this
    simpa [sectionIdeal_def] using this
  · rintro _ (rfl | rfl) <;> simp

theorem mem_sectionIdeal_iff {r : PointedNodeRing γ δ s t} :
    r ∈ sectionIdeal γ δ s t ↔ sectionEval γ δ s t r = 0 := by
  rw [← ker_sectionEval, RingHom.mem_ker]

/-- The node-section matrix `Φ` of the pointed node ring, at the coordinates `(u, v)` and the
section `(s, t)`. -/
def sectionMatrix : Matrix (Fin 2) (Fin 2) (PointedNodeRing γ δ s t) :=
  (nodeForm (algebraMap A _ γ) (algebraMap A _ δ)).sectionMatrix (coordX γ δ s t) (coordY γ δ s t)
    (algebraMap A _ s) (algebraMap A _ t)

theorem sectionMatrix_def :
    sectionMatrix γ δ s t =
      (nodeForm (algebraMap A _ γ) (algebraMap A _ δ)).sectionMatrix (coordX γ δ s t)
        (coordY γ δ s t) (algebraMap A _ s) (algebraMap A _ t) :=
  (rfl)

/-- The node-section matrix of the pointed node ring is singular: `det Φ = q(u, v) - q(s, t)`
vanishes. Expanded, this is the relation `c * b + d * a = 0` between the section coordinates
`c = u - s`, `d = v - t` and the entries `b = u + s + γ * t`, `a = δ * v + δ * t + γ * u`. -/
@[simp]
theorem det_sectionMatrix : (sectionMatrix γ δ s t).det = 0 := by
  rw [sectionMatrix_def, BinaryQuadraticForm.det_sectionMatrix, eval_coordX_coordY,
    eval_nodeForm_map, sub_self]

/-- On the pointed node ring the node-section factorization becomes `Φ * Ψ = 0`. -/
theorem sectionMatrix_mul_adjugate :
    sectionMatrix γ δ s t * (sectionMatrix γ δ s t).adjugate = 0 := by
  rw [Matrix.mul_adjugate, det_sectionMatrix, zero_smul]

/-- On the pointed node ring the node-section factorization becomes `Ψ * Φ = 0`. -/
theorem adjugate_mul_sectionMatrix :
    (sectionMatrix γ δ s t).adjugate * sectionMatrix γ δ s t = 0 := by
  rw [Matrix.adjugate_mul, det_sectionMatrix, zero_smul]

end PointedNodeRing

end TauCeti
