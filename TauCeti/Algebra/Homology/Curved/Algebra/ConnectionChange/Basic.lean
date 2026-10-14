/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Tactic.NoncommRing
public import TauCeti.Algebra.Homology.Curved.Algebra.Defs
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Change of connection for curved differential graded algebras

Let `(A, d, w)` be a curved differential graded algebra and let `a ∈ A¹`. Adding the graded
commutator with `a` to the differential,

`d^a b = d b + a * b - (-1) ^ |b| • (b * a),`

gives a new degree-one derivation, and `(A, d^a, w^a)` is again a curved differential graded
algebra with the changed curvature

`w^a = w - d a - a * a.`

This is the algebraic form of changing a connection by a one-form: the curvature changes by the
covariant derivative and the square of the connection form. Applied to an ordinary differential
graded algebra, it produces a curved one of curvature `-(d a + a * a)`, which need not vanish.
Twisting by a connection form is not a strict morphism of curved differential graded
algebras; strict morphisms preserve both `d` and `w`.

## Main definitions

* `TauCeti.oddInnerDerivation 𝒜 a`: the graded commutator `b ↦ a * b - (-1) ^ |b| • (b * a)`
  with an element `a` of odd degree.
* `TauCeti.connectionChange 𝒜 d a`: the differential `d + [a, -]` twisted by the connection form
  `a`.

## Main results

* `TauCeti.IsCurvedDGAlgebra.connectionChange`: for `a ∈ A¹`, the twisted differential `d^a`
  and the curvature `w - d a - a * a` form a curved differential graded algebra.
* `TauCeti.IsDGAlgebra.connectionChange`: twisting a differential graded algebra gives a curved
  one of curvature `-(d a + a * a)`.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 6.2, for
  the change-of-connection formula; the sign of the curvature follows the right-module convention
  `d (d a) = a * w - w * a` of `TauCeti.IsCurvedDGAlgebra`, so it is the negative of his.
-/

public section

open DirectSum

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

section Decomposition

/-!
### The twisted differential

The twisted differential only uses the homogeneous decomposition of `A`, through the Koszul sign
of `TauCeti.InternalGrading.koszulTwist`; the graded multiplication enters only in the
change-of-connection theorems below.
-/

variable (𝒜 : ℤ → Submodule R A) [DirectSum.Decomposition 𝒜]

/-- The graded commutator with an element `a` of odd degree: on a homogeneous element `b`,
`a * b - (-1) ^ |b| • (b * a)`. For `a` of degree one this is the inner derivation by `a`. -/
noncomputable def oddInnerDerivation (a : A) : A →ₗ[R] A :=
  LinearMap.mulLeft R a -
    (LinearMap.mulRight R a).comp ((InternalGrading.ofDecomposition 𝒜).koszulTwist 1)

/-- The value of the odd inner derivation on a homogeneous element. -/
theorem oddInnerDerivation_apply_of_mem {p : ℤ} {b : A} (hb : b ∈ 𝒜 p) (a : A) :
    oddInnerDerivation 𝒜 a b = a * b - p.negOnePow • (b * a) := by
  have hb' : b ∈ (InternalGrading.ofDecomposition 𝒜).piece p := by
    rwa [InternalGrading.ofDecomposition_piece]
  rw [oddInnerDerivation, LinearMap.sub_apply, LinearMap.comp_apply,
    InternalGrading.koszulTwist_apply_of_mem _ hb', LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, one_mul, Int.cast_smul_eq_zsmul, smul_mul_assoc, Units.smul_def]

/-- The differential twisted by a connection form `a`: `d + [a, -]`, where `[a, -]` is the graded
commutator with `a`. -/
noncomputable def connectionChange (d : A →ₗ[R] A) (a : A) : A →ₗ[R] A :=
  d + oddInnerDerivation 𝒜 a

/-- The twisted differential is the differential plus the odd inner derivation. -/
@[simp]
theorem connectionChange_apply (d : A →ₗ[R] A) (a b : A) :
    connectionChange 𝒜 d a b = d b + oddInnerDerivation 𝒜 a b := by rfl

/-- The value of the twisted differential on a homogeneous element. -/
theorem connectionChange_apply_of_mem {p : ℤ} {b : A} (hb : b ∈ 𝒜 p) (d : A →ₗ[R] A) (a : A) :
    connectionChange 𝒜 d a b = d b + a * b - p.negOnePow • (b * a) := by
  rw [connectionChange_apply, oddInnerDerivation_apply_of_mem 𝒜 hb, add_sub_assoc]

end Decomposition

variable {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

/-- **Change of connection.** Twisting the differential of a curved differential graded algebra
by a connection form `a` of degree one changes the curvature to `w - d a - a * a`. -/
theorem IsCurvedDGAlgebra.connectionChange (h : IsCurvedDGAlgebra 𝒜 d w) {a : A}
    (ha : a ∈ 𝒜 1) : IsCurvedDGAlgebra 𝒜 (connectionChange 𝒜 d a) (w - d a - a * a) where
  map_mem {p b} hb := by
    rw [connectionChange_apply_of_mem 𝒜 hb, Units.smul_def]
    refine sub_mem (add_mem (h.map_mem hb) ?_) (zsmul_mem (SetLike.mul_mem_graded hb ha) _)
    rw [add_comm]
    exact SetLike.mul_mem_graded ha hb
  leibniz {q b} hb c := by
    induction c using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous r c =>
      obtain ⟨c, hc⟩ := c
      simp only
      rw [connectionChange_apply_of_mem 𝒜 (SetLike.mul_mem_graded hb hc),
        connectionChange_apply_of_mem 𝒜 hb, connectionChange_apply_of_mem 𝒜 hc, h.leibniz hb c,
        Int.negOnePow_add]
      simp only [Units.smul_def, Units.val_mul]
      rcases Int.units_eq_one_or q.negOnePow with hq | hq <;>
        rcases Int.units_eq_one_or r.negOnePow with hr | hr <;>
        simp only [hq, hr, Units.val_one, Units.val_neg, one_zsmul, neg_one_zsmul, one_mul,
          neg_one_mul, neg_neg] <;>
        noncomm_ring
    | add c c' hc hc' =>
      simp only [mul_add, map_add, hc, hc', smul_add]
      abel
  curvature_mem := by
    refine sub_mem (sub_mem h.curvature_mem ?_) ?_
    · simpa using h.map_mem ha
    · simpa using SetLike.mul_mem_graded ha ha
  sq_eq b := by
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous q b =>
      obtain ⟨b, hb⟩ := b
      simp only
      have hab : a * b ∈ 𝒜 (q + 1) := by
        rw [add_comm]
        exact SetLike.mul_mem_graded ha hb
      rw [connectionChange_apply_of_mem 𝒜 hb, Units.smul_def, map_sub, map_add, map_zsmul,
        connectionChange_apply_of_mem 𝒜 (h.map_mem hb), connectionChange_apply_of_mem 𝒜 hab,
        connectionChange_apply_of_mem 𝒜 (SetLike.mul_mem_graded hb ha), h.sq_eq, h.leibniz ha b,
        h.leibniz hb a, Int.negOnePow_one, Units.neg_smul, one_smul, Int.negOnePow_succ]
      simp only [Units.smul_def, Units.val_neg]
      rcases Int.units_eq_one_or q.negOnePow with hq | hq <;>
        simp only [hq, Units.val_one, Units.val_neg, one_zsmul, neg_one_zsmul, neg_neg] <;>
        noncomm_ring
    | add b b' hb hb' =>
      rw [map_add, map_add, hb, hb', add_mul, mul_add]
      abel
  map_curvature := by
    rw [connectionChange_apply_of_mem 𝒜 (sub_mem (sub_mem h.curvature_mem
      (by simpa using h.map_mem ha)) (by simpa using SetLike.mul_mem_graded ha ha)),
      Int.negOnePow_even _ even_two, one_smul, map_sub, map_sub, h.map_curvature, h.sq_eq,
      h.leibniz ha a, Int.negOnePow_one, Units.neg_smul, one_smul]
    noncomm_ring

/-- Twisting the differential of a differential graded algebra by a connection form `a` of degree
one gives a curved differential graded algebra of curvature `-(d a + a * a)`. -/
theorem IsDGAlgebra.connectionChange (h : IsDGAlgebra 𝒜 d) {a : A} (ha : a ∈ 𝒜 1) :
    IsCurvedDGAlgebra 𝒜 (connectionChange 𝒜 d a) (-(d a + a * a)) := by
  have := h.isCurvedDGAlgebra_zero.connectionChange ha
  rwa [zero_sub, ← neg_add'] at this

end TauCeti
