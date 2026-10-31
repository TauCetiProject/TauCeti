/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.DehnSurgery.Filling
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.MatrixAction

/-!
# Dehn fillings with linear gluings depend only on the slope

A Dehn filling `TauCeti.DehnFilling h s Y` of a knot exterior `E` glues the solid torus
`V = D² × S¹` to `E` along a homeomorphism `g` of the boundary tori `S¹ × S¹`. Two fillings `Y`,
`Y'` with gluings `g`, `g'` are homeomorphic, by the identity on `E`, as soon as the torus map
`g'⁻¹ ∘ g` extends to a homeomorphism `ψ` of `V`: the homeomorphism is `E ∪ V ≅ E ∪ V` given by
the identity and `ψ` (`TauCeti.DehnFilling.homeomorphOfSolidTorus`).

A homeomorphism of `S¹ × S¹` induced by an invertible integral matrix
(`Matrix.GeneralLinearGroup.torusHomeomorph`) whose matrix fixes the meridian `(1, 0)` up to sign,
`(a, b) ↦ (a ^ ε * b ^ k, b ^ δ)` with `ε, δ = ±1`, extends to `V` as
`(z, b) ↦ (z * b ^ k, b ^ δ)`, with `z` replaced by its complex conjugate when `ε = -1`
(`TauCeti.SolidTorus.exists_homeomorph_boundaryInclusion_torusHomeomorph`). Two such matrix
gluings with the same filling slope differ by a matrix of this form, so **Dehn fillings along
gluings given by integral matrices depend, up to homeomorphism, only on the slope**
(`TauCeti.DehnFilling.nonempty_homeomorph_of_gluing_eq_torusHomeomorph`). This is the part of the
classical well-definedness of Dehn filling (Rolfsen, *Knots and Links*, 9F) that concerns the
filling solid torus. The rest, that every homeomorphism of the torus is isotopic to one induced by
a matrix and that such an isotopy can be absorbed into a collar of the boundary of the exterior,
is not formalized here.

In particular any filling along the meridian with a matrix gluing is the ambient space, the
`∞`-surgery (`TauCeti.DehnFilling.nonempty_homeomorph_of_fillingSlope_meridian`).

## Main results

* `TauCeti.IsSolidTorusNeighborhood.fillingSlope_torusHomeomorph`: the filling slope of the
  gluing induced by a matrix `A` is the slope of the `(A₀₀, A₁₀)` curve.
* `TauCeti.IsSolidTorusNeighborhood.fillingSlope_torusHomeomorph_eq_iff`: two matrix gluings
  have the same filling slope exactly when their first columns agree up to sign.
* `TauCeti.IsSolidTorusNeighborhood.exists_fillingSlope_torusHomeomorph_eq`: every slope is the
  filling slope of a matrix gluing.
* `TauCeti.DehnFilling.nonempty_homeomorph_of_gluing_eq_torusHomeomorph`: two fillings along the
  same slope with matrix gluings are homeomorphic.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9, Section 9F (Dehn surgery:
  the filled manifold depends only on the curve to which the meridian of the filling solid torus is
  sent, since a homeomorphism of the boundary torus preserving the meridian extends over the solid
  torus).
-/

public section

noncomputable section

open Set Metric

namespace TauCeti

/-! ### The filling slope of a matrix gluing -/

namespace IsSolidTorusNeighborhood

variable {X : Type} [TopologicalSpace X] [T2Space X] {f : Circle → X} {Φ : SolidTorus → X}

/-- **The filling slope of a matrix gluing.** Gluing the solid torus by the homeomorphism induced
by an invertible integral matrix `A` sends its meridian to the `(A₀₀, A₁₀)` curve, so the filling
slope is the slope of that curve, of value `A₀₀ / A₁₀` in the framing of `Φ`. -/
theorem fillingSlope_torusHomeomorph (h : IsSolidTorusNeighborhood f Φ) (A : GL (Fin 2) ℤ) :
    h.fillingSlope A.torusHomeomorph =
      Slope.mk (FramedBoundaryTorus.torusCurveClass h.exteriorFrontierHomeomorph (A 0 0) (A 1 0))
        ((FramedBoundaryTorus.isPrimitive_torusCurveClass_iff _ _ _).2 (A.isCoprime_col 0)) :=
  h.fillingSlope_eq_of_apply_torusCurve (A.isCoprime_col 0) fun t ↦ by
    simpa using A.torusHomeomorph_torusCurve 1 0 t

/-- Two matrix gluings have the same filling slope exactly when the first columns of their
matrices agree up to sign. -/
theorem fillingSlope_torusHomeomorph_eq_iff (h : IsSolidTorusNeighborhood f Φ)
    (A A' : GL (Fin 2) ℤ) :
    h.fillingSlope A.torusHomeomorph = h.fillingSlope A'.torusHomeomorph ↔
      (A 0 0 = A' 0 0 ∧ A 1 0 = A' 1 0) ∨ (A 0 0 = -A' 0 0 ∧ A 1 0 = -A' 1 0) := by
  rw [fillingSlope_torusHomeomorph, fillingSlope_torusHomeomorph, Slope.mk_eq_mk_iff,
    ← h.framedBoundaryTorus.coord.injective.eq_iff, ← h.framedBoundaryTorus.coord.injective.eq_iff,
    map_neg, FramedBoundaryTorus.coord_torusCurveClass, FramedBoundaryTorus.coord_torusCurveClass,
    Prod.neg_mk, Prod.mk.injEq, Prod.mk.injEq]

/-- **Every slope is the filling slope of a matrix gluing.** A primitive class with coordinates
`(p, q)` in the framing of `Φ` is the first column of an invertible integral matrix
`[[p, -b], [q, a]]`, with `a p + b q = 1`, and gluing the solid torus by the homeomorphism of
`S¹ × S¹` that this matrix induces sends its meridian to the class. -/
theorem exists_fillingSlope_torusHomeomorph_eq (h : IsSolidTorusNeighborhood f Φ)
    (s : Slope h.framedBoundaryTorus.H) :
    ∃ A : GL (Fin 2) ℤ, h.fillingSlope A.torusHomeomorph = s := by
  induction s using Slope.induction_on with
  | h v hv =>
    set c := h.framedBoundaryTorus.coord v with hc
    have hcop : IsCoprime c.1 c.2 :=
      isPrimitive_prod_iff.1 ((h.framedBoundaryTorus.coord.isPrimitive_iff).2 hv)
    obtain ⟨M, hM₀, hM₁⟩ := hcop.exists_SL2_col 0
    refine ⟨Matrix.SpecialLinearGroup.toGL M, ?_⟩
    rw [fillingSlope_torusHomeomorph]
    refine Slope.mk_eq_mk _ _ (Or.inl (h.framedBoundaryTorus.coord.injective ?_))
    rw [FramedBoundaryTorus.coord_torusCurveClass, ← hc,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hM₀, hM₁]

end IsSolidTorusNeighborhood

/-! ### Fillings along the same slope -/

namespace DehnFilling

variable {X : Type} [TopologicalSpace X] [T2Space X] {f : Circle → X} {Φ : SolidTorus → X}
  {h : IsSolidTorusNeighborhood f Φ} {s : Slope h.framedBoundaryTorus.H}
  {Y Y' : Type*} [TopologicalSpace Y] [TopologicalSpace Y']

/-- **Dehn fillings with matrix gluings depend only on the slope.** Two Dehn fillings of the same
knot exterior along the same slope, whose gluings are induced by invertible integral matrices, are
homeomorphic, by a homeomorphism that is the identity on the exterior. -/
theorem nonempty_homeomorph_of_gluing_eq_torusHomeomorph (F : DehnFilling h s Y)
    (F' : DehnFilling h s Y') {A A' : GL (Fin 2) ℤ} (hA : F.gluing = A.torusHomeomorph)
    (hA' : F'.gluing = A'.torusHomeomorph) : Nonempty (Y ≃ₜ Y') := by
  have hslope : h.fillingSlope A.torusHomeomorph = h.fillingSlope A'.torusHomeomorph := by
    rw [← hA, ← hA', F.fillingSlope_gluing, F'.fillingSlope_gluing]
  -- The matrix `A'⁻¹ A` relating the gluings fixes the meridian `(1, 0)` up to sign.
  have hinv : ((A'⁻¹ * A' : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by simp
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at hinv
  have hB : ((A'⁻¹ * A : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    rcases (h.fillingSlope_torusHomeomorph_eq_iff A A').1 hslope with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩
    · rw [h₀, h₁]
      exact hinv
    · rw [h₀, h₁]
      linear_combination -hinv
  obtain ⟨ψ, hψ⟩ := SolidTorus.exists_homeomorph_boundaryInclusion_torusHomeomorph _ hB
  refine ⟨homeomorphOfSolidTorus F F' ψ fun q ↦ ?_⟩
  rw [hψ, hA, hA', Matrix.GeneralLinearGroup.symm_torusHomeomorph,
    Matrix.GeneralLinearGroup.torusHomeomorph_mul, Homeomorph.trans_apply]

/-- **`∞`-surgery.** A Dehn filling along the meridian whose gluing is induced by an invertible
integral matrix is homeomorphic to the ambient space of the knot. -/
theorem nonempty_homeomorph_of_fillingSlope_meridian
    (F : DehnFilling h h.framedBoundaryTorus.meridian Y) {A : GL (Fin 2) ℤ}
    (hA : F.gluing = A.torusHomeomorph) : Nonempty (Y ≃ₜ X) :=
  F.nonempty_homeomorph_of_gluing_eq_torusHomeomorph h.meridianDehnFilling hA
    (by rw [IsSolidTorusNeighborhood.meridianDehnFilling_gluing,
      Matrix.GeneralLinearGroup.torusHomeomorph_one])

end DehnFilling

end TauCeti
