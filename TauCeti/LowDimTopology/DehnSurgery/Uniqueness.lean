/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.DehnSurgery.Filling
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.Isotopy
public import TauCeti.LowDimTopology.SolidTorusNeighborhood.MatrixAction

/-!
# Dehn fillings with gluings isotopic to linear ones depend only on the slope

A Dehn filling `TauCeti.DehnFilling h s Y` of a knot exterior `E` glues the solid torus
`V = D² × S¹` to `E` along a homeomorphism `g` of the boundary tori `S¹ × S¹`. Two fillings `Y`,
`Y'` with gluings `g`, `g'` are homeomorphic, by the identity on `E`, as soon as the torus map
`g'⁻¹ ∘ g` extends to a homeomorphism `ψ` of `V`: the homeomorphism is `E ∪ V ≅ E ∪ V` given by
the identity and `ψ` (`TauCeti.DehnFilling.homeomorphOfSolidTorus`).

A homeomorphism of `S¹ × S¹` induced by an invertible integral matrix
(`Matrix.GeneralLinearGroup.torusHomeomorph`) whose matrix fixes the meridian `(1, 0)` up to sign,
`(a, b) ↦ (a ^ ε * b ^ k, b ^ δ)` with `ε, δ = ±1`, extends to `V` as
`(z, b) ↦ (z * b ^ k, b ^ δ)`, with `z` replaced by its complex conjugate when `ε = -1`
(`TauCeti.SolidTorus.exists_homeomorph_boundaryInclusion_torusHomeomorph`). Two matrix gluings
with the same filling slope differ by a matrix of this form
(`IsSolidTorusNeighborhood.exists_homeomorph_boundaryInclusion_symm_apply_of_fillingSlope_eq`).
If two homeomorphisms `g`, `k` of the torus are isotopic, then `g⁻¹ ∘ k` extends over `V` too, the
isotopy being absorbed into a collar inside `V`
(`TauCeti.SolidTorus.exists_homeomorph_boundaryInclusion_symm_apply_of_isotopic`). Hence:

* **Dehn fillings with isotopic gluings are homeomorphic**
  (`TauCeti.DehnFilling.exists_homeomorph_of_isotopic`);
* **Dehn fillings whose gluings are isotopic to gluings given by integral matrices depend, up to
  homeomorphism, only on the slope**
  (`TauCeti.DehnFilling.exists_homeomorph_of_isotopic_torusHomeomorph`): writing `A`, `A'` for
  the matrices, `g'⁻¹ ∘ g` is the composite of `g'⁻¹ ∘ A'`, `A'⁻¹ ∘ A` and `A⁻¹ ∘ g`, each of which
  extends over `V`. The two matrix gluings have the same slope as `g` and `g'`, since homotopic
  gluings have the same slope (`TauCeti.IsSolidTorusNeighborhood.fillingSlope_eq_of_homotopic`).

This is the classical well-definedness of Dehn filling (Rolfsen, *Knots and Links*, 9F), except
for one input that is not formalized here: that every homeomorphism of the torus is isotopic to
one induced by a matrix.

In particular any filling along the meridian whose gluing is isotopic to a matrix gluing is the
ambient space, the `∞`-surgery (`TauCeti.DehnFilling.nonempty_homeomorph_of_fillingSlope_meridian`).

## Main results

* `TauCeti.IsSolidTorusNeighborhood.fillingSlope_torusHomeomorph`: the filling slope of the
  gluing induced by a matrix `A` is the slope of the `(A₀₀, A₁₀)` curve.
* `TauCeti.IsSolidTorusNeighborhood.fillingSlope_torusHomeomorph_eq_iff`: two matrix gluings
  have the same filling slope exactly when their first columns agree up to sign.
* `TauCeti.IsSolidTorusNeighborhood.exists_fillingSlope_torusHomeomorph_eq`: every slope is the
  filling slope of a matrix gluing.
* `IsSolidTorusNeighborhood.exists_homeomorph_boundaryInclusion_symm_apply_of_fillingSlope_eq`:
  two matrix gluings with the same slope differ by a homeomorphism extending over the solid torus.
* `TauCeti.DehnFilling.exists_homeomorph_of_isotopic`: two fillings with isotopic gluings are
  homeomorphic, by the identity on the exterior.
* `TauCeti.DehnFilling.exists_homeomorph_of_isotopic_torusHomeomorph`: two fillings along the
  same slope with gluings isotopic to matrix gluings are homeomorphic, by the identity on the
  exterior.

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

/-- **Matrix gluings with the same filling slope differ over the solid torus.** If the gluings
induced by two invertible integral matrices `A`, `A'` have the same filling slope, the
homeomorphism `A'⁻¹ ∘ A` of the boundary torus extends over the solid torus: its matrix fixes the
meridian `(1, 0)` up to sign. -/
theorem exists_homeomorph_boundaryInclusion_symm_apply_of_fillingSlope_eq
    (h : IsSolidTorusNeighborhood f Φ) {A A' : GL (Fin 2) ℤ}
    (hslope : h.fillingSlope A.torusHomeomorph = h.fillingSlope A'.torusHomeomorph) :
    ∃ ψ : SolidTorus ≃ₜ SolidTorus, ∀ q, ψ (SolidTorus.boundaryInclusion q) =
      SolidTorus.boundaryInclusion (A'.torusHomeomorph.symm (A.torusHomeomorph q)) := by
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
  refine ⟨ψ, fun q ↦ ?_⟩
  rw [hψ, Matrix.GeneralLinearGroup.symm_torusHomeomorph,
    Matrix.GeneralLinearGroup.torusHomeomorph_mul, Homeomorph.trans_apply]

end IsSolidTorusNeighborhood

/-! ### Fillings along the same slope -/

namespace DehnFilling

variable {X : Type} [TopologicalSpace X] [T2Space X] {f : Circle → X} {Φ : SolidTorus → X}
  {h : IsSolidTorusNeighborhood f Φ} {s s' : Slope h.framedBoundaryTorus.H}
  {Y Y' : Type*} [TopologicalSpace Y] [TopologicalSpace Y']

/-- **Dehn fillings with isotopic gluings are homeomorphic.** If the gluings of two Dehn fillings
of the same knot exterior are isotopic homeomorphisms of the torus `S¹ × S¹`, the filled spaces
are homeomorphic, by a homeomorphism that is the identity on the exterior. The two fillings then
have the same slope (`TauCeti.IsSolidTorusNeighborhood.fillingSlope_eq_of_homotopic`). -/
theorem exists_homeomorph_of_isotopic (F : DehnFilling h s Y) (F' : DehnFilling h s' Y')
    (hFF' : Isotopic (F.gluing : C(Circle × Circle, Circle × Circle)) F'.gluing) :
    ∃ e : Y ≃ₜ Y', ∀ x, e (F.exteriorEmbedding x) = F'.exteriorEmbedding x := by
  obtain ⟨ψ, hψ⟩ := SolidTorus.exists_homeomorph_boundaryInclusion_symm_apply_of_isotopic hFF'.symm
  exact ⟨homeomorphOfSolidTorus F F' ψ hψ, homeomorphOfSolidTorus_exteriorEmbedding F F' ψ hψ⟩

/-- **Dehn fillings with gluings isotopic to matrix gluings depend only on the slope.** Two Dehn
fillings of the same knot exterior along the same slope, whose gluings are isotopic to
homeomorphisms induced by invertible integral matrices, are homeomorphic, by a homeomorphism that
is the identity on the exterior. -/
theorem exists_homeomorph_of_isotopic_torusHomeomorph (F : DehnFilling h s Y)
    (F' : DehnFilling h s Y') {A A' : GL (Fin 2) ℤ}
    (hA : Isotopic (F.gluing : C(Circle × Circle, Circle × Circle)) A.torusHomeomorph)
    (hA' : Isotopic (F'.gluing : C(Circle × Circle, Circle × Circle)) A'.torusHomeomorph) :
    ∃ e : Y ≃ₜ Y', ∀ x, e (F.exteriorEmbedding x) = F'.exteriorEmbedding x := by
  have hslope : h.fillingSlope A.torusHomeomorph = h.fillingSlope A'.torusHomeomorph := by
    rw [← h.fillingSlope_eq_of_homotopic hA.homotopic,
      ← h.fillingSlope_eq_of_homotopic hA'.homotopic, F.fillingSlope_gluing,
      F'.fillingSlope_gluing]
  -- With `g`, `g'` the gluings, `g'⁻¹ ∘ g = (g'⁻¹ ∘ A') ∘ (A'⁻¹ ∘ A) ∘ (A⁻¹ ∘ g)`, and each of the
  -- three factors extends over the solid torus.
  obtain ⟨ψ₁, hψ₁⟩ := SolidTorus.exists_homeomorph_boundaryInclusion_symm_apply_of_isotopic hA'
  obtain ⟨ψ₂, hψ₂⟩ := h.exists_homeomorph_boundaryInclusion_symm_apply_of_fillingSlope_eq hslope
  obtain ⟨ψ₃, hψ₃⟩ := SolidTorus.exists_homeomorph_boundaryInclusion_symm_apply_of_isotopic hA.symm
  have hψ (q : Circle × Circle) : (ψ₃.trans (ψ₂.trans ψ₁)) (SolidTorus.boundaryInclusion q) =
      SolidTorus.boundaryInclusion (F'.gluing.symm (F.gluing q)) := by
    rw [Homeomorph.trans_apply, Homeomorph.trans_apply, hψ₃, hψ₂, hψ₁,
      Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  exact ⟨homeomorphOfSolidTorus F F' _ hψ, homeomorphOfSolidTorus_exteriorEmbedding F F' _ hψ⟩

/-- **`∞`-surgery.** A Dehn filling along the meridian whose gluing is isotopic to a homeomorphism
induced by an invertible integral matrix is homeomorphic to the ambient space of the knot. -/
theorem nonempty_homeomorph_of_fillingSlope_meridian
    (F : DehnFilling h h.framedBoundaryTorus.meridian Y) {A : GL (Fin 2) ℤ}
    (hA : Isotopic (F.gluing : C(Circle × Circle, Circle × Circle)) A.torusHomeomorph) :
    Nonempty (Y ≃ₜ X) := by
  have h₁ : Isotopic (h.meridianDehnFilling.gluing : C(Circle × Circle, Circle × Circle))
      (1 : GL (Fin 2) ℤ).torusHomeomorph := by
    rw [IsSolidTorusNeighborhood.meridianDehnFilling_gluing,
      Matrix.GeneralLinearGroup.torusHomeomorph_one]
    exact Isotopic.refl _ (Homeomorph.refl _).isEmbedding
  obtain ⟨e, -⟩ := F.exists_homeomorph_of_isotopic_torusHomeomorph h.meridianDehnFilling hA h₁
  exact ⟨e⟩

end DehnFilling

end TauCeti
