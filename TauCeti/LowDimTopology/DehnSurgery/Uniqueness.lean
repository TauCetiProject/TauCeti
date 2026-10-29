/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Coprime
public import TauCeti.LowDimTopology.DehnSurgery.Unknot
public import TauCeti.Topology.Circle.MatrixAction

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
`(z, b) ↦ (z * b ^ k, b ^ δ)`, with `z` replaced by its conjugate `z̄` when `ε = -1`
(`TauCeti.SolidTorus.exists_homeomorph_boundaryInclusion_torusHomeomorph`). Two such matrix
gluings with the same filling slope differ by a matrix of this form, so **Dehn fillings along
gluings given by integral matrices depend, up to homeomorphism, only on the slope**
(`TauCeti.DehnFilling.nonempty_homeomorph_of_gluing_eq_torusHomeomorph`). This is the part of the
classical well-definedness of Dehn filling (Rolfsen, *Knots and Links*, 9F) that concerns the
filling solid torus. The rest, that every homeomorphism of the torus is isotopic to one induced by
a matrix and that such an isotopy can be absorbed into a collar of the boundary of the exterior,
is not formalized here.

In particular any filling along the meridian with a matrix gluing is the ambient space, the
`∞`-surgery (`TauCeti.DehnFilling.nonempty_homeomorph_of_fillingSlope_meridian`), and any filling
of the exterior of the unknot along the longitude with a matrix gluing is `S¹ × S²`, the
`0`-surgery (`TauCeti.DehnFilling.nonempty_homeomorph_circle_prod_sphere_of_unknot_longitude`).

## Main definitions

* `TauCeti.DehnFilling.homeomorphOfSolidTorus`: the homeomorphism between two fillings whose
  gluings differ by the boundary values of a homeomorphism of the solid torus.

## Main results

* `TauCeti.SolidTorus.exists_homeomorph_boundaryInclusion_torusHomeomorph`: matrices fixing the
  meridian up to sign act on the boundary torus by maps that extend over the solid torus.
* `TauCeti.IsSolidTorusNeighborhood.fillingSlope_torusHomeomorph`: the filling slope of the
  gluing induced by a matrix `A` is the slope of the `(A₀₀, A₁₀)` curve.
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

/-! ### Extending torus maps over the solid torus -/

namespace SolidTorus

/-- The identity of `ℂ` for `ε = 1` and complex conjugation for `ε = -1`; on the unit circle it
is `a ↦ a ^ ε` (`discSign_coe`). -/
private def discSign (ε : ℤˣ) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  if ε = 1 then LinearIsometryEquiv.refl ℝ ℂ else Complex.conjLIE

private theorem discSign_discSign (ε : ℤˣ) (z : ℂ) : discSign ε (discSign ε z) = z := by
  unfold discSign
  split_ifs <;> simp

private theorem discSign_coe (ε : ℤˣ) (a : Circle) :
    discSign ε a = ((a ^ (ε : ℤ) : Circle) : ℂ) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp [discSign]
  · rw [discSign, ite_eq_right (by decide), Complex.conjLIE_apply, Units.val_neg, Units.val_one,
      zpow_neg_one, Circle.coe_inv_eq_conj]

private theorem norm_discSign_mul (ε : ℤˣ) (z : ℂ) (c : Circle) : ‖discSign ε z * c‖ = ‖z‖ := by
  rw [norm_mul, LinearIsometryEquiv.norm_map, Circle.norm_coe, mul_one]

/-- The homeomorphism `(z, b) ↦ (σ z * b ^ k, b ^ δ)` of the solid torus, with `σ` the identity
for `ε = 1` and complex conjugation for `ε = -1`. -/
private def extension (ε δ : ℤˣ) (k : ℤ) : SolidTorus ≃ₜ SolidTorus where
  toFun p := (⟨discSign ε p.1 * (p.2 ^ k : Circle), by
    rw [mem_closedBall_zero_iff, norm_discSign_mul]; exact mem_closedBall_zero_iff.mp p.1.2⟩,
    p.2 ^ (δ : ℤ))
  invFun p := (⟨discSign ε (p.1 * (p.2 ^ (-((δ : ℤ) * k)) : Circle)), by
    rw [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map, norm_mul, Circle.norm_coe,
      mul_one]; exact mem_closedBall_zero_iff.mp p.1.2⟩,
    p.2 ^ (δ : ℤ))
  left_inv p := by
    have hδ := Int.units_coe_mul_self δ
    have hk : p.2 ^ k * (p.2 ^ (δ : ℤ)) ^ (-((δ : ℤ) * k)) = 1 := by
      rw [← zpow_mul, ← zpow_add, show k + (δ : ℤ) * -((δ : ℤ) * k) = 0 by
        linear_combination (-k) * hδ, zpow_zero]
    refine Prod.ext (Subtype.ext ?_) ?_
    · dsimp only
      rw [mul_assoc, ← Circle.coe_mul, hk, Circle.coe_one, mul_one, discSign_discSign]
    · dsimp only
      rw [← zpow_mul, hδ, zpow_one]
  right_inv p := by
    have hδ := Int.units_coe_mul_self δ
    refine Prod.ext (Subtype.ext ?_) ?_
    · dsimp only
      rw [discSign_discSign, mul_assoc, ← Circle.coe_mul, ← zpow_mul, ← zpow_add, neg_add_cancel,
        zpow_zero, Circle.coe_one, mul_one]
    · dsimp only
      rw [← zpow_mul, hδ, zpow_one]
  continuous_toFun := by
    have hc : Continuous ((↑) : Circle → ℂ) := continuous_subtype_val
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (by fun_prop)
    exact ((discSign ε).continuous.comp (by fun_prop)).mul (hc.comp (by fun_prop))
  continuous_invFun := by
    have hc : Continuous ((↑) : Circle → ℂ) := continuous_subtype_val
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (by fun_prop)
    exact (discSign ε).continuous.comp ((continuous_subtype_val.comp continuous_fst).mul
      (hc.comp (by fun_prop)))

private theorem extension_boundaryInclusion (ε δ : ℤˣ) (k : ℤ) (q : Circle × Circle) :
    extension ε δ k (boundaryInclusion q) =
      boundaryInclusion (q.1 ^ (ε : ℤ) * q.2 ^ k, q.2 ^ (δ : ℤ)) :=
  Prod.ext (Subtype.ext (by simp [extension, discSign_coe])) (by simp [extension])

/-- **Torus maps fixing the meridian extend over the solid torus.** If an invertible integral
matrix `A` has `A₁₀ = 0`, so that it fixes the meridian class `(1, 0)` up to sign, the induced
homeomorphism `(a, b) ↦ (a ^ A₀₀ * b ^ A₀₁, b ^ A₁₁)` of the boundary torus `S¹ × S¹` is the
restriction of a homeomorphism of the solid torus `D² × S¹`. -/
theorem exists_homeomorph_boundaryInclusion_torusHomeomorph (A : GL (Fin 2) ℤ) (hA : A 1 0 = 0) :
    ∃ ψ : SolidTorus ≃ₜ SolidTorus,
      ∀ q, ψ (boundaryInclusion q) = boundaryInclusion (A.torusHomeomorph q) := by
  have h₀ := A.isCoprime_col 0
  have h₁ := A.isCoprime_row 1
  rw [hA, isCoprime_zero_right] at h₀
  rw [hA, isCoprime_zero_left] at h₁
  obtain ⟨ε, hε⟩ := h₀
  obtain ⟨δ, hδ⟩ := h₁
  refine ⟨extension ε δ (A 0 1), fun q ↦ ?_⟩
  rw [extension_boundaryInclusion, Matrix.GeneralLinearGroup.torusHomeomorph_apply, hA, hε, hδ,
    zpow_zero, one_mul]

end SolidTorus

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

end IsSolidTorusNeighborhood

/-! ### Homeomorphisms between fillings -/

namespace DehnFilling

variable {X : Type} [TopologicalSpace X] [T2Space X] {f : Circle → X} {Φ : SolidTorus → X}
  {h : IsSolidTorusNeighborhood f Φ} {s s' : Slope h.framedBoundaryTorus.H}
  {Y Y' : Type*} [TopologicalSpace Y] [TopologicalSpace Y']

/-- The compatibility of a homeomorphism of the solid torus with two gluings, read backwards. -/
private theorem symm_apply_boundaryInclusion (F : DehnFilling h s Y) (F' : DehnFilling h s' Y')
    {ψ : SolidTorus ≃ₜ SolidTorus}
    (hψ : ∀ q, ψ (SolidTorus.boundaryInclusion q) =
      SolidTorus.boundaryInclusion (F'.gluing.symm (F.gluing q))) (q : Circle × Circle) :
    ψ.symm (SolidTorus.boundaryInclusion q) =
      SolidTorus.boundaryInclusion (F.gluing.symm (F'.gluing q)) := by
  rw [Homeomorph.symm_apply_eq, hψ, Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]

/-- The continuous map from one filling to another which is the identity on the exterior and `ψ`
on the filling solid torus, for `ψ` compatible with the two gluings. -/
private def descOfSolidTorus (F : DehnFilling h s Y) (F' : DehnFilling h s' Y')
    (ψ : SolidTorus ≃ₜ SolidTorus)
    (hψ : ∀ q, ψ (SolidTorus.boundaryInclusion q) =
      SolidTorus.boundaryInclusion (F'.gluing.symm (F.gluing q))) : C(Y, Y') :=
  F.desc ⟨_, F'.isClosedEmbedding_exteriorEmbedding.continuous⟩
    ⟨_, F'.isClosedEmbedding_solidTorusEmbedding.continuous.comp ψ.continuous⟩ fun q ↦ by
      simp only [ContinuousMap.coe_mk, Function.comp_apply, hψ,
        ← F'.exteriorEmbedding_exteriorBoundaryInclusion, Homeomorph.apply_symm_apply]

private theorem descOfSolidTorus_comp (F : DehnFilling h s Y) (F' : DehnFilling h s' Y')
    (ψ : SolidTorus ≃ₜ SolidTorus)
    (hψ : ∀ q, ψ (SolidTorus.boundaryInclusion q) =
      SolidTorus.boundaryInclusion (F'.gluing.symm (F.gluing q))) (y : Y) :
    descOfSolidTorus F' F ψ.symm (symm_apply_boundaryInclusion F F' hψ)
      (descOfSolidTorus F F' ψ hψ y) = y := by
  refine DFunLike.congr_fun (F.hom_ext (φ := (descOfSolidTorus F' F ψ.symm
    (symm_apply_boundaryInclusion F F' hψ)).comp (descOfSolidTorus F F' ψ hψ))
    (ψ := ContinuousMap.id Y) (fun x ↦ ?_) (fun p ↦ ?_)) y <;>
  simp [descOfSolidTorus]

/-- **Fillings with gluings related over the solid torus are homeomorphic.** If the torus map
`g'⁻¹ ∘ g` between the gluings `g`, `g'` of two Dehn fillings `Y`, `Y'` of the same knot exterior is
the restriction of a homeomorphism `ψ` of the solid torus to its boundary, then `Y` and `Y'` are
homeomorphic, by the identity on the exterior and by `ψ` on the filling solid torus. -/
def homeomorphOfSolidTorus (F : DehnFilling h s Y) (F' : DehnFilling h s' Y')
    (ψ : SolidTorus ≃ₜ SolidTorus)
    (hψ : ∀ q, ψ (SolidTorus.boundaryInclusion q) =
      SolidTorus.boundaryInclusion (F'.gluing.symm (F.gluing q))) : Y ≃ₜ Y' where
  toFun := descOfSolidTorus F F' ψ hψ
  invFun := descOfSolidTorus F' F ψ.symm (symm_apply_boundaryInclusion F F' hψ)
  left_inv := descOfSolidTorus_comp F F' ψ hψ
  right_inv y := by
    simpa only [Homeomorph.symm_symm] using descOfSolidTorus_comp F' F ψ.symm
      (symm_apply_boundaryInclusion F F' hψ) y
  continuous_toFun := (descOfSolidTorus F F' ψ hψ).continuous
  continuous_invFun := (descOfSolidTorus F' F ψ.symm _).continuous

/-- The homeomorphism between fillings is the identity on the knot exterior. -/
@[simp]
theorem homeomorphOfSolidTorus_exteriorEmbedding (F : DehnFilling h s Y)
    (F' : DehnFilling h s' Y') (ψ : SolidTorus ≃ₜ SolidTorus)
    (hψ : ∀ q, ψ (SolidTorus.boundaryInclusion q) =
      SolidTorus.boundaryInclusion (F'.gluing.symm (F.gluing q))) (x : knotExterior (Φ := Φ)) :
    homeomorphOfSolidTorus F F' ψ hψ (F.exteriorEmbedding x) = F'.exteriorEmbedding x :=
  F.desc_exteriorEmbedding _ _ _ x

/-- The homeomorphism between fillings is `ψ` on the filling solid torus. -/
@[simp]
theorem homeomorphOfSolidTorus_solidTorusEmbedding (F : DehnFilling h s Y)
    (F' : DehnFilling h s' Y') (ψ : SolidTorus ≃ₜ SolidTorus)
    (hψ : ∀ q, ψ (SolidTorus.boundaryInclusion q) =
      SolidTorus.boundaryInclusion (F'.gluing.symm (F.gluing q))) (p : SolidTorus) :
    homeomorphOfSolidTorus F F' ψ hψ (F.solidTorusEmbedding p) = F'.solidTorusEmbedding (ψ p) :=
  F.desc_solidTorusEmbedding _ _ _ p

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

/-- The matrix exchanging the two coordinates, which acts on the torus by exchanging the circle
factors. -/
private def swapMatrix : GL (Fin 2) ℤ where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by simp [Matrix.one_fin_two]
  inv_val := by simp [Matrix.one_fin_two]

private theorem swapMatrix_torusHomeomorph :
    swapMatrix.torusHomeomorph = Homeomorph.prodComm Circle Circle :=
  Homeomorph.ext fun q ↦ Prod.ext (by simp [swapMatrix]) (by simp [swapMatrix])

/-- **`0`-surgery on the unknot.** A Dehn filling of the exterior of the unknot along the longitude
of its standard solid torus neighbourhood, the slope `0` in the preferred framing, whose gluing is
induced by an invertible integral matrix, is homeomorphic to `S¹ × S²`. -/
theorem nonempty_homeomorph_circle_prod_sphere_of_unknot_longitude
    (F : DehnFilling isSolidTorusNeighborhood_unknotSolidTorus
      isSolidTorusNeighborhood_unknotSolidTorus.framedBoundaryTorus.longitude Y)
    {A : GL (Fin 2) ℤ} (hA : F.gluing = A.torusHomeomorph) :
    Nonempty (Y ≃ₜ Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  F.nonempty_homeomorph_of_gluing_eq_torusHomeomorph unknotZeroDehnFilling hA
    (by rw [unknotZeroDehnFilling_gluing, swapMatrix_torusHomeomorph])

end DehnFilling

end TauCeti
