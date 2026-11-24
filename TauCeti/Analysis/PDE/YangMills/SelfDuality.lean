/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Isometry
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.VectorValued
public import TauCeti.Analysis.PDE.YangMills.StructureGroup

/-!
# Self-duality of Lie-algebra-valued two-forms in dimension four

The curvature of a connection on an oriented four-dimensional space is, at each point, a
`𝔤`-valued two-form `F`. As in `TauCeti.Analysis.InnerProductSpace.HodgeStar.VectorValued`, such a
form is a linear map `F : ⋀² E →ₗ[ℝ] 𝔤`, the inner product on `𝔤` is a bilinear form `B`, and the
Hodge star acts on the form side, `⋆F = F ∘ ⋆⁻¹`, so that it is `⋆ ⊗ id_𝔤` and commutes with every
linear map of the values, in particular with `Ad(g)`. That file proves the self-dual splitting
`F = F⁺ + F⁻`, `|F|² = |F⁺|² + |F⁻|²`, `⟨F, ⋆F⟩ = |F⁺|² - |F⁻|²` and the pointwise Bogomol'nyi
inequality in this coordinate-free form.

This file reads these statements in a positively oriented orthonormal frame `(e₀, e₁, e₂, e₃)`,
with coefficients `F_ij = F (eᵢ ∧ eⱼ)`, in the normalisation used for Yang–Mills curvature:
`|F|² = ∑_{i < j} ⟨F_ij, F_ij⟩`, and the density `⋆⟨F ∧ F⟩` of the wedge square of
`F` paired by `B` is `2 (⟨F₀₁, F₂₃⟩ - ⟨F₀₂, F₁₃⟩ + ⟨F₀₃, F₁₂⟩)`. The main identity is that this
density is `⟨F, ⋆F⟩` (`Orientation.two_mul_wedgeDensity_eq_vectorFormInner_vectorFormHodgeStar`),
hence `|F⁺|² - |F⁻|²`, and that its absolute value is at most `|F|²`, with equality exactly when
`F⁺ = 0` or `F⁻ = 0`. For a compact matrix structure group, `Ad(g)` preserves the pairing of
forms (`TauCeti.CompactMatrixStructureGroup.vectorFormInner_matrixAdjointRepresentation_comp`).

The examples at the end fix the normalisation. For a nonzero `X`, the form
`F = X (e⁰ ∧ e¹ + e² ∧ e³)` is self-dual with `|F|² = ⋆⟨F ∧ F⟩ = 2 |X|²`, so the Bogomol'nyi
inequality is an equality; `F = X e⁰ ∧ e¹` has `F^± = ½ X (e⁰ ∧ e¹ ± e² ∧ e³)`, `|F|² = |X|²` and
`⋆⟨F ∧ F⟩ = 0`, so it is strict. Summing over all indices instead, as `8 (⟨F₀₁, F₂₃⟩ - …)`, would
make the first example violate the inequality.

## Main results

* `LinearMap.BilinForm.vectorFormInner_two_eq_sum_finFour`: the pairing of two-forms in a frame,
  `⟨F, G⟩ = ∑_{i < j} B (F_ij, G_ij)`.
* `Orientation.vectorFormInner_vectorFormHodgeStar_finFour`: `⟨F, ⋆G⟩` in a positive frame.
* `Orientation.two_mul_wedgeDensity_eq_sub`: `⋆⟨F ∧ F⟩ = |F⁺|² - |F⁻|²`.
* `Orientation.abs_two_mul_wedgeDensity_le`: the pointwise Bogomol'nyi inequality
  `|⋆⟨F ∧ F⟩| ≤ |F|²` in coordinates, and `Orientation.abs_two_mul_wedgeDensity_eq_iff`: its
  equality case.
* `TauCeti.CompactMatrixStructureGroup.vectorFormInner_matrixAdjointRepresentation_comp`: `Ad(g)`
  preserves the pairing of `𝔤`-valued forms.

## References

* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), arXiv:1709.08604, Lemma 1.31.
* S.-J. Oh and D. Tataru, *The Yang–Mills heat flow and the caloric gauge*, Astérisque 436
  (2022), arXiv:1709.08599, Lemma 6.9.
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup V] [Module ℝ V]

/-! ### The pairing in a frame -/

namespace OrthonormalBasis

variable (e : OrthonormalBasis (Fin 4) ℝ E)

/-- The six wedges `eᵢ ∧ eⱼ`, `i < j`, of an orthonormal basis indexed by `Fin 4`, in
lexicographic order. -/
private def wedgeTwoFamily : Fin 6 → ⋀[ℝ]^2 E :=
  ![ιMulti ℝ 2 ![e 0, e 1], ιMulti ℝ 2 ![e 0, e 2], ιMulti ℝ 2 ![e 0, e 3],
    ιMulti ℝ 2 ![e 1, e 2], ιMulti ℝ 2 ![e 1, e 3], ιMulti ℝ 2 ![e 2, e 3]]

private theorem orthonormal_wedgeTwoFamily : Orthonormal ℝ e.wedgeTwoFamily := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [wedgeTwoFamily, inner_ιMulti_two, e.inner_eq_ite]

private theorem top_le_span_wedgeTwoFamily :
    ⊤ ≤ Submodule.span ℝ (Set.range e.wedgeTwoFamily) := by
  intro x _
  have hmem (i : Fin 6) : e.wedgeTwoFamily i ∈ Submodule.span ℝ (Set.range e.wedgeTwoFamily) :=
    Submodule.subset_span ⟨i, rfl⟩
  rw [e.eq_sum_inner_smul_ιMulti_two x]
  refine add_mem (add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_) ?_ <;>
    refine Submodule.smul_mem _ _ ?_
  exacts [hmem 0, hmem 1, hmem 2, hmem 3, hmem 4, hmem 5]

/-- The orthonormal basis `eᵢ ∧ eⱼ`, `i < j`, of `⋀² E`, indexed by `Fin 6`. -/
private def wedgeTwoBasis : OrthonormalBasis (Fin 6) ℝ (⋀[ℝ]^2 E) :=
  OrthonormalBasis.mk e.orthonormal_wedgeTwoFamily e.top_le_span_wedgeTwoFamily

end OrthonormalBasis

namespace LinearMap.BilinForm

variable (B : LinearMap.BilinForm ℝ V)

/-- **The pairing of two-forms in a frame**: for an orthonormal basis `e` indexed by `Fin 4`,
`⟨F, G⟩ = ∑_{i < j} B (F (eᵢ ∧ eⱼ), G (eᵢ ∧ eⱼ))`. -/
theorem vectorFormInner_two_eq_sum_finFour (e : OrthonormalBasis (Fin 4) ℝ E)
    (F G : ⋀[ℝ]^2 E →ₗ[ℝ] V) :
    vectorFormInner B 2 F G =
      B (F (ιMulti ℝ 2 ![e 0, e 1])) (G (ιMulti ℝ 2 ![e 0, e 1])) +
        B (F (ιMulti ℝ 2 ![e 0, e 2])) (G (ιMulti ℝ 2 ![e 0, e 2])) +
        B (F (ιMulti ℝ 2 ![e 0, e 3])) (G (ιMulti ℝ 2 ![e 0, e 3])) +
        B (F (ιMulti ℝ 2 ![e 1, e 2])) (G (ιMulti ℝ 2 ![e 1, e 2])) +
        B (F (ιMulti ℝ 2 ![e 1, e 3])) (G (ιMulti ℝ 2 ![e 1, e 3])) +
        B (F (ιMulti ℝ 2 ![e 2, e 3])) (G (ιMulti ℝ 2 ![e 2, e 3])) := by
  rw [vectorFormInner_eq_sum e.wedgeTwoBasis]
  simp [Fin.sum_univ_six, OrthonormalBasis.wedgeTwoBasis, OrthonormalBasis.wedgeTwoFamily]

/-- For `F = X (e⁰ ∧ e¹ + e² ∧ e³)`, `|F|² = 2 B (X, X)`. -/
theorem vectorFormInner_smulRight_innerₗ_add (e : OrthonormalBasis (Fin 4) ℝ E) (X : V) :
    vectorFormInner B 2
        ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X)
        ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X) =
      2 * B X X := by
  rw [B.vectorFormInner_two_eq_sum_finFour e]
  simp [inner_ιMulti_two, e.inner_eq_ite]
  ring

/-- For `F = X e⁰ ∧ e¹`, `|F|² = B (X, X)`. -/
theorem vectorFormInner_smulRight_innerₗ (e : OrthonormalBasis (Fin 4) ℝ E) (X : V) :
    vectorFormInner B 2 ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1])).smulRight X)
        ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1])).smulRight X) = B X X := by
  rw [B.vectorFormInner_two_eq_sum_finFour e]
  simp [inner_ιMulti_two, e.inner_eq_ite]

end LinearMap.BilinForm

/-! ### The Hodge star and the wedge density in a positive frame -/

namespace Orientation

open LinearMap.BilinForm

variable [Fact (finrank ℝ E = 4)] {o : Orientation ℝ E (Fin 4)} (hkl : 2 + 2 = finrank ℝ E)
  {e : OrthonormalBasis (Fin 4) ℝ E} (he : e.toBasis.orientation = o)
include he

/-- For a positively oriented orthonormal basis `e` in dimension four, `⋆(e₁ ∧ e₃) = -(e₀ ∧ e₂)`. -/
private theorem hodgeStar_ιMulti_one_three :
    o.hodgeStar hkl (ιMulti ℝ 2 ![e 1, e 3]) = -ιMulti ℝ 2 ![e 0, e 2] := by
  rw [← neg_neg (ιMulti ℝ 2 ![e 1, e 3]), ← o.hodgeStar_ιMulti_zero_two hkl he, map_neg,
    o.hodgeStar_hodgeStar_of_even even_two hkl]

/-- For a positively oriented orthonormal basis `e` in dimension four, `⋆(e₁ ∧ e₂) = e₀ ∧ e₃`. -/
private theorem hodgeStar_ιMulti_one_two :
    o.hodgeStar hkl (ιMulti ℝ 2 ![e 1, e 2]) = ιMulti ℝ 2 ![e 0, e 3] := by
  rw [← o.hodgeStar_ιMulti_zero_three hkl he, o.hodgeStar_hodgeStar_of_even even_two hkl]

/-- **The pairing with a Hodge star in a positive frame**: for a positively oriented orthonormal
basis `e` in dimension four, with `F_ij = F (eᵢ ∧ eⱼ)`, `⟨F, ⋆G⟩` is
`B (F₀₁, G₂₃) - B (F₀₂, G₁₃) + B (F₀₃, G₁₂) + B (F₁₂, G₀₃) - B (F₁₃, G₀₂) + B (F₂₃, G₀₁)`. -/
theorem vectorFormInner_vectorFormHodgeStar_finFour (B : LinearMap.BilinForm ℝ V)
    (F G : ⋀[ℝ]^2 E →ₗ[ℝ] V) :
    vectorFormInner B 2 F (o.vectorFormHodgeStar hkl G) =
      B (F (ιMulti ℝ 2 ![e 0, e 1])) (G (ιMulti ℝ 2 ![e 2, e 3])) -
        B (F (ιMulti ℝ 2 ![e 0, e 2])) (G (ιMulti ℝ 2 ![e 1, e 3])) +
        B (F (ιMulti ℝ 2 ![e 0, e 3])) (G (ιMulti ℝ 2 ![e 1, e 2])) +
        B (F (ιMulti ℝ 2 ![e 1, e 2])) (G (ιMulti ℝ 2 ![e 0, e 3])) -
        B (F (ιMulti ℝ 2 ![e 1, e 3])) (G (ιMulti ℝ 2 ![e 0, e 2])) +
        B (F (ιMulti ℝ 2 ![e 2, e 3])) (G (ιMulti ℝ 2 ![e 0, e 1])) := by
  simp only [B.vectorFormInner_two_eq_sum_finFour e, o.vectorFormHodgeStar_apply_of_even even_two,
    o.hodgeStar_ιMulti_zero_one hkl he, o.hodgeStar_ιMulti_zero_two hkl he,
    o.hodgeStar_ιMulti_zero_three hkl he, hodgeStar_ιMulti_one_two hkl he,
    hodgeStar_ιMulti_one_three hkl he, o.hodgeStar_ιMulti_two_three hkl he, map_neg]
  ring

/-- **The wedge density in a positive frame**: for a symmetric `B` and a positively oriented
orthonormal basis `e` in dimension four, the density `⋆⟨F ∧ F⟩ = 2 (B (F₀₁, F₂₃) - B (F₀₂, F₁₃) +
B (F₀₃, F₁₂))` of the wedge square of `F` paired by `B` is `⟨F, ⋆F⟩`. -/
theorem two_mul_wedgeDensity_eq_vectorFormInner_vectorFormHodgeStar
    {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm) (F : ⋀[ℝ]^2 E →ₗ[ℝ] V) :
    2 * (B (F (ιMulti ℝ 2 ![e 0, e 1])) (F (ιMulti ℝ 2 ![e 2, e 3])) -
        B (F (ιMulti ℝ 2 ![e 0, e 2])) (F (ιMulti ℝ 2 ![e 1, e 3])) +
        B (F (ιMulti ℝ 2 ![e 0, e 3])) (F (ιMulti ℝ 2 ![e 1, e 2]))) =
      vectorFormInner B 2 F (o.vectorFormHodgeStar hkl F) := by
  rw [o.vectorFormInner_vectorFormHodgeStar_finFour hkl he, hB.eq (F (ιMulti ℝ 2 ![e 1, e 2])),
    hB.eq (F (ιMulti ℝ 2 ![e 1, e 3])), hB.eq (F (ιMulti ℝ 2 ![e 2, e 3]))]
  ring

/-- **The wedge density through the self-dual splitting**: for a symmetric `B` and a positively
oriented orthonormal basis in dimension four, `⋆⟨F ∧ F⟩ = |F⁺|² - |F⁻|²`. -/
theorem two_mul_wedgeDensity_eq_sub {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm)
    (F : ⋀[ℝ]^2 E →ₗ[ℝ] V) :
    2 * (B (F (ιMulti ℝ 2 ![e 0, e 1])) (F (ιMulti ℝ 2 ![e 2, e 3])) -
        B (F (ιMulti ℝ 2 ![e 0, e 2])) (F (ιMulti ℝ 2 ![e 1, e 3])) +
        B (F (ιMulti ℝ 2 ![e 0, e 3])) (F (ιMulti ℝ 2 ![e 1, e 2]))) =
      vectorFormInner B 2 (o.vectorFormSelfDualPart hkl F) (o.vectorFormSelfDualPart hkl F) -
        vectorFormInner B 2 (o.vectorFormAntiSelfDualPart hkl F)
          (o.vectorFormAntiSelfDualPart hkl F) := by
  rw [o.two_mul_wedgeDensity_eq_vectorFormInner_vectorFormHodgeStar hkl he hB,
    o.vectorFormInner_vectorFormHodgeStar_right_eq_sub even_two hkl]

/-- **The pointwise Bogomol'nyi inequality in a positive frame**: for a symmetric positive
semidefinite `B` and a positively oriented orthonormal basis in dimension four,
`|⋆⟨F ∧ F⟩| ≤ |F|²`. -/
theorem abs_two_mul_wedgeDensity_le {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm)
    (hB' : B.IsNonneg) (F : ⋀[ℝ]^2 E →ₗ[ℝ] V) :
    |2 * (B (F (ιMulti ℝ 2 ![e 0, e 1])) (F (ιMulti ℝ 2 ![e 2, e 3])) -
        B (F (ιMulti ℝ 2 ![e 0, e 2])) (F (ιMulti ℝ 2 ![e 1, e 3])) +
        B (F (ιMulti ℝ 2 ![e 0, e 3])) (F (ιMulti ℝ 2 ![e 1, e 2])))| ≤
      vectorFormInner B 2 F F := by
  have hkl : 2 + 2 = finrank ℝ E := by rw [(Fact.out : finrank ℝ E = 4)]
  rw [o.two_mul_wedgeDensity_eq_vectorFormInner_vectorFormHodgeStar hkl he hB]
  exact o.abs_vectorFormInner_vectorFormHodgeStar_le even_two hkl hB' F

/-- **The equality case of the Bogomol'nyi inequality in a positive frame**: for a symmetric
positive definite `B`, `|⋆⟨F ∧ F⟩| = |F|²` exactly when `F⁺ = 0` or `F⁻ = 0`. -/
theorem abs_two_mul_wedgeDensity_eq_iff {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm)
    (hB' : B.toQuadraticMap.PosDef) (F : ⋀[ℝ]^2 E →ₗ[ℝ] V) :
    |2 * (B (F (ιMulti ℝ 2 ![e 0, e 1])) (F (ιMulti ℝ 2 ![e 2, e 3])) -
        B (F (ιMulti ℝ 2 ![e 0, e 2])) (F (ιMulti ℝ 2 ![e 1, e 3])) +
        B (F (ιMulti ℝ 2 ![e 0, e 3])) (F (ιMulti ℝ 2 ![e 1, e 2])))| =
        vectorFormInner B 2 F F ↔
      o.vectorFormSelfDualPart hkl F = 0 ∨ o.vectorFormAntiSelfDualPart hkl F = 0 := by
  rw [o.two_mul_wedgeDensity_eq_vectorFormInner_vectorFormHodgeStar hkl he hB]
  exact o.abs_vectorFormInner_vectorFormHodgeStar_eq_iff even_two hkl hB' F

/-! ### Examples fixing the normalisation -/

/-- The form `F = X (e⁰ ∧ e¹ + e² ∧ e³)` is self-dual. -/
theorem vectorFormHodgeStar_smulRight_innerₗ_add (X : V) :
    o.vectorFormHodgeStar hkl
        ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X) =
      (innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X := by
  refine LinearMap.ext fun x ↦ ?_
  have hs : ⟪ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3], o.hodgeStar hkl x⟫ =
      ⟪o.hodgeStar hkl (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3]), x⟫ :=
    (o.isSymmetric_hodgeStar_of_even even_two hkl _ x).symm
  rw [map_add, o.hodgeStar_ιMulti_zero_one hkl he,
    o.hodgeStar_ιMulti_two_three hkl he, add_comm (ιMulti ℝ 2 ![e 2, e 3])] at hs
  rw [o.vectorFormHodgeStar_apply_of_even even_two, LinearMap.smulRight_apply,
    LinearMap.smulRight_apply, innerₗ_apply_apply, innerₗ_apply_apply, hs]

/-- **The self-dual example**: for `F = X (e⁰ ∧ e¹ + e² ∧ e³)`,
`⋆⟨F ∧ F⟩ = 2 B (X, X) = |F|²`, so the Bogomol'nyi inequality is an equality. -/
theorem two_mul_wedgeDensity_smulRight_innerₗ_add (B : LinearMap.BilinForm ℝ V) (X : V) :
    vectorFormInner B 2
        ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X)
        (o.vectorFormHodgeStar hkl
          ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X)) =
      2 * B X X := by
  rw [o.vectorFormHodgeStar_smulRight_innerₗ_add hkl he, B.vectorFormInner_smulRight_innerₗ_add e]

/-- **The normalisation is pinned**: for `F = X (e⁰ ∧ e¹ + e² ∧ e³)` with `B (X, X) > 0`, the
all-index sum `8 (B (F₀₁, F₂₃) - …)`, four times `⋆⟨F ∧ F⟩`, exceeds `|F|²`, so with that
normalisation the Bogomol'nyi inequality would fail. -/
theorem vectorFormInner_smulRight_innerₗ_add_lt {B : LinearMap.BilinForm ℝ V} {X : V}
    (hX : 0 < B X X) :
    vectorFormInner B 2
        ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X)
        ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X) <
      4 * vectorFormInner B 2
        ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X)
        (o.vectorFormHodgeStar hkl
          ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X)) := by
  rw [o.two_mul_wedgeDensity_smulRight_innerₗ_add hkl he, B.vectorFormInner_smulRight_innerₗ_add e]
  linarith

/-- For `F = X e⁰ ∧ e¹`, the self-dual part is `F⁺ = ½ X (e⁰ ∧ e¹ + e² ∧ e³)`. -/
theorem vectorFormSelfDualPart_smulRight_innerₗ (X : V) :
    o.vectorFormSelfDualPart hkl ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1])).smulRight X) =
      (innerₗ (⋀[ℝ]^2 E)
        ((2⁻¹ : ℝ) • (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3]))).smulRight X := by
  refine LinearMap.ext fun x ↦ ?_
  rw [vectorFormSelfDualPart_apply, LinearMap.smul_apply, LinearMap.add_apply,
    o.vectorFormHodgeStar_apply_of_even even_two]
  have hs : ⟪ιMulti ℝ 2 ![e 0, e 1], o.hodgeStar hkl x⟫ =
      ⟪o.hodgeStar hkl (ιMulti ℝ 2 ![e 0, e 1]), x⟫ :=
    (o.isSymmetric_hodgeStar_of_even even_two hkl _ x).symm
  rw [o.hodgeStar_ιMulti_zero_one hkl he] at hs
  simp only [LinearMap.smulRight_apply, innerₗ_apply_apply, hs, real_inner_smul_left,
    inner_add_left]
  module

/-- For `F = X e⁰ ∧ e¹`, the anti-self-dual part is `F⁻ = ½ X (e⁰ ∧ e¹ - e² ∧ e³)`. -/
theorem vectorFormAntiSelfDualPart_smulRight_innerₗ (X : V) :
    o.vectorFormAntiSelfDualPart hkl ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1])).smulRight X) =
      (innerₗ (⋀[ℝ]^2 E)
        ((2⁻¹ : ℝ) • (ιMulti ℝ 2 ![e 0, e 1] - ιMulti ℝ 2 ![e 2, e 3]))).smulRight X := by
  refine LinearMap.ext fun x ↦ ?_
  rw [vectorFormAntiSelfDualPart_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    o.vectorFormHodgeStar_apply_of_even even_two]
  have hs : ⟪ιMulti ℝ 2 ![e 0, e 1], o.hodgeStar hkl x⟫ =
      ⟪o.hodgeStar hkl (ιMulti ℝ 2 ![e 0, e 1]), x⟫ :=
    (o.isSymmetric_hodgeStar_of_even even_two hkl _ x).symm
  rw [o.hodgeStar_ιMulti_zero_one hkl he] at hs
  simp only [LinearMap.smulRight_apply, innerₗ_apply_apply, hs, real_inner_smul_left,
    inner_sub_left]
  module

/-- **The strict example**: for `F = X e⁰ ∧ e¹`, `⋆⟨F ∧ F⟩ = 0`, so when `B (X, X) > 0` the
Bogomol'nyi inequality `|⋆⟨F ∧ F⟩| ≤ |F|² = B (X, X)` is strict. -/
theorem vectorFormInner_smulRight_innerₗ_vectorFormHodgeStar (B : LinearMap.BilinForm ℝ V)
    (X : V) :
    vectorFormInner B 2 ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1])).smulRight X)
        (o.vectorFormHodgeStar hkl
          ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1])).smulRight X)) = 0 := by
  rw [o.vectorFormInner_vectorFormHodgeStar_finFour hkl he]
  simp [inner_ιMulti_two, e.inner_eq_ite]

end Orientation

/-! ### The adjoint action of a structure group -/

namespace TauCeti.CompactMatrixStructureGroup

open LinearMap.BilinForm

variable {n : Type*} [Fintype n] [DecidableEq n] (S : CompactMatrixStructureGroup n) {k : ℕ}

/-- The inner product of a compact matrix structure group, pulled back along `Ad(g)`, is itself. -/
@[simp]
theorem innerForm_compl₁₂_matrixAdjointRepresentation (g : S.group) :
    S.innerForm.compl₁₂ (S.group.matrixAdjointRepresentation g)
      (S.group.matrixAdjointRepresentation g) = S.innerForm :=
  LinearMap.ext fun X ↦ LinearMap.ext fun Y ↦ S.innerForm_matrixAdjointRepresentation g X Y

/-- **`Ad(g)` preserves the pairing of `𝔤`-valued forms**: for `g` in a compact matrix structure
group, `⟨Ad(g) F, Ad(g) G⟩ = ⟨F, G⟩`. Together with
`Orientation.vectorFormSelfDualPart_comp`, `Ad(g)` commutes with the Hodge star and the self-dual
splitting and preserves `|F⁺|` and `|F⁻|`. -/
theorem vectorFormInner_matrixAdjointRepresentation_comp (g : S.group)
    (F G : ⋀[ℝ]^k E →ₗ[ℝ] S.group.matrixLieAlgebra) :
    vectorFormInner S.innerForm k (S.group.matrixAdjointRepresentation g ∘ₗ F)
        (S.group.matrixAdjointRepresentation g ∘ₗ G) =
      vectorFormInner S.innerForm k F G := by
  rw [vectorFormInner_comp_comp, innerForm_compl₁₂_matrixAdjointRepresentation]

end TauCeti.CompactMatrixStructureGroup
