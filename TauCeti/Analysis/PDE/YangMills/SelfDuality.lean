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
`F` paired by `B` is `2 (⟨F₀₁, F₂₃⟩ - ⟨F₀₂, F₁₃⟩ + ⟨F₀₃, F₁₂⟩)`
(`LinearMap.BilinForm.wedgeDensity`). The main identity, read off from the frame expansion
`Orientation.vectorFormInner_vectorFormHodgeStar_fin_four` of `⟨F, ⋆G⟩`, is that this density is
`⟨F, ⋆F⟩` (`Orientation.wedgeDensity_eq_vectorFormInner_vectorFormHodgeStar`),
hence `|F⁺|² - |F⁻|²`, and that its absolute value is at most `|F|²`, with equality exactly when
`F⁺ = 0` or `F⁻ = 0`. For a compact matrix structure group, `Ad(g)` preserves the pairing of
forms (`TauCeti.CompactMatrixStructureGroup.vectorFormInner_matrixAdjointRepresentation_comp`).

The examples at the end fix the normalisation. For a nonzero `X`, the form
`F = X (e⁰ ∧ e¹ + e² ∧ e³)` is self-dual with `|F|² = ⋆⟨F ∧ F⟩ = 2 |X|²`, so the Bogomol'nyi
inequality is an equality; `F = X e⁰ ∧ e¹` has `F^± = ½ X (e⁰ ∧ e¹ ± e² ∧ e³)`, `|F|² = |X|²` and
`⋆⟨F ∧ F⟩ = 0`, so it is strict. Summing over all indices instead, as `8 (⟨F₀₁, F₂₃⟩ - …)`, would
make the first example violate the inequality. The examples specialise the decomposable-form
lemmas `Orientation.vectorFormHodgeStar_innerₗ`,
`LinearMap.BilinForm.vectorFormInner_smulRight_innerₗ_smulRight_innerₗ`,
`Orientation.vectorFormInner_smulRight_innerₗ_vectorFormHodgeStar_smulRight_innerₗ`,
`Orientation.vectorFormSelfDualPart_smulRight_innerₗ` and
`Orientation.vectorFormAntiSelfDualPart_smulRight_innerₗ` to the frame wedges.

## Main definitions

* `LinearMap.BilinForm.wedgeDensity`: the density `⋆⟨F ∧ F⟩` of a two-form in a frame.

## Main results

* `Orientation.wedgeDensity_eq_sub`: `⋆⟨F ∧ F⟩ = |F⁺|² - |F⁻|²`.
* `Orientation.abs_wedgeDensity_le`: the pointwise Bogomol'nyi inequality `|⋆⟨F ∧ F⟩| ≤ |F|²` in
  coordinates, and `Orientation.abs_wedgeDensity_eq_iff`: its equality case.
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

namespace LinearMap.BilinForm

variable (B : LinearMap.BilinForm ℝ V)

/-- For `F = X (e⁰ ∧ e¹ + e² ∧ e³)`, `|F|² = 2 B (X, X)`. -/
theorem vectorFormInner_smulRight_innerₗ_ιMulti_zero_one_add_ιMulti_two_three
    (e : OrthonormalBasis (Fin 4) ℝ E) (X : V) :
    vectorFormInner B 2
        ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X)
        ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X) =
      2 * B X X := by
  rw [vectorFormInner_smulRight_innerₗ_smulRight_innerₗ, inner_add_left, inner_add_right,
    inner_add_right]
  simp [inner_ιMulti_two, e.inner_eq_ite]
  ring

/-- For `F = X e⁰ ∧ e¹`, `|F|² = B (X, X)`. -/
theorem vectorFormInner_smulRight_innerₗ_ιMulti_zero_one (e : OrthonormalBasis (Fin 4) ℝ E)
    (X : V) :
    vectorFormInner B 2 ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1])).smulRight X)
        ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1])).smulRight X) = B X X := by
  rw [vectorFormInner_smulRight_innerₗ_smulRight_innerₗ, inner_ιMulti_two]
  simp [e.inner_eq_ite]

/-- **The wedge density in a frame**: for an orthonormal basis `e` indexed by `Fin 4` and a
`V`-valued two-form `F` with coefficients `F_ij = F (eᵢ ∧ eⱼ)`, the density
`⋆⟨F ∧ F⟩ = 2 (B (F₀₁, F₂₃) - B (F₀₂, F₁₃) + B (F₀₃, F₁₂))` of the wedge square of `F` paired
by `B`. For a symmetric `B` and a positively oriented `e` it is `⟨F, ⋆F⟩`
(`Orientation.wedgeDensity_eq_vectorFormInner_vectorFormHodgeStar`). -/
def wedgeDensity (e : OrthonormalBasis (Fin 4) ℝ E) (F : ⋀[ℝ]^2 E →ₗ[ℝ] V) : ℝ :=
  2 * (B (F (ιMulti ℝ 2 ![e 0, e 1])) (F (ιMulti ℝ 2 ![e 2, e 3])) -
    B (F (ιMulti ℝ 2 ![e 0, e 2])) (F (ιMulti ℝ 2 ![e 1, e 3])) +
    B (F (ιMulti ℝ 2 ![e 0, e 3])) (F (ιMulti ℝ 2 ![e 1, e 2])))

omit [FiniteDimensional ℝ E] in
theorem wedgeDensity_def (e : OrthonormalBasis (Fin 4) ℝ E) (F : ⋀[ℝ]^2 E →ₗ[ℝ] V) :
    B.wedgeDensity e F =
      2 * (B (F (ιMulti ℝ 2 ![e 0, e 1])) (F (ιMulti ℝ 2 ![e 2, e 3])) -
        B (F (ιMulti ℝ 2 ![e 0, e 2])) (F (ιMulti ℝ 2 ![e 1, e 3])) +
        B (F (ιMulti ℝ 2 ![e 0, e 3])) (F (ιMulti ℝ 2 ![e 1, e 2]))) :=
  (rfl)

end LinearMap.BilinForm

/-! ### The Hodge star and the wedge density in a positive frame -/

namespace Orientation

open LinearMap.BilinForm

variable [Fact (finrank ℝ E = 4)] {o : Orientation ℝ E (Fin 4)} (hkl : 2 + 2 = finrank ℝ E)
  {e : OrthonormalBasis (Fin 4) ℝ E} (he : e.toBasis.orientation = o)
include he

/-- **The wedge density in a positive frame**: for a symmetric `B` and a positively oriented
orthonormal basis `e` in dimension four, the density `⋆⟨F ∧ F⟩ = 2 (B (F₀₁, F₂₃) - B (F₀₂, F₁₃) +
B (F₀₃, F₁₂))` of the wedge square of `F` paired by `B` is `⟨F, ⋆F⟩`. -/
theorem wedgeDensity_eq_vectorFormInner_vectorFormHodgeStar {B : LinearMap.BilinForm ℝ V}
    (hB : B.IsSymm) (F : ⋀[ℝ]^2 E →ₗ[ℝ] V) :
    B.wedgeDensity e F = vectorFormInner B 2 F (o.vectorFormHodgeStar hkl F) := by
  rw [wedgeDensity_def, o.vectorFormInner_vectorFormHodgeStar_fin_four hkl he,
    hB.eq (F (ιMulti ℝ 2 ![e 1, e 2])),
    hB.eq (F (ιMulti ℝ 2 ![e 1, e 3])), hB.eq (F (ιMulti ℝ 2 ![e 2, e 3]))]
  ring

/-- **The wedge density through the self-dual splitting**: for a symmetric `B` and a positively
oriented orthonormal basis in dimension four, `⋆⟨F ∧ F⟩ = |F⁺|² - |F⁻|²`. -/
theorem wedgeDensity_eq_sub {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm)
    (F : ⋀[ℝ]^2 E →ₗ[ℝ] V) :
    B.wedgeDensity e F =
      vectorFormInner B 2 (o.vectorFormSelfDualPart hkl F) (o.vectorFormSelfDualPart hkl F) -
        vectorFormInner B 2 (o.vectorFormAntiSelfDualPart hkl F)
          (o.vectorFormAntiSelfDualPart hkl F) := by
  rw [o.wedgeDensity_eq_vectorFormInner_vectorFormHodgeStar hkl he hB,
    o.vectorFormInner_vectorFormHodgeStar_right_eq_sub even_two hkl]

/-- **The pointwise Bogomol'nyi inequality in a positive frame**: for a symmetric positive
semidefinite `B` and a positively oriented orthonormal basis in dimension four,
`|⋆⟨F ∧ F⟩| ≤ |F|²`. -/
theorem abs_wedgeDensity_le {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm)
    (hB' : B.IsNonneg) (F : ⋀[ℝ]^2 E →ₗ[ℝ] V) :
    |B.wedgeDensity e F| ≤ vectorFormInner B 2 F F := by
  have hkl : 2 + 2 = finrank ℝ E := by rw [(Fact.out : finrank ℝ E = 4)]
  rw [o.wedgeDensity_eq_vectorFormInner_vectorFormHodgeStar hkl he hB]
  exact o.abs_vectorFormInner_vectorFormHodgeStar_le even_two hkl hB' F

/-- **The equality case of the Bogomol'nyi inequality in a positive frame**: for a symmetric
positive definite `B`, `|⋆⟨F ∧ F⟩| = |F|²` exactly when `F⁺ = 0` or `F⁻ = 0`. -/
theorem abs_wedgeDensity_eq_iff {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm)
    (hB' : B.toQuadraticMap.PosDef) (F : ⋀[ℝ]^2 E →ₗ[ℝ] V) :
    |B.wedgeDensity e F| = vectorFormInner B 2 F F ↔
      o.vectorFormSelfDualPart hkl F = 0 ∨ o.vectorFormAntiSelfDualPart hkl F = 0 := by
  rw [o.wedgeDensity_eq_vectorFormInner_vectorFormHodgeStar hkl he hB]
  exact o.abs_vectorFormInner_vectorFormHodgeStar_eq_iff even_two hkl hB' F

/-! ### Examples fixing the normalisation -/

/-- The form `F = X (e⁰ ∧ e¹ + e² ∧ e³)` is self-dual. -/
theorem vectorFormHodgeStar_smulRight_innerₗ_ιMulti_zero_one_add_ιMulti_two_three_eq_self
    (X : V) :
    o.vectorFormHodgeStar hkl
        ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X) =
      (innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X := by
  rw [vectorFormHodgeStar_smulRight, vectorFormHodgeStar_innerₗ, map_add,
    o.hodgeStar_ιMulti_zero_one hkl he, o.hodgeStar_ιMulti_two_three hkl he, add_comm]

/-- **The self-dual example**: for `F = X (e⁰ ∧ e¹ + e² ∧ e³)`, `⟨F, ⋆F⟩ = 2 B (X, X) = |F|²`.
For symmetric `B` this is the density `⋆⟨F ∧ F⟩`, so the Bogomol'nyi inequality is an
equality. -/
theorem vectorFormInner_smulRight_innerₗ_ιMulti_zero_one_add_ιMulti_two_three_vectorFormHodgeStar
    (B : LinearMap.BilinForm ℝ V) (X : V) :
    vectorFormInner B 2
        ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X)
        (o.vectorFormHodgeStar hkl
          ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X)) =
      2 * B X X := by
  rw [o.vectorFormHodgeStar_smulRight_innerₗ_ιMulti_zero_one_add_ιMulti_two_three_eq_self hkl he,
    B.vectorFormInner_smulRight_innerₗ_ιMulti_zero_one_add_ιMulti_two_three e]

/-- **The normalisation is pinned**: for `F = X (e⁰ ∧ e¹ + e² ∧ e³)` with `B (X, X) > 0`, the
all-index sum `8 (B (F₀₁, F₂₃) - …)`, four times `⋆⟨F ∧ F⟩`, exceeds `|F|²`, so with that
normalisation the Bogomol'nyi inequality would fail. -/
theorem vectorFormInner_smulRight_innerₗ_ιMulti_zero_one_add_ιMulti_two_three_lt
    {B : LinearMap.BilinForm ℝ V} {X : V} (hX : 0 < B X X) :
    vectorFormInner B 2
        ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X)
        ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X) <
      4 * vectorFormInner B 2
        ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X)
        (o.vectorFormHodgeStar hkl
          ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])).smulRight X)) := by
  rw [vectorFormInner_smulRight_innerₗ_ιMulti_zero_one_add_ιMulti_two_three_vectorFormHodgeStar
      hkl he,
    B.vectorFormInner_smulRight_innerₗ_ιMulti_zero_one_add_ιMulti_two_three e]
  linarith

/-- For `F = X e⁰ ∧ e¹`, the self-dual part is `F⁺ = ½ X (e⁰ ∧ e¹ + e² ∧ e³)`. -/
theorem vectorFormSelfDualPart_smulRight_innerₗ_ιMulti_zero_one (X : V) :
    o.vectorFormSelfDualPart hkl ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1])).smulRight X) =
      (innerₗ (⋀[ℝ]^2 E)
        ((2⁻¹ : ℝ) • (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3]))).smulRight X := by
  rw [vectorFormSelfDualPart_smulRight_innerₗ, o.hodgeStar_ιMulti_zero_one hkl he]

/-- For `F = X e⁰ ∧ e¹`, the anti-self-dual part is `F⁻ = ½ X (e⁰ ∧ e¹ - e² ∧ e³)`. -/
theorem vectorFormAntiSelfDualPart_smulRight_innerₗ_ιMulti_zero_one (X : V) :
    o.vectorFormAntiSelfDualPart hkl ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1])).smulRight X) =
      (innerₗ (⋀[ℝ]^2 E)
        ((2⁻¹ : ℝ) • (ιMulti ℝ 2 ![e 0, e 1] - ιMulti ℝ 2 ![e 2, e 3]))).smulRight X := by
  rw [vectorFormAntiSelfDualPart_smulRight_innerₗ, o.hodgeStar_ιMulti_zero_one hkl he]

/-- **The strict example**: for `F = X e⁰ ∧ e¹`, `⟨F, ⋆F⟩ = 0`. For symmetric `B` this is the
density `⋆⟨F ∧ F⟩`, so when `B (X, X) > 0` the Bogomol'nyi inequality
`|⋆⟨F ∧ F⟩| ≤ |F|² = B (X, X)` is strict. -/
theorem vectorFormInner_smulRight_innerₗ_ιMulti_zero_one_vectorFormHodgeStar
    (B : LinearMap.BilinForm ℝ V) (X : V) :
    vectorFormInner B 2 ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1])).smulRight X)
        (o.vectorFormHodgeStar hkl
          ((innerₗ (⋀[ℝ]^2 E) (ιMulti ℝ 2 ![e 0, e 1])).smulRight X)) = 0 := by
  rw [vectorFormInner_smulRight_innerₗ_vectorFormHodgeStar_smulRight_innerₗ,
    o.hodgeStar_ιMulti_zero_one hkl he, inner_ιMulti_two]
  simp [e.inner_eq_ite]

end Orientation

/-! ### The adjoint action of a structure group -/

namespace TauCeti.CompactMatrixStructureGroup

open LinearMap.BilinForm

variable {n : Type*} [Fintype n] [DecidableEq n] (S : CompactMatrixStructureGroup n) {k : ℕ}

/-- **`Ad(g)` preserves the pairing of `𝔤`-valued forms**: for `g` in a compact matrix structure
group, `⟨Ad(g) F, Ad(g) G⟩ = ⟨F, G⟩`. Together with
`Orientation.vectorFormSelfDualPart_comp`, `Ad(g)` commutes with the Hodge star and the self-dual
splitting and preserves `|F⁺|` and `|F⁻|`. -/
theorem vectorFormInner_matrixAdjointRepresentation_comp (g : S.group)
    (F G : ⋀[ℝ]^k E →ₗ[ℝ] S.group.matrixLieAlgebra) :
    vectorFormInner S.innerForm k (S.group.matrixAdjointRepresentation g ∘ₗ F)
        (S.group.matrixAdjointRepresentation g ∘ₗ G) =
      vectorFormInner S.innerForm k F G := by
  have hAd : S.innerForm.compl₁₂ (S.group.matrixAdjointRepresentation g)
      (S.group.matrixAdjointRepresentation g) = S.innerForm :=
    LinearMap.ext fun X ↦ LinearMap.ext fun Y ↦ S.innerForm_matrixAdjointRepresentation g X Y
  rw [vectorFormInner_comp_comp, hAd]

end TauCeti.CompactMatrixStructureGroup
