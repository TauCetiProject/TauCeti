/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import TauCeti.Analysis.InnerProductSpace.Comass
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.AlternatingForm

/-!
# Vector-valued forms: Hodge star, pairing and self-duality

Let `E` be a finite-dimensional oriented real inner product space and `V` a real vector space.
A `V`-valued `k`-form on `E` is recorded here as a linear map `F : ⋀ᵏ E →ₗ[ℝ] V` on the
`k`-vectors of `E`; its coefficients in a frame `(eᵢ)` are `F (e_{i₁} ∧ ⋯ ∧ e_{iₖ})`. Continuous
alternating maps `E [⋀^Fin k]→L[ℝ] V` correspond to these linear maps through
`exteriorPower.continuousAlternatingMapLinearEquiv`. The typical `V` is the Lie algebra `𝔤` of a
compact structure group, carrying an `Ad`-invariant inner product given as a bilinear form `B`
on `V`: the curvature of a connection is a `𝔤`-valued two-form.

* The **Hodge star** `Orientation.vectorFormHodgeStar` acts on `V`-valued forms by precomposition
  with the inverse of the Hodge star of `⋀ˡ E`. On real-valued forms it is the Hodge star of forms
  `Orientation.formHodgeStar`
  (`Orientation.vectorFormHodgeStar_continuousAlternatingMapLinearEquiv`), and it commutes with
  every linear map `V → W` (`Orientation.vectorFormHodgeStar_comp`), so it is the Hodge star
  applied to each coefficient.
* The **pairing** `LinearMap.BilinForm.vectorFormInner B k` is `⟨F, G⟩ = ∑ᵢ B (F cᵢ) (G cᵢ)` for
  any orthonormal basis `(cᵢ)` of `⋀ᵏ E` (`LinearMap.BilinForm.vectorFormInner_eq_sum`). In an
  orthonormal frame of `E` it is `∑_{i₁ < ⋯ < iₖ} B (F_I, G_I)`
  (`LinearMap.BilinForm.vectorFormInner_eq_sum_powersetCard`), so for two-forms
  `|F|² = ∑_{j < k} ⟨F_jk, F_jk⟩`. For real-valued forms it is the inner product of forms
  `TauCeti.alternatingFormInner`.

In an even middle degree `k + k = dim E`, for instance two-forms in dimension four, the star is an
involution, self-adjoint for every pairing. A form splits as `F = F⁺ + F⁻` into its self-dual part
`F⁺ = (F + ⋆F) / 2` and anti-self-dual part `F⁻ = (F - ⋆F) / 2`, which are orthogonal, so
`|F|² = |F⁺|² + |F⁻|²`. The density `⟨F, ⋆F⟩` is `|F⁺|² - |F⁻|²`. For forms `X α` and `Y β` with
real-valued `α`, `β` it is `B (X, Y)` times the coefficient of `α ∧ β` on a positively oriented
orthonormal frame (`Orientation.vectorFormInner_smulRight_vectorFormHodgeStar_smulRight`); by
bilinearity `⟨F, ⋆F⟩` is therefore the density `⋆⟨F ∧ F⟩` of the wedge square of `F` paired by
`B`, the integrand of the characteristic number of a curvature form. When `B` is
positive semidefinite this gives the pointwise **Bogomol'nyi inequality** `|⋆⟨F ∧ F⟩| ≤ |F|²`,
with equality, for `B` positive definite, exactly when `F` is self-dual or anti-self-dual. A linear
map `T : V → W`, such as `Ad(g)` on `𝔤`, commutes with `⋆` and with both projections, and
preserves the pairing when it preserves `B`; reversing the orientation exchanges `F⁺` and `F⁻`.

## Main definitions

* `Orientation.vectorFormHodgeStar`: the Hodge star of `V`-valued forms.
* `LinearMap.BilinForm.vectorFormInner`: the pairing of `V`-valued forms induced by a bilinear form
  on `V`.
* `Orientation.vectorFormSelfDualPart`, `Orientation.vectorFormAntiSelfDualPart`: the maps
  `F ↦ (F ± ⋆F) / 2`.

## Main results

* `Orientation.vectorFormInner_vectorFormHodgeStar`: the Hodge star preserves the pairing.
* `Orientation.vectorFormInner_vectorFormHodgeStar_left`: in an even middle degree it is
  self-adjoint.
* `Orientation.vectorFormAntiSelfDualPart_eq_zero_iff`,
  `Orientation.vectorFormSelfDualPart_eq_zero_iff`: `F⁻ = 0 ↔ ⋆F = F` and `F⁺ = 0 ↔ ⋆F = -F`.
* `Orientation.vectorFormInner_eq_add`: `⟨F, G⟩ = ⟨F⁺, G⁺⟩ + ⟨F⁻, G⁻⟩`.
* `Orientation.vectorFormInner_vectorFormHodgeStar_right_eq_sub`: `⟨F, ⋆G⟩ = ⟨F⁺, G⁺⟩ - ⟨F⁻, G⁻⟩`.
* `Orientation.abs_vectorFormInner_vectorFormHodgeStar_le`: the Bogomol'nyi inequality
  `|⟨F, ⋆F⟩| ≤ ⟨F, F⟩`, and `Orientation.abs_vectorFormInner_vectorFormHodgeStar_eq_iff`: its
  equality case.
* `Orientation.vectorFormSelfDualPart_neg_orientation`: reversing the orientation exchanges the two
  parts.

## References

* M. F. Atiyah, N. J. Hitchin and I. M. Singer, *Self-duality in four-dimensional Riemannian
  geometry*, Proc. Roy. Soc. London Ser. A 362 (1978), 425–461.
* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), arXiv:1709.08604, Lemma 1.31 (the
  computation `⋆⟨F ∧ F⟩ = |F⁺|² - |F⁻|²`).
* S.-J. Oh and D. Tataru, *The Yang–Mills heat flow and the caloric gauge*, Astérisque 436
  (2022), arXiv:1709.08599, Lemma 6.9 (the self-dual splitting and the Bogomol'nyi inequality).
* E. B. Bogomol'nyi, *The stability of classical solutions*, Sov. J. Nucl. Phys. 24 (1976)
  (the Bogomol'nyi inequality).
-/

public section

noncomputable section

open Module exteriorPower Set
open scoped RealInnerProductSpace

variable {E V W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

namespace LinearMap.BilinForm

open TauCeti

/-! ### The pairing of vector-valued forms -/

/-- The pairing `⟨F, G⟩ = ∑ᵢ B (F cᵢ) (G cᵢ)` of `V`-valued `k`-forms `F, G : ⋀ᵏ E →ₗ[ℝ] V`
induced by a bilinear form `B` on `V`, where `(cᵢ)` is any orthonormal basis of `⋀ᵏ E`
(`LinearMap.BilinForm.vectorFormInner_eq_sum`): the metric trace of the bilinear form
`B (F ·) (G ·)` on `⋀ᵏ E`. In an orthonormal frame of `E` it is the sum of `B` over the coefficients
with increasing indices (`LinearMap.BilinForm.vectorFormInner_eq_sum_powersetCard`). -/
def vectorFormInner (B : LinearMap.BilinForm ℝ V) (k : ℕ) :
    LinearMap.BilinForm ℝ (⋀[ℝ]^k E →ₗ[ℝ] V) :=
  LinearMap.mk₂ ℝ (fun F G ↦ bilinFormTrace (B.compl₁₂ F G))
    (fun _ _ _ ↦ by
      simp [bilinFormTrace_eq_sum _ (stdOrthonormalBasis ℝ _), Finset.sum_add_distrib])
    (fun _ _ _ ↦ by simp [bilinFormTrace_eq_sum _ (stdOrthonormalBasis ℝ _), Finset.mul_sum])
    (fun _ _ _ ↦ by
      simp [bilinFormTrace_eq_sum _ (stdOrthonormalBasis ℝ _), Finset.sum_add_distrib])
    (fun _ _ _ ↦ by simp [bilinFormTrace_eq_sum _ (stdOrthonormalBasis ℝ _), Finset.mul_sum])

variable {B : LinearMap.BilinForm ℝ V} {k : ℕ}

/-- The pairing is the metric trace of the bilinear form `B (F ·) (G ·)` on `⋀ᵏ E`. -/
theorem vectorFormInner_apply (F G : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    vectorFormInner B k F G = bilinFormTrace (B.compl₁₂ F G) :=
  (rfl)

/-- **The pairing in an orthonormal basis** `(cᵢ)` of `⋀ᵏ E`:
`⟨F, G⟩ = ∑ᵢ B (F cᵢ) (G cᵢ)`. -/
theorem vectorFormInner_eq_sum {ι : Type*} [Fintype ι] (c : OrthonormalBasis ι ℝ (⋀[ℝ]^k E))
    (F G : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    vectorFormInner B k F G = ∑ i, B (F (c i)) (G (c i)) := by
  rw [vectorFormInner_apply, bilinFormTrace_eq_sum _ c]
  simp

/-- **The pairing in an orthonormal frame** `(eᵢ)` of `E` indexed by a linear order:
`⟨F, G⟩ = ∑ B (F (e_{i₁} ∧ ⋯ ∧ e_{iₖ})) (G (e_{i₁} ∧ ⋯ ∧ e_{iₖ}))`, the sum running over the
increasing `k`-tuples `i₁ < ⋯ < iₖ`. For two-forms with coefficients `F_jk` this is
`∑_{j < k} B (F_jk, G_jk)`. -/
theorem vectorFormInner_eq_sum_powersetCard {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : OrthonormalBasis ι ℝ E) (F G : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    vectorFormInner B k F G = ∑ s : powersetCard ι k,
      B (F (ιMulti ℝ k (b ∘ powersetCard.ofFinEmbEquiv.symm s)))
        (G (ιMulti ℝ k (b ∘ powersetCard.ofFinEmbEquiv.symm s))) := by
  rw [vectorFormInner_eq_sum (b.exteriorPower k)]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [← OrthonormalBasis.coe_toBasis, OrthonormalBasis.toBasis_exteriorPower, basis_apply,
    ιMulti_family, OrthonormalBasis.coe_toBasis]

/-- The pairing of `T ∘ F` and `T ∘ G` for a linear map `T : V → W` is the pairing of `F` and `G`
for the pulled-back form `B (T ·) (T ·)`. In particular a linear map preserving the bilinear forms
preserves the pairing. -/
@[simp]
theorem vectorFormInner_comp_comp (B : LinearMap.BilinForm ℝ W) (T : V →ₗ[ℝ] W)
    (F G : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    vectorFormInner B k (T ∘ₗ F) (T ∘ₗ G) = vectorFormInner (B.compl₁₂ T T) k F G := by
  simp [vectorFormInner_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^k E))]

/-- The pairing of the decomposable forms `X f` and `Y g`, with `f, g` real-valued and `X, Y ∈ V`,
is `B (X, Y)` times the pairing of `f` and `g`. -/
theorem vectorFormInner_smulRight_smulRight (f g : ⋀[ℝ]^k E →ₗ[ℝ] ℝ) (X Y : V) :
    vectorFormInner B k (f.smulRight X) (g.smulRight Y) =
      B X Y * vectorFormInner (LinearMap.mul ℝ ℝ) k f g := by
  simp only [vectorFormInner_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^k E)), LinearMap.smulRight_apply,
    map_smul, LinearMap.smul_apply, smul_eq_mul, LinearMap.mul_apply', Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- For real-valued forms, read as linear maps on `⋀ᵏ E`, the pairing for the product of real
numbers is the inner product of forms `TauCeti.alternatingFormInner`. -/
@[simp]
theorem vectorFormInner_mul_continuousAlternatingMapLinearEquiv
    (α β : E [⋀^Fin k]→L[ℝ] ℝ) :
    vectorFormInner (LinearMap.mul ℝ ℝ) k (continuousAlternatingMapLinearEquiv ℝ E k ℝ α)
        (continuousAlternatingMapLinearEquiv ℝ E k ℝ β) =
      alternatingFormInner E k α β := by
  obtain ⟨a, rfl⟩ := (alternatingFormEquiv E k).surjective α
  obtain ⟨b, rfl⟩ := (alternatingFormEquiv E k).surjective β
  rw [continuousAlternatingMapLinearEquiv_alternatingFormEquiv,
    continuousAlternatingMapLinearEquiv_alternatingFormEquiv,
    alternatingFormInner_alternatingFormEquiv,
    vectorFormInner_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^k E)),
    ← (stdOrthonormalBasis ℝ (⋀[ℝ]^k E)).sum_inner_mul_inner a b]
  simp [real_inner_comm b]

/-- The pairing is symmetric when `B` is. -/
theorem isSymm_vectorFormInner (hB : B.IsSymm) :
    (vectorFormInner B k : LinearMap.BilinForm ℝ (⋀[ℝ]^k E →ₗ[ℝ] V)).IsSymm :=
  ⟨fun F G ↦ by simp only [vectorFormInner_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^k E)), hB.eq (F _)]⟩

/-- The pairing is nonnegative when `B` is. -/
theorem isNonneg_vectorFormInner (hB : B.IsNonneg) :
    (vectorFormInner B k : LinearMap.BilinForm ℝ (⋀[ℝ]^k E →ₗ[ℝ] V)).IsNonneg :=
  ⟨fun F ↦ by
    rw [vectorFormInner_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^k E))]
    exact Finset.sum_nonneg fun _ _ ↦ hB.nonneg _⟩

/-- The pairing is definite when `B` is positive definite: `⟨F, F⟩ = 0` only for `F = 0`. -/
theorem vectorFormInner_self_eq_zero (hB : B.toQuadraticMap.PosDef) {F : ⋀[ℝ]^k E →ₗ[ℝ] V} :
    vectorFormInner B k F F = 0 ↔ F = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  set c := stdOrthonormalBasis ℝ (⋀[ℝ]^k E)
  have hnonneg (X : V) : 0 ≤ B X X := hB.nonneg X
  rw [vectorFormInner_eq_sum c, Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ hnonneg _] at h
  refine c.toBasis.ext fun i ↦ ?_
  rw [OrthonormalBasis.coe_toBasis, LinearMap.zero_apply]
  exact hB.anisotropic _ (h i (Finset.mem_univ i))

/-- The pairing is positive definite when `B` is. -/
theorem posDef_vectorFormInner (hB : B.toQuadraticMap.PosDef) :
    (vectorFormInner B k : LinearMap.BilinForm ℝ (⋀[ℝ]^k E →ₗ[ℝ] V)).toQuadraticMap.PosDef :=
  fun F hF ↦ lt_of_le_of_ne ((isNonneg_vectorFormInner ⟨hB.nonneg⟩).nonneg F)
    (Ne.symm ((vectorFormInner_self_eq_zero hB).not.mpr hF))

end LinearMap.BilinForm

namespace Orientation

open TauCeti LinearMap.BilinForm

variable {n : ℕ} [_i : Fact (finrank ℝ E = n)] (o : Orientation ℝ E (Fin n))

/-! ### The Hodge star of vector-valued forms -/

/-- The Hodge star of `V`-valued forms, `k`-forms to `l`-forms for `k + l = finrank ℝ E`: a form
`F : ⋀ᵏ E →ₗ[ℝ] V` is sent to `F ∘ ⋆⁻¹`. On real-valued forms it is the Hodge star of forms
(`Orientation.vectorFormHodgeStar_continuousAlternatingMapLinearEquiv`), and it commutes with
linear maps of the values (`Orientation.vectorFormHodgeStar_comp`), so it acts coefficientwise. -/
def vectorFormHodgeStar {k l : ℕ} (hkl : k + l = finrank ℝ E) :
    (⋀[ℝ]^k E →ₗ[ℝ] V) ≃ₗ[ℝ] ⋀[ℝ]^l E →ₗ[ℝ] V :=
  (o.hodgeStar hkl).arrowCongr (LinearEquiv.refl ℝ V)

variable {k l : ℕ}

/-- The Hodge star of `F` evaluates on an `l`-vector `x` as `F (⋆⁻¹ x)`. -/
@[simp]
theorem vectorFormHodgeStar_apply (hkl : k + l = finrank ℝ E) (F : ⋀[ℝ]^k E →ₗ[ℝ] V)
    (x : ⋀[ℝ]^l E) : o.vectorFormHodgeStar hkl F x = F ((o.hodgeStar hkl).symm x) := by
  simp [vectorFormHodgeStar]

/-- The inverse Hodge star of an `l`-form `G` evaluates on a `k`-vector `y` as `G (⋆y)`. -/
@[simp]
theorem vectorFormHodgeStar_symm_apply (hkl : k + l = finrank ℝ E) (G : ⋀[ℝ]^l E →ₗ[ℝ] V)
    (y : ⋀[ℝ]^k E) : (o.vectorFormHodgeStar hkl).symm G y = G (o.hodgeStar hkl y) := by
  simp [vectorFormHodgeStar]

/-- The Hodge star of `V`-valued forms commutes with every linear map `T : V → W` of the values. -/
@[simp]
theorem vectorFormHodgeStar_comp (hkl : k + l = finrank ℝ E) (T : V →ₗ[ℝ] W)
    (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    o.vectorFormHodgeStar hkl (T ∘ₗ F) = T ∘ₗ o.vectorFormHodgeStar hkl F := by
  ext x
  simp

/-- The Hodge star of a decomposable form `X f`, with `f` real-valued, is `X ⋆f`. -/
@[simp]
theorem vectorFormHodgeStar_smulRight (hkl : k + l = finrank ℝ E) (f : ⋀[ℝ]^k E →ₗ[ℝ] ℝ)
    (X : V) :
    o.vectorFormHodgeStar hkl (f.smulRight X) = (o.vectorFormHodgeStar hkl f).smulRight X := by
  refine LinearMap.ext fun x ↦ ?_
  simp

/-- On real-valued forms, read as linear maps on `⋀ᵏ E`, the Hodge star of vector-valued forms is
the Hodge star of forms. -/
@[simp]
theorem vectorFormHodgeStar_continuousAlternatingMapLinearEquiv (hkl : k + l = finrank ℝ E)
    (α : E [⋀^Fin k]→L[ℝ] ℝ) :
    o.vectorFormHodgeStar hkl (continuousAlternatingMapLinearEquiv ℝ E k ℝ α) =
      continuousAlternatingMapLinearEquiv ℝ E l ℝ (o.formHodgeStar hkl α) := by
  obtain ⟨a, rfl⟩ := (alternatingFormEquiv E k).surjective α
  rw [formHodgeStar_alternatingFormEquiv, continuousAlternatingMapLinearEquiv_alternatingFormEquiv,
    continuousAlternatingMapLinearEquiv_alternatingFormEquiv]
  refine LinearMap.ext fun x ↦ ?_
  -- `⟪a, ⋆⁻¹ x⟫ = ⟪⋆a, x⟫`, since the Hodge star is an isometry.
  rw [vectorFormHodgeStar_apply, innerₗ_apply_apply, innerₗ_apply_apply,
    ← o.inner_hodgeStar_hodgeStar hkl, LinearEquiv.apply_symm_apply]

/-- Reversing the orientation negates the Hodge star of vector-valued forms. -/
@[simp]
theorem vectorFormHodgeStar_neg_orientation (hkl : k + l = finrank ℝ E)
    (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    (-o).vectorFormHodgeStar hkl F = -o.vectorFormHodgeStar hkl F := by
  refine LinearMap.ext fun x ↦ ?_
  have hx : ((-o).hodgeStar hkl).symm x = -(o.hodgeStar hkl).symm x := by
    rw [LinearEquiv.symm_apply_eq, hodgeStar_neg_orientation, map_neg, neg_neg,
      LinearEquiv.apply_symm_apply]
  simp [hx]

/-- **The Hodge star preserves the pairing** of vector-valued forms. -/
@[simp]
theorem vectorFormInner_vectorFormHodgeStar (B : LinearMap.BilinForm ℝ V)
    (hkl : k + l = finrank ℝ E) (F G : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    vectorFormInner B l (o.vectorFormHodgeStar hkl F) (o.vectorFormHodgeStar hkl G) =
      vectorFormInner B k F G := by
  set c := stdOrthonormalBasis ℝ (⋀[ℝ]^k E)
  rw [vectorFormInner_eq_sum (c.map (o.hodgeStarIsometry hkl)), vectorFormInner_eq_sum c]
  simp [hodgeStarIsometry_apply]

/-! ### The even middle degree -/

section Even

variable (hk : Even k) (hkk : k + k = finrank ℝ E)
include hk

/-- In an even middle degree the Hodge star of vector-valued forms is precomposition with `⋆`. -/
theorem vectorFormHodgeStar_apply_of_even (F : ⋀[ℝ]^k E →ₗ[ℝ] V) (x : ⋀[ℝ]^k E) :
    o.vectorFormHodgeStar hkk F x = F (o.hodgeStar hkk x) := by
  rw [vectorFormHodgeStar_apply]
  congr 1
  rw [LinearEquiv.symm_apply_eq, o.hodgeStar_hodgeStar_of_even hk]

/-- In an even middle degree the Hodge star of vector-valued forms is an involution. -/
@[simp]
theorem vectorFormHodgeStar_vectorFormHodgeStar_of_even (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    o.vectorFormHodgeStar hkk (o.vectorFormHodgeStar hkk F) = F := by
  refine LinearMap.ext fun x ↦ ?_
  rw [o.vectorFormHodgeStar_apply_of_even hk, o.vectorFormHodgeStar_apply_of_even hk,
    o.hodgeStar_hodgeStar_of_even hk]

/-- In an even middle degree the Hodge star is self-adjoint for every pairing:
`⟨⋆F, G⟩ = ⟨F, ⋆G⟩`. -/
theorem vectorFormInner_vectorFormHodgeStar_left (B : LinearMap.BilinForm ℝ V)
    (F G : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    vectorFormInner B k (o.vectorFormHodgeStar hkk F) G =
      vectorFormInner B k F (o.vectorFormHodgeStar hkk G) := by
  conv_lhs => rw [← o.vectorFormHodgeStar_vectorFormHodgeStar_of_even hk hkk G]
  exact o.vectorFormInner_vectorFormHodgeStar B hkk F _

/-- **The density of the wedge square on decomposable forms**: for real-valued forms `α`, `β`,
vectors `X, Y ∈ V` and a positively oriented orthonormal basis `b`, in an even middle degree,
`⟨X α, ⋆(Y β)⟩ = B (X, Y) (α ∧ β)(b₁, …, bₙ)`. So `⟨F, ⋆G⟩` is the coefficient on `b` of the
wedge of `F` and `G` paired by `B`. -/
theorem vectorFormInner_smulRight_vectorFormHodgeStar_smulRight (B : LinearMap.BilinForm ℝ V)
    (b : OrthonormalBasis (Fin n) ℝ E) (hb : b.toBasis.orientation = o)
    (α β : E [⋀^Fin k]→L[ℝ] ℝ) (X Y : V) :
    vectorFormInner B k ((continuousAlternatingMapLinearEquiv ℝ E k ℝ α).smulRight X)
        (o.vectorFormHodgeStar hkk ((continuousAlternatingMapLinearEquiv ℝ E k ℝ β).smulRight Y)) =
      B X Y * α.wedge β (b ∘ finCongr (hkk.trans _i.out)) := by
  rw [vectorFormHodgeStar_smulRight, vectorFormInner_smulRight_smulRight,
    vectorFormHodgeStar_continuousAlternatingMapLinearEquiv,
    vectorFormInner_mul_continuousAlternatingMapLinearEquiv,
    o.wedge_apply_orthonormalBasis hk hkk b hb]

/-! ### Self-dual and anti-self-dual parts -/

omit hk

/-- The **self-dual part** `F⁺ = (F + ⋆F) / 2` of a middle-degree vector-valued form. -/
def vectorFormSelfDualPart : (⋀[ℝ]^k E →ₗ[ℝ] V) →ₗ[ℝ] ⋀[ℝ]^k E →ₗ[ℝ] V :=
  (2⁻¹ : ℝ) • (LinearMap.id + (o.vectorFormHodgeStar hkk).toLinearMap)

/-- The **anti-self-dual part** `F⁻ = (F - ⋆F) / 2` of a middle-degree vector-valued form. -/
def vectorFormAntiSelfDualPart : (⋀[ℝ]^k E →ₗ[ℝ] V) →ₗ[ℝ] ⋀[ℝ]^k E →ₗ[ℝ] V :=
  (2⁻¹ : ℝ) • (LinearMap.id - (o.vectorFormHodgeStar hkk).toLinearMap)

/-- The self-dual part is `F⁺ = (F + ⋆F) / 2`. -/
theorem vectorFormSelfDualPart_apply (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    o.vectorFormSelfDualPart hkk F = (2⁻¹ : ℝ) • (F + o.vectorFormHodgeStar hkk F) :=
  (rfl)

/-- The anti-self-dual part is `F⁻ = (F - ⋆F) / 2`. -/
theorem vectorFormAntiSelfDualPart_apply (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    o.vectorFormAntiSelfDualPart hkk F = (2⁻¹ : ℝ) • (F - o.vectorFormHodgeStar hkk F) :=
  (rfl)

/-- A middle-degree form is the sum of its self-dual and anti-self-dual parts, `F = F⁺ + F⁻`. -/
@[simp]
theorem vectorFormSelfDualPart_add_vectorFormAntiSelfDualPart (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    o.vectorFormSelfDualPart hkk F + o.vectorFormAntiSelfDualPart hkk F = F := by
  rw [vectorFormSelfDualPart_apply, vectorFormAntiSelfDualPart_apply]
  module

/-- The difference of the two parts is the Hodge star, `F⁺ - F⁻ = ⋆F`. -/
@[simp]
theorem vectorFormSelfDualPart_sub_vectorFormAntiSelfDualPart (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    o.vectorFormSelfDualPart hkk F - o.vectorFormAntiSelfDualPart hkk F =
      o.vectorFormHodgeStar hkk F := by
  rw [vectorFormSelfDualPart_apply, vectorFormAntiSelfDualPart_apply]
  module

/-- The anti-self-dual part vanishes exactly when the form is self-dual: `F⁻ = 0 ↔ ⋆F = F`. -/
theorem vectorFormAntiSelfDualPart_eq_zero_iff {F : ⋀[ℝ]^k E →ₗ[ℝ] V} :
    o.vectorFormAntiSelfDualPart hkk F = 0 ↔ o.vectorFormHodgeStar hkk F = F := by
  rw [vectorFormAntiSelfDualPart_apply, smul_eq_zero_iff_right (inv_ne_zero two_ne_zero),
    sub_eq_zero, eq_comm]

/-- The self-dual part vanishes exactly when the form is anti-self-dual: `F⁺ = 0 ↔ ⋆F = -F`. -/
theorem vectorFormSelfDualPart_eq_zero_iff {F : ⋀[ℝ]^k E →ₗ[ℝ] V} :
    o.vectorFormSelfDualPart hkk F = 0 ↔ o.vectorFormHodgeStar hkk F = -F := by
  rw [vectorFormSelfDualPart_apply, smul_eq_zero_iff_right (inv_ne_zero two_ne_zero),
    add_eq_zero_iff_eq_neg']

/-- A form equals its self-dual part exactly when it is self-dual: `F⁺ = F ↔ ⋆F = F`. -/
theorem vectorFormSelfDualPart_eq_self_iff {F : ⋀[ℝ]^k E →ₗ[ℝ] V} :
    o.vectorFormSelfDualPart hkk F = F ↔ o.vectorFormHodgeStar hkk F = F := by
  rw [← vectorFormAntiSelfDualPart_eq_zero_iff]
  nth_rw 2 [← o.vectorFormSelfDualPart_add_vectorFormAntiSelfDualPart hkk F]
  exact left_eq_add

/-- A form equals its anti-self-dual part exactly when it is anti-self-dual:
`F⁻ = F ↔ ⋆F = -F`. -/
theorem vectorFormAntiSelfDualPart_eq_self_iff {F : ⋀[ℝ]^k E →ₗ[ℝ] V} :
    o.vectorFormAntiSelfDualPart hkk F = F ↔ o.vectorFormHodgeStar hkk F = -F := by
  rw [← vectorFormSelfDualPart_eq_zero_iff]
  nth_rw 2 [← o.vectorFormSelfDualPart_add_vectorFormAntiSelfDualPart hkk F]
  exact right_eq_add

include hk

/-- The self-dual part is self-dual, `⋆F⁺ = F⁺`. -/
@[simp]
theorem vectorFormHodgeStar_vectorFormSelfDualPart (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    o.vectorFormHodgeStar hkk (o.vectorFormSelfDualPart hkk F) =
      o.vectorFormSelfDualPart hkk F := by
  rw [vectorFormSelfDualPart_apply, map_smul, map_add,
    o.vectorFormHodgeStar_vectorFormHodgeStar_of_even hk, add_comm]

/-- The anti-self-dual part is anti-self-dual, `⋆F⁻ = -F⁻`. -/
@[simp]
theorem vectorFormHodgeStar_vectorFormAntiSelfDualPart (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    o.vectorFormHodgeStar hkk (o.vectorFormAntiSelfDualPart hkk F) =
      -o.vectorFormAntiSelfDualPart hkk F := by
  rw [vectorFormAntiSelfDualPart_apply, map_smul, map_sub,
    o.vectorFormHodgeStar_vectorFormHodgeStar_of_even hk, ← smul_neg, neg_sub]

/-- The self-dual part of a self-dual part is itself, `(F⁺)⁺ = F⁺`. -/
@[simp]
theorem vectorFormSelfDualPart_vectorFormSelfDualPart (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    o.vectorFormSelfDualPart hkk (o.vectorFormSelfDualPart hkk F) =
      o.vectorFormSelfDualPart hkk F :=
  (o.vectorFormSelfDualPart_eq_self_iff hkk).mpr
    (o.vectorFormHodgeStar_vectorFormSelfDualPart hk hkk F)

/-- The anti-self-dual part of a self-dual part vanishes, `(F⁺)⁻ = 0`. -/
@[simp]
theorem vectorFormAntiSelfDualPart_vectorFormSelfDualPart (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    o.vectorFormAntiSelfDualPart hkk (o.vectorFormSelfDualPart hkk F) = 0 :=
  (o.vectorFormAntiSelfDualPart_eq_zero_iff hkk).mpr
    (o.vectorFormHodgeStar_vectorFormSelfDualPart hk hkk F)

/-- The anti-self-dual part of an anti-self-dual part is itself, `(F⁻)⁻ = F⁻`. -/
@[simp]
theorem vectorFormAntiSelfDualPart_vectorFormAntiSelfDualPart (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    o.vectorFormAntiSelfDualPart hkk (o.vectorFormAntiSelfDualPart hkk F) =
      o.vectorFormAntiSelfDualPart hkk F :=
  (o.vectorFormAntiSelfDualPart_eq_self_iff hkk).mpr
    (o.vectorFormHodgeStar_vectorFormAntiSelfDualPart hk hkk F)

/-- The self-dual part of an anti-self-dual part vanishes, `(F⁻)⁺ = 0`. -/
@[simp]
theorem vectorFormSelfDualPart_vectorFormAntiSelfDualPart (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    o.vectorFormSelfDualPart hkk (o.vectorFormAntiSelfDualPart hkk F) = 0 :=
  (o.vectorFormSelfDualPart_eq_zero_iff hkk).mpr
    (o.vectorFormHodgeStar_vectorFormAntiSelfDualPart hk hkk F)

/-- A self-dual form and an anti-self-dual form are orthogonal for every pairing. -/
theorem vectorFormInner_eq_zero_of_vectorFormHodgeStar_eq (B : LinearMap.BilinForm ℝ V)
    {F G : ⋀[ℝ]^k E →ₗ[ℝ] V} (hF : o.vectorFormHodgeStar hkk F = F)
    (hG : o.vectorFormHodgeStar hkk G = -G) : vectorFormInner B k F G = 0 := by
  have h := o.vectorFormInner_vectorFormHodgeStar_left hk hkk B F G
  rw [hF, hG, map_neg] at h
  linarith

/-- An anti-self-dual form and a self-dual form are orthogonal for every pairing. -/
theorem vectorFormInner_eq_zero_of_vectorFormHodgeStar_eq_neg (B : LinearMap.BilinForm ℝ V)
    {F G : ⋀[ℝ]^k E →ₗ[ℝ] V} (hF : o.vectorFormHodgeStar hkk F = -F)
    (hG : o.vectorFormHodgeStar hkk G = G) : vectorFormInner B k F G = 0 := by
  have h := o.vectorFormInner_vectorFormHodgeStar_left hk hkk B F G
  rw [hF, hG, map_neg, LinearMap.neg_apply] at h
  linarith

/-- The self-dual part of `F` is orthogonal to the anti-self-dual part of `G`. -/
@[simp]
theorem vectorFormInner_vectorFormSelfDualPart_vectorFormAntiSelfDualPart
    (B : LinearMap.BilinForm ℝ V) (F G : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    vectorFormInner B k (o.vectorFormSelfDualPart hkk F) (o.vectorFormAntiSelfDualPart hkk G) =
      0 :=
  o.vectorFormInner_eq_zero_of_vectorFormHodgeStar_eq hk hkk B
    (o.vectorFormHodgeStar_vectorFormSelfDualPart hk hkk F)
    (o.vectorFormHodgeStar_vectorFormAntiSelfDualPart hk hkk G)

/-- The anti-self-dual part of `F` is orthogonal to the self-dual part of `G`. -/
@[simp]
theorem vectorFormInner_vectorFormAntiSelfDualPart_vectorFormSelfDualPart
    (B : LinearMap.BilinForm ℝ V) (F G : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    vectorFormInner B k (o.vectorFormAntiSelfDualPart hkk F) (o.vectorFormSelfDualPart hkk G) =
      0 :=
  o.vectorFormInner_eq_zero_of_vectorFormHodgeStar_eq_neg hk hkk B
    (o.vectorFormHodgeStar_vectorFormAntiSelfDualPart hk hkk F)
    (o.vectorFormHodgeStar_vectorFormSelfDualPart hk hkk G)

/-- **The self-dual splitting is orthogonal**: `⟨F, G⟩ = ⟨F⁺, G⁺⟩ + ⟨F⁻, G⁻⟩`; in particular
`|F|² = |F⁺|² + |F⁻|²`. -/
theorem vectorFormInner_eq_add (B : LinearMap.BilinForm ℝ V) (F G : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    vectorFormInner B k F G =
      vectorFormInner B k (o.vectorFormSelfDualPart hkk F) (o.vectorFormSelfDualPart hkk G) +
        vectorFormInner B k (o.vectorFormAntiSelfDualPart hkk F)
          (o.vectorFormAntiSelfDualPart hkk G) := by
  conv_lhs => rw [← o.vectorFormSelfDualPart_add_vectorFormAntiSelfDualPart hkk F,
    ← o.vectorFormSelfDualPart_add_vectorFormAntiSelfDualPart hkk G]
  simp only [map_add, LinearMap.add_apply,
    o.vectorFormInner_vectorFormSelfDualPart_vectorFormAntiSelfDualPart hk,
    o.vectorFormInner_vectorFormAntiSelfDualPart_vectorFormSelfDualPart hk]
  ring

/-- **The density of the wedge square through the self-dual splitting**:
`⟨F, ⋆G⟩ = ⟨F⁺, G⁺⟩ - ⟨F⁻, G⁻⟩`; in particular `⋆⟨F ∧ F⟩ = ⟨F, ⋆F⟩ = |F⁺|² - |F⁻|²`. -/
theorem vectorFormInner_vectorFormHodgeStar_right_eq_sub (B : LinearMap.BilinForm ℝ V)
    (F G : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    vectorFormInner B k F (o.vectorFormHodgeStar hkk G) =
      vectorFormInner B k (o.vectorFormSelfDualPart hkk F) (o.vectorFormSelfDualPart hkk G) -
        vectorFormInner B k (o.vectorFormAntiSelfDualPart hkk F)
          (o.vectorFormAntiSelfDualPart hkk G) := by
  conv_lhs => rw [← o.vectorFormSelfDualPart_sub_vectorFormAntiSelfDualPart hkk G,
    ← o.vectorFormSelfDualPart_add_vectorFormAntiSelfDualPart hkk F]
  simp only [map_add, map_sub, LinearMap.add_apply,
    o.vectorFormInner_vectorFormSelfDualPart_vectorFormAntiSelfDualPart hk,
    o.vectorFormInner_vectorFormAntiSelfDualPart_vectorFormSelfDualPart hk]
  ring

/-- **The pointwise Bogomol'nyi inequality** `|⋆⟨F ∧ F⟩| ≤ |F|²`: for a positive semidefinite
`B`, `|⟨F, ⋆F⟩| ≤ ⟨F, F⟩`. -/
theorem abs_vectorFormInner_vectorFormHodgeStar_le {B : LinearMap.BilinForm ℝ V}
    (hB : B.IsNonneg) (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    |vectorFormInner B k F (o.vectorFormHodgeStar hkk F)| ≤ vectorFormInner B k F F := by
  have h₁ := (isNonneg_vectorFormInner (k := k) (E := E) hB).nonneg (o.vectorFormSelfDualPart hkk F)
  have h₂ := (isNonneg_vectorFormInner (k := k) (E := E) hB).nonneg
    (o.vectorFormAntiSelfDualPart hkk F)
  rw [o.vectorFormInner_vectorFormHodgeStar_right_eq_sub hk hkk,
    o.vectorFormInner_eq_add hk hkk B F F, abs_le]
  constructor <;> linarith

/-- **The equality case of the Bogomol'nyi inequality**: for a positive definite `B`,
`|⟨F, ⋆F⟩| = ⟨F, F⟩` exactly when `F` is anti-self-dual (`F⁺ = 0`) or self-dual (`F⁻ = 0`). -/
theorem abs_vectorFormInner_vectorFormHodgeStar_eq_iff {B : LinearMap.BilinForm ℝ V}
    (hB : B.toQuadraticMap.PosDef) (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    |vectorFormInner B k F (o.vectorFormHodgeStar hkk F)| = vectorFormInner B k F F ↔
      o.vectorFormSelfDualPart hkk F = 0 ∨ o.vectorFormAntiSelfDualPart hkk F = 0 := by
  have hB' : (vectorFormInner B k : LinearMap.BilinForm ℝ (⋀[ℝ]^k E →ₗ[ℝ] V)).IsNonneg :=
    isNonneg_vectorFormInner ⟨hB.nonneg⟩
  have h₁ := hB'.nonneg (o.vectorFormSelfDualPart hkk F)
  have h₂ := hB'.nonneg (o.vectorFormAntiSelfDualPart hkk F)
  rw [o.vectorFormInner_vectorFormHodgeStar_right_eq_sub hk hkk,
    o.vectorFormInner_eq_add hk hkk B F F,
    ← vectorFormInner_self_eq_zero hB (F := o.vectorFormSelfDualPart hkk F),
    ← vectorFormInner_self_eq_zero hB (F := o.vectorFormAntiSelfDualPart hkk F)]
  constructor
  · intro h
    rcases (abs_eq (add_nonneg h₁ h₂)).mp h with h | h
    · right
      linarith
    · left
      linarith
  · rintro (h | h) <;> rw [h]
    · rw [zero_sub, zero_add, abs_neg, abs_of_nonneg h₂]
    · rw [sub_zero, add_zero, abs_of_nonneg h₁]

omit hk

/-- The self-dual part commutes with every linear map of the values, such as `Ad(g)` on a Lie
algebra. -/
@[simp]
theorem vectorFormSelfDualPart_comp (T : V →ₗ[ℝ] W) (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    o.vectorFormSelfDualPart hkk (T ∘ₗ F) = T ∘ₗ o.vectorFormSelfDualPart hkk F := by
  rw [vectorFormSelfDualPart_apply, vectorFormSelfDualPart_apply, vectorFormHodgeStar_comp,
    LinearMap.comp_smul, LinearMap.comp_add]

/-- The anti-self-dual part commutes with every linear map of the values, such as `Ad(g)` on a Lie
algebra. -/
@[simp]
theorem vectorFormAntiSelfDualPart_comp (T : V →ₗ[ℝ] W) (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    o.vectorFormAntiSelfDualPart hkk (T ∘ₗ F) = T ∘ₗ o.vectorFormAntiSelfDualPart hkk F := by
  rw [vectorFormAntiSelfDualPart_apply, vectorFormAntiSelfDualPart_apply, vectorFormHodgeStar_comp,
    LinearMap.comp_smul, LinearMap.comp_sub]

/-- Reversing the orientation turns the self-dual part into the anti-self-dual part. -/
@[simp]
theorem vectorFormSelfDualPart_neg_orientation (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    (-o).vectorFormSelfDualPart hkk F = o.vectorFormAntiSelfDualPart hkk F := by
  rw [vectorFormSelfDualPart_apply, vectorFormAntiSelfDualPart_apply,
    vectorFormHodgeStar_neg_orientation, ← sub_eq_add_neg]

/-- Reversing the orientation turns the anti-self-dual part into the self-dual part. -/
@[simp]
theorem vectorFormAntiSelfDualPart_neg_orientation (F : ⋀[ℝ]^k E →ₗ[ℝ] V) :
    (-o).vectorFormAntiSelfDualPart hkk F = o.vectorFormSelfDualPart hkk F := by
  rw [vectorFormSelfDualPart_apply, vectorFormAntiSelfDualPart_apply,
    vectorFormHodgeStar_neg_orientation, sub_neg_eq_add]

end Even

end Orientation
