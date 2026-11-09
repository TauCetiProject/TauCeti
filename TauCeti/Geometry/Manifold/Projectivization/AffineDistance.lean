/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.Geometry.Manifold.Morse.Cell.Band
public import TauCeti.Geometry.Manifold.Morse.ScalarComposition
public import TauCeti.Geometry.Manifold.RegularValue.Polynomial
public import TauCeti.Topology.Algebra.Projectivization.AffineDistance
public import TauCeti.Topology.Algebra.Projectivization.ZeroLocus
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Relative homology of a projective variety modulo a neighbourhood of a hyperplane section

Let `X` be a closed subset of projective space `ℙ(𝕜ⁿ⁺¹)`, over `ℝ` or `ℂ`, and `H = {x_i = 0}` a
coordinate hyperplane. Suppose the image `Z ⊆ 𝕜ⁿ` of `X \ H` in the standard affine chart is a
manifold of real dimension `m` on which the squared Euclidean distance `ρ = ‖z - a‖²` from a centre
`a` is a Morse function whose critical points all have index at most `d`. The reciprocal transform
`F = (1 + ρ)⁻¹`, extended by `0` on `H`, is the continuous function
`Projectivization.affineChartInvOneAddDistSq i a` on projective space. Its sublevel
`X_ε = X ∩ {F ≤ ε}` is a closed neighbourhood of the hyperplane section `X ∩ H` in `X`.

On `Z`, the function `F` is Morse with indices `m - λ ≥ m - d` at the critical points of `ρ`, and
for `ε > 0` the band `{ε ≤ F}` is compact. Running Morse theory for `F` from `X_ε` up to all of `X`
therefore attaches only cells of dimension at least `m - d`, so the relative singular homology
`Hⱼ(X, X_ε)` vanishes for `j < m - d` whenever `ε > 0` is a regular value of `F` on `Z`
(`TauCeti.isZero_singularHomology_inter_setOf_affineChartInvOneAddDistSq_le`). Since `F` vanishes on
`H`, excision of the open set `{F < ε}` identifies `Hⱼ(X, X_ε)` with the relative homology of the
sublevel pair `({F ≤ 1}, {F ≤ ε})` of `F` on the manifold `Z`.

For a complex projective zero locus whose affine part `X \ H` is a smooth complete intersection of
complex dimension `k`, the squared distance from almost every centre is such a Morse function with
`m = 2k` and `d = k`, so `Hⱼ(X, X_ε)` vanishes for `j < k`
(`TauCeti.ae_isZero_singularHomology_complexProjectiveZeroLocus_inter_setOf_le`). No smoothness is
assumed at the points of `X ∩ H`. This is the homological form of the reversed handle attachment in
Milnor's proof of the Lefschetz hyperplane theorem; it reduces `Hⱼ(X, X ∩ H) = 0` for `j < k` to
the comparison of `X ∩ H` with its neighbourhoods `X_ε`.

## Main results

* `TauCeti.isZero_singularHomology_inter_setOf_affineChartInvOneAddDistSq_le`: `Hⱼ(X, X_ε) = 0`
  for `j + d < m`.
* `TauCeti.ae_isZero_singularHomology_complexProjectiveZeroLocus_inter_setOf_le`: for almost every
  centre, `Hⱼ(X, X_ε) = 0` for `j` below the dimension of the smooth affine complete intersection
  `X \ H`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 7.4 and its proof.
* A. Andreotti and T. Frankel, *The Lefschetz theorem on hyperplane sections*, Annals of
  Mathematics 69 (1959), 713–717.
-/

public section

noncomputable section

open CategoryTheory Limits MeasureTheory Module MvPolynomial Projectivization Set Topology
open scoped ContDiff LinearAlgebra.Projectivization Manifold

universe u v w

namespace TauCeti

variable {𝕜 : Type u} [RCLike 𝕜] {n : ℕ} {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

variable {X : Set (ℙ 𝕜 (Fin (n + 1) → 𝕜))} {i : Fin (n + 1)} {Z : Set (Fin n → 𝕜)}
  {a : EuclideanSpace 𝕜 (Fin n)} {ε : ℝ}

/-- On the affine part of `X`, the function `affineChartInvOneAddDistSq i a` is the reciprocal
transform of the squared distance on `Z`. -/
private theorem inv_one_add_norm_sub_sq_interAffineOpenHomeomorph
    (hZ : affineChart i '' (X ∩ affineOpen i) = Z) (y : ↥(X ∩ affineOpen i)) :
    (1 + ‖WithLp.toLp 2 (interAffineOpenHomeomorph hZ y : Fin n → 𝕜) - a‖ ^ 2)⁻¹ =
      affineChartInvOneAddDistSq i a y := by
  rw [affineChartInvOneAddDistSq_of_mem y.2.2, dist_eq_norm]
  simp

/-- **Excision onto the affine part.** For `ε > 0`, the inclusion of the sublevel pair
`({g ≤ ε + 1}, {g ≤ ε})` of `g = (1 + ‖z - a‖²)⁻¹` on `Z` into `(X, X ∩ {F ≤ ε})` induces
isomorphisms on relative homology: the open set `{F < ε}` contains the hyperplane section and lies
in the subspace, and its complement lies in the affine part. -/
private theorem isZero_singularHomology_inter_setOf_le_of_isZero_sublevelPair
    (hZ : affineChart i '' (X ∩ affineOpen i) = Z) (hε : 0 < ε)
    {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C] (R : C) (j : ℕ)
    (h : IsZero ((sublevelPair (fun z : Z ↦ (1 + ‖WithLp.toLp 2 (z : Fin n → 𝕜) - a‖ ^ 2)⁻¹)
      (by linarith : ε ≤ ε + 1)).singularHomology R j)) :
    IsZero ((TopPair.ofInclusion (X := TopCat.of (ℙ 𝕜 (Fin (n + 1) → 𝕜)))
      (inter_subset_left : X ∩ {x | affineChartInvOneAddDistSq i a x ≤ ε} ⊆ X)).singularHomology
        R j) := by
  set g : Z → ℝ := fun z ↦ (1 + ‖WithLp.toLp 2 (z : Fin n → 𝕜) - a‖ ^ 2)⁻¹
  have hF : Continuous fun x : X ↦ affineChartInvOneAddDistSq i a x :=
    (continuous_affineChartInvOneAddDistSq i a).comp continuous_subtype_val
  -- The affine part of `X`, as a subspace of `X`, is the image of `Z`.
  let φ : C({z | g z ≤ ε + 1}, X) :=
    ⟨inclusion inter_subset_left ∘ (interAffineOpenHomeomorph hZ).symm ∘ Subtype.val, by fun_prop⟩
  have hφ (z : {z | g z ≤ ε + 1}) : affineChartInvOneAddDistSq i a (φ z) = g z := by
    have : (φ z : ℙ 𝕜 (Fin (n + 1) → 𝕜)) = ((interAffineOpenHomeomorph hZ).symm z : _) := rfl
    rw [this, ← inv_one_add_norm_sub_sq_interAffineOpenHomeomorph hZ, Homeomorph.apply_symm_apply]
  let f := TopPair.ofInclusionMap (X := TopCat.of Z) (Y := TopCat.of (ℙ 𝕜 (Fin (n + 1) → 𝕜)))
    (sublevel_mono g (by linarith : ε ≤ ε + 1))
    (inter_subset_left : X ∩ {x | affineChartInvOneAddDistSq i a x ≤ ε} ⊆ X) φ
    fun z hz ↦ ⟨(φ z).2, (hφ ⟨z, _⟩).trans_le hz⟩
  have hf (z : {z | g z ≤ ε + 1}) : TopPair.Hom.fst f z = φ z :=
    TopPair.ofInclusionMap_fst_apply (X := TopCat.of Z) (Y := TopCat.of (ℙ 𝕜 (Fin (n + 1) → 𝕜)))
      φ _ z
  have hfφ : ⇑(ConcreteCategory.hom (TopPair.Hom.fst f)) = ⇑φ := funext hf
  have hemb : IsEmbedding (TopPair.Hom.fst f) := by
    rw [hfφ]
    exact (IsEmbedding.inclusion inter_subset_left).comp
      ((interAffineOpenHomeomorph hZ).symm.isEmbedding.comp IsEmbedding.subtypeVal)
  -- The open set `{F < ε}` lies in the subspace and `{0 < F}` in the image of `Z`; they cover `X`.
  let U : Bool → Set X := fun b ↦
    bif b then {x | affineChartInvOneAddDistSq i a x < ε}
    else {x | 0 < affineChartInvOneAddDistSq i a x}
  have hiso := TopPair.isIso_singularHomologyMap_of_open_cover R f hemb
    (fun z ⟨⟨y, hyS⟩, hy⟩ ↦ by
      have hyz : y = (φ z : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :=
        (congrArg (Subtype.val : X → ℙ 𝕜 (Fin (n + 1) → 𝕜)) hy).trans (congrArg _ (hf z))
      exact ⟨⟨z.1, (hφ z).symm.trans_le (hyz ▸ hyS.2)⟩, rfl⟩)
    U (fun b ↦ by cases b <;> exact isOpen_lt (by fun_prop) (by fun_prop))
    (eq_univ_iff_forall.2 fun ⟨x, _⟩ ↦ mem_iUnion.2 <| by
      by_cases hx : affineChartInvOneAddDistSq i a x < ε
      exacts [⟨true, hx⟩, ⟨false, hε.trans_le (not_lt.1 hx)⟩])
    (fun b ↦ by
      cases b
      · -- Where `F` is positive, `X` lies in the affine part.
        refine Or.inr ?_
        rintro ⟨x, hxX⟩ (hx : 0 < affineChartInvOneAddDistSq i a x)
        have hxU : x ∈ affineOpen i := (affineChartInvOneAddDistSq_pos_iff i a).1 hx
        set z := interAffineOpenHomeomorph hZ ⟨x, hxX, hxU⟩
        have h₁ := inv_one_add_norm_sub_sq_le_one (WithLp.toLp 2 (z : Fin n → 𝕜)) a
        refine ⟨⟨z, (by linarith : g z ≤ ε + 1)⟩, (hf _).trans (Subtype.ext ?_)⟩
        simp [φ, z]
      · refine Or.inl ?_
        rintro ⟨x, hxX⟩ (hx : affineChartInvOneAddDistSq i a x < ε)
        exact ⟨⟨x, hxX, hx.le⟩, rfl⟩) j
  exact h.of_iso (asIso (TopPair.singularHomologyMap f R j)).symm

/-- **The relative homology of a projective variety modulo a reciprocal distance sublevel.** Let
`X ⊆ ℙ(𝕜ⁿ⁺¹)` be closed, and suppose the image `Z ⊆ 𝕜ⁿ` of `X \ {x_i = 0}` in the standard affine
chart is a smooth manifold of dimension `m` on which the squared distance `‖z - a‖²` is a Morse
function whose critical points all have index at most `d`. Let `F` be
`Projectivization.affineChartInvOneAddDistSq i a` and `ε > 0` a regular value of `F` on `Z`. Then
the relative singular homology `Hⱼ(X, X ∩ {F ≤ ε}; R)` vanishes for every `j` with `j + d < m` and
every coefficient object `R` of an abelian category with coproducts. -/
theorem isZero_singularHomology_inter_setOf_affineChartInvOneAddDistSq_le
    (hX : IsClosed X) (hZ : affineChart i '' (X ∩ affineOpen i) = Z) [ChartedSpace H Z]
    [IsManifold I ∞ Z] (hρ : IsMorse I fun z : Z ↦ ‖WithLp.toLp 2 (z : Fin n → 𝕜) - a‖ ^ 2) {d : ℕ}
    (hd : ∀ z ∈ criticalPoints I fun z : Z ↦ ‖WithLp.toLp 2 (z : Fin n → 𝕜) - a‖ ^ 2,
      manifoldMorseIndex I (fun z : Z ↦ ‖WithLp.toLp 2 (z : Fin n → 𝕜) - a‖ ^ 2) z ≤ d)
    (hε : 0 < ε)
    (hreg : IsRegularValue I 𝓘(ℝ) (fun z : Z ↦ (1 + ‖WithLp.toLp 2 (z : Fin n → 𝕜) - a‖ ^ 2)⁻¹) ε)
    {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{u} C] (R : C) {j : ℕ}
    (hj : j + d < finrank ℝ E) :
    IsZero ((TopPair.ofInclusion (X := TopCat.of (ℙ 𝕜 (Fin (n + 1) → 𝕜)))
      (inter_subset_left : X ∩ {x | affineChartInvOneAddDistSq i a x ≤ ε} ⊆ X)).singularHomology
        R j) := by
  refine isZero_singularHomology_inter_setOf_le_of_isZero_sublevelPair hZ hε R j ?_
  set ρ : Z → ℝ := fun z ↦ ‖WithLp.toLp 2 (z : Fin n → 𝕜) - a‖ ^ 2
  have hρ₀ (z : Z) : 1 + ρ z ≠ 0 := by positivity
  have hg₁ (z : Z) : (1 + ρ z)⁻¹ ≤ 1 := inv_one_add_norm_sub_sq_le_one _ a
  -- The band `{ε ≤ (1 + ρ)⁻¹}` is the image of the compact set `X ∩ {ε ≤ F}` in the chart.
  have hcompact : IsCompact ((fun z ↦ (1 + ρ z)⁻¹) ⁻¹' Icc ε (ε + 1)) := by
    have hK : IsCompact {y : ↥(X ∩ affineOpen i) | ε ≤ affineChartInvOneAddDistSq i a y} := by
      rw [Subtype.isCompact_iff]
      convert (isCompact_setOf_le_affineChartInvOneAddDistSq i a ε).inter_left hX using 1
      ext x
      exact ⟨fun ⟨y, hy, hyx⟩ ↦ hyx ▸ ⟨y.2.1, hy⟩, fun hx ↦
        ⟨⟨x, hx.1, setOf_le_affineChartInvOneAddDistSq_subset_affineOpen i a hε hx.2⟩, hx.2,
          rfl⟩⟩
    convert hK.image (interAffineOpenHomeomorph hZ).continuous using 1
    ext z
    obtain ⟨y, rfl⟩ := (interAffineOpenHomeomorph hZ).surjective z
    have hy := inv_one_add_norm_sub_sq_interAffineOpenHomeomorph (a := a) hZ y
    have hy₁ := hg₁ (interAffineOpenHomeomorph hZ y)
    simp only [ρ, mem_preimage, mem_Icc, mem_image, mem_ofPred_eq,
      (interAffineOpenHomeomorph hZ).injective.eq_iff, exists_eq_right] at hy₁ ⊢
    rw [hy] at hy₁ ⊢
    exact ⟨And.left, fun h ↦ ⟨h, by linarith⟩⟩
  -- Every critical point of `(1 + ρ)⁻¹` is one of `ρ`, where its index is `m` minus that of `ρ`.
  have hidx : ∀ p ∈ criticalPoints I (fun z ↦ (1 + ρ z)⁻¹) ∩
      (fun z ↦ (1 + ρ z)⁻¹) ⁻¹' Icc ε (ε + 1),
      finrank ℝ E - d ≤ manifoldMorseIndex I (fun z ↦ (1 + ρ z)⁻¹) p := by
    rintro p ⟨hp, -⟩
    have hpρ : p ∈ criticalPoints I ρ := by
      refine (mem_criticalPoints_scalar_comp_iff (φ := fun t ↦ (1 + t)⁻¹)
        ((hρ.contMDiff p).mdifferentiableAt (by simp)) ?_).1 hp
      rw [deriv_fun_inv'' (differentiableAt_id.const_add 1) (hρ₀ p)]
      simp [hρ₀ p]
    have hsum := (hρ.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints hpρ
      ).manifoldMorseIndex_inv_one_add_add_manifoldMorseIndex_eq_finrank (hρ₀ p)
    have := hd p hpρ
    omega
  exact (hρ.inv_one_add hρ₀).isZero_singularHomology_sublevelPair_of_le_manifoldMorseIndex _
    hcompact hreg (isRegularValue_iff.2 fun z hz ↦
      absurd hz ((hg₁ z).trans_lt (by linarith : (1 : ℝ) < ε + 1)).ne) hidx R (by omega)

/-- **The relative homology of a projective zero locus modulo a reciprocal distance sublevel.** Let
`X ⊆ ℂℙⁿ` be the zero locus of a finite family of homogeneous polynomials, and suppose that its part
outside the hyperplane `{x_i = 0}` is a smooth affine complete intersection of complex dimension
`k = n - |ι|`: the dehomogenized equations have surjective Jacobian at each of their common zeros.
For almost every centre `a`, with respect to any additive Haar measure, and every regular value
`ε > 0` of `F = Projectivization.affineChartInvOneAddDistSq i a` on the affine part, the relative
singular homology `Hⱼ(X, X ∩ {F ≤ ε}; R)` vanishes for every `j < k`. No smoothness is assumed at
the points of `X ∩ {x_i = 0}`. -/
theorem ae_isZero_singularHomology_complexProjectiveZeroLocus_inter_setOf_le {ι : Type*}
    [Fintype ι] {p : ι → MvPolynomial (Fin (n + 1)) ℂ} {d : ι → ℕ}
    (hp : ∀ k, (p k).IsHomogeneous (d k)) (i : Fin (n + 1))
    (hrank : ∀ z ∈ affineZeroLocus fun k ↦ dehomogenize i (p k),
      Function.Surjective (jacobiMatrixAt (fun k ↦ dehomogenize i (p k)) z).mulVec)
    (μ : Measure (EuclideanSpace ℂ (Fin n))) [μ.IsAddHaarMeasure]
    {C : Type v} [Category.{w} C] [Abelian C] [HasCoproducts.{0} C] (R : C) {j : ℕ}
    (hj : j < n - Fintype.card ι) :
    ∀ᵐ a ∂μ, ∀ ε, 0 < ε →
      (letI := affineZeroLocusChartedSpace hrank;
        IsRegularValue 𝓘(ℝ, Fin (Fintype.card (Fin n) - Fintype.card ι) → ℂ) 𝓘(ℝ)
          (fun z : affineZeroLocus (fun k ↦ dehomogenize i (p k)) ↦
            (1 + ‖WithLp.toLp 2 (z : Fin n → ℂ) - a‖ ^ 2)⁻¹) ε) →
      IsZero ((TopPair.ofInclusion (X := TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ)))
        (inter_subset_left : complexProjectiveZeroLocus p ∩
          {x | affineChartInvOneAddDistSq i a x ≤ ε} ⊆ complexProjectiveZeroLocus p)
          ).singularHomology R j) := by
  let _ := affineZeroLocusChartedSpace hrank
  have := isManifold_affineZeroLocus hrank ∞
  have : IsManifold 𝓘(ℝ, Fin (Fintype.card (Fin n) - Fintype.card ι) → ℂ) ∞
      (affineZeroLocus fun k ↦ dehomogenize i (p k)) :=
    IsManifold.restrictScalars ℝ (isManifold_affineZeroLocus hrank ∞)
  have hdim : finrank ℝ (Fin (Fintype.card (Fin n) - Fintype.card ι) → ℂ) =
      2 * (n - Fintype.card ι) := by
    rw [finrank_real_eq_two_mul_finrank_complex, Module.finrank_fin_fun, Fintype.card_fin]
  filter_upwards [ae_isMorse_and_manifoldMorseIndex_norm_sq_sub_comp_le μ
    (contMDiff_toLp_coe_affineZeroLocus hrank ∞)
    (injective_mvfderiv_toLp_coe_affineZeroLocus hrank)] with a ha ε hε hreg
  obtain ⟨ha, hidx⟩ := ha
  rw [Module.finrank_fin_fun] at hidx
  exact isZero_singularHomology_inter_setOf_affineChartInvOneAddDistSq_le
    (isClosed_complexProjectiveZeroLocus p)
    (image_affineChart_complexProjectiveZeroLocus_inter_affineOpen hp i) ha hidx hε hreg R
    (by rw [hdim, Fintype.card_fin]; omega)

end TauCeti
