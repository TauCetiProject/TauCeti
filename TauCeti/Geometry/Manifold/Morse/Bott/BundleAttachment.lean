/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Analysis.Calculus.Morse.HandleRetraction.Bundle
import TauCeti.Analysis.Calculus.Morse.QuadraticHandle
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.Morse.Deformation
import TauCeti.Geometry.Manifold.Morse.MilnorFunction
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Prod
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Topology.Homotopy.DeformationRetract
import TauCeti.Topology.VectorBundle.DiscSphere

/-!
# Attaching negative disc bundles of bundle normal forms across a Morse–Bott critical level

Let `f` be a smooth function on a boundaryless finite-dimensional manifold `M`, and let `c` be a
critical value. Near a compact nondegenerate critical submanifold `C` of index `λ`, the Morse–Bott
lemma puts `f` in the form `f = c - ‖u‖² + ‖v‖²` on a neighbourhood of the zero section of the
Whitney sum `ν⁻ ⊕ ν⁺` of the negative and positive normal bundles of `C`, where `u` runs over the
fibre of `ν⁻`, of rank `λ`, and `v` over the fibre of `ν⁺`. Bott's theorem says that passing the
level `c` attaches the disc bundle of `ν⁻` along its sphere bundle: for small `ε > 0`, the sublevel
`M_{c+ε} = {f ≤ c + ε}` deformation retracts onto the lower sublevel `M_{c-ε} = {f ≤ c - ε}`
together with the negative disc bundles `{‖u‖² ≤ ε, v = 0}` of the critical submanifolds on the
level. For a single critical point the base is a point, and this is Milnor's attachment of a
`λ`-cell.

This file proves this in the form taking the normal forms as input. Each critical submanifold is
represented by a partial diffeomorphism `Ψ i` from an open subset of `M` to the total space of a
Whitney sum `Eᵤ i ×ᵇ Eₛ i` of two smooth vector bundles with smooth fibre metrics over a compact
base `B i`, whose target contains the closed tube `‖u‖² + ‖v‖² ≤ 2ε` and in which
`f = c - ‖u‖² + ‖v‖²`. Different submanifolds may have different dimensions, indices and
codimensions. If the sources of the `Ψ i` are disjoint, the band `f⁻¹[c - ε, c + ε]` is compact
and its critical points lie in these sources, then `M_{c-ε}` with the negative disc bundles of the
`Ψ i` attached is a strong deformation retract of `M_{c+ε}`
(`TauCeti.exists_sublevel_union_negativeDiscBundles_deformation`). The companion theorem
`TauCeti.exists_sublevel_union_negativeDiscBundle_deformation` (`Morse/Bott/Attachment.lean`)
states the attachment intrinsically on `M`, for a tube carrying the squared norms `s, t` and a
scaling of the positive directions; here the normal forms are maps to actual Whitney sums of
vector bundles, whose targets need not be star-shaped in the positive directions.

The proof is Milnor's (Theorem 3.2), run fibrewise. The function `F = f - μ(‖u‖² + 2‖v‖²)`, where
`μ` is a smooth nonincreasing cutoff with `μ = 2ε` on `(-∞, ε]` and `μ = 0` on `[2ε, ∞)`, agrees
with `f` outside the tubes `‖u‖² + 2‖v‖² ≤ 2ε`, which are compact because the bases are; its
smoothness and the absence of critical points outside the tubes come from the construction
`TauCeti.lowerOn` shared with the cell attachment theorem. It has the same sublevel
`{F ≤ c + ε} = M_{c+ε}`, and no critical points in the band `F⁻¹[c - ε, c + ε]`. Inside a tube,
the derivative of `F` along the curve which scales `v` is `2‖v‖²(1 - 2μ') > 0` unless `v = 0`, and
on `v = 0` the value `c - ‖u‖² - μ(‖u‖²)` lies below `c - ε`. Only fibre directions are
differentiated, so no metric connection or horizontal derivative is involved. Hence `M_{c+ε}`
deformation retracts onto `{F ≤ c - ε}` (`TauCeti.exists_sublevelDeformation`). This set is
preserved by shrinking `v`, so Milnor's fibrewise retraction
`TauCeti.bundleQuadraticHandleDeformation`, read in the `Ψ i` and glued to the identity outside them
(`TauCeti.exists_inter_deformation_of_charts`), retracts it onto `M_{c-ε}` with the negative disc
bundles attached.

## Main results

* `TauCeti.exists_sublevel_union_negativeDiscBundles_deformation`: the sublevel `M_{c+ε}` strong
  deformation retracts onto `M_{c-ε}` with the negative disc bundles of Morse–Bott normal forms
  attached.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse Theory: Lecture Notes*, Theorem 15.4.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  proof of Theorem 3.2.
-/

public section

noncomputable section

open Bundle Function Set Filter Topology Metric
open scoped ContDiff Manifold

namespace TauCeti

section Scaling

variable {B Fᵤ Fₛ : Type*} {Eᵤ Eₛ : B → Type*} [∀ b, NormedAddCommGroup (Eᵤ b)]
  [∀ b, NormedAddCommGroup (Eₛ b)] [∀ b, NormedSpace ℝ (Eₛ b)]

/-- Scaling the second component `v` of a vector `(u, v)` of the Whitney sum `Eᵤ ×ᵇ Eₛ` by `σ`,
keeping its base point and its first component. -/
private def fibreScale (σ : ℝ) (z : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)) :
    TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ) :=
  ⟨z.proj, (z.2.1, σ • z.2.2)⟩

private theorem norm_fibreScale_snd_fst (σ : ℝ) (z : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)) :
    ‖(fibreScale σ z).2.1‖ = ‖z.2.1‖ :=
  rfl

omit [∀ b, NormedAddCommGroup (Eᵤ b)] in
private theorem norm_fibreScale_snd_snd (σ : ℝ) (z : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)) :
    ‖(fibreScale σ z).2.2‖ = |σ| * ‖z.2.2‖ := by
  rw [← Real.norm_eq_abs]
  exact norm_smul σ z.2.2

/-- Scaling the second component of a point of the closed tube `‖u‖² + ‖v‖² ≤ r` by a factor in
`[0, 1]` keeps it in the tube. -/
private theorem fibreScale_mem_tube {r s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {z : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)} (hz : z ∈ {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ r}) :
    fibreScale s z ∈ {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ r} := by
  rw [mem_ofPred_eq] at hz ⊢
  rw [norm_fibreScale_snd_fst, norm_fibreScale_snd_snd, mul_pow, sq_abs]
  linarith [mul_le_of_le_one_left (sq_nonneg ‖z.2.2‖) (pow_le_one₀ (n := 2) hs.1 hs.2)]

/-- The curve scaling the second component of a vector of a Whitney sum is smooth. -/
private theorem contMDiff_fibreScale {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
    [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B]
    [ChartedSpace HB B] [NormedAddCommGroup Fᵤ] [NormedSpace ℝ Fᵤ] [NormedAddCommGroup Fₛ]
    [NormedSpace ℝ Fₛ] [TopologicalSpace (TotalSpace Fᵤ Eᵤ)] [TopologicalSpace (TotalSpace Fₛ Eₛ)]
    [FiberBundle Fᵤ Eᵤ] [FiberBundle Fₛ Eₛ] [VectorBundle ℝ Fₛ Eₛ]
    (z : TotalSpace (Fᵤ × Fₛ) (Eᵤ ×ᵇ Eₛ)) :
    ContMDiff 𝓘(ℝ) (IB.prod 𝓘(ℝ, Fᵤ × Fₛ)) ∞ fun σ : ℝ ↦ fibreScale σ z := fun σ ↦
  Bundle.contMDiffAt_totalSpace_prod_iff.2 ⟨by simpa only [fibreScale] using contMDiffAt_const,
    (contMDiff_id.smul_totalSpace (contMDiff_const (c := (⟨z.proj, z.2.2⟩ :
      TotalSpace Fₛ Eₛ)))) σ⟩

end Scaling

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {ι : Type*} {EB : ι → Type*} [∀ i, NormedAddCommGroup (EB i)] [∀ i, NormedSpace ℝ (EB i)]
  {HB : ι → Type*} [∀ i, TopologicalSpace (HB i)] {IB : ∀ i, ModelWithCorners ℝ (EB i) (HB i)}
  {B : ι → Type*} [∀ i, TopologicalSpace (B i)] [∀ i, ChartedSpace (HB i) (B i)]
  {Fᵤ Fₛ : ι → Type*} [∀ i, NormedAddCommGroup (Fᵤ i)] [∀ i, NormedSpace ℝ (Fᵤ i)]
  [∀ i, NormedAddCommGroup (Fₛ i)] [∀ i, NormedSpace ℝ (Fₛ i)]
  {Eᵤ Eₛ : ∀ i, B i → Type*} [∀ i b, NormedAddCommGroup (Eᵤ i b)]
  [∀ i b, NormedAddCommGroup (Eₛ i b)]
  [∀ i, TopologicalSpace (TotalSpace (Fᵤ i) (Eᵤ i))]
  [∀ i, TopologicalSpace (TotalSpace (Fₛ i) (Eₛ i))]
  [∀ i, FiberBundle (Fᵤ i) (Eᵤ i)] [∀ i, FiberBundle (Fₛ i) (Eₛ i)]
  {f : M → ℝ} {c ε : ℝ}

section MilnorFunction

variable
  {Ψ : ∀ i, PartialDiffeomorph I ((IB i).prod 𝓘(ℝ, Fᵤ i × Fₛ i)) M
    (TotalSpace (Fᵤ i × Fₛ i) (Eᵤ i ×ᵇ Eₛ i)) ∞}
  {μ : ℝ → ℝ} {i : ι} {x : M}

/-- Milnor's function `f - μ(‖u‖² + 2‖v‖²)`, lowered in the source of each `Ψ i`, where
`Ψ i x = (u, v)`, and equal to `f` outside these sources. -/
private def milnorBottFunction [Fintype ι]
    (Ψ : ∀ i, PartialDiffeomorph I ((IB i).prod 𝓘(ℝ, Fᵤ i × Fₛ i)) M
      (TotalSpace (Fᵤ i × Fₛ i) (Eᵤ i ×ᵇ Eₛ i)) ∞)
    (f : M → ℝ) (μ : ℝ → ℝ) : M → ℝ :=
  lowerOn (fun i ↦ (Ψ i).source) (fun i y ↦ μ (‖(Ψ i y).2.1‖ ^ 2 + 2 * ‖(Ψ i y).2.2‖ ^ 2)) f

/-- In a normal form, the model set `bundleQuadraticSublevelUnionCell` of Milnor's retraction
is the part of the source in the lower sublevel or in the negative disc bundle. -/
private theorem mem_bundleQuadraticSublevelUnionCell_iff
    (hf : ∀ y ∈ (Ψ i).source, f y = c - ‖(Ψ i y).2.1‖ ^ 2 + ‖(Ψ i y).2.2‖ ^ 2)
    (hx : x ∈ (Ψ i).source) :
    Ψ i x ∈ bundleQuadraticSublevelUnionCell (Fᵤ i) (Fₛ i) (Eᵤ i) (Eₛ i) ε ↔
      f x ≤ c - ε ∨ x ∈ (Ψ i).source ∩ Ψ i ⁻¹' {z | ‖z.2.1‖ ^ 2 ≤ ε ∧ z.2.2 = 0} := by
  rw [mem_bundleQuadraticSublevelUnionCell, hf x hx]
  exact or_congr ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩ (by simp [hx])

/-- Each lowering term of Milnor's function vanishes in the source of its normal form outside
the image of the closed tube `‖u‖² + ‖v‖² ≤ 2ε`. -/
private theorem eqOn_zero_of_notMem_image (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0) (i : ι) :
    EqOn (fun y ↦ μ (‖(Ψ i y).2.1‖ ^ 2 + 2 * ‖(Ψ i y).2.2‖ ^ 2)) 0
      ((Ψ i).source \ (Ψ i).toOpenPartialHomeomorph.symm ''
        {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε}) := by
  rintro y ⟨hys, hy⟩
  have hlt : 2 * ε < ‖(Ψ i y).2.1‖ ^ 2 + ‖(Ψ i y).2.2‖ ^ 2 := by
    by_contra h
    exact hy ⟨Ψ i y, not_lt.1 h, (Ψ i).toOpenPartialHomeomorph.left_inv hys⟩
  exact hμ₀ _ (by nlinarith [sq_nonneg ‖(Ψ i y).2.2‖])

/-- The image of the closed tube `‖u‖² + ‖v‖² ≤ 2ε` lies in the source of its normal form. -/
private theorem image_tube_subset_source
    (hdisc : ∀ i, {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} ⊆ (Ψ i).target) (i : ι) :
    (Ψ i).toOpenPartialHomeomorph.symm '' {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} ⊆
      (Ψ i).source := by
  rintro _ ⟨z, hz, rfl⟩
  exact (Ψ i).toOpenPartialHomeomorph.map_target (hdisc i hz)

variable [Fintype ι] (hΨ : Pairwise (Disjoint on fun i ↦ (Ψ i).source))
include hΨ

/-- In the source of `Ψ i`, Milnor's function is `f - μ(‖u‖² + 2‖v‖²)`. -/
private theorem milnorBottFunction_of_mem (hx : x ∈ (Ψ i).source) :
    milnorBottFunction Ψ f μ x = f x - μ (‖(Ψ i x).2.1‖ ^ 2 + 2 * ‖(Ψ i x).2.2‖ ^ 2) :=
  lowerOn_of_mem hΨ hx

variable (hf : ∀ i, ∀ y ∈ (Ψ i).source, f y = c - ‖(Ψ i y).2.1‖ ^ 2 + ‖(Ψ i y).2.2‖ ^ 2)
include hf

/-- In the coordinates `(u, v)` of a normal form, `f` is `c - ‖u‖² + ‖v‖²` and Milnor's function
is `c - ‖u‖² + ‖v‖² - μ(‖u‖² + 2‖v‖²)`. -/
private theorem milnorBottFunction_symm_apply {z : TotalSpace (Fᵤ i × Fₛ i) (Eᵤ i ×ᵇ Eₛ i)}
    (hz : z ∈ (Ψ i).target) :
    f ((Ψ i).toOpenPartialHomeomorph.symm z) = c - ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ∧
      milnorBottFunction Ψ f μ ((Ψ i).toOpenPartialHomeomorph.symm z) =
        c - ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 - μ (‖z.2.1‖ ^ 2 + 2 * ‖z.2.2‖ ^ 2) := by
  set φ := (Ψ i).toOpenPartialHomeomorph
  have hx : φ.symm z ∈ (Ψ i).source := φ.map_target hz
  have hΨz : Ψ i (φ.symm z) = z := φ.right_inv hz
  have hfz := hf i _ hx
  rw [hΨz] at hfz
  refine ⟨hfz, ?_⟩
  rw [milnorBottFunction_of_mem hΨ hx, hΨz, hfz]

variable [∀ i b, NormedSpace ℝ (Eₛ i b)] in
/-- Scaling the second component of a point of the closed tube `‖u‖² + ‖v‖² ≤ 2ε` by a factor
in `[0, 1]` does not increase Milnor's function. -/
private theorem milnorBottFunction_symm_scale_le (hμa : Antitone μ)
    (hdisc : {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} ⊆ (Ψ i).target) (hx : x ∈ (Ψ i).source)
    (hxε : Ψ i x ∈ {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε}) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    milnorBottFunction Ψ f μ ((Ψ i).toOpenPartialHomeomorph.symm (fibreScale s (Ψ i x))) ≤
      milnorBottFunction Ψ f μ x := by
  rw [(milnorBottFunction_symm_apply hΨ hf (μ := μ) (hdisc (fibreScale_mem_tube hs hxε))).2,
    milnorBottFunction_of_mem hΨ hx, hf i x hx, norm_fibreScale_snd_fst, norm_fibreScale_snd_snd,
    mul_pow, sq_abs]
  have hst := mul_le_of_le_one_left (sq_nonneg ‖(Ψ i x).2.2‖) (pow_le_one₀ (n := 2) hs.1 hs.2)
  have harg : ‖(Ψ i x).2.1‖ ^ 2 + 2 * (s ^ 2 * ‖(Ψ i x).2.2‖ ^ 2) ≤
      ‖(Ψ i x).2.1‖ ^ 2 + 2 * ‖(Ψ i x).2.2‖ ^ 2 := by
    linarith
  linarith [hμa harg]

/-- Milnor's function lies below `c - ε` on the negative disc bundle `{‖u‖² ≤ ε, v = 0}` of a
normal form. -/
private theorem milnorBottFunction_le_of_mem_disc (hμ_eq : ∀ r ≤ ε, μ r = 2 * ε)
    (hx : x ∈ (Ψ i).source) (hxε : ‖(Ψ i x).2.1‖ ^ 2 ≤ ε) (hxv : (Ψ i x).2.2 = 0) :
    milnorBottFunction Ψ f μ x ≤ c - ε := by
  rw [milnorBottFunction_of_mem hΨ hx, hf i x hx, hxv]
  simp only [norm_zero, zero_pow two_ne_zero, mul_zero, add_zero]
  rw [hμ_eq _ hxε]
  linarith [sq_nonneg ‖(Ψ i x).2.1‖]

/-- A point of `{F ≤ c - ε}` lies in the lower sublevel with the negative disc bundles attached
exactly when its image in every normal form containing it lies in the model set of Milnor's
retraction. -/
private theorem mem_sublevel_union_negativeDiscBundles_iff
    (hxX : milnorBottFunction Ψ f μ x ≤ c - ε) :
    x ∈ {x | f x ≤ c - ε} ∪ ⋃ i, (Ψ i).source ∩ Ψ i ⁻¹' {z | ‖z.2.1‖ ^ 2 ≤ ε ∧ z.2.2 = 0} ↔
      ∀ i, x ∈ (Ψ i).toOpenPartialHomeomorph.source →
        (Ψ i).toOpenPartialHomeomorph x ∈
          bundleQuadraticSublevelUnionCell (Fᵤ i) (Fₛ i) (Eᵤ i) (Eₛ i) ε := by
  -- Read the open partial homeomorphisms underlying the `Ψ i` as the partial diffeomorphisms.
  simp only [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
    PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv]
  refine ⟨fun hxS i hi ↦ (mem_bundleQuadraticSublevelUnionCell_iff (hf i) hi).2 ?_, fun h ↦ ?_⟩
  · rcases hxS with h | h
    · exact .inl h
    · obtain ⟨j, hj⟩ := mem_iUnion.1 h
      obtain rfl : j = i := hΨ.eq (not_disjoint_iff.2 ⟨x, hj.1, hi⟩)
      exact .inr hj
  · by_cases hx : ∃ i, x ∈ (Ψ i).source
    · obtain ⟨i, hi⟩ := hx
      rcases (mem_bundleQuadraticSublevelUnionCell_iff (hf i) hi).1 (h i hi) with h' | h'
      · exact .inl h'
      · exact .inr (mem_iUnion.2 ⟨i, h'⟩)
    · rw [milnorBottFunction, lowerOn_of_forall_notMem (not_exists.1 hx)] at hxX
      exact .inl hxX

variable (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0)
include hμ₀

/-- Milnor's function has the same sublevel `{F ≤ c + ε}` as `f`: inside the tube
`‖u‖² + 2‖v‖² < 2ε` of a normal form, `f = c - ‖u‖² + ‖v‖² < c + ε`. -/
private theorem setOf_milnorBottFunction_le (hμ_nonneg : ∀ r, 0 ≤ μ r) :
    {x | milnorBottFunction Ψ f μ x ≤ c + ε} = {x | f x ≤ c + ε} := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ (lowerOn_le (fun _ _ _ ↦ hμ_nonneg _) x).trans hx⟩
  rw [mem_ofPred_eq] at hx ⊢
  by_cases hxs : ∃ i, x ∈ (Ψ i).source
  · obtain ⟨i, hi⟩ := hxs
    rw [milnorBottFunction_of_mem hΨ hi] at hx
    rcases le_or_gt (2 * ε) (‖(Ψ i x).2.1‖ ^ 2 + 2 * ‖(Ψ i x).2.2‖ ^ 2) with h | h
    · rwa [hμ₀ _ h, sub_zero] at hx
    · rw [hf i x hi]
      nlinarith [sq_nonneg ‖(Ψ i x).2.1‖]
  · rwa [milnorBottFunction, lowerOn_of_forall_notMem (not_exists.1 hxs)] at hx

/-- Points of `{F ≤ c - ε}` moved by Milnor's retraction lie in the closed tubes
`‖u‖² + ‖v‖² ≤ 2ε`, where the retraction only shrinks the second component, so it keeps them
in the tube and in `{F ≤ c - ε}`. -/
private theorem bundleQuadraticHandleDeformation_mem_tube_and_mem
    [∀ i b, InnerProductSpace ℝ (Eᵤ i b)] [∀ i b, InnerProductSpace ℝ (Eₛ i b)]
    [∀ i, VectorBundle ℝ (Fᵤ i) (Eᵤ i)] [∀ i, VectorBundle ℝ (Fₛ i) (Eₛ i)]
    [∀ i, IsContinuousRiemannianBundle (Fᵤ i) (Eᵤ i)]
    [∀ i, IsContinuousRiemannianBundle (Fₛ i) (Eₛ i)] (hμa : Antitone μ)
    (hdisc : ∀ i, {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} ⊆ (Ψ i).target) (i : ι) (x : M)
    (hx : x ∈ {x | milnorBottFunction Ψ f μ x ≤ c - ε} ∩ (Ψ i).toOpenPartialHomeomorph.source)
    (hxQ : (Ψ i).toOpenPartialHomeomorph x ∉
      bundleQuadraticSublevelUnionCell (Fᵤ i) (Fₛ i) (Eᵤ i) (Eₛ i) ε) (t : unitInterval) :
    bundleQuadraticHandleDeformation (TauCeti.continuous_norm_bundle (Fᵤ i) (Eᵤ i))
        (TauCeti.continuous_norm_bundle (Fₛ i) (Eₛ i)) ε
        (t, (Ψ i).toOpenPartialHomeomorph x) ∈ {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} ∧
      (Ψ i).toOpenPartialHomeomorph.symm (bundleQuadraticHandleDeformation
        (TauCeti.continuous_norm_bundle (Fᵤ i) (Eᵤ i))
        (TauCeti.continuous_norm_bundle (Fₛ i) (Eₛ i)) ε
        (t, (Ψ i).toOpenPartialHomeomorph x)) ∈ {x | milnorBottFunction Ψ f μ x ≤ c - ε} := by
  -- Read the open partial homeomorphism underlying `Ψ i` as the partial diffeomorphism, keeping
  -- its inverse.
  simp only [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
    PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv] at hx hxQ ⊢
  obtain ⟨hxX, hx⟩ := hx
  rw [mem_ofPred_eq] at hxX
  -- Outside the tube, Milnor's function is `f`, so the point lies in the lower sublevel and in
  -- the model set of the retraction.
  have hxε : Ψ i x ∈ {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} := by
    rw [mem_ofPred_eq]
    by_contra hlt
    refine hxQ ((mem_bundleQuadraticSublevelUnionCell_iff (hf i) hx).2 (.inl ?_))
    rwa [milnorBottFunction_of_mem hΨ hx, hμ₀ _ (by nlinarith [sq_nonneg ‖(Ψ i x).2.2‖]),
      sub_zero] at hxX
  obtain ⟨s, hs, hst⟩ := exists_quadraticHandleDeformation_apply_eq_smul ε t (Ψ i x).2
  have hG : bundleQuadraticHandleDeformation (TauCeti.continuous_norm_bundle (Fᵤ i) (Eᵤ i))
      (TauCeti.continuous_norm_bundle (Fₛ i) (Eₛ i)) ε (t, Ψ i x) = fibreScale s (Ψ i x) := by
    rw [bundleQuadraticHandleDeformation_apply]
    exact congrArg (TotalSpace.mk (Ψ i x).proj) hst
  rw [hG, mem_ofPred_eq]
  exact ⟨fibreScale_mem_tube hs hxε,
    (milnorBottFunction_symm_scale_le hΨ hf hμa (hdisc i) hx hxε hs).trans hxX⟩

omit hμ₀ in
variable [∀ i b, NormedSpace ℝ (Eₛ i b)] [∀ i, VectorBundle ℝ (Fₛ i) (Eₛ i)] in
/-- At a critical point `x` of Milnor's function in the source of `Ψ i`, the second component `v`
of `Ψ i x` vanishes. Along the curve scaling `v` by `t`, Milnor's function is
`c - ‖u‖² + t²‖v‖² - μ(‖u‖² + 2t²‖v‖²)`, whose derivative `2‖v‖²(1 - 2μ')` at `t = 1` is `0`,
while `μ' ≤ 0`. -/
private theorem snd_eq_zero_of_mfderiv_milnorBottFunction_eq_zero (hμ : ContDiff ℝ ∞ μ)
    (hμa : Antitone μ) (hF : MDifferentiableAt I 𝓘(ℝ) (milnorBottFunction Ψ f μ) x)
    (hx : x ∈ (Ψ i).source) (h0 : mfderiv I 𝓘(ℝ) (milnorBottFunction Ψ f μ) x = 0) :
    (Ψ i x).2.2 = 0 := by
  set φ := (Ψ i).toOpenPartialHomeomorph
  set z := Ψ i x
  -- The curve `γ` scales the second component of `Ψ i x` by `t`.
  set γ : ℝ → M := fun t ↦ φ.symm (fibreScale t z)
  have h1 : fibreScale 1 z = z := by simp [fibreScale]
  have hz : fibreScale 1 z ∈ (Ψ i).target := by
    rw [h1]
    exact φ.map_source hx
  have hγ1 : γ 1 = x := by
    simp only [γ, h1]
    exact φ.left_inv hx
  -- `F ∘ γ` has derivative `0` at `1`, since `x = γ 1` is a critical point of `F`.
  rw [← hγ1] at hF h0
  have hd : HasFDerivAt (milnorBottFunction Ψ f μ ∘ γ) (0 : ℝ →L[ℝ] ℝ) 1 := by
    -- The inverse of `φ` is the inverse `(Ψ i).symm` of the partial diffeomorphism: both are the
    -- inverse function of `Ψ i`.
    have hφ : ⇑φ.symm = ⇑(Ψ i).symm := rfl
    have hγ : MDifferentiableAt 𝓘(ℝ) I γ 1 := by
      simp only [γ, hφ]
      exact ((Ψ i).symm.mdifferentiableAt (by simp) (by simpa using hz)).comp 1
        ((contMDiff_fibreScale z 1).mdifferentiableAt (by simp))
    have h := hF.hasMFDerivAt.comp 1 hγ.hasMFDerivAt
    rwa [h0, ContinuousLinearMap.zero_comp, hasMFDerivAt_iff_hasFDerivAt] at h
  -- Explicitly, `F (γ t) = c - ‖u‖² + t² ‖v‖² - μ (‖u‖² + 2 t² ‖v‖²)` near `t = 1`.
  have heq : milnorBottFunction Ψ f μ ∘ γ =ᶠ[𝓝 1]
      fun t ↦ c - ‖z.2.1‖ ^ 2 + t ^ 2 * ‖z.2.2‖ ^ 2 -
        μ (‖z.2.1‖ ^ 2 + 2 * (t ^ 2 * ‖z.2.2‖ ^ 2)) := by
    filter_upwards [(contMDiff_fibreScale (IB := IB i) z).continuous.continuousAt.preimage_mem_nhds
      ((Ψ i).open_target.mem_nhds hz)] with t ht
    simpa only [γ, comp_apply, norm_fibreScale_snd_fst, norm_fibreScale_snd_snd, mul_pow,
      sq_abs] using (milnorBottFunction_symm_apply hΨ hf (μ := μ) ht).2
  simpa using eq_zero_of_hasDerivAt_add_sq_mul_sub_comp (hμ.differentiable (by simp)) hμa heq
    (by simpa using hd.hasDerivAt)

omit hμ₀ in
variable [∀ i b, NormedSpace ℝ (Eₛ i b)] [∀ i, VectorBundle ℝ (Fₛ i) (Eₛ i)] in
/-- **Milnor's function has no critical points in the sources of the normal forms above
`c - ε`.** At a critical point the second component vanishes, and there Milnor's function is
`c - ‖u‖² - μ(‖u‖²) < c - ε`. -/
private theorem mfderiv_milnorBottFunction_ne_zero (hε : 0 < ε) (hμ : ContDiff ℝ ∞ μ)
    (hμa : Antitone μ) (hμ_nonneg : ∀ r, 0 ≤ μ r) (hμ_eq : ∀ r ≤ ε, μ r = 2 * ε)
    (hF : MDifferentiableAt I 𝓘(ℝ) (milnorBottFunction Ψ f μ) x) (hx : x ∈ (Ψ i).source)
    (hxε : c - ε ≤ milnorBottFunction Ψ f μ x) :
    mfderiv I 𝓘(ℝ) (milnorBottFunction Ψ f μ) x ≠ 0 := by
  intro h0
  have hv := snd_eq_zero_of_mfderiv_milnorBottFunction_eq_zero hΨ hf hμ hμa hF hx h0
  rw [milnorBottFunction_of_mem hΨ hx, hf i x hx, hv, norm_zero] at hxε
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at hxε
  set a := ‖(Ψ i x).2.1‖ ^ 2
  have ha : 0 ≤ a := sq_nonneg _
  rcases le_or_gt a ε with h | h
  · rw [hμ_eq a h] at hxε
    linarith
  · linarith [hμ_nonneg a]

variable [∀ i b, InnerProductSpace ℝ (Eᵤ i b)] [∀ i b, InnerProductSpace ℝ (Eₛ i b)]
  [∀ i, VectorBundle ℝ (Fᵤ i) (Eᵤ i)] [∀ i, VectorBundle ℝ (Fₛ i) (Eₛ i)]
  [∀ i, IsContMDiffRiemannianBundle (IB i) ∞ (Fᵤ i) (Eᵤ i)]
  [∀ i, IsContMDiffRiemannianBundle (IB i) ∞ (Fₛ i) (Eₛ i)]
  [∀ i, CompactSpace (B i)]
  [∀ i, FiniteDimensional ℝ (Fᵤ i)] [∀ i, FiniteDimensional ℝ (Fₛ i)]
  (hdisc : ∀ i, {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} ⊆ (Ψ i).target)
include hdisc

omit [Fintype ι] hΨ hf hμ₀ in
private theorem isCompact_image_tube (i : ι) :
    IsCompact ((Ψ i).toOpenPartialHomeomorph.symm ''
      {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε}) :=
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (HB := HB i) (IB := IB i)
    (n := ∞) (F := Fᵤ i) (V := Eᵤ i)
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (HB := HB i) (IB := IB i)
    (n := ∞) (F := Fₛ i) (V := Eₛ i)
  (isCompact_setOf_norm_sq_add_norm_sq_le_prod_bundle (r := fun _ ↦ 2 * ε)
    continuous_const).image_of_continuousOn
    ((Ψ i).toOpenPartialHomeomorph.continuousOn_symm.mono (hdisc i))

variable [T2Space M]

omit hΨ hf in
/-- **Milnor's function is smooth.** -/
private theorem contMDiff_milnorBottFunction (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hμ : ContDiff ℝ ∞ μ) : ContMDiff I 𝓘(ℝ) ∞ (milnorBottFunction Ψ f μ) :=
  contMDiff_lowerOn (eqOn_zero_of_notMem_image hμ₀)
    (fun i ↦ (isCompact_image_tube hdisc i).isClosed) (fun i ↦ (Ψ i).open_source)
    (image_tube_subset_source hdisc) hfs fun i ↦
    -- `μ (s + 2 t)` is a smooth function of `(s, t) = (‖u‖², ‖v‖²)`.
    have hg : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ μ (p.1 + 2 * p.2) := hμ.comp (by fun_prop)
    hg.contMDiff.comp_contMDiffOn
      ((((contMDiff_norm_sq_bundle (IB := IB i) (n := ∞) (Fᵤ i) (Eᵤ i)).comp
        Bundle.Prod.contMDiff_fst).comp_contMDiffOn (Ψ i).contMDiffOn).prodMk_space
      (((contMDiff_norm_sq_bundle (IB := IB i) (n := ∞) (Fₛ i) (Eₛ i)).comp
        Bundle.Prod.contMDiff_snd).comp_contMDiffOn (Ψ i).contMDiffOn))

/-- Milnor's function has no critical points in the band `F⁻¹[c - ε, c + ε]`, provided the
critical points of `f` in the band `f⁻¹[c - ε, c + ε]` lie in the sources of the normal forms. -/
private theorem mfderiv_milnorBottFunction_ne_zero_of_mem_Icc
    (hε : 0 < ε) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) (hμ : ContDiff ℝ ∞ μ) (hμa : Antitone μ)
    (hμ_nonneg : ∀ r, 0 ≤ μ r) (hμ_eq : ∀ r ≤ ε, μ r = 2 * ε)
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (Ψ i).source)
    (hx : milnorBottFunction Ψ f μ x ∈ Icc (c - ε) (c + ε)) :
    mfderiv I 𝓘(ℝ) (milnorBottFunction Ψ f μ) x ≠ 0 := by
  by_cases hxs : ∃ i, x ∈ (Ψ i).source
  · obtain ⟨i, hi⟩ := hxs
    exact mfderiv_milnorBottFunction_ne_zero hΨ hf hε hμ hμa hμ_nonneg hμ_eq
      ((contMDiff_milnorBottFunction hμ₀ hdisc hfs hμ).mdifferentiableAt (by simp)) hi hx.1
  · exact mfderiv_lowerOn_ne_zero_of_forall_notMem (eqOn_zero_of_notMem_image hμ₀)
      (fun i ↦ (isCompact_image_tube hdisc i).isClosed) (image_tube_subset_source hdisc) hcrit
      (not_exists.1 hxs) hx

end MilnorFunction

section Attachment

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [∀ i b, InnerProductSpace ℝ (Eᵤ i b)] [∀ i b, InnerProductSpace ℝ (Eₛ i b)]
  [∀ i, VectorBundle ℝ (Fᵤ i) (Eᵤ i)] [∀ i, VectorBundle ℝ (Fₛ i) (Eₛ i)]
  [∀ i, IsContMDiffRiemannianBundle (IB i) ∞ (Fᵤ i) (Eᵤ i)]
  [∀ i, IsContMDiffRiemannianBundle (IB i) ∞ (Fₛ i) (Eₛ i)]
  [∀ i, CompactSpace (B i)]
  [∀ i, FiniteDimensional ℝ (Fᵤ i)] [∀ i, FiniteDimensional ℝ (Fₛ i)]

/-- **Attaching negative disc bundles across a Morse–Bott critical level** (Bott; Milnor's
Theorem 3.2 run fibrewise). Let `f` be smooth, and let `Ψ i` be partial diffeomorphisms from
open subsets of `M`, with pairwise disjoint sources, onto open subsets of the total spaces of
Whitney sums `Eᵤ i ×ᵇ Eₛ i` of smooth vector bundles with smooth fibre metrics and
finite-dimensional fibres over compact bases, in which
`f = c - ‖u‖² + ‖v‖²` for `Ψ i x = (u, v)`. Suppose each target contains the closed tube
`‖u‖² + ‖v‖² ≤ 2ε`, the band `f⁻¹[c - ε, c + ε]` is compact, and its critical points lie in the
sources of the `Ψ i`. The negative disc bundle of `Ψ i` is the set of points with
`‖u‖² ≤ ε` and `v = 0`.

Then the lower sublevel `{f ≤ c - ε}` with these negative disc bundles attached is a strong
deformation retract of `{f ≤ c + ε}`: there is a retraction of `{f ≤ c + ε}` onto it, and a
homotopy in `{f ≤ c + ε}` from this retraction to the identity which fixes it pointwise. The disc
bundles lie in `{f ≤ c}`, so intersecting with `{f ≤ c + ε}` does not change the retract. -/
theorem exists_sublevel_union_negativeDiscBundles_deformation [Finite ι]
    (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (Ψ : ∀ i, PartialDiffeomorph I ((IB i).prod 𝓘(ℝ, Fᵤ i × Fₛ i)) M
      (TotalSpace (Fᵤ i × Fₛ i) (Eᵤ i ×ᵇ Eₛ i)) ∞)
    (hΨ : Pairwise (Disjoint on fun i ↦ (Ψ i).source))
    (hdisc : ∀ i, {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} ⊆ (Ψ i).target)
    (hf : ∀ i, ∀ y ∈ (Ψ i).source, f y = c - ‖(Ψ i y).2.1‖ ^ 2 + ‖(Ψ i y).2.2‖ ^ 2)
    (hcompact : IsCompact (f ⁻¹' Icc (c - ε) (c + ε)))
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (Ψ i).source) :
    ∃ r : C({x | f x ≤ c + ε}, ↥({x | f x ≤ c + ε} ∩ ({x | f x ≤ c - ε} ∪
        ⋃ i, (Ψ i).source ∩ Ψ i ⁻¹' {z | ‖z.2.1‖ ^ 2 ≤ ε ∧ z.2.2 = 0}))),
      (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
        (ContinuousMap.id _) {x | (x : M) ∈ {x | f x ≤ c - ε} ∪
          ⋃ i, (Ψ i).source ∩ Ψ i ⁻¹' {z | ‖z.2.1‖ ^ 2 ≤ ε ∧ z.2.2 = 0}}) := by
  rcases le_or_gt ε 0 with hε | hε
  · -- For `ε ≤ 0` the sublevel `{f ≤ c + ε}` lies in `{f ≤ c - ε}`, so the retraction is trivial.
    have hsub : ∀ x : {x | f x ≤ c + ε}, (x : M) ∈ {x | f x ≤ c - ε} ∪
        ⋃ i, (Ψ i).source ∩ Ψ i ⁻¹' {z | ‖z.2.1‖ ^ 2 ≤ ε ∧ z.2.2 = 0} :=
      -- `x.2 : (x : M) ∈ {x | f x ≤ c + ε}` is the inequality `f x ≤ c + ε` by the definition of
      -- membership in a set-builder set.
      fun x ↦ Or.inl (le_trans (b := c + ε) x.2 (by linarith))
    exact ⟨⟨fun x ↦ ⟨x.1, x.2, hsub x⟩, continuous_subtype_val.subtype_mk _⟩, fun x ↦ rfl,
      ⟨ContinuousMap.HomotopyRel.refl _ _⟩⟩
  have := Fintype.ofFinite ι
  have (i : ι) := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (HB := HB i)
    (IB := IB i) (n := ∞) (F := Fᵤ i) (V := Eᵤ i)
  have (i : ι) := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (HB := HB i)
    (IB := IB i) (n := ∞) (F := Fₛ i) (V := Eₛ i)
  -- Milnor's cutoff, equal to `2ε` on `(-∞, ε]` and to `0` on `[2ε, ∞)`.
  obtain ⟨μ, hμ, hμa, hμ_nonneg, hμ₀, hμ_eq, -⟩ :=
    exists_contDiff_antitone_cutoff (by linarith : ε < 2 * ε) (by positivity : 0 ≤ 2 * ε)
  set F := milnorBottFunction Ψ f μ
  have hFs : ContMDiff I 𝓘(ℝ) ∞ F := contMDiff_milnorBottFunction hμ₀ hdisc hfs hμ
  have hFf (x : M) : F x ≤ f x := lowerOn_le (fun _ _ _ ↦ hμ_nonneg _) x
  have hX : {x | F x ≤ c + ε} = {x | f x ≤ c + ε} :=
    setOf_milnorBottFunction_le hΨ hf hμ₀ hμ_nonneg
  have hab : c - ε ≤ c + ε := by linarith
  have hYX : {x | F x ≤ c - ε} ⊆ {x | F x ≤ c + ε} := sublevel_mono F hab
  have hSY : {x | f x ≤ c - ε} ∪
      ⋃ i, (Ψ i).source ∩ Ψ i ⁻¹' {z | ‖z.2.1‖ ^ 2 ≤ ε ∧ z.2.2 = 0} ⊆ {x | F x ≤ c - ε} :=
    union_subset (fun x hx ↦ (hFf x).trans hx) <| iUnion_subset
      fun i x ⟨hxi, hxε, hxv⟩ ↦ milnorBottFunction_le_of_mem_disc hΨ hf hμ_eq hxi hxε hxv
  have hFcompact : IsCompact (F ⁻¹' Icc (c - ε) (c + ε)) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hFs.continuous) fun x hx ↦
      ⟨hx.1.trans (hFf x), (Set.ext_iff.1 hX x).1 hx.2⟩
  -- `{F ≤ c + ε}` retracts onto `{F ≤ c - ε}`, as `F` has no critical points in the compact band.
  have hband := exists_sublevelDeformation hFs hab hFcompact fun _ h₁ h₂ ↦
    mfderiv_milnorBottFunction_ne_zero_of_mem_Icc hΨ hf hμ₀ hdisc hε hfs hμ hμa hμ_nonneg hμ_eq
      hcrit ⟨h₁, h₂⟩
  rw [sublevelInclusion_eq_inclusion] at hband
  -- `{F ≤ c - ε}` retracts onto the lower sublevel with the negative disc bundles attached, as
  -- shrinking the second component of a normal form lowers `F`.
  have hcell := exists_inter_deformation_of_charts (φ := fun i ↦ (Ψ i).toOpenPartialHomeomorph)
    (G := fun i ↦ bundleQuadraticHandleDeformation (TauCeti.continuous_norm_bundle (Fᵤ i) (Eᵤ i))
      (TauCeti.continuous_norm_bundle (Fₛ i) (Eₛ i)) ε)
    hΨ hdisc (bundleQuadraticHandleDeformation_mem_tube_and_mem hΨ hf hμ₀ hμa hdisc)
    (fun i ↦ isCompact_setOf_norm_sq_add_norm_sq_le_prod_bundle (r := fun _ ↦ 2 * ε)
      continuous_const)
    (fun i ↦ bundleQuadraticHandleRetraction_mem _ _)
    fun x hx ↦ mem_sublevel_union_negativeDiscBundles_iff hΨ hf hx
  -- The goal is stated for `{f ≤ c + ε}`, which is the same set as `{F ≤ c + ε}`.
  rw [← hX]
  exact ContinuousMap.HomotopicRel.exists_inter_deformation_trans hYX
    (inter_subset_right.trans hSY) hband hcell

end Attachment

end TauCeti
