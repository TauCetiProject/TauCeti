/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.Morse.HandleRetraction.Bundle
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.Morse.Deformation
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Prod
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Topology.FiberBundle.Prod
import TauCeti.Topology.Homotopy.DeformationRetract
import TauCeti.Topology.VectorBundle.DiscSphere

/-!
# Attaching negative disc bundles across a Morse–Bott critical level

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
(`TauCeti.exists_sublevel_union_negativeDiscBundles_deformation`).

The proof is Milnor's (Theorem 3.2), run fibrewise. The function `F = f - μ(‖u‖² + 2‖v‖²)`, where
`μ` is a smooth nonincreasing cutoff with `μ = 2ε` on `(-∞, ε]` and `μ = 0` on `[2ε, ∞)`, agrees
with `f` outside the tubes `‖u‖² + 2‖v‖² ≤ 2ε`, which are compact because the bases are. It has
the same sublevel `{F ≤ c + ε} = M_{c+ε}`, and no critical points in the band
`F⁻¹[c - ε, c + ε]`. Inside a tube, the derivative of `F` along the curve which scales `v` is
`2‖v‖²(1 - 2μ') > 0` unless `v = 0`, and on `v = 0` the value `c - ‖u‖² - μ(‖u‖²)` lies below
`c - ε`. Only fibre directions are differentiated, so no metric connection or horizontal
derivative is involved. Hence `M_{c+ε}` deformation retracts onto `{F ≤ c - ε}`
(`TauCeti.exists_sublevelDeformation`). This set is preserved by shrinking `v`, so Milnor's
fibrewise retraction `TauCeti.bundleQuadraticHandleDeformation`, read in the `Ψ i` and glued to
the identity outside them (`TauCeti.exists_inter_deformation_of_charts`), retracts it onto
`M_{c-ε}` with the negative disc bundles attached.

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

section SmoothNorms

variable (i : ι)

variable [∀ i b, InnerProductSpace ℝ (Eᵤ i b)] [∀ i, VectorBundle ℝ (Fᵤ i) (Eᵤ i)]
  [∀ i, IsContMDiffRiemannianBundle (IB i) ∞ (Fᵤ i) (Eᵤ i)] in
/-- The squared norm `‖u‖²` of the first component of a vector of a Whitney sum is a smooth
function on the total space when the first summand is a smooth Riemannian bundle. -/
private theorem contMDiff_norm_fst_sq :
    ContMDiff ((IB i).prod 𝓘(ℝ, Fᵤ i × Fₛ i)) 𝓘(ℝ) ∞
      fun z : TotalSpace (Fᵤ i × Fₛ i) (Eᵤ i ×ᵇ Eₛ i) ↦ ‖z.2.1‖ ^ 2 := by
  have h := (Bundle.Prod.contMDiff_fst (I := IB i) (F₁ := Fᵤ i) (F₂ := Fₛ i) (E₁ := Eᵤ i)
    (E₂ := Eₛ i) (n := ∞)).inner_bundle Bundle.Prod.contMDiff_fst
  simpa only [real_inner_self_eq_norm_sq] using h

variable [∀ i b, InnerProductSpace ℝ (Eₛ i b)] [∀ i, VectorBundle ℝ (Fₛ i) (Eₛ i)]
  [∀ i, IsContMDiffRiemannianBundle (IB i) ∞ (Fₛ i) (Eₛ i)] in
/-- The squared norm `‖v‖²` of the second component of a vector of a Whitney sum is a smooth
function on the total space when the second summand is a smooth Riemannian bundle. -/
private theorem contMDiff_norm_snd_sq :
    ContMDiff ((IB i).prod 𝓘(ℝ, Fᵤ i × Fₛ i)) 𝓘(ℝ) ∞
      fun z : TotalSpace (Fᵤ i × Fₛ i) (Eᵤ i ×ᵇ Eₛ i) ↦ ‖z.2.2‖ ^ 2 := by
  have h := (Bundle.Prod.contMDiff_snd (I := IB i) (F₁ := Fᵤ i) (F₂ := Fₛ i) (E₁ := Eᵤ i)
    (E₂ := Eₛ i) (n := ∞)).inner_bundle Bundle.Prod.contMDiff_snd
  simpa only [real_inner_self_eq_norm_sq] using h

end SmoothNorms

section Tube

variable (i : ι) [∀ b, InnerProductSpace ℝ (Eᵤ i b)] [∀ b, InnerProductSpace ℝ (Eₛ i b)]
  [VectorBundle ℝ (Fᵤ i) (Eᵤ i)] [VectorBundle ℝ (Fₛ i) (Eₛ i)]
  [IsContinuousRiemannianBundle (Fᵤ i) (Eᵤ i)] [IsContinuousRiemannianBundle (Fₛ i) (Eₛ i)]

/-- The closed tube `‖u‖² + ‖v‖² ≤ r` of a Whitney sum of continuous Riemannian bundles with
finite-dimensional fibres over a compact Hausdorff base is compact. -/
private theorem isCompact_tube [CompactSpace (B i)] [T2Space (B i)]
    [FiniteDimensional ℝ (Fᵤ i)] [FiniteDimensional ℝ (Fₛ i)] (r : ℝ) :
    IsCompact {z : TotalSpace (Fᵤ i × Fₛ i) (Eᵤ i ×ᵇ Eₛ i) | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ r} := by
  -- The tube lies in the product of the closed disc bundles of radius `√r` of the summands.
  have hdiag := FiberBundle.Prod.isClosedEmbedding_diag (E₁ := Eᵤ i) (E₂ := Eₛ i)
    (FiberBundle.continuous_proj (Fᵤ i) (Eᵤ i)) (FiberBundle.continuous_proj (Fₛ i) (Eₛ i))
  have hu := (TauCeti.continuous_norm_bundle (Fᵤ i) (Eᵤ i)).comp
    (FiberBundle.Prod.continuous_totalSpaceFst (F₂ := Fₛ i) (E₂ := Eₛ i))
  have hv := (TauCeti.continuous_norm_bundle (Fₛ i) (Eₛ i)).comp
    (FiberBundle.Prod.continuous_totalSpaceSnd (F₁ := Fᵤ i) (E₁ := Eᵤ i))
  refine (hdiag.isCompact_preimage
    ((isCompact_setOf_norm_le_bundle (F := Fᵤ i) (V := Eᵤ i) (continuous_const (y := √r))).prod
      (isCompact_setOf_norm_le_bundle (F := Fₛ i) (V := Eₛ i)
        (continuous_const (y := √r))))).of_isClosed_subset
    (isClosed_le ((hu.pow 2).add (hv.pow 2)) continuous_const) fun z hz ↦ ?_
  have hz : ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ r := hz
  exact ⟨Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖z.2.2‖]),
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖z.2.1‖])⟩

end Tube

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
    (f : M → ℝ) (μ : ℝ → ℝ) (x : M) : ℝ :=
  f x - ∑ i, (Ψ i).source.indicator (fun y ↦ μ (‖(Ψ i y).2.1‖ ^ 2 + 2 * ‖(Ψ i y).2.2‖ ^ 2)) x

variable [Fintype ι]

private theorem milnorBottFunction_of_mem (hΨ : Pairwise (Disjoint on fun i ↦ (Ψ i).source))
    (hx : x ∈ (Ψ i).source) :
    milnorBottFunction Ψ f μ x = f x - μ (‖(Ψ i x).2.1‖ ^ 2 + 2 * ‖(Ψ i x).2.2‖ ^ 2) := by
  rw [milnorBottFunction, Finset.sum_eq_single i (fun j _ hji ↦ indicator_of_notMem
    (fun hj ↦ (hΨ hji).ne_of_mem hj hx rfl) _) (by simp), indicator_of_mem hx]

private theorem milnorBottFunction_of_forall_notMem (hx : ∀ i, x ∉ (Ψ i).source) :
    milnorBottFunction Ψ f μ x = f x := by
  simp [milnorBottFunction, indicator_of_notMem (hx _)]

private theorem milnorBottFunction_le (hμ : ∀ r, 0 ≤ μ r) (x : M) :
    milnorBottFunction Ψ f μ x ≤ f x :=
  sub_le_self _ (Finset.sum_nonneg fun _ _ ↦ indicator_nonneg (fun _ _ ↦ hμ _) _)

variable (hΨ : Pairwise (Disjoint on fun i ↦ (Ψ i).source))
  (hf : ∀ i, ∀ y ∈ (Ψ i).source, f y = c - ‖(Ψ i y).2.1‖ ^ 2 + ‖(Ψ i y).2.2‖ ^ 2)
include hΨ hf

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
    (hxε : ‖(Ψ i x).2.1‖ ^ 2 + ‖(Ψ i x).2.2‖ ^ 2 ≤ 2 * ε) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    milnorBottFunction Ψ f μ ((Ψ i).toOpenPartialHomeomorph.symm (fibreScale s (Ψ i x))) ≤
      milnorBottFunction Ψ f μ x := by
  have hs2 : s ^ 2 ≤ 1 := pow_le_one₀ hs.1 hs.2
  have hw : fibreScale s (Ψ i x) ∈ (Ψ i).target := hdisc <| by
    rw [mem_ofPred_eq, norm_fibreScale_snd_fst, norm_fibreScale_snd_snd, mul_pow, sq_abs]
    linarith [mul_le_of_le_one_left (sq_nonneg ‖(Ψ i x).2.2‖) hs2]
  rw [(milnorBottFunction_symm_apply hΨ hf (μ := μ) hw).2, milnorBottFunction_of_mem hΨ hx,
    hf i x hx, norm_fibreScale_snd_fst, norm_fibreScale_snd_snd, mul_pow, sq_abs]
  have hst := mul_le_of_le_one_left (sq_nonneg ‖(Ψ i x).2.2‖) hs2
  have hμle := hμa (show ‖(Ψ i x).2.1‖ ^ 2 + 2 * (s ^ 2 * ‖(Ψ i x).2.2‖ ^ 2) ≤
    ‖(Ψ i x).2.1‖ ^ 2 + 2 * ‖(Ψ i x).2.2‖ ^ 2 by linarith)
  linarith

/-- Milnor's function lies below `c - ε` on the negative disc bundle `{‖u‖² ≤ ε, v = 0}` of a
normal form. -/
private theorem milnorBottFunction_le_of_mem_disc (hμ_eq : ∀ r ≤ ε, μ r = 2 * ε)
    (hx : x ∈ (Ψ i).source) (hxε : ‖(Ψ i x).2.1‖ ^ 2 ≤ ε) (hxv : (Ψ i x).2.2 = 0) :
    milnorBottFunction Ψ f μ x ≤ c - ε := by
  rw [milnorBottFunction_of_mem hΨ hx, hf i x hx, hxv, norm_zero,
    show ‖(Ψ i x).2.1‖ ^ 2 + 2 * (0 : ℝ) ^ 2 = ‖(Ψ i x).2.1‖ ^ 2 by ring, hμ_eq _ hxε]
  linarith [sq_nonneg ‖(Ψ i x).2.1‖]

variable (hμ₀ : ∀ r, 2 * ε ≤ r → μ r = 0)
include hμ₀

omit hf in
/-- Outside the closed tube `‖u‖² + ‖v‖² ≤ 2ε` of a normal form, Milnor's function agrees with
`f`. -/
private theorem milnorBottFunction_eq_of_lt (hx : x ∈ (Ψ i).source)
    (hxε : 2 * ε < ‖(Ψ i x).2.1‖ ^ 2 + ‖(Ψ i x).2.2‖ ^ 2) :
    milnorBottFunction Ψ f μ x = f x := by
  rw [milnorBottFunction_of_mem hΨ hx, hμ₀ _ (by nlinarith [sq_nonneg ‖(Ψ i x).2.2‖]), sub_zero]

omit [Fintype ι] hΨ hf in
/-- Each lowering term of Milnor's function vanishes outside the image of the closed tube
`‖u‖² + ‖v‖² ≤ 2ε` of its normal form. -/
private theorem indicator_eq_zero_of_notMem_image [Finite ι] (i : ι) {y : M}
    (hy : y ∉ (Ψ i).toOpenPartialHomeomorph.symm ''
      {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε}) :
    (Ψ i).source.indicator (fun y ↦ μ (‖(Ψ i y).2.1‖ ^ 2 + 2 * ‖(Ψ i y).2.2‖ ^ 2)) y = 0 := by
  have := Fintype.ofFinite ι
  by_cases hys : y ∈ (Ψ i).source
  · have hlt : 2 * ε < ‖(Ψ i y).2.1‖ ^ 2 + ‖(Ψ i y).2.2‖ ^ 2 := by
      by_contra h
      exact hy ⟨Ψ i y, not_lt.1 h, (Ψ i).toOpenPartialHomeomorph.left_inv hys⟩
    rw [indicator_of_mem hys]
    exact hμ₀ _ (by nlinarith [sq_nonneg ‖(Ψ i y).2.2‖])
  · exact indicator_of_notMem hys _

/-- Milnor's function has the same sublevel `{F ≤ c + ε}` as `f`: inside the tube
`‖u‖² + 2‖v‖² < 2ε` of a normal form, `f = c - ‖u‖² + ‖v‖² < c + ε`. -/
private theorem setOf_milnorBottFunction_le (hμ_nonneg : ∀ r, 0 ≤ μ r) :
    {x | milnorBottFunction Ψ f μ x ≤ c + ε} = {x | f x ≤ c + ε} := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ (milnorBottFunction_le hμ_nonneg x).trans hx⟩
  by_cases hxs : ∃ i, x ∈ (Ψ i).source
  · obtain ⟨i, hi⟩ := hxs
    have hfx := hf i x hi
    have hFx := milnorBottFunction_of_mem (f := f) (μ := μ) hΨ hi
    rcases le_or_gt (2 * ε) (‖(Ψ i x).2.1‖ ^ 2 + 2 * ‖(Ψ i x).2.2‖ ^ 2) with h | h
    · rw [mem_ofPred_eq, hFx, hμ₀ _ h, sub_zero] at hx
      exact hx
    · rw [mem_ofPred_eq, hfx]
      nlinarith [sq_nonneg ‖(Ψ i x).2.1‖]
  · rwa [mem_ofPred_eq, milnorBottFunction_of_forall_notMem (not_exists.1 hxs)] at hx

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
  set a := ‖z.2.1‖ ^ 2
  set b := ‖z.2.2‖ ^ 2
  -- The curve `γ` scales the second component of `Ψ i x` by `t`.
  set γ : ℝ → M := fun t ↦ (Ψ i).symm (fibreScale t z)
  have h1 : fibreScale 1 z = z := by simp [fibreScale]
  have hz : fibreScale 1 z ∈ (Ψ i).target := by
    rw [h1]
    exact φ.map_source hx
  -- `F ∘ γ` has derivative `0` at `1`, since `x = γ 1` is a critical point of `F`.
  rw [← show γ 1 = x from (congrArg φ.symm h1).trans (φ.left_inv hx)] at hF h0
  have hd : HasFDerivAt (milnorBottFunction Ψ f μ ∘ γ) (0 : ℝ →L[ℝ] ℝ) 1 := by
    have hγ : MDifferentiableAt 𝓘(ℝ) I γ 1 := (((Ψ i).contMDiffOn_invFun.contMDiffAt
      ((Ψ i).open_target.mem_nhds hz)).mdifferentiableAt (by simp)).comp 1
      ((contMDiff_fibreScale z 1).mdifferentiableAt (by simp))
    have h := hF.hasMFDerivAt.comp 1 hγ.hasMFDerivAt
    rwa [h0, ContinuousLinearMap.zero_comp, hasMFDerivAt_iff_hasFDerivAt] at h
  -- Explicitly, `F (γ t) = c - a + t² b - μ (a + 2 t² b)` near `t = 1`.
  have heq : milnorBottFunction Ψ f μ ∘ γ =ᶠ[𝓝 1]
      fun t ↦ c - a + t ^ 2 * b - μ (a + 2 * (t ^ 2 * b)) := by
    filter_upwards [(contMDiff_fibreScale (IB := IB i) z).continuous.continuousAt.preimage_mem_nhds
      ((Ψ i).open_target.mem_nhds hz)] with t ht
    have h := (milnorBottFunction_symm_apply hΨ hf (μ := μ) ht).2
    rw [norm_fibreScale_snd_fst, norm_fibreScale_snd_snd, mul_pow, sq_abs] at h
    exact h
  have hq := (hasDerivAt_pow 2 (1 : ℝ)).mul_const b
  have hg := ((hq.const_add (c - a))).sub
    (((hμ.differentiable (by simp)) _).hasDerivAt.comp 1 ((hq.const_mul 2).const_add a))
  have hval := (hg.congr_of_eventuallyEq heq).unique (by simpa using hd.hasDerivAt)
  have h : b * (2 - 4 * deriv μ (a + 2 * (1 ^ 2 * b))) = 0 := by linear_combination hval
  have := hμa.deriv_nonpos (x := a + 2 * (1 ^ 2 * b))
  simpa [b] using (mul_eq_zero.1 h).resolve_right (by linarith)

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
  [∀ i, CompactSpace (B i)] [∀ i, T2Space (B i)]
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
  (isCompact_tube i (2 * ε)).image_of_continuousOn
    ((Ψ i).toOpenPartialHomeomorph.continuousOn_symm.mono (hdisc i))

variable [T2Space M]

omit hΨ hf in
/-- Away from the images of the closed tubes `‖u‖² + ‖v‖² ≤ 2ε`, Milnor's function agrees with
`f` on a neighbourhood. -/
private theorem milnorBottFunction_eventuallyEq
    (hx : x ∉ ⋃ i, (Ψ i).toOpenPartialHomeomorph.symm ''
      {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε}) :
    milnorBottFunction Ψ f μ =ᶠ[𝓝 x] f := by
  have hclosed : IsClosed (⋃ i, (Ψ i).toOpenPartialHomeomorph.symm ''
      {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε}) :=
    isClosed_iUnion_of_finite fun i ↦ (isCompact_image_tube hdisc i).isClosed
  filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with y hy
  rw [milnorBottFunction, Finset.sum_eq_zero fun i _ ↦
    indicator_eq_zero_of_notMem_image hμ₀ i fun h ↦ hy (mem_iUnion.2 ⟨i, h⟩), sub_zero]

omit hΨ hf in
/-- **Milnor's function is smooth.** -/
private theorem contMDiff_milnorBottFunction (hfs : ContMDiff I 𝓘(ℝ) ∞ f)
    (hμ : ContDiff ℝ ∞ μ) : ContMDiff I 𝓘(ℝ) ∞ (milnorBottFunction Ψ f μ) := by
  refine ContMDiff.sub hfs (ContMDiff.sum fun i _ ↦ contMDiff_of_tsupport fun y hy ↦ ?_)
  -- The lowering term is supported in the compact image of the tube, inside the source.
  have hK : tsupport ((Ψ i).source.indicator
        fun y ↦ μ (‖(Ψ i y).2.1‖ ^ 2 + 2 * ‖(Ψ i y).2.2‖ ^ 2)) ⊆
      (Ψ i).toOpenPartialHomeomorph.symm '' {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} :=
    closure_minimal (fun y hy ↦ not_not.1 fun h ↦ hy
      (indicator_eq_zero_of_notMem_image hμ₀ i h))
      (isCompact_image_tube hdisc i).isClosed
  obtain ⟨z, hz, rfl⟩ := hK hy
  have hs : (Ψ i).toOpenPartialHomeomorph.symm z ∈ (Ψ i).source :=
    (Ψ i).toOpenPartialHomeomorph.map_target (hdisc i hz)
  have hΨ' : ContMDiffAt I ((IB i).prod 𝓘(ℝ, Fᵤ i × Fₛ i)) ∞ (Ψ i)
      ((Ψ i).toOpenPartialHomeomorph.symm z) :=
    (Ψ i).contMDiffOn.contMDiffAt ((Ψ i).open_source.mem_nhds hs)
  have hterm : ContMDiffAt I 𝓘(ℝ) ∞
      (fun y ↦ μ (‖(Ψ i y).2.1‖ ^ 2 + 2 * ‖(Ψ i y).2.2‖ ^ 2))
      ((Ψ i).toOpenPartialHomeomorph.symm z) :=
    -- `μ (s + 2 t)` is a smooth function of `(s, t) = (‖u‖², ‖v‖²)`.
    have hg : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ μ (p.1 + 2 * p.2) := hμ.comp (by fun_prop)
    hg.contMDiff.contMDiffAt.comp _ (((contMDiff_norm_fst_sq i).contMDiffAt.comp _ hΨ').prodMk_space
      ((contMDiff_norm_snd_sq i).contMDiffAt.comp _ hΨ'))
  exact hterm.congr_of_eventuallyEq
    (eventuallyEq_of_mem ((Ψ i).open_source.mem_nhds hs) fun y hy ↦ indicator_of_mem hy _)

/-- Milnor's function has no critical points in the band `F⁻¹[c - ε, c + ε]`, provided the
critical points of `f` in the band `f⁻¹[c - ε, c + ε]` lie in the sources of the normal forms. -/
private theorem mfderiv_milnorBottFunction_ne_zero_of_mem_Icc
    (hε : 0 < ε) (hfs : ContMDiff I 𝓘(ℝ) ∞ f) (hμ : ContDiff ℝ ∞ μ) (hμa : Antitone μ)
    (hμ_nonneg : ∀ r, 0 ≤ μ r) (hμ_eq : ∀ r ≤ ε, μ r = 2 * ε)
    (hcrit : criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ ⋃ i, (Ψ i).source)
    (h₁ : c - ε ≤ milnorBottFunction Ψ f μ x) (h₂ : milnorBottFunction Ψ f μ x ≤ c + ε) :
    mfderiv I 𝓘(ℝ) (milnorBottFunction Ψ f μ) x ≠ 0 := by
  by_cases hxs : ∃ i, x ∈ (Ψ i).source
  · obtain ⟨i, hi⟩ := hxs
    exact mfderiv_milnorBottFunction_ne_zero hΨ hf hε hμ hμa hμ_nonneg hμ_eq
      ((contMDiff_milnorBottFunction hμ₀ hdisc hfs hμ).mdifferentiableAt (by simp)) hi h₁
  · replace hxs := not_exists.1 hxs
    have hK : x ∉ ⋃ i, (Ψ i).toOpenPartialHomeomorph.symm ''
        {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} := by
      intro h
      obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.1 h
      exact hxs i ((Ψ i).toOpenPartialHomeomorph.map_target (hdisc i hz))
    have hfx := milnorBottFunction_of_forall_notMem (f := f) (μ := μ) hxs
    rw [(milnorBottFunction_eventuallyEq hμ₀ hdisc hK).mfderiv_eq]
    intro h0
    obtain ⟨i, hi⟩ := mem_iUnion.1
      (hcrit ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 h0, hfx ▸ h₁, hfx ▸ h₂⟩)
    exact hxs i hi

end MilnorFunction

section Attachment

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [∀ i b, InnerProductSpace ℝ (Eᵤ i b)] [∀ i b, InnerProductSpace ℝ (Eₛ i b)]
  [∀ i, VectorBundle ℝ (Fᵤ i) (Eᵤ i)] [∀ i, VectorBundle ℝ (Fₛ i) (Eₛ i)]
  [∀ i, IsContMDiffRiemannianBundle (IB i) ∞ (Fᵤ i) (Eᵤ i)]
  [∀ i, IsContMDiffRiemannianBundle (IB i) ∞ (Fₛ i) (Eₛ i)]
  [∀ i, CompactSpace (B i)] [∀ i, T2Space (B i)]
  [∀ i, FiniteDimensional ℝ (Fᵤ i)] [∀ i, FiniteDimensional ℝ (Fₛ i)]

/-- **Attaching negative disc bundles across a Morse–Bott critical level** (Bott; Milnor's
Theorem 3.2 run fibrewise). Let `f` be smooth, and let `Ψ i` be partial diffeomorphisms from
open subsets of `M`, with pairwise disjoint sources, onto open subsets of the total spaces of
Whitney sums `Eᵤ i ×ᵇ Eₛ i` of smooth vector bundles with smooth fibre metrics and
finite-dimensional fibres over compact Hausdorff bases, in which
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
    (hΨ : Pairwise (Disjoint on fun i ↦ (Ψ i).source)) (hε : 0 < ε)
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
  have := Fintype.ofFinite ι
  have (i : ι) := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (HB := HB i)
    (IB := IB i) (n := ∞) (F := Fᵤ i) (V := Eᵤ i)
  have (i : ι) := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (HB := HB i)
    (IB := IB i) (n := ∞) (F := Fₛ i) (V := Eₛ i)
  -- Milnor's cutoff, equal to `2ε` on `(-∞, ε]` and to `0` on `[2ε, ∞)`.
  obtain ⟨μ, hμ, hμa, hμ_nonneg, hμ₀, hμ_eq, -⟩ :=
    exists_contDiff_antitone_cutoff (by linarith : ε < 2 * ε) (by positivity : 0 ≤ 2 * ε)
  set F := milnorBottFunction Ψ f μ
  set S := {x | f x ≤ c - ε} ∪ ⋃ i, (Ψ i).source ∩ Ψ i ⁻¹' {z | ‖z.2.1‖ ^ 2 ≤ ε ∧ z.2.2 = 0}
  have hFs : ContMDiff I 𝓘(ℝ) ∞ F := contMDiff_milnorBottFunction hμ₀ hdisc hfs hμ
  have hX : {x | F x ≤ c + ε} = {x | f x ≤ c + ε} :=
    setOf_milnorBottFunction_le hΨ hf hμ₀ hμ_nonneg
  have hSY : S ⊆ {x | F x ≤ c - ε} :=
    union_subset (fun x hx ↦ (milnorBottFunction_le hμ_nonneg x).trans hx) <| iUnion_subset
      fun i x ⟨hxi, hxε, hxv⟩ ↦ milnorBottFunction_le_of_mem_disc hΨ hf hμ_eq hxi hxε hxv
  have hab : c - ε ≤ c + ε := by linarith
  have hYX : {x | F x ≤ c - ε} ⊆ {x | F x ≤ c + ε} := fun _ hx ↦ le_trans hx hab
  have hFcompact : IsCompact (F ⁻¹' Icc (c - ε) (c + ε)) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hFs.continuous) fun x hx ↦
      ⟨hx.1.trans (milnorBottFunction_le hμ_nonneg x), (Set.ext_iff.1 hX x).1 hx.2⟩
  -- In a normal form, the model set of Milnor's retraction is the part of `S` in the source.
  have hQ (i : ι) {x : M} (hx : x ∈ (Ψ i).source) :
      Ψ i x ∈ bundleQuadraticSublevelUnionCell (Fᵤ i) (Fₛ i) (Eᵤ i) (Eₛ i) ε ↔
        f x ≤ c - ε ∨ x ∈ (Ψ i).source ∩ Ψ i ⁻¹' {z | ‖z.2.1‖ ^ 2 ≤ ε ∧ z.2.2 = 0} := by
    rw [mem_bundleQuadraticSublevelUnionCell, hf i x hx]
    exact or_congr ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩ (by simp [hx])
  have hS (x : M) (hxX : x ∈ {x | F x ≤ c - ε}) :
      x ∈ S ↔ ∀ i, x ∈ (Ψ i).toOpenPartialHomeomorph.source →
        (Ψ i).toOpenPartialHomeomorph x ∈
          bundleQuadraticSublevelUnionCell (Fᵤ i) (Fₛ i) (Eᵤ i) (Eₛ i) ε := by
    refine ⟨fun hxS i hi ↦ (hQ i hi).2 ?_, fun h ↦ ?_⟩
    · rcases hxS with h | h
      · exact .inl h
      · obtain ⟨j, hj⟩ := mem_iUnion.1 h
        obtain rfl : j = i := hΨ.eq (not_disjoint_iff.2 ⟨x, hj.1, hi⟩)
        exact .inr hj
    · by_cases hx : ∃ i, x ∈ (Ψ i).source
      · obtain ⟨i, hi⟩ := hx
        rcases (hQ i hi).1 (h i hi) with h' | h'
        · exact .inl h'
        · exact .inr (mem_iUnion.2 ⟨i, h'⟩)
      · have hxX' : F x ≤ c - ε := hxX
        rw [show F x = f x from milnorBottFunction_of_forall_notMem (not_exists.1 hx)] at hxX'
        exact .inl hxX'
  -- Points of `{F ≤ c - ε}` moved by Milnor's retraction lie in the tubes, where the retraction
  -- only shrinks the second component.
  have hXmove (i : ι) (x : M)
      (hx : x ∈ {x | F x ≤ c - ε} ∩ (Ψ i).toOpenPartialHomeomorph.source)
      (hxQ : (Ψ i).toOpenPartialHomeomorph x ∉
        bundleQuadraticSublevelUnionCell (Fᵤ i) (Fₛ i) (Eᵤ i) (Eₛ i) ε) (t : unitInterval) :
      bundleQuadraticHandleDeformation (TauCeti.continuous_norm_bundle (Fᵤ i) (Eᵤ i))
          (TauCeti.continuous_norm_bundle (Fₛ i) (Eₛ i)) ε
          (t, (Ψ i).toOpenPartialHomeomorph x) ∈ {z | ‖z.2.1‖ ^ 2 + ‖z.2.2‖ ^ 2 ≤ 2 * ε} ∧
        (Ψ i).toOpenPartialHomeomorph.symm (bundleQuadraticHandleDeformation
          (TauCeti.continuous_norm_bundle (Fᵤ i) (Eᵤ i))
          (TauCeti.continuous_norm_bundle (Fₛ i) (Eₛ i)) ε
          (t, (Ψ i).toOpenPartialHomeomorph x)) ∈ {x | F x ≤ c - ε} := by
    obtain ⟨hxX, hx⟩ := hx
    have hxε : ‖(Ψ i x).2.1‖ ^ 2 + ‖(Ψ i x).2.2‖ ^ 2 ≤ 2 * ε := by
      by_contra hlt
      refine hxQ ((hQ i hx).2 (.inl ?_))
      have hxX' : F x ≤ c - ε := hxX
      rwa [show F x = f x from milnorBottFunction_eq_of_lt hΨ hμ₀ hx (lt_of_not_ge hlt)] at hxX'
    obtain ⟨s, hs, hst⟩ := exists_quadraticHandleDeformation_apply_eq_smul ε t (Ψ i x).2
    have hG : bundleQuadraticHandleDeformation (TauCeti.continuous_norm_bundle (Fᵤ i) (Eᵤ i))
        (TauCeti.continuous_norm_bundle (Fₛ i) (Eₛ i)) ε (t, (Ψ i).toOpenPartialHomeomorph x) =
          fibreScale s (Ψ i x) := by
      rw [bundleQuadraticHandleDeformation_apply]
      exact congrArg (TotalSpace.mk (Ψ i x).proj) hst
    rw [hG]
    refine ⟨?_, (milnorBottFunction_symm_scale_le hΨ hf hμa (hdisc i) hx hxε hs).trans hxX⟩
    rw [mem_ofPred_eq, norm_fibreScale_snd_fst, norm_fibreScale_snd_snd, mul_pow, sq_abs]
    linarith [mul_le_of_le_one_left (sq_nonneg ‖(Ψ i x).2.2‖) (pow_le_one₀ (n := 2) hs.1 hs.2)]
  -- `{F ≤ c + ε}` retracts onto `{F ≤ c - ε}`, as `F` has no critical points in the compact band,
  -- which retracts onto `S`, as shrinking the second component of a normal form lowers `F`.
  exact hX ▸ ContinuousMap.HomotopicRel.exists_inter_deformation_trans hYX
    (inter_subset_right.trans hSY)
    (sublevelInclusion_eq_inclusion F hab ▸ exists_sublevelDeformation hFs hab hFcompact fun _ ↦
      mfderiv_milnorBottFunction_ne_zero_of_mem_Icc hΨ hf hμ₀ hdisc hε hfs hμ hμa hμ_nonneg
        hμ_eq hcrit)
    (exists_inter_deformation_of_charts (φ := fun i ↦ (Ψ i).toOpenPartialHomeomorph)
      (G := fun i ↦ bundleQuadraticHandleDeformation
        (TauCeti.continuous_norm_bundle (Fᵤ i) (Eᵤ i))
        (TauCeti.continuous_norm_bundle (Fₛ i) (Eₛ i)) ε)
      hΨ hdisc hXmove (fun i ↦ isCompact_tube i (2 * ε))
      (fun i ↦ bundleQuadraticHandleRetraction_mem _ _) hS)

end Attachment

end TauCeti
