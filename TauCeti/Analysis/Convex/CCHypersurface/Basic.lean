/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.MetricSpace.Lipschitz
public import TauCeti.Analysis.Convex.Subdifferential

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Convex.SubgradientImage
import TauCeti.Analysis.InnerProductSpace.LinearIsometry
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Delta-convex (`c - c`) hypersurfaces and Zajíček's theorem

In a real inner product space `E`, a *`c - c` hypersurface* (or *delta-convex hypersurface*) is the
graph over `(ℝ ∙ e)ᗮ` (for unit `e`) of `f - g` for continuous convex `f, g : ↥(ℝ ∙ e)ᗮ → ℝ`; a
*Lipschitz hypersurface* is the graph of a globally Lipschitz function. Both classes are closed,
Borel measurable, and invariant under translations and continuous linear equivalences. In finite
dimension, every `c - c` hypersurface is covered by countably many Lipschitz hypersurfaces and is
additive-Haar null, and Zajíček's theorem characterizes subsets of convex nondifferentiability loci
as sets covered by countably many `c - c` hypersurfaces.

## Main declarations

* `TauCeti.IsCCHypersurface`, `TauCeti.IsLipschitzHypersurface` — `c - c` and Lipschitz
  hypersurfaces, with parametric (`*_iff_exists_eq_range`), orthonormal coordinate
  (`*_iff_exists_linearIsometryEquiv`), and 1D (`*_iff_exists_eq_singleton`) characterizations.
* `TauCeti.isCCHypersurface_vadd_iff`, `TauCeti.isCCHypersurface_image_continuousLinearEquiv_iff`,
  `TauCeti.isLipschitzHypersurface_vadd_iff`,
  `TauCeti.isLipschitzHypersurface_image_continuousLinearEquiv_iff` — affine invariance.
* `TauCeti.IsCCHypersurface.exists_subset_iUnion_isLipschitzHypersurface`,
  `TauCeti.IsLipschitzHypersurface.addHaar_eq_zero`, `TauCeti.IsCCHypersurface.addHaar_eq_zero` —
  countable Lipschitz covering and additive-Haar nullity.
* `TauCeti.exists_countable_isCCHypersurface_cover_not_subsingleton_subdifferential`,
  `TauCeti.exists_countable_isCCHypersurface_cover_mem_interior_not_differentiableAt_toReal`,
  `Convex.exists_countable_isCCHypersurface_cover_frontier` — countable `c - c` coverings.
* `TauCeti.IsCCHypersurface.exists_convexOn_lipschitzWith_add_sub_two_mul_eq`,
  `TauCeti.IsCCHypersurface.exists_convexOn_lipschitzWith_measurable_forall_add_inner_le_ne`,
  `TauCeti.exists_convexOn_subset_not_differentiableAt_iff`,
  `TauCeti.exists_convexOn_subset_not_differentiableAt_iff_nat` — Zajíček's theorem.

## References

* L. Zajíček, *On the differentiation of convex functions in finite and infinite dimensional
  spaces*, Czechoslovak Math. J. 29 (1979), 340–348.
* L. Ambrosio and N. Gigli, *A user's guide to optimal transport*, LNM 2062, Springer, 2013,
  Definition 1.23 and Theorem 1.24.
-/

public section

noncomputable section

open Set Filter MeasureTheory Metric Submodule
open scoped NNReal Topology Pointwise

namespace TauCeti

section Defs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A subset `s` of a real inner product space `E` is a *`c - c` hypersurface* (or *delta-convex
hypersurface*) if there exist a unit vector `e : E` and continuous convex `f, g : ↥(ℝ ∙ e)ᗮ → ℝ`
with `s = {x | ⟪x, e⟫ = f (P x) - g (P x)}`, where `P` projects orthogonally onto `(ℝ ∙ e)ᗮ`. -/
def IsCCHypersurface (s : Set E) : Prop :=
  ∃ (e : E) (_ : ‖e‖ = 1) (f g : ↥(ℝ ∙ e)ᗮ → ℝ),
    Continuous f ∧ Continuous g ∧ ConvexOn ℝ univ f ∧ ConvexOn ℝ univ g ∧
    s = {x : E | inner ℝ x e =
      f ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) - g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)}

/-- Unfolding characterization of `IsCCHypersurface`. -/
theorem isCCHypersurface_def {s : Set E} :
    IsCCHypersurface s ↔
      ∃ (e : E) (_ : ‖e‖ = 1) (f g : ↥(ℝ ∙ e)ᗮ → ℝ),
        Continuous f ∧ Continuous g ∧ ConvexOn ℝ univ f ∧ ConvexOn ℝ univ g ∧
        s = {x : E | inner ℝ x e =
          f ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) - g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} :=
  Iff.rfl

/-- A subset `s` of a real inner product space `E` is a *Lipschitz hypersurface* if there exist a
unit vector `e : E`, `K : ℝ≥0`, and a `K`-Lipschitz `h : ↥(ℝ ∙ e)ᗮ → ℝ` such that
`s = {x | ⟪x, e⟫ = h (P x)}`, where `P` projects orthogonally onto `(ℝ ∙ e)ᗮ`. -/
def IsLipschitzHypersurface (s : Set E) : Prop :=
  ∃ (e : E) (_ : ‖e‖ = 1) (K : ℝ≥0) (h : ↥(ℝ ∙ e)ᗮ → ℝ),
    LipschitzWith K h ∧ s = {x : E | inner ℝ x e = h ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)}

/-- Unfolding characterization of `IsLipschitzHypersurface`. -/
theorem isLipschitzHypersurface_def {s : Set E} :
    IsLipschitzHypersurface s ↔
      ∃ (e : E) (_ : ‖e‖ = 1) (K : ℝ≥0) (h : ↥(ℝ ∙ e)ᗮ → ℝ),
        LipschitzWith K h ∧ s = {x : E | inner ℝ x e = h ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} :=
  Iff.rfl

/-- Parametric graph characterization of `IsCCHypersurface`. -/
theorem isCCHypersurface_iff_exists_eq_range {s : Set E} :
    IsCCHypersurface s ↔
      ∃ (e : E) (_ : ‖e‖ = 1) (f g : ↥(ℝ ∙ e)ᗮ → ℝ),
        Continuous f ∧ Continuous g ∧ ConvexOn ℝ univ f ∧ ConvexOn ℝ univ g ∧
        s = range fun y : ↥(ℝ ∙ e)ᗮ => (y : E) + (f y - g y) • e :=
  exists_congr fun e => exists_congr fun he => exists_congr fun f => exists_congr fun g => by
    simp_rw [real_inner_comm e _, setOf_inner_eq_eq_range he (fun y => f y - g y)]

/-- Parametric graph characterization of `IsLipschitzHypersurface`. -/
theorem isLipschitzHypersurface_iff_exists_eq_range {s : Set E} :
    IsLipschitzHypersurface s ↔
      ∃ (e : E) (_ : ‖e‖ = 1) (K : ℝ≥0) (h : ↥(ℝ ∙ e)ᗮ → ℝ),
        LipschitzWith K h ∧ s = range fun y : ↥(ℝ ∙ e)ᗮ => (y : E) + h y • e :=
  exists_congr fun e => exists_congr fun he => by
    simp_rw [real_inner_comm e _, setOf_inner_eq_eq_range he]

/-- A trivial (zero-dimensional) space contains no `c - c` hypersurface. -/
theorem not_isCCHypersurface_of_subsingleton [Subsingleton E] (s : Set E) : ¬ IsCCHypersurface s :=
  fun ⟨e, he, _⟩ => by simp [Subsingleton.elim e 0] at he

/-- A trivial (zero-dimensional) space contains no Lipschitz hypersurface. -/
theorem not_isLipschitzHypersurface_of_subsingleton [Subsingleton E] (s : Set E) :
    ¬ IsLipschitzHypersurface s := fun ⟨e, he, _⟩ => by simp [Subsingleton.elim e 0] at he

/-- Every `c - c` hypersurface is nonempty. -/
theorem IsCCHypersurface.nonempty {s : Set E} (hs : IsCCHypersurface s) : s.Nonempty :=
  let ⟨_, _, _, _, _, _, _, _, h⟩ := isCCHypersurface_iff_exists_eq_range.1 hs; h ▸ range_nonempty _

/-- The empty set is not a `c - c` hypersurface. -/
@[simp]
theorem not_isCCHypersurface_empty : ¬ IsCCHypersurface (∅ : Set E) := (·.nonempty.ne_empty rfl)

/-- Every Lipschitz hypersurface is nonempty. -/
theorem IsLipschitzHypersurface.nonempty {s : Set E} (hs : IsLipschitzHypersurface s) :
    s.Nonempty :=
  let ⟨_, _, _, _, _, h⟩ := isLipschitzHypersurface_iff_exists_eq_range.1 hs; h ▸ range_nonempty _

/-- The empty set is not a Lipschitz hypersurface. -/
@[simp]
theorem not_isLipschitzHypersurface_empty : ¬ IsLipschitzHypersurface (∅ : Set E) :=
  (·.nonempty.ne_empty rfl)

/-- Every affine hyperplane `{x | ⟪x, e⟫ = c}` normal to unit `e` is a `c - c` hypersurface. -/
theorem isCCHypersurface_setOf_inner_eq {e : E} (he : ‖e‖ = 1) (c : ℝ) :
    IsCCHypersurface {x : E | inner ℝ x e = c} :=
  ⟨e, he, fun _ => c, fun _ => 0, continuous_const, continuous_const,
    convexOn_const c convex_univ, convexOn_const 0 convex_univ, by simp⟩

/-- Every affine hyperplane `{x | ⟪x, e⟫ = c}` normal to unit `e` is a Lipschitz hypersurface. -/
theorem isLipschitzHypersurface_setOf_inner_eq {e : E} (he : ‖e‖ = 1) (c : ℝ) :
    IsLipschitzHypersurface {x : E | inner ℝ x e = c} :=
  ⟨e, he, 0, fun _ => c, LipschitzWith.const c, by simp⟩

/-- Every `c - c` hypersurface is closed. -/
theorem IsCCHypersurface.isClosed {s : Set E} (hs : IsCCHypersurface s) : IsClosed s :=
  let ⟨_, _, _, _, hfc, hgc, _, _, hs'⟩ := hs; hs' ▸ isClosed_eq (by fun_prop) (by fun_prop)

/-- Every `c - c` hypersurface is Borel measurable. -/
theorem IsCCHypersurface.measurableSet [MeasurableSpace E] [OpensMeasurableSpace E] {s : Set E}
    (hs : IsCCHypersurface s) : MeasurableSet s := hs.isClosed.measurableSet

/-- Every Lipschitz hypersurface is closed. -/
theorem IsLipschitzHypersurface.isClosed {s : Set E} (hs : IsLipschitzHypersurface s) :
    IsClosed s :=
  let ⟨_, _, _, _, hh, h⟩ := hs; h ▸ isClosed_eq (by fun_prop) (hh.continuous.comp (by fun_prop))

/-- Every Lipschitz hypersurface is Borel measurable. -/
theorem IsLipschitzHypersurface.measurableSet [MeasurableSpace E] [OpensMeasurableSpace E]
    {s : Set E} (hs : IsLipschitzHypersurface s) : MeasurableSet s := hs.isClosed.measurableSet

/-- Translates of `c - c` hypersurfaces are `c - c` hypersurfaces. -/
theorem IsCCHypersurface.vadd {s : Set E} (hs : IsCCHypersurface s) (v : E) :
    IsCCHypersurface (v +ᵥ s) := by
  obtain ⟨e, he, f, g, hfc, hgc, hf, hg, rfl⟩ := hs; let v₀ := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto v
  have hsub {w : ↥(ℝ ∙ e)ᗮ → ℝ} (hw : ConvexOn ℝ univ w) : ConvexOn ℝ univ (w ∘ (· - v₀)) := by
    simpa [Function.comp_def, sub_eq_add_neg] using hw.translate_left (-v₀)
  exact ⟨e, he, fun y => f (y - v₀) + inner ℝ v e, fun y => g (y - v₀), by fun_prop, by fun_prop,
    (hsub hf).add_const _, hsub hg,
    by simpa [v₀, real_inner_comm e, sub_add_eq_add_sub] using
      vadd_setOf_inner_eq (𝕜 := ℝ) e v (fun y => f y - g y)⟩

/-- A translate `v +ᵥ s` is a `c - c` hypersurface if and only if `s` is. -/
@[simp]
theorem isCCHypersurface_vadd_iff {s : Set E} {v : E} :
    IsCCHypersurface (v +ᵥ s) ↔ IsCCHypersurface s :=
  ⟨fun h => by simpa using h.vadd (-v), fun h => h.vadd v⟩

/-- Translates of Lipschitz hypersurfaces are Lipschitz hypersurfaces. -/
theorem IsLipschitzHypersurface.vadd {s : Set E} (hs : IsLipschitzHypersurface s) (v : E) :
    IsLipschitzHypersurface (v +ᵥ s) :=
  let ⟨e, he, K, h, hh, hs'⟩ := hs; let v₀ := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto v
  hs' ▸ ⟨e, he, K, fun y => h (y - v₀) + inner ℝ v e,
    ((hh.comp (LipschitzWith.id.sub (.const v₀))).add (.const _)).weaken (by simp),
    by simpa [v₀, real_inner_comm e] using vadd_setOf_inner_eq (𝕜 := ℝ) e v h⟩

/-- A translate `v +ᵥ s` is a Lipschitz hypersurface if and only if `s` is. -/
@[simp]
theorem isLipschitzHypersurface_vadd_iff {s : Set E} {v : E} :
    IsLipschitzHypersurface (v +ᵥ s) ↔ IsLipschitzHypersurface s :=
  ⟨fun h => by simpa using h.vadd (-v), fun h => h.vadd v⟩

private theorem image_continuousLinearEquiv_setOf_inner_eq {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (L : E ≃L[ℝ] F) {e : E} (he : ‖e‖ = 1)
    (w : ↥(ℝ ∙ e)ᗮ → ℝ) :
    ∃ (e' : F) (_ : ‖e'‖ = 1) (c : ℝ) (_ : 0 < c)
      (B : ↥(ℝ ∙ e')ᗮ →L[ℝ] ↥(ℝ ∙ e)ᗮ) (ℓ : ↥(ℝ ∙ e')ᗮ →L[ℝ] ℝ),
      L '' {x : E | inner ℝ x e = w ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} =
        {z : F | inner ℝ z e' = c * w (B ((ℝ ∙ e')ᗮ.orthogonalProjectionOnto z)) -
          ℓ ((ℝ ∙ e')ᗮ.orthogonalProjectionOnto z)} := by
  let c := ‖L e‖; let e' : F := c⁻¹ • L e
  have hc : 0 < c := norm_pos_iff.2 ((map_ne_zero_iff L L.injective).2 fun h => by simp [h] at he)
  have he' : ‖e'‖ = 1 := by simp [e', c, norm_smul, inv_mul_cancel₀ hc.ne']
  let B : ↥(ℝ ∙ e')ᗮ →L[ℝ] ↥(ℝ ∙ e)ᗮ :=
    (ℝ ∙ e)ᗮ.orthogonalProjectionOnto.comp (L.symm.toContinuousLinearMap.comp (ℝ ∙ e')ᗮ.subtypeL)
  let ℓ : ↥(ℝ ∙ e')ᗮ →L[ℝ] ℝ :=
    c • ((innerSL ℝ e).comp (L.symm.toContinuousLinearMap.comp (ℝ ∙ e')ᗮ.subtypeL))
  refine ⟨e', he', c, hc, B, ℓ, Set.ext fun z => ?_⟩
  have hd := congrArg L.symm (real_inner_comm e' z ▸ orthogonalProjectionOnto_add_inner_smul he' z)
  simp only [map_add, map_smul, show L.symm e' = c⁻¹ • e by simp [e', map_smul], smul_smul] at hd
  have hproj : (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (L.symm z) =
      B ((ℝ ∙ e')ᗮ.orthogonalProjectionOnto z) := by
    simpa [B, map_add, map_smul, orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]
      using (congrArg (ℝ ∙ e)ᗮ.orthogonalProjectionOnto hd).symm
  have hi : c * inner ℝ (L.symm z) e = ℓ ((ℝ ∙ e')ᗮ.orthogonalProjectionOnto z) + inner ℝ z e' := by
    have h : inner ℝ (L.symm ((ℝ ∙ e')ᗮ.orthogonalProjectionOnto z)) e + inner ℝ z e' * c⁻¹ =
        inner ℝ (L.symm z) e := by
      simpa [inner_add_left, real_inner_smul_left, he] using congrArg (inner ℝ · e) hd
    rw [← h, mul_add]; simp [ℓ, real_inner_comm e]; field_simp [hc.ne']
  simp only [mem_image, mem_ofPred_eq]
  refine ⟨?_, fun hz => ⟨L.symm z, mul_left_cancel₀ hc.ne' (by rw [hproj]; linarith),
    L.apply_symm_apply z⟩⟩
  rintro ⟨x, hx, rfl⟩; rw [L.symm_apply_apply] at hproj hi
  have hmul := congrArg (c * ·) hx; rw [hproj] at hmul; linarith

/-- Continuous linear equivalences preserve `c - c` hypersurfaces. -/
theorem IsCCHypersurface.image_continuousLinearEquiv {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {s : Set E} (hs : IsCCHypersurface s) (L : E ≃L[ℝ] F) :
    IsCCHypersurface (L '' s) := by
  obtain ⟨e, he, f, g, hfc, hgc, hf, hg, rfl⟩ := hs
  obtain ⟨e', he', c, hc, B, ℓ, himg⟩ :=
    image_continuousLinearEquiv_setOf_inner_eq L he (fun y => f y - g y)
  exact ⟨e', he', fun y => c * f (B y), fun y => c * g (B y) + ℓ y, by fun_prop, by fun_prop,
    (hf.comp_linearMap B.toLinearMap).smul hc.le,
    ((hg.comp_linearMap B.toLinearMap).smul hc.le).add
      ⟨convex_univ, fun _ _ _ _ _ _ _ _ _ => by simp⟩, by simpa only [mul_sub, sub_sub] using himg⟩

/-- Images under continuous linear equivalences preserve `c - c` hypersurfaces. -/
@[simp]
theorem isCCHypersurface_image_continuousLinearEquiv_iff {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {s : Set E} (L : E ≃L[ℝ] F) :
    IsCCHypersurface (L '' s) ↔ IsCCHypersurface s :=
  ⟨fun h => by simpa [image_image] using h.image_continuousLinearEquiv L.symm,
    fun h => h.image_continuousLinearEquiv L⟩

/-- Linear isometric equivalences preserve `c - c` hypersurfaces. -/
theorem IsCCHypersurface.image_linearIsometryEquiv {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {s : Set E} (hs : IsCCHypersurface s) (L : E ≃ₗᵢ[ℝ] F) :
    IsCCHypersurface (L '' s) :=
  hs.image_continuousLinearEquiv L.toContinuousLinearEquiv

/-- Images under linear isometric equivalences preserve `c - c` hypersurfaces. -/
@[simp]
theorem isCCHypersurface_image_linearIsometryEquiv_iff {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {s : Set E} (L : E ≃ₗᵢ[ℝ] F) :
    IsCCHypersurface (L '' s) ↔ IsCCHypersurface s :=
  isCCHypersurface_image_continuousLinearEquiv_iff (s := s) L.toContinuousLinearEquiv

/-- Continuous linear equivalences preserve Lipschitz hypersurfaces. -/
theorem IsLipschitzHypersurface.image_continuousLinearEquiv {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {s : Set E} (hs : IsLipschitzHypersurface s) (L : E ≃L[ℝ] F) :
    IsLipschitzHypersurface (L '' s) := by
  obtain ⟨e, he, _, h, hh, rfl⟩ := hs
  obtain ⟨e', he', c, hc, B, ℓ, himg⟩ := image_continuousLinearEquiv_setOf_inner_eq L he h
  have hmul : LipschitzWith ⟨c, hc.le⟩ (c * ·) := LipschitzWith.of_dist_le_mul fun _ _ =>
    by rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hc, Real.dist_eq]; exact le_rfl
  exact ⟨e', he', _, _, (hmul.comp (hh.comp B.lipschitzWith)).sub ℓ.lipschitzWith, himg⟩

/-- Images under continuous linear equivalences preserve Lipschitz hypersurfaces. -/
@[simp]
theorem isLipschitzHypersurface_image_continuousLinearEquiv_iff {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {s : Set E} (L : E ≃L[ℝ] F) :
    IsLipschitzHypersurface (L '' s) ↔ IsLipschitzHypersurface s :=
  ⟨fun h => by simpa [image_image] using h.image_continuousLinearEquiv L.symm,
    fun h => h.image_continuousLinearEquiv L⟩

/-- Linear isometric equivalences preserve Lipschitz hypersurfaces. -/
theorem IsLipschitzHypersurface.image_linearIsometryEquiv {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {s : Set E} (hs : IsLipschitzHypersurface s) (L : E ≃ₗᵢ[ℝ] F) :
    IsLipschitzHypersurface (L '' s) :=
  hs.image_continuousLinearEquiv L.toContinuousLinearEquiv

/-- Images under linear isometric equivalences preserve Lipschitz hypersurfaces. -/
@[simp]
theorem isLipschitzHypersurface_image_linearIsometryEquiv_iff {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {s : Set E} (L : E ≃ₗᵢ[ℝ] F) :
    IsLipschitzHypersurface (L '' s) ↔ IsLipschitzHypersurface s :=
  isLipschitzHypersurface_image_continuousLinearEquiv_iff (s := s) L.toContinuousLinearEquiv

end Defs

section Coordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem exists_linearIsometryEquiv_of_unit [FiniteDimensional ℝ E] {e : E} (he : ‖e‖ = 1) :
    ∃ (Φ : E ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) × ℝ))
      (ψ : ↥(ℝ ∙ e)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))),
      (∀ x, (Φ x).fst = ψ ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)) ∧
      (∀ x, (Φ x).snd = inner ℝ x e) := by
  have hdim : Module.finrank ℝ ↥(ℝ ∙ e)ᗮ = Module.finrank ℝ E - 1 :=
    Submodule.finrank_orthogonal_span_singleton_eq_finrank_sub_one (fun h => by simp [h] at he)
  let ψ : ↥(ℝ ∙ e)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    (stdOrthonormalBasis ℝ ↥(ℝ ∙ e)ᗮ).repr.trans (.piLpCongrLeft 2 ℝ ℝ (finCongr hdim))
  let Φ := (orthogonalLineIsometry e he).symm.trans (ψ.withLpProdCongr 2 (.refl ℝ ℝ))
  have hΦ (x : E) :
      Φ x = WithLp.toLp 2 (ψ ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x), inner ℝ x e) := by
    simp [Φ, show (orthogonalLineIsometry e he).symm x =
        WithLp.toLp 2 ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x, inner ℝ x e) from
      (orthogonalLineIsometry e he).injective <| by
        rw [LinearIsometryEquiv.apply_symm_apply, orthogonalLineIsometry_apply,
          real_inner_comm e x, orthogonalProjectionOnto_add_inner_smul he]]
  exact ⟨Φ, ψ, fun x => by simp [hΦ x], fun x => by simp [hΦ x]⟩

private theorem exists_unit_of_linearIsometryEquiv
    (Φ : E ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) × ℝ)) :
    ∃ (e : E) (_ : ‖e‖ = 1)
      (ψ : ↥(ℝ ∙ e)ᗮ →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))),
      (∀ x, ψ ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) = (Φ x).fst) ∧
      (∀ x, inner ℝ x e = (Φ x).snd) := by
  let p₀ : WithLp 2 (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) × ℝ) := .toLp 2 (0, 1)
  let e : E := Φ.symm p₀
  have he : ‖e‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one,
      WithLp.prod_norm_sq_eq_of_L2]; simp [p₀]
  have hin (x : E) : inner ℝ x e = (Φ x).snd := by
    simpa [e, p₀, WithLp.prod_inner_apply] using (Φ.inner_map_map x e).symm
  let ψ : ↥(ℝ ∙ e)ᗮ →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    { toFun := fun y => (Φ (y : E)).fst, map_add' := by simp, map_smul' := by simp
      norm_map' := fun y => by
        rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_coe, ← Φ.norm_map (y : E),
          WithLp.prod_norm_sq_eq_of_L2, ← hin (y : E),
          Submodule.mem_orthogonal_singleton_iff_inner_left.mp y.property]; simp }
  refine ⟨e, he, ψ, fun x => ?_, hin⟩
  simpa [ψ, map_add, map_smul, show (Φ e).fst = 0 by simp [e, p₀]] using
    congrArg (fun z => (Φ z).fst) (orthogonalProjectionOnto_add_inner_smul (𝕜 := ℝ) he x)

/-- **Orthonormal coordinate characterization of `c - c` hypersurfaces.** In finite dimension `d`,
`s ⊆ E` is a `c - c` hypersurface iff in some orthonormal splitting `Φ : E ≃ₗᵢ[ℝ] ℝ^{d-1} ×₂ ℝ`
it is `{x | (Φ x).snd = f (Φ x).fst - g (Φ x).fst}` for convex `f, g` (both false when `d = 0`). -/
theorem isCCHypersurface_iff_exists_linearIsometryEquiv [FiniteDimensional ℝ E] {s : Set E} :
    IsCCHypersurface s ↔
      ∃ (Φ : E ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) × ℝ))
        (f g : EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) → ℝ),
        ConvexOn ℝ univ f ∧ ConvexOn ℝ univ g ∧
        s = {x : E | (Φ x).snd = f (Φ x).fst - g (Φ x).fst} := by
  refine ⟨fun ⟨e, he, f, g, _, _, hf, hg, hs⟩ => ?_, fun ⟨Φ, f, g, hf, hg, hs⟩ => ?_⟩
  · obtain ⟨Φ, ψ, hfst, hsnd⟩ := exists_linearIsometryEquiv_of_unit he
    exact ⟨Φ, f ∘ ψ.symm, g ∘ ψ.symm, hf.comp_linearMap ψ.symm.toLinearMap,
      hg.comp_linearMap ψ.symm.toLinearMap, by rw [hs]; ext x; simp [hfst, hsnd]⟩
  · obtain ⟨e, he, ψ, hfst, hsnd⟩ := exists_unit_of_linearIsometryEquiv Φ
    exact ⟨e, he, f ∘ ψ, g ∘ ψ,
      (continuousOn_univ.1 (hf.continuousOn isOpen_univ)).comp ψ.continuous,
      (continuousOn_univ.1 (hg.continuousOn isOpen_univ)).comp ψ.continuous,
      hf.comp_linearMap ψ.toLinearMap, hg.comp_linearMap ψ.toLinearMap,
      by rw [hs]; ext x; simp [hfst, hsnd]⟩

/-- **Orthonormal coordinate characterization of Lipschitz hypersurfaces.** In finite dimension `d`,
`s ⊆ E` is a Lipschitz hypersurface iff in some orthonormal splitting `Φ : E ≃ₗᵢ[ℝ] ℝ^{d-1} ×₂ ℝ`
it is `{x | (Φ x).snd = h (Φ x).fst}` for globally Lipschitz `h` (both false when `d = 0`). -/
theorem isLipschitzHypersurface_iff_exists_linearIsometryEquiv [FiniteDimensional ℝ E] {s : Set E} :
    IsLipschitzHypersurface s ↔
      ∃ (Φ : E ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) × ℝ))
        (K : ℝ≥0) (h : EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) → ℝ),
        LipschitzWith K h ∧ s = {x : E | (Φ x).snd = h (Φ x).fst} := by
  refine ⟨fun ⟨e, he, K, h, hh, hs⟩ => ?_, fun ⟨Φ, K, h, hh, hs⟩ => ?_⟩
  · obtain ⟨Φ, ψ, hfst, hsnd⟩ := exists_linearIsometryEquiv_of_unit he
    exact ⟨Φ, K, h ∘ ψ.symm, by simpa using hh.comp ψ.symm.lipschitzWith,
      by rw [hs]; ext x; simp [hfst, hsnd]⟩
  · obtain ⟨e, he, ψ, hfst, hsnd⟩ := exists_unit_of_linearIsometryEquiv Φ
    exact ⟨e, he, K, h ∘ ψ, by simpa using hh.comp ψ.lipschitzWith,
      by rw [hs]; ext x; simp [hfst, hsnd]⟩

private theorem range_eq_singleton_of_finrank_eq_one (hdim : Module.finrank ℝ E = 1) {e : E}
    (he : ‖e‖ = 1) (φ : ↥(ℝ ∙ e)ᗮ → ℝ) :
    (range fun y : ↥(ℝ ∙ e)ᗮ => (y : E) + φ y • e) = {φ 0 • e} := by
  have horth := Submodule.orthogonal_span_singleton_eq_bot_of_finrank_eq_one hdim (v := e)
    (fun h => by simp [h] at he)
  ext z; refine ⟨?_, by rintro rfl; exact ⟨0, by simp⟩⟩
  rintro ⟨y, rfl⟩; simp [show y = 0 from Subtype.ext ((Submodule.mem_bot ℝ).1 (horth ▸ y.property))]

private theorem exists_unit_singleton_eq_setOf_inner_eq (hdim : Module.finrank ℝ E = 1) (x : E) :
    ∃ (e : E) (_ : ‖e‖ = 1), {x} = {z : E | inner ℝ z e = inner ℝ x e} := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
  obtain ⟨e, he⟩ := exists_norm_eq E (zero_le_one (α := ℝ))
  have horth := Submodule.orthogonal_span_singleton_eq_bot_of_finrank_eq_one hdim (v := e)
    (fun h => by simp [h] at he)
  have hrep (w : E) : inner ℝ w e • e = w := by
    have h := orthogonalProjectionOnto_add_inner_smul (𝕜 := ℝ) he w
    have h0 := (Submodule.mem_bot ℝ).1 (show ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto w : E) ∈ ⊥ by
      rw [← horth]; exact Subtype.prop _)
    simpa only [h0, zero_add, real_inner_comm] using h
  exact ⟨e, he, Set.ext fun z => ⟨by rintro rfl; simp, fun h =>
    mem_singleton_iff.2 (by rw [← hrep z, ← hrep x, mem_ofPred_eq.mp h])⟩⟩

/-- **Dimension-one characterization of `c - c` hypersurfaces.** In a one-dimensional real inner
product space, the `c - c` hypersurfaces are precisely the singletons. -/
theorem isCCHypersurface_iff_exists_eq_singleton (hdim : Module.finrank ℝ E = 1) {s : Set E} :
    IsCCHypersurface s ↔ ∃ x : E, s = {x} :=
  ⟨fun hs => let ⟨_, he, f, g, _, _, _, _, h⟩ := isCCHypersurface_iff_exists_eq_range.1 hs
    ⟨_, h.trans (range_eq_singleton_of_finrank_eq_one hdim he (fun y => f y - g y))⟩,
   fun ⟨x, hx⟩ => let ⟨_, he, heq⟩ := exists_unit_singleton_eq_setOf_inner_eq hdim x
    hx ▸ heq ▸ isCCHypersurface_setOf_inner_eq he _⟩

/-- **Dimension-one characterization of Lipschitz hypersurfaces.** In a one-dimensional real inner
product space, the Lipschitz hypersurfaces are precisely the singletons. -/
theorem isLipschitzHypersurface_iff_exists_eq_singleton (hdim : Module.finrank ℝ E = 1)
    {s : Set E} : IsLipschitzHypersurface s ↔ ∃ x : E, s = {x} :=
  ⟨fun hs => let ⟨_, he, _, h, _, hs'⟩ := isLipschitzHypersurface_iff_exists_eq_range.1 hs
    ⟨_, hs'.trans (range_eq_singleton_of_finrank_eq_one hdim he h)⟩,
   fun ⟨x, hx⟩ => let ⟨_, he, heq⟩ := exists_unit_singleton_eq_setOf_inner_eq hdim x
    hx ▸ heq ▸ isLipschitzHypersurface_setOf_inner_eq he _⟩

end Coordinates

section MeasureAndLipschitz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Every `c - c` hypersurface in a finite-dimensional real inner product space is covered by
countably many Lipschitz hypersurfaces. -/
theorem IsCCHypersurface.exists_subset_iUnion_isLipschitzHypersurface {s : Set E}
    (hs : IsCCHypersurface s) :
    ∃ t : ℕ → Set E, (∀ n, IsLipschitzHypersurface (t n)) ∧ s ⊆ ⋃ n, t n := by
  obtain ⟨e, he, f, g, -, -, hf, hg, rfl⟩ := hs; let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  choose Kf f' _ hLf hff' using fun n : ℕ =>
    hf.exists_convexOn_lipschitzWith_eqOn isOpen_univ (isCompact_closedBall 0 n) (subset_univ _)
  choose Kg g' _ hLg hgg' using fun n : ℕ =>
    hg.exists_convexOn_lipschitzWith_eqOn isOpen_univ (isCompact_closedBall 0 n) (subset_univ _)
  refine ⟨fun n => {x | inner ℝ x e = (f' n - g' n) (P x)},
    fun n => ⟨e, he, Kf n + Kg n, f' n - g' n, (hLf n).sub (hLg n), rfl⟩, fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_ge ‖P x‖
  have hmem : P x ∈ closedBall (0 : ↥(ℝ ∙ e)ᗮ) n := mem_closedBall_zero_iff.2 hn
  exact mem_iUnion.2 ⟨n, by simpa [← hff' n hmem, ← hgg' n hmem] using hx⟩

/-- Every Lipschitz hypersurface has measure zero for any additive Haar measure on `E`. -/
theorem IsLipschitzHypersurface.addHaar_eq_zero [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {s : Set E} (hs : IsLipschitzHypersurface s) :
    μ s = 0 := by
  have hmeas := hs.measurableSet; rcases hs with ⟨e, he, _, h, _, rfl⟩
  refine Measure.addHaar_eq_zero_of_prod_mk_preimage_image_eq_zero μ volume volume
    (orthogonalLineEquiv e he).symm hmeas
    (Eventually.of_forall fun y => measure_mono_null (t := {h y}) ?_ (by simp))
  rintro r ⟨x, hx, hφx⟩
  have hx_eq : x = (y : E) + r • e := by
    simpa [orthogonalLineEquiv_apply] using
      (ContinuousLinearEquiv.symm_apply_eq (orthogonalLineEquiv e he)).1 hφx
  rw [mem_ofPred_eq, hx_eq, orthogonalProjectionOnto_coe_add_smul,
    real_inner_comm e _, inner_add_smul e he] at hx; exact mem_singleton_iff.2 hx

/-- Every `c - c` hypersurface has measure zero for any additive Haar measure on `E`. -/
theorem IsCCHypersurface.addHaar_eq_zero [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {s : Set E} (hs : IsCCHypersurface s) :
    μ s = 0 :=
  let ⟨_, ht, hsub⟩ := hs.exists_subset_iUnion_isLipschitzHypersurface
  measure_mono_null hsub (measure_iUnion_null fun n => (ht n).addHaar_eq_zero μ)

end MeasureAndLipschitz

section SubdifferentialSeparation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem exists_mem_subdifferential_inner_eq {u : E → EReal} {x e p q : E} {c M : ℝ}
    (hp : p ∈ subdifferential (innerₗ E) u x) (hq : q ∈ subdifferential (innerₗ E) u x)
    (hpM : ‖p‖ ≤ M) (hqM : ‖q‖ ≤ M) (hpc : inner ℝ p e ≤ c) (hcq : c ≤ inner ℝ q e) :
    ∃ α ∈ subdifferential (innerₗ E) u x, ‖α‖ ≤ M ∧ inner ℝ α e = c := by
  rcases eq_or_lt_of_le (hpc.trans hcq) with hpeq | hplt
  · exact ⟨p, hp, hpM, le_antisymm hpc (hpeq ▸ hcq)⟩
  set θ := (c - inner ℝ p e) / (inner ℝ q e - inner ℝ p e)
  have hden : 0 < inner ℝ q e - inner ℝ p e := sub_pos.2 hplt
  have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.2 hpc) hden.le
  have h1θ : 0 ≤ 1 - θ := sub_nonneg.2 ((div_le_one hden).2 (by linarith))
  refine ⟨(1 - θ) • p + θ • q, convex_subdifferential (innerₗ E) u x hp hq h1θ hθ0 (by ring),
    ?_, by simp only [inner_add_left, real_inner_smul_left, θ]; field_simp [hden.ne']; ring⟩
  exact ((norm_add_le _ _).trans_eq (by rw [norm_smul, norm_smul, Real.norm_of_nonneg h1θ,
    Real.norm_of_nonneg hθ0])).trans (by nlinarith)

private theorem exists_convexOn_eq_toReal_sub_mul_inner {u : E → EReal} {e : E} (he : ‖e‖ = 1)
    {M : ℝ} (c : ℝ) {S : Set E} (hS : S.Nonempty) (α : S → E)
    (hα : ∀ x : S, α x ∈ subdifferential (innerₗ E) u x ∧ ‖α x‖ ≤ M ∧ inner ℝ (α x) e = c) :
    ∃ F : ↥(ℝ ∙ e)ᗮ → ℝ, Continuous F ∧ ConvexOn ℝ univ F ∧
      ∀ x : S, F ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) = (u x).toReal - c * inner ℝ (x : E) e := by
  obtain ⟨x₀, hx₀S⟩ := hS; have : Nonempty S := ⟨⟨x₀, hx₀S⟩⟩
  have hM : 0 ≤ M := (norm_nonneg _).trans (hα ⟨x₀, hx₀S⟩).2.1
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  obtain ⟨F, hconv, hlip, hF⟩ := exists_convexOn_lipschitzWith_apply_eq
    (x := fun x : S => P x) (p := fun x : S => P (α x))
    (a := fun x : S => (u x).toReal - c * inner ℝ (x : E) e) (L := ⟨M, hM⟩)
    (fun x => (norm_orthogonalProjectionOnto_apply_le _ _).trans (hα x).2.1) fun x₁ x₂ => by
      have hsubg : (u x₁).toReal + inner ℝ ((x₂ : E) - x₁) (α x₁) ≤ (u x₂).toReal := by
        simpa only [innerₗ_apply_apply] using toReal_add_le_toReal_of_mem_subdifferential
          (innerₗ E) (hα x₁).1 (ne_top_of_mem_subdifferential (innerₗ E) (hα x₂).1)
      have hdec : inner ℝ ((x₂ : E) - x₁) (α x₁) =
          inner ℝ (P x₂ - P x₁) (P (α x₁)) + c * inner ℝ ((x₂ : E) - x₁) e := by
        have hαeq := orthogonalProjectionOnto_add_inner_smul (𝕜 := ℝ) he (α x₁)
        rw [real_inner_comm, (hα x₁).2.2] at hαeq; nth_rw 1 [← hαeq]
        rw [inner_add_right, real_inner_smul_right,
          ← inner_orthogonalProjectionOnto_eq_of_mem_right, map_sub]
      simp only [inner_sub_left] at hdec hsubg ⊢; linarith
  exact ⟨F, hlip.continuous, hconv, hF⟩

/-- **Single-slice subdifferential separation lies in a `c - c` hypersurface.** In any real inner
product space `E`, for any `u : E → EReal`, unit vector `e`, `a < b`, and `M : ℝ`, the set of
points `x` admitting subgradients `p, q ∈ ∂u(x)` of norm at most `M` with `⟪p, e⟫ ≤ a` and
`b ≤ ⟪q, e⟫` is contained in a single `c - c` hypersurface. -/
theorem exists_isCCHypersurface_of_subdifferential_separation {u : E → EReal} {e : E}
    (he : ‖e‖ = 1) {a b : ℝ} (hab : a < b) (M : ℝ) :
    ∃ s : Set E, IsCCHypersurface s ∧
      {x : E | ∃ p ∈ subdifferential (innerₗ E) u x, ∃ q ∈ subdifferential (innerₗ E) u x,
          ‖p‖ ≤ M ∧ ‖q‖ ≤ M ∧ inner ℝ p e ≤ a ∧ b ≤ inner ℝ q e} ⊆ s := by
  set S := {x : E | ∃ p ∈ subdifferential (innerₗ E) u x, ∃ q ∈ subdifferential (innerₗ E) u x,
      ‖p‖ ≤ M ∧ ‖q‖ ≤ M ∧ inner ℝ p e ≤ a ∧ b ≤ inner ℝ q e}
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · exact ⟨{x | inner ℝ x e = 0}, isCCHypersurface_setOf_inner_eq he 0, hS0 ▸ empty_subset _⟩
  choose α hα using fun x : S => let ⟨_, hp, _, hq, hpM, hqM, hpa, hbq⟩ := x.property
    exists_mem_subdifferential_inner_eq hp hq hpM hqM hpa (hab.le.trans hbq)
  choose β hβ using fun x : S => let ⟨_, hp, _, hq, hpM, hqM, hpa, hbq⟩ := x.property
    exists_mem_subdifferential_inner_eq hp hq hpM hqM (hpa.trans hab.le) hbq
  obtain ⟨Fa, hFa_cont, hFa_conv, hFa⟩ := exists_convexOn_eq_toReal_sub_mul_inner he a hSne α hα
  obtain ⟨Fb, hFb_cont, hFb_conv, hFb⟩ := exists_convexOn_eq_toReal_sub_mul_inner he b hSne β hβ
  have hba : 0 < b - a := sub_pos.2 hab
  refine ⟨_, ⟨e, he, (b - a)⁻¹ • Fa, (b - a)⁻¹ • Fb, hFa_cont.const_smul _, hFb_cont.const_smul _,
    hFa_conv.smul (inv_nonneg.2 hba.le), hFb_conv.smul (inv_nonneg.2 hba.le), rfl⟩, fun x hx => ?_⟩
  simp only [mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, hFa ⟨x, hx⟩, hFb ⟨x, hx⟩]
  field_simp [hba.ne']; ring

/-- **Subdifferential singular locus is covered by countably many `c - c` hypersurfaces.** For any
extended-real function `u : E → EReal` on a separable real inner product space, the set of points
`x` at which `∂u(x)` has more than one element is covered by a countable family of `c - c`
hypersurfaces. -/
theorem exists_countable_isCCHypersurface_cover_not_subsingleton_subdifferential
    [TopologicalSpace.SeparableSpace E] (u : E → EReal) :
    ∃ C : Set (Set E), C.Countable ∧ (∀ s ∈ C, IsCCHypersurface s) ∧
      {x : E | ¬ (subdifferential (innerₗ E) u x).Subsingleton} ⊆ ⋃₀ C := by
  obtain ⟨D, hD_count, hD_dense⟩ := TopologicalSpace.exists_countable_dense E
  have : Countable {d : E // d ∈ D ∧ d ≠ 0} :=
    (hD_count.mono (show {d : E | d ∈ D ∧ d ≠ 0} ⊆ D from fun _ h => h.1)).to_subtype
  let I := {t : {d : E // d ∈ D ∧ d ≠ 0} × ℚ × ℚ × ℕ | t.2.1 < t.2.2.1}
  have : Countable I := Subtype.countable
  choose s hs hsub using fun t : I => exists_isCCHypersurface_of_subdifferential_separation (u := u)
    (e := ‖(t.val.1 : E)‖⁻¹ • (t.val.1 : E))
    (by simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 t.val.1.property.2)])
    (Rat.cast_lt.2 t.property) (t.val.2.2.2 : ℝ)
  refine ⟨range s, countable_range s, forall_mem_range.2 hs, fun x hx => ?_⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := Set.not_subsingleton_iff.1 hx
  obtain ⟨d, hd_in, hdD⟩ := hD_dense.inter_open_nonempty {w : E | inner ℝ (p - q) w ≠ 0}
    (isOpen_ne.preimage (by fun_prop)) ⟨p - q, by simp [sub_ne_zero.2 hpq]⟩
  have hd0 : d ≠ 0 := fun h0 => by simp [h0] at hd_in
  let d' : {d : E // d ∈ D ∧ d ≠ 0} := ⟨d, hdD, hd0⟩; let e : E := ‖(d' : E)‖⁻¹ • (d' : E)
  have hstep {p' q' : E} (hp' : p' ∈ subdifferential (innerₗ E) u x)
      (hq' : q' ∈ subdifferential (innerₗ E) u x) (hlt : inner ℝ p' e < inner ℝ q' e) :
      x ∈ ⋃₀ range s := by
    obtain ⟨M, hM⟩ := exists_nat_ge (max ‖p'‖ ‖q'‖)
    obtain ⟨r₁, hr₁, hr₂⟩ := exists_rat_btwn hlt; obtain ⟨r₂, hr₃, hr₄⟩ := exists_rat_btwn hr₂
    exact mem_sUnion.2 ⟨s ⟨(d', r₁, r₂, M), Rat.cast_lt.1 hr₃⟩, mem_range_self _, hsub _
      ⟨p', hp', q', hq', (le_max_left _ _).trans hM, (le_max_right _ _).trans hM, hr₁.le, hr₄.le⟩⟩
  refine (lt_or_gt_of_ne (fun heq => hd_in ?_)).elim (hstep hp hq) (hstep hq hp)
  have : inner ℝ (p - q) e = 0 := by rw [inner_sub_left, heq, sub_self]
  simpa [e, d', real_inner_smul_right, inv_eq_zero, norm_eq_zero, hd0] using this

end SubdifferentialSeparation

section FiniteDimensionalCovers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- For any extended-real function `u : E → EReal` with convex real epigraph, the set of interior
points of its effective domain at which `u.toReal` is not differentiable is covered by countably
many `c - c` hypersurfaces. -/
theorem exists_countable_isCCHypersurface_cover_mem_interior_not_differentiableAt_toReal
    {u : E → EReal} (hu : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) :
    ∃ C : Set (Set E), C.Countable ∧ (∀ s ∈ C, IsCCHypersurface s) ∧
      {x : E | x ∈ interior {z | u z ≠ ⊤} ∧ ¬ DifferentiableAt ℝ (fun z => (u z).toReal) x} ⊆
        ⋃₀ C :=
  let ⟨C, hC, hs, h⟩ := exists_countable_isCCHypersurface_cover_not_subsingleton_subdifferential u
  ⟨C, hC, hs, fun _ ⟨hx, hnd⟩ => h <| by
    rwa [mem_ofPred_eq, ← differentiableAt_toReal_iff_subsingleton_subdifferential hu hx]⟩

private theorem exists_countable_isCCHypersurface_cover_closure_of_not_nonempty_interior {K : Set E}
    (hK : Convex ℝ K) (hint : ¬ (interior K).Nonempty) :
    ∃ C : Set (Set E), C.Countable ∧ (∀ s ∈ C, IsCCHypersurface s) ∧ closure K ⊆ ⋃₀ C := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨∅, countable_empty, by simp, by simp⟩
  have hdir : (affineSpan ℝ K).direction ≠ ⊤ :=
    mt (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨x₀, subset_affineSpan ℝ K hx₀⟩).1
      (mt hK.interior_nonempty_iff_affineSpan_eq_top.2 hint)
  obtain ⟨v, hv_mem, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (mt Submodule.orthogonal_eq_bot_iff.1 hdir)
  let e : E := ‖v‖⁻¹ • v
  have he : ‖e‖ = 1 := by simp [e, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)]
  refine ⟨{{x | inner ℝ x e = inner ℝ x₀ e}}, countable_singleton _,
    by simpa using isCCHypersurface_setOf_inner_eq he _, ?_⟩
  simpa using closure_minimal (fun x hx => by
    rw [mem_ofPred_eq, ← sub_eq_zero, ← inner_sub_left]
    exact (Submodule.mem_orthogonal _ _).1 (Submodule.smul_mem _ _ hv_mem) _
      (AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ K hx) (subset_affineSpan ℝ K hx₀)))
    (isClosed_eq (by fun_prop) continuous_const)

/-- **Frontier of a convex set is covered by countably many `c - c` hypersurfaces.** For any convex
subset `K` of a finite-dimensional real inner product space `E`, `frontier K` (and hence also
`K \ interior K`) is covered by a countable family of `c - c` hypersurfaces. -/
theorem _root_.Convex.exists_countable_isCCHypersurface_cover_frontier {K : Set E}
    (hK : Convex ℝ K) :
    ∃ C : Set (Set E), C.Countable ∧ (∀ s ∈ C, IsCCHypersurface s) ∧ frontier K ⊆ ⋃₀ C := by
  by_cases hint : (interior K).Nonempty
  · obtain ⟨z₀, hz₀⟩ := hint; let K₀ : Set E := (z₀ + ·) ⁻¹' K
    have hK₀ : Convex ℝ K₀ := hK.translate_preimage_right z₀
    have hnhds : K₀ ∈ 𝓝 (0 : E) := (continuous_const.add continuous_id).continuousAt
      |>.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hz₀)
    have hgc : ConvexOn ℝ univ (gauge K₀) := ⟨convex_univ, fun _ _ _ _ _ _ ha hb _ =>
      (gauge_add_le hK₀ (absorbent_nhds_zero hnhds) _ _).trans_eq
        (by rw [gauge_smul_of_nonneg ha, gauge_smul_of_nonneg hb, smul_eq_mul, smul_eq_mul])⟩
    let u : E → ℝ := fun z => max (gauge K₀ (z - z₀)) 1
    have hu : ConvexOn ℝ univ u := ConvexOn.sup
      (by simpa [Function.comp_def, sub_eq_add_neg] using hgc.translate_left (-z₀))
      (convexOn_const 1 convex_univ)
    obtain ⟨C, hC, hs, hsub⟩ :=
      exists_countable_isCCHypersurface_cover_mem_interior_not_differentiableAt_toReal
        (u := fun z => (u z : EReal)) (by simpa using convexOn_iff_convex_epigraph_ite.1 hu)
    refine ⟨C, hC, hs, fun x hx => hsub ⟨by simp, ?_⟩⟩; simp only [EReal.toReal_coe]
    have hg1 : gauge K₀ (x - z₀) = 1 := (gauge_eq_one_iff_mem_frontier hK₀ hnhds).2 <| by
      dsimp only [K₀]
      rw [← Homeomorph.coe_addLeft z₀, ← (Homeomorph.addLeft z₀).preimage_frontier]
      simpa [add_sub_cancel] using hx
    refine not_differentiableAt_of_add_sub_two_mul_ge (v := x - z₀) zero_lt_one zero_lt_one
      fun t ht => ?_
    have hmul (s : ℝ) (hs : 0 ≤ 1 + s) : gauge K₀ (x + s • (x - z₀) - z₀) = 1 + s := by
      rw [show x + s • (x - z₀) - z₀ = (1 + s) • (x - z₀) by rw [add_smul, one_smul]; abel,
        gauge_smul_of_nonneg hs, smul_eq_mul, hg1, mul_one]
    have hm : gauge K₀ (x - t • (x - z₀) - z₀) = 1 - t := by
      simpa only [sub_eq_add_neg, neg_smul] using hmul (-t) (by linarith [ht.2])
    simp only [u, hmul t (by linarith [ht.1]), hm, hg1,
      max_eq_left (by linarith [ht.1] : (1 : ℝ) ≤ 1 + t),
      max_eq_right (by linarith [ht.1] : 1 - t ≤ 1), max_self]; linarith
  · exact let ⟨C, hC, hs, hcl⟩ :=
      exists_countable_isCCHypersurface_cover_closure_of_not_nonempty_interior hK hint
      ⟨C, hC, hs, frontier_subset_closure.trans hcl⟩

end FiniteDimensionalCovers

private theorem exists_measurable_piecewise_subgradient_max {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {u₁ u₂ : E → ℝ} {b₁ b₂ : E → E}
    (hu₁ : Continuous u₁) (hu₂ : Continuous u₂) (hb₁ : Measurable b₁) (hb₂ : Measurable b₂)
    (h₁ : ∀ x z, u₂ x ≤ u₁ x → max (u₁ x) (u₂ x) + inner ℝ (z - x) (b₁ x) ≤ max (u₁ z) (u₂ z))
    (h₂ : ∀ x z, u₁ x ≤ u₂ x → max (u₁ x) (u₂ x) + inner ℝ (z - x) (b₂ x) ≤ max (u₁ z) (u₂ z)) :
    ∃ T₁ T₂ : E → E, Measurable T₁ ∧ Measurable T₂ ∧
      (∀ x z, max (u₁ x) (u₂ x) + inner ℝ (z - x) (T₁ x) ≤ max (u₁ z) (u₂ z)) ∧
      (∀ x z, max (u₁ x) (u₂ x) + inner ℝ (z - x) (T₂ x) ≤ max (u₁ z) (u₂ z)) ∧
      (∀ x, u₁ x = u₂ x → T₁ x = b₁ x ∧ T₂ x = b₂ x) := by
  classical
  exact ⟨fun x => if u₂ x ≤ u₁ x then b₁ x else b₂ x, fun x => if u₁ x ≤ u₂ x then b₂ x else b₁ x,
    Measurable.ite (isClosed_le hu₂ hu₁).measurableSet hb₁ hb₂,
    Measurable.ite (isClosed_le hu₁ hu₂).measurableSet hb₂ hb₁,
    fun x z => by dsimp only; split_ifs with hx; exacts [h₁ x z hx, h₂ x z (le_of_not_ge hx)],
    fun x z => by dsimp only; split_ifs with hx; exacts [h₂ x z hx, h₁ x z (le_of_not_ge hx)],
    fun x heq => by simp [heq]⟩

private theorem summable_and_convexOn_tsum_weighted {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : ℕ → ℝ≥0} {ψ : ℕ → E → ℝ}
    (hconv : ∀ m, ConvexOn ℝ univ (ψ m)) (hψ0 : ∀ m, ψ m 0 = 0)
    (hlip : ∀ m, LipschitzWith (K m) (ψ m)) :
    let w : ℕ → ℝ := fun m => (1 / 2 : ℝ) ^ (m + 1) / ((K m : ℝ) + 1)
    (∀ x, Summable (fun m => w m * ψ m x)) ∧ ConvexOn ℝ univ (fun x => ∑' m, w m * ψ m x) := by
  intro w; have hw_pos (m : ℕ) : 0 < w m := by positivity
  have hsum (x : E) : Summable (fun m => w m * ψ m x) :=
    Summable.of_norm_bounded (g := fun m => (1 / 2 : ℝ) ^ (m + 1) * ‖x‖)
      (((summable_geometric_two.mul_left (1 / 2 : ℝ)).congr fun m => by ring).mul_right ‖x‖)
      fun m => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hw_pos m)]
        have hd : |ψ m x| ≤ (K m : ℝ) * ‖x‖ := by
          simpa [hψ0 m, Real.dist_eq, dist_zero_right] using (hlip m).dist_le_mul x 0
        exact (mul_le_mul_of_nonneg_left (hd.trans (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right zero_le_one) (norm_nonneg x))) (hw_pos m).le).trans_eq
          (by dsimp [w]; field_simp [show (K m : ℝ) + 1 ≠ 0 by positivity])
  refine ⟨hsum, convex_univ, fun x _ y _ a b ha hb hab => (Summable.tsum_le_tsum (fun m => ?_)
    (hsum (a • x + b • y)) (((hsum x).mul_left a).add ((hsum y).mul_left b))).trans_eq
    (by simp only [smul_eq_mul, Summable.tsum_add ((hsum x).mul_left a) ((hsum y).mul_left b),
      tsum_mul_left])⟩
  have hc := (hconv m).2 (mem_univ x) (mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hc; linarith [mul_le_mul_of_nonneg_left hc (hw_pos m).le]

section Zajicek

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_lipschitz_branch_data {s : Set E} (hs : IsCCHypersurface s) (R : ℝ) :
    ∃ (e : E) (_ : ‖e‖ = 1) (Lf Lg : ℝ≥0) (f' g' : ↥(ℝ ∙ e)ᗮ → ℝ),
      ConvexOn ℝ univ f' ∧ ConvexOn ℝ univ g' ∧ LipschitzWith Lf f' ∧ LipschitzWith Lg g' ∧
      ConvexOn ℝ univ (fun x : E => max (f' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x))
        (g' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) + inner ℝ x e)) ∧
      LipschitzWith (max Lf (Lg + 1)) (fun x : E => max (f' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x))
        (g' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) + inner ℝ x e)) ∧
      ∀ x ∈ s ∩ closedBall 0 R, g' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) + inner ℝ x e =
        f' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) := by
  obtain ⟨e, he, f, g, -, -, hf, hg, hs_eq⟩ := hs; let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  obtain ⟨Lf, f', hf', hLf', hff'⟩ := hf.exists_convexOn_lipschitzWith_eqOn isOpen_univ
    (isCompact_closedBall 0 (max R 0)) (subset_univ _)
  obtain ⟨Lg, g', hg', hLg', hgg'⟩ := hg.exists_convexOn_lipschitzWith_eqOn isOpen_univ
    (isCompact_closedBall 0 (max R 0)) (subset_univ _)
  have hlip_in : LipschitzWith 1 (fun x : E => inner ℝ x e) := LipschitzWith.mk_one fun _ _ => by
    rw [Real.dist_eq, ← inner_sub_left, dist_eq_norm]
    exact (abs_real_inner_le_norm _ _).trans_eq (by rw [he, mul_one])
  refine ⟨e, he, Lf, Lg, f', g', hf', hg', hLf', hLg',
    (hf'.comp_linearMap P.toLinearMap).sup ((hg'.comp_linearMap P.toLinearMap).add
      ⟨convex_univ, fun _ _ _ _ _ _ _ _ _ => by simp [inner_add_left, real_inner_smul_left]⟩),
    ((hLf'.comp (Submodule.lipschitzWith_orthogonalProjectionOnto _)).weaken (by simp)).max
      (((hLg'.comp (Submodule.lipschitzWith_orthogonalProjectionOnto _)).weaken (by simp) :
        LipschitzWith Lg (fun x => g' (P x))).add hlip_in),
    fun x ⟨hxs, hxR⟩ => ?_⟩
  have hPx : P x ∈ closedBall (0 : ↥(ℝ ∙ e)ᗮ) (max R 0) := mem_closedBall_zero_iff.2 <|
    (norm_orthogonalProjectionOnto_apply_le _ x).trans <|
      (mem_closedBall_zero_iff.1 hxR).trans (le_max_left R 0)
  rw [hs_eq, mem_ofPred_eq] at hxs; rw [← hff' hPx, ← hgg' hPx, hxs]; ring

/-- **Lipschitz convex potential with unit second-difference slope along a `c - c` hypersurface.**
Given a `c - c` hypersurface `s ⊆ E` and `R : ℝ`, there exist `K : ℝ≥0`, a unit vector `e : E`, and
a `K`-Lipschitz convex `ψ : E → ℝ` with `ψ 0 = 0` and
`ψ (x + t • e) + ψ (x - t • e) - 2 * ψ x = t` for every `x ∈ s ∩ closedBall 0 R` and `t ≥ 0`. -/
theorem IsCCHypersurface.exists_convexOn_lipschitzWith_add_sub_two_mul_eq {s : Set E}
    (hs : IsCCHypersurface s) (R : ℝ) :
    ∃ (K : ℝ≥0) (e : E) (_ : ‖e‖ = 1) (ψ : E → ℝ),
      ConvexOn ℝ univ ψ ∧ ψ 0 = 0 ∧ LipschitzWith K ψ ∧
      ∀ x ∈ s ∩ closedBall 0 R, ∀ t : ℝ, 0 ≤ t →
        ψ (x + t • e) + ψ (x - t • e) - 2 * ψ x = t := by
  obtain ⟨e, he, Lf, Lg, f', g', -, -, -, -, hconv₀, hlip₀, heq_on⟩ :=
    exists_lipschitz_branch_data hs R
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  let ψ : E → ℝ := fun x => max (f' (P x)) (g' (P x) + inner ℝ x e) - max (f' 0) (g' 0)
  refine ⟨max Lf (Lg + 1), e, he, ψ, hconv₀.add_const (-max (f' 0) (g' 0)), by simp [ψ, P],
    (hlip₀.sub (.const _)).weaken (by simp), fun x hx t ht => ?_⟩
  have hin (s : ℝ) : inner ℝ (x + s • e) e = inner ℝ x e + s := by
    simp [inner_add_left, real_inner_smul_left, he]
  have hin_sub : inner ℝ (x - t • e) e = inner ℝ x e - t := by
    simpa [sub_eq_add_neg, neg_smul] using hin (-t)
  simp only [ψ, P, map_add, map_sub, map_smul,
    orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero,
    smul_zero, add_zero, sub_zero, hin t, hin_sub]
  rw [← add_assoc, ← add_sub_assoc (g' _), heq_on x hx,
    max_eq_right (le_add_of_nonneg_right ht),
    max_eq_left (sub_le_self _ ht), max_self]
  ring

/-- **Borel measurable subgradient splitting along a `c - c` hypersurface.** Given a `c - c`
hypersurface `s ⊆ E` and `R : ℝ`, there exist `K : ℝ≥0`, a `K`-Lipschitz convex `ψ : E → ℝ`, and
Borel measurable maps `T₁, T₂ : E → E` bounded by `K` that are subgradients of `ψ` everywhere and
satisfy `T₁ x ≠ T₂ x` at every `x ∈ s ∩ closedBall 0 R`. -/
theorem IsCCHypersurface.exists_convexOn_lipschitzWith_measurable_forall_add_inner_le_ne
    [MeasurableSpace E] [BorelSpace E] {s : Set E} (hs : IsCCHypersurface s) (R : ℝ) :
    ∃ (K : ℝ≥0) (ψ : E → ℝ) (T₁ T₂ : E → E),
      ConvexOn ℝ univ ψ ∧ LipschitzWith K ψ ∧ Measurable T₁ ∧ Measurable T₂ ∧
      (∀ x z, ψ x + inner ℝ (z - x) (T₁ x) ≤ ψ z) ∧
      (∀ x z, ψ x + inner ℝ (z - x) (T₂ x) ≤ ψ z) ∧
      (∀ x, ‖T₁ x‖ ≤ K) ∧ (∀ x, ‖T₂ x‖ ≤ K) ∧
      (∀ x ∈ s ∩ closedBall 0 R, T₁ x ≠ T₂ x) := by
  obtain ⟨e, he, Lf, Lg, f', g', hf', hg', hLf', hLg', hconv, hlip, heq_on⟩ :=
    exists_lipschitz_branch_data hs R
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  obtain ⟨Gf, hGf_meas, hGf⟩ := hf'.exists_measurable_forall_add_inner_le isOpen_univ
  obtain ⟨Gg, hGg_meas, hGg⟩ := hg'.exists_measurable_forall_add_inner_le isOpen_univ
  have hsub₁ (x z : E) (hx : g' (P x) + inner ℝ x e ≤ f' (P x)) :
      max (f' (P x)) (g' (P x) + inner ℝ x e) + inner ℝ (z - x) (Gf (P x) : E) ≤
        max (f' (P z)) (g' (P z) + inner ℝ z e) := by
    rw [max_eq_left hx, ← inner_orthogonalProjectionOnto_eq_of_mem_right, map_sub]
    exact (hGf (P x) (mem_univ _) (P z) (mem_univ _)).trans (le_max_left _ _)
  have hsub₂ (x z : E) (hx : f' (P x) ≤ g' (P x) + inner ℝ x e) :
      max (f' (P x)) (g' (P x) + inner ℝ x e) + inner ℝ (z - x) ((Gg (P x) : E) + e) ≤
        max (f' (P z)) (g' (P z) + inner ℝ z e) := by
    rw [max_eq_right hx, inner_add_right, ← inner_orthogonalProjectionOnto_eq_of_mem_right,
      map_sub, inner_sub_left z x e]
    linarith [(add_le_add_left (hGg (P x) (mem_univ _) (P z) (mem_univ _)) (inner ℝ z e)).trans
      (le_max_right (f' (P z)) _)]
  obtain ⟨T₁, T₂, hT₁m, hT₂m, hT₁, hT₂, hTeq⟩ := exists_measurable_piecewise_subgradient_max
    (hLf'.continuous.comp P.continuous) ((hLg'.continuous.comp P.continuous).add (by fun_prop))
    (measurable_subtypeVal.comp (hGf_meas.comp P.measurable))
    ((measurable_subtypeVal.comp (hGg_meas.comp P.measurable)).add measurable_const) hsub₁ hsub₂
  refine ⟨max Lf (Lg + 1), _, T₁, T₂, hconv, hlip, hT₁m, hT₂m, hT₁, hT₂,
    fun x => hlip.norm_le_of_forall_add_inner_le (hT₁ x),
    fun x => hlip.norm_le_of_forall_add_inner_le (hT₂ x), fun x hx hEq => ?_⟩
  obtain ⟨h₁, h₂⟩ := hTeq x (heq_on x hx).symm
  have hin₁ : inner ℝ (T₁ x) e = 0 :=
    h₁ ▸ Submodule.mem_orthogonal_singleton_iff_inner_left.mp (Gf (P x)).property
  have hin₂ : inner ℝ (T₂ x) e = 1 := by
    simp [h₂, inner_add_left,
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp (Gg (P x)).property, he]
  linarith [congrArg (inner ℝ · e) hEq]

private theorem exists_convexOn_subset_not_differentiableAt_of_seq (s : ℕ → Set E)
    (hs : ∀ n, IsCCHypersurface (s n)) :
    ∃ u : E → ℝ, ConvexOn ℝ univ u ∧ (⋃ n, s n) ⊆ {x | ¬ DifferentiableAt ℝ u x} := by
  choose K e _ ψ hconv hψ0 hlip hcorner using fun m : ℕ =>
    (hs m.unpair.1).exists_convexOn_lipschitzWith_add_sub_two_mul_eq (m.unpair.2 : ℝ)
  let w : ℕ → ℝ := fun m => (1 / 2 : ℝ) ^ (m + 1) / ((K m : ℝ) + 1)
  have hw_pos (m : ℕ) : 0 < w m := by positivity
  obtain ⟨hsum, hu_conv⟩ := summable_and_convexOn_tsum_weighted hconv hψ0 hlip
  refine ⟨fun x => ∑' m, w m * ψ m x, hu_conv, fun x hx => ?_⟩
  obtain ⟨n, hxn⟩ := mem_iUnion.1 hx; obtain ⟨R, hR⟩ := exists_nat_ge ‖x‖; let m₀ := Nat.pair n R
  have hm₀ : x ∈ s m₀.unpair.1 ∩ closedBall 0 (m₀.unpair.2 : ℝ) := by
    simpa only [m₀, Nat.unpair_pair] using ⟨hxn, mem_closedBall_zero_iff.2 hR⟩
  refine not_differentiableAt_of_add_sub_two_mul_ge (v := e m₀) (hw_pos m₀) zero_lt_one
    fun t ht => ?_
  have hs₁ := hsum (x + t • e m₀); have hs₂ := hsum (x - t • e m₀); have hs₃ := (hsum x).mul_left 2
  rw [show (∑' m, w m * ψ m (x + t • e m₀)) + (∑' m, w m * ψ m (x - t • e m₀)) -
      2 * (∑' m, w m * ψ m x) =
      ∑' m, w m * (ψ m (x + t • e m₀) + ψ m (x - t • e m₀) - 2 * ψ m x) by
    rw [← Summable.tsum_add hs₁ hs₂, ← tsum_mul_left, ← Summable.tsum_sub (hs₁.add hs₂) hs₃]
    congr 1; ext m; ring]
  nth_rw 1 [← hcorner m₀ x hm₀ t ht.1.le]
  have hs_diff : Summable fun m => w m * (ψ m (x + t • e m₀) + ψ m (x - t • e m₀) - 2 * ψ m x) :=
    ((hs₁.add hs₂).sub hs₃).congr fun m => by dsimp only [w]; ring
  refine Summable.le_tsum hs_diff m₀ fun m _ => mul_nonneg (hw_pos m).le ?_
  have hmid := (hconv m).2 (mem_univ (x + t • e m₀)) (mem_univ (x - t • e m₀))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [show (1 / 2 : ℝ) • (x + t • e m₀) + (1 / 2 : ℝ) • (x - t • e m₀) = x by
    rw [smul_add, smul_sub]; module] at hmid; simp only [smul_eq_mul] at hmid; linarith

/-- **Zajíček's theorem.** In a finite-dimensional real inner product space `E`, a subset `A ⊆ E`
is contained in the nondifferentiability locus of some convex `u : E → ℝ` iff `A` can be covered by
countably many `c - c` hypersurfaces. -/
theorem exists_convexOn_subset_not_differentiableAt_iff {A : Set E} :
    (∃ u : E → ℝ, ConvexOn ℝ univ u ∧ A ⊆ {x | ¬ DifferentiableAt ℝ u x}) ↔
      ∃ C : Set (Set E), C.Countable ∧ (∀ s ∈ C, IsCCHypersurface s) ∧ A ⊆ ⋃₀ C := by
  refine ⟨fun ⟨u, hu, hA⟩ => ?_, fun ⟨C, hC, hs, hA⟩ => ?_⟩
  · obtain ⟨C, hC, hs, hsub⟩ :=
      exists_countable_isCCHypersurface_cover_mem_interior_not_differentiableAt_toReal
        (u := fun z => (u z : EReal)) (by simpa using convexOn_iff_convex_epigraph_ite.1 hu)
    exact ⟨C, hC, hs, hA.trans fun x hx => hsub ⟨by simp, by simpa using hx⟩⟩
  · rcases C.eq_empty_or_nonempty with rfl | hCne
    · simp only [sUnion_empty, subset_empty_iff] at hA
      exact ⟨0, convexOn_const 0 convex_univ, hA ▸ empty_subset _⟩
    · obtain ⟨s, rfl⟩ := hC.exists_eq_range hCne
      exact let ⟨u, hu, hsub⟩ :=
        exists_convexOn_subset_not_differentiableAt_of_seq s (forall_mem_range.1 hs)
        ⟨u, hu, hA.trans (sUnion_range s ▸ hsub)⟩

/-- **Zajíček's theorem (`ℕ`-indexed sequence form).** In a nontrivial finite-dimensional real inner
product space `E`, a subset `A ⊆ E` is contained in the nondifferentiability locus of some convex
`u : E → ℝ` iff `A` is covered by a sequence `s : ℕ → Set E` of `c - c` hypersurfaces. -/
theorem exists_convexOn_subset_not_differentiableAt_iff_nat [Nontrivial E] {A : Set E} :
    (∃ u : E → ℝ, ConvexOn ℝ univ u ∧ A ⊆ {x | ¬ DifferentiableAt ℝ u x}) ↔
      ∃ s : ℕ → Set E, (∀ n, IsCCHypersurface (s n)) ∧ A ⊆ ⋃ n, s n := by
  rw [exists_convexOn_subset_not_differentiableAt_iff]
  refine ⟨fun ⟨C, hC, hs, hA⟩ => ?_, fun ⟨s, hs, hA⟩ =>
    ⟨range s, countable_range s, forall_mem_range.2 hs, sUnion_range s ▸ hA⟩⟩
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · obtain ⟨e, he⟩ := exists_norm_eq E (zero_le_one (α := ℝ))
    exact ⟨fun _ => {x | inner ℝ x e = 0},
      fun _ => isCCHypersurface_setOf_inner_eq he 0, hA.trans (by simp)⟩
  · obtain ⟨s, rfl⟩ := hC.exists_eq_range hCne
    exact ⟨s, forall_mem_range.1 hs, sUnion_range s ▸ hA⟩

end Zajicek

end TauCeti
