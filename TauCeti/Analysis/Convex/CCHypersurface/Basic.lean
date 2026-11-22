/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Convex.Continuous
import TauCeti.Analysis.InnerProductSpace.OrthogonalLine

/-!
# Delta-convex (`c - c`) and Lipschitz hypersurfaces

In a real inner product space `E`, a *`c - c` hypersurface* (or *delta-convex hypersurface*) is the
graph over `(ℝ ∙ e)ᗮ` (for unit `e`) of `f - g` for continuous convex `f, g : ↥(ℝ ∙ e)ᗮ → ℝ`; a
*Lipschitz hypersurface* is the graph of a globally Lipschitz function. Both classes are closed,
Borel measurable, and invariant under translations and continuous linear equivalences. In finite
dimensions, they are equivalently graphs in orthonormal coordinates `E ≃ₗᵢ[ℝ] ℝ^{d-1} ×₂ ℝ`, and in
dimension one they are precisely the singletons.

## Main declarations

* `TauCeti.IsCCHypersurface`, `TauCeti.IsLipschitzHypersurface` — `c - c` and Lipschitz
  hypersurfaces, with parametric (`*_iff_exists_eq_range`), orthonormal coordinate
  (`*_iff_exists_linearIsometryEquiv`), and 1D (`*_iff_exists_eq_singleton`) characterizations.
* `TauCeti.isCCHypersurface_vadd_iff`, `TauCeti.isCCHypersurface_image_continuousLinearEquiv_iff`,
  `TauCeti.isLipschitzHypersurface_vadd_iff`,
  `TauCeti.isLipschitzHypersurface_image_continuousLinearEquiv_iff` — affine invariance.

## References

* L. Zajíček, *On the differentiation of convex functions in finite and infinite dimensional
  spaces*, Czechoslovak Math. J. 29 (1979), 340–348.
* L. Ambrosio and N. Gigli, *A user's guide to optimal transport*, LNM 2062, Springer, 2013,
  Definition 1.23 and Theorem 1.24.
-/

public section

noncomputable section

open Set Submodule
open scoped NNReal Pointwise

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
@[simp]
theorem not_isCCHypersurface_of_subsingleton [Subsingleton E] (s : Set E) : ¬ IsCCHypersurface s :=
  fun ⟨e, he, _⟩ => by simp [Subsingleton.elim e 0] at he

/-- A trivial (zero-dimensional) space contains no Lipschitz hypersurface. -/
@[simp]
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
  obtain ⟨e, he, f, g, hfc, hgc, hf, hg, rfl⟩ := hs
  let v₀ := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto v
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
  let ⟨e, he, K, h, hh, hs'⟩ := hs
  let v₀ := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto v
  hs' ▸ ⟨e, he, K, fun y => h (y - v₀) + inner ℝ v e,
    ((hh.comp (LipschitzWith.id.sub (.const v₀))).add (.const _)).weaken (by simp),
    by simpa [v₀, real_inner_comm e] using vadd_setOf_inner_eq (𝕜 := ℝ) e v h⟩

/-- A translate `v +ᵥ s` is a Lipschitz hypersurface if and only if `s` is. -/
@[simp]
theorem isLipschitzHypersurface_vadd_iff {s : Set E} {v : E} :
    IsLipschitzHypersurface (v +ᵥ s) ↔ IsLipschitzHypersurface s :=
  ⟨fun h => by simpa using h.vadd (-v), fun h => h.vadd v⟩

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

end TauCeti
