/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Convex.Continuous
import TauCeti.Analysis.InnerProductSpace.OrthogonalLine

/-!
# Delta-convex (`c - c`) and Lipschitz hypersurfaces

In a real inner product space `E`, a *`c - c` hypersurface* (or *delta-convex hypersurface*) is the
graph over `(ℝ ∙ e)ᗮ` (for unit `e`) of `f - g` for continuous convex `f, g : ↥(ℝ ∙ e)ᗮ → ℝ`; a
*Lipschitz hypersurface* is the graph of a globally Lipschitz function. Both classes are closed and
invariant under translations and continuous linear equivalences. In separable spaces, every `c - c`
hypersurface is covered by countably many Lipschitz hypersurfaces. In finite dimensions, they are
equivalently graphs in orthonormal coordinates `E ≃ₗᵢ[ℝ] ℝ^{d-1} ×₂ ℝ`, and in dimension one they
are precisely the singletons.

## Main declarations

* `TauCeti.IsCCHypersurface`, `TauCeti.IsLipschitzHypersurface` — `c - c` and Lipschitz
  hypersurfaces, with direct graph constructors (`TauCeti.isCCHypersurface_setOf_inner_eq_sub`,
  `TauCeti.isLipschitzHypersurface_setOf_inner_eq_of_lipschitzWith`), parametric
  (`*_iff_exists_eq_range`), orthonormal coordinate (`*_iff_exists_linearIsometryEquiv`), and 1D
  (`*_iff_exists_eq_singleton`) characterizations.
* `TauCeti.isCCHypersurface_vadd_iff`, `TauCeti.isCCHypersurface_image_continuousLinearEquiv_iff`,
  `TauCeti.isLipschitzHypersurface_vadd_iff`,
  `TauCeti.isLipschitzHypersurface_image_continuousLinearEquiv_iff` — affine invariance.
* `TauCeti.IsCCHypersurface.exists_subset_iUnion_isLipschitzHypersurface` — countable Lipschitz
  covering of any `c - c` hypersurface in a separable space.

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

/-- Every graph `{x | ⟪x, e⟫ = f (P x) - g (P x)}` over `(ℝ ∙ e)ᗮ` of a difference of
continuous convex functions is a `c - c` hypersurface. -/
theorem isCCHypersurface_setOf_inner_eq_sub {e : E} (he : ‖e‖ = 1) {f g : ↥(ℝ ∙ e)ᗮ → ℝ}
    (hfc : Continuous f) (hgc : Continuous g) (hf : ConvexOn ℝ univ f) (hg : ConvexOn ℝ univ g) :
    IsCCHypersurface {x : E | inner ℝ x e =
      f ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) - g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} :=
  ⟨e, he, f, g, hfc, hgc, hf, hg, rfl⟩

/-- Every graph `{x | ⟪x, e⟫ = h (P x)}` over `(ℝ ∙ e)ᗮ` of a globally Lipschitz function is
a Lipschitz hypersurface. -/
theorem isLipschitzHypersurface_setOf_inner_eq_of_lipschitzWith {e : E} (he : ‖e‖ = 1)
    {K : ℝ≥0} {h : ↥(ℝ ∙ e)ᗮ → ℝ} (hh : LipschitzWith K h) :
    IsLipschitzHypersurface {x : E | inner ℝ x e = h ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} :=
  ⟨e, he, K, h, hh, rfl⟩

/-- Every affine hyperplane `{x | ⟪x, e⟫ = c}` normal to unit `e` is a `c - c` hypersurface. -/
theorem isCCHypersurface_setOf_inner_eq {e : E} (he : ‖e‖ = 1) (c : ℝ) :
    IsCCHypersurface {x : E | inner ℝ x e = c} := by
  simpa using isCCHypersurface_setOf_inner_eq_sub he continuous_const continuous_const
    (convexOn_const c convex_univ) (convexOn_const 0 convex_univ)

/-- Every affine hyperplane `{x | ⟪x, e⟫ = c}` normal to unit `e` is a Lipschitz hypersurface. -/
theorem isLipschitzHypersurface_setOf_inner_eq {e : E} (he : ‖e‖ = 1) (c : ℝ) :
    IsLipschitzHypersurface {x : E | inner ℝ x e = c} :=
  isLipschitzHypersurface_setOf_inner_eq_of_lipschitzWith he (LipschitzWith.const c)

/-- Every `c - c` hypersurface is closed. -/
theorem IsCCHypersurface.isClosed {s : Set E} (hs : IsCCHypersurface s) : IsClosed s :=
  let ⟨_, _, _, _, hfc, hgc, _, _, hs'⟩ := hs; hs' ▸ isClosed_eq (by fun_prop) (by fun_prop)

/-- Every Lipschitz hypersurface is closed. -/
theorem IsLipschitzHypersurface.isClosed {s : Set E} (hs : IsLipschitzHypersurface s) :
    IsClosed s :=
  let ⟨_, _, _, _, hh, h⟩ := hs; h ▸ isClosed_eq (by fun_prop) (hh.continuous.comp (by fun_prop))

/-- Translates of `c - c` hypersurfaces are `c - c` hypersurfaces. -/
theorem IsCCHypersurface.vadd {s : Set E} (hs : IsCCHypersurface s) (v : E) :
    IsCCHypersurface (v +ᵥ s) := by
  obtain ⟨e, he, f, g, hfc, hgc, hf, hg, rfl⟩ := hs
  let v₀ := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto v
  have hsub {w : ↥(ℝ ∙ e)ᗮ → ℝ} (hw : ConvexOn ℝ univ w) : ConvexOn ℝ univ (w ∘ (· - v₀)) := by
    simpa [Function.comp_def, sub_eq_add_neg] using hw.translate_left (-v₀)
  have heq : v +ᵥ {x : E | inner ℝ x e =
        f ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) - g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} =
      {x : E | inner ℝ x e =
        (f ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x - v₀) + inner ℝ v e) -
          g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x - v₀)} := by
    simpa [v₀, real_inner_comm e, sub_add_eq_add_sub] using
      vadd_setOf_inner_eq (𝕜 := ℝ) e v (fun y => f y - g y)
  exact heq ▸ isCCHypersurface_setOf_inner_eq_sub he (by fun_prop) (by fun_prop)
    ((hsub hf).add_const _) (hsub hg)

/-- A translate `v +ᵥ s` is a `c - c` hypersurface if and only if `s` is. -/
@[simp]
theorem isCCHypersurface_vadd_iff {s : Set E} {v : E} :
    IsCCHypersurface (v +ᵥ s) ↔ IsCCHypersurface s :=
  ⟨fun h => by simpa using h.vadd (-v), fun h => h.vadd v⟩

/-- Translates of Lipschitz hypersurfaces are Lipschitz hypersurfaces. -/
theorem IsLipschitzHypersurface.vadd {s : Set E} (hs : IsLipschitzHypersurface s) (v : E) :
    IsLipschitzHypersurface (v +ᵥ s) := by
  obtain ⟨e, he, K, h, hh, rfl⟩ := hs
  let v₀ := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto v
  have heq : v +ᵥ {x : E | inner ℝ x e = h ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} =
      {x : E | inner ℝ x e = h ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x - v₀) + inner ℝ v e} := by
    simpa [v₀, real_inner_comm e] using vadd_setOf_inner_eq (𝕜 := ℝ) e v h
  exact heq ▸ isLipschitzHypersurface_setOf_inner_eq_of_lipschitzWith he
    (LipschitzWith.of_dist_le_mul fun a b =>
      (dist_add_right _ _ _).le.trans ((hh.dist_le_mul (a - v₀) (b - v₀)).trans_eq
        (by rw [dist_sub_right])))

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
  have heq : L '' {x : E | inner ℝ x e =
        f ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) - g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} =
      {z : F | inner ℝ z e' = c * f (B ((ℝ ∙ e')ᗮ.orthogonalProjectionOnto z)) -
        (c * g (B ((ℝ ∙ e')ᗮ.orthogonalProjectionOnto z)) +
          ℓ ((ℝ ∙ e')ᗮ.orthogonalProjectionOnto z))} := by
    simpa only [mul_sub, sub_sub] using himg
  exact heq ▸ isCCHypersurface_setOf_inner_eq_sub he' (by fun_prop) (by fun_prop)
    ((hf.comp_linearMap B.toLinearMap).smul hc.le)
    (((hg.comp_linearMap B.toLinearMap).smul hc.le).add
      ⟨convex_univ, fun _ _ _ _ _ _ _ _ _ => by simp⟩)

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
  exact himg ▸ isLipschitzHypersurface_setOf_inner_eq_of_lipschitzWith he'
    ((hmul.comp (hh.comp B.lipschitzWith)).sub ℓ.lipschitzWith)

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

section LipschitzCover

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace.SeparableSpace E]

/-- Every `c - c` hypersurface in a separable real inner product space is covered by countably many
Lipschitz hypersurfaces. -/
theorem IsCCHypersurface.exists_subset_iUnion_isLipschitzHypersurface {s : Set E}
    (hs : IsCCHypersurface s) :
    ∃ t : ℕ → Set E, (∀ n, IsLipschitzHypersurface (t n)) ∧ s ⊆ ⋃ n, t n := by
  obtain ⟨e, he, f, g, hfc, hgc, hf, hg, rfl⟩ := isCCHypersurface_def.1 hs
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  have hloc_f := (hf.locallyLipschitzOn_iff_continuousOn isOpen_univ).2 hfc.continuousOn
  have hloc_g := (hg.locallyLipschitzOn_iff_continuousOn isOpen_univ).2 hgc.continuousOn
  choose Kf Uf hUf hLf using fun y => hloc_f (mem_univ y)
  choose Kg Ug hUg hLg using fun y => hloc_g (mem_univ y)
  have hU_nhds (y : ↥(ℝ ∙ e)ᗮ) : Uf y ∩ Ug y ∈ nhds y := by
    rw [← nhdsWithin_univ]
    exact Filter.inter_mem (hUf y) (hUg y)
  choose h hhLip hhEq using fun y =>
    (((hLf y).mono inter_subset_left).sub ((hLg y).mono inter_subset_right)).extend_real
  obtain ⟨C, hC_count, hC_cov⟩ := TopologicalSpace.countable_cover_nhds hU_nhds
  have hC_ne : C.Nonempty := by
    by_contra hC0
    rw [not_nonempty_iff_eq_empty.1 hC0, biUnion_empty] at hC_cov
    exact absurd hC_cov empty_ne_univ
  obtain ⟨y, rfl⟩ := hC_count.exists_eq_range hC_ne
  refine ⟨fun n => {x | inner ℝ x e = h (y n) (P x)},
    fun n => isLipschitzHypersurface_setOf_inner_eq_of_lipschitzWith he (hhLip (y n)),
    fun x hx => ?_⟩
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := mem_iUnion₂.1 (hC_cov.symm ▸ mem_univ (P x))
  exact mem_iUnion.2 ⟨n, by simpa [← hhEq (y n) hn] using hx⟩

end LipschitzCover

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
    have hs' : s = {x : E | inner ℝ x e =
        (f ∘ ψ) ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) -
          (g ∘ ψ) ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} := by
      rw [hs]; ext x; simp [hfst, hsnd]
    exact hs' ▸ isCCHypersurface_setOf_inner_eq_sub he
      ((continuousOn_univ.1 (hf.continuousOn isOpen_univ)).comp ψ.continuous)
      ((continuousOn_univ.1 (hg.continuousOn isOpen_univ)).comp ψ.continuous)
      (hf.comp_linearMap ψ.toLinearMap) (hg.comp_linearMap ψ.toLinearMap)

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
    have hs' : s = {x : E | inner ℝ x e = (h ∘ ψ) ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} := by
      rw [hs]; ext x; simp [hfst, hsnd]
    exact hs' ▸ isLipschitzHypersurface_setOf_inner_eq_of_lipschitzWith he
      (by simpa using hh.comp ψ.lipschitzWith)

/-- **Dimension-one characterization of `c - c` hypersurfaces.** In a one-dimensional real inner
product space, the `c - c` hypersurfaces are precisely the singletons. -/
theorem isCCHypersurface_iff_exists_eq_singleton (hdim : Module.finrank ℝ E = 1) {s : Set E} :
    IsCCHypersurface s ↔ ∃ x : E, s = {x} :=
  ⟨fun hs => let ⟨_, he, f, g, _, _, _, _, h⟩ := isCCHypersurface_iff_exists_eq_range.1 hs
    ⟨_, h.trans (range_eq_singleton_of_finrank_eq_one hdim (fun h0 => by simp [h0] at he)
      (fun y => f y - g y))⟩,
   fun ⟨x, hx⟩ => let ⟨_, he, heq⟩ := exists_unit_singleton_eq_setOf_inner_eq hdim x
    hx ▸ heq ▸ isCCHypersurface_setOf_inner_eq he _⟩

/-- **Dimension-one characterization of Lipschitz hypersurfaces.** In a one-dimensional real inner
product space, the Lipschitz hypersurfaces are precisely the singletons. -/
theorem isLipschitzHypersurface_iff_exists_eq_singleton (hdim : Module.finrank ℝ E = 1)
    {s : Set E} : IsLipschitzHypersurface s ↔ ∃ x : E, s = {x} :=
  ⟨fun hs => let ⟨_, he, _, h, _, hs'⟩ := isLipschitzHypersurface_iff_exists_eq_range.1 hs
    ⟨_, hs'.trans (range_eq_singleton_of_finrank_eq_one hdim (fun h0 => by simp [h0] at he) h)⟩,
   fun ⟨x, hx⟩ => let ⟨_, he, heq⟩ := exists_unit_singleton_eq_setOf_inner_eq hdim x
    hx ▸ heq ▸ isLipschitzHypersurface_setOf_inner_eq he _⟩

end Coordinates

end TauCeti
