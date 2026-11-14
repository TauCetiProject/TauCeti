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

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.Convex.SubgradientImage
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Delta-convex (`c - c`) hypersurfaces and Zajíček's theorem

In a real inner product space `E`, a *`c - c` hypersurface* (or *delta-convex hypersurface*) is the
graph over `(ℝ ∙ e)ᗮ` of a unit vector `e` of the difference `f - g` of two real functions convex
on `(ℝ ∙ e)ᗮ`; a *Lipschitz hypersurface* is the graph over `(ℝ ∙ e)ᗮ` of a globally Lipschitz
function. In finite dimension, every `c - c` hypersurface is closed, is covered by countably many
Lipschitz hypersurfaces, and is additive-Haar null. Zajíček proved that a subset `A ⊆ E` lies in
the nondifferentiability locus of some convex function `u : E → ℝ` if and only if `A` is covered by
countably many `c - c` hypersurfaces.

Without any convexity assumption on `u : E → EReal`, the locus where `∂u(x)` has more than one
element is covered by countably many `c - c` hypersurfaces (refining the `E × ℝ` Lipschitz-graph
covering in `TauCeti/Analysis/Convex/SingularSet.lean`), whence so is the frontier of every convex
set. Conversely, for each `c - c` hypersurface `s` and radius `R` we build a globally convex
Lipschitz potential `ψ : E → ℝ` with a unit corner along `s ∩ closedBall 0 R`, together with two
Borel measurable subgradient selections `T₁, T₂` separating `s ∩ closedBall 0 R`.

## Main definitions

* `TauCeti.IsCCHypersurface s` — `s` is `{x | ⟪x, e⟫ = f (P x) - g (P x)}` over
  `P = (ℝ ∙ e)ᗮ.orthogonalProjectionOnto` for a unit vector `e` and convex `f, g` on `(ℝ ∙ e)ᗮ`.
* `TauCeti.IsLipschitzHypersurface s` — `s` is `{x | ⟪x, e⟫ = h (P x)}` for a unit vector `e` and
  globally Lipschitz `h` on `(ℝ ∙ e)ᗮ`.

## Main statements

* `TauCeti.isCCHypersurface_iff_exists_linearIsometryEquiv` and
  `TauCeti.isCCHypersurface_iff_exists_eq_singleton` — orthonormal coordinate-splitting and
  dimension-`1` singleton characterizations;
* `TauCeti.IsCCHypersurface.subset_iUnion_isLipschitzHypersurface`,
  `TauCeti.IsLipschitzHypersurface.addHaar_eq_zero`, and `TauCeti.IsCCHypersurface.addHaar_eq_zero`
  — countable Lipschitz covering and additive-Haar nullity;
* `TauCeti.exists_countable_isCCHypersurface_cover_not_subsingleton_subdifferential` and
  `Convex.exists_countable_isCCHypersurface_cover_frontier` — countable `c - c` coverings of
  multivalued subgradients and convex frontiers;
* `TauCeti.IsCCHypersurface.exists_convexOn_lipschitzWith_measurable_subgradients` — global convex
  Lipschitz corner potential with Borel measurable subgradients separating `s ∩ closedBall 0 R`;
* `TauCeti.exists_convexOn_subset_not_differentiableAt_iff` and
  `TauCeti.exists_convexOn_subset_not_differentiableAt_iff_nat` — **Zajíček's theorem**.

## References

* L. Zajíček, *On the differentiation of convex functions in finite and infinite dimensional
  spaces*, Czechoslovak Mathematical Journal 29 (1979), 340–348.
* L. Ambrosio and N. Gigli, *A user's guide to optimal transport*, Lecture Notes in Mathematics
  2062, Springer, 2013, Definition 1.23 and Theorem 1.24.
-/

public section

noncomputable section

open Set Filter MeasureTheory Metric Submodule
open scoped NNReal Topology Pointwise

namespace TauCeti

section Defs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A subset `s` of a real inner product space `E` is a *`c - c` hypersurface* (or *delta-convex
hypersurface*) if there exist a unit vector `e : E` and two real functions `f, g` convex on the
orthogonal complement `(ℝ ∙ e)ᗮ` such that `s` is the graph
`{x | ⟪x, e⟫ = f (P x) - g (P x)}`, where `P` is orthogonal projection onto `(ℝ ∙ e)ᗮ`. -/
def IsCCHypersurface (s : Set E) : Prop :=
  ∃ (e : E) (_ : ‖e‖ = 1) (f g : ↥(ℝ ∙ e)ᗮ → ℝ),
    ConvexOn ℝ univ f ∧ ConvexOn ℝ univ g ∧
    s = {x : E | inner ℝ x e =
      f ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) - g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)}

/-- Unfolding characterization of `IsCCHypersurface`. -/
theorem isCCHypersurface_def {s : Set E} :
    IsCCHypersurface s ↔
      ∃ (e : E) (_ : ‖e‖ = 1) (f g : ↥(ℝ ∙ e)ᗮ → ℝ),
        ConvexOn ℝ univ f ∧ ConvexOn ℝ univ g ∧
        s = {x : E | inner ℝ x e =
          f ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) - g ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} :=
  Iff.rfl

/-- A subset `s` of a real inner product space `E` is a *Lipschitz hypersurface* if there exist a
unit vector `e : E`, a constant `K : ℝ≥0`, and a `K`-Lipschitz function `h : ↥(ℝ ∙ e)ᗮ → ℝ` such
that `s = {x | ⟪x, e⟫ = h (P x)}`, where `P` is orthogonal projection onto `(ℝ ∙ e)ᗮ`. -/
def IsLipschitzHypersurface (s : Set E) : Prop :=
  ∃ (e : E) (_ : ‖e‖ = 1) (K : ℝ≥0) (h : ↥(ℝ ∙ e)ᗮ → ℝ),
    LipschitzWith K h ∧ s = {x : E | inner ℝ x e = h ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)}

/-- Unfolding characterization of `IsLipschitzHypersurface`. -/
theorem isLipschitzHypersurface_def {s : Set E} :
    IsLipschitzHypersurface s ↔
      ∃ (e : E) (_ : ‖e‖ = 1) (K : ℝ≥0) (h : ↥(ℝ ∙ e)ᗮ → ℝ),
        LipschitzWith K h ∧ s = {x : E | inner ℝ x e = h ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} :=
  Iff.rfl

private theorem orthogonalProjectionOnto_add_inner_smul {e : E} (he : ‖e‖ = 1) (x : E) :
    ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x : E) + inner ℝ x e • e = x := by
  have h := (ℝ ∙ e).starProjection_add_starProjection_orthogonal x
  rw [starProjection_unit_singleton ℝ he, real_inner_comm] at h
  simpa only [starProjection_apply, add_comm] using h

private theorem inner_coe_orthogonal_singleton (e : E) (y : ↥(ℝ ∙ e)ᗮ) :
    inner ℝ (y : E) e = 0 :=
  real_inner_comm e y ▸ (Submodule.mem_orthogonal (ℝ ∙ e) y).1 y.2 e (mem_span_singleton_self e)

private theorem orthogonalProjectionOnto_coe_add_smul (e : E) (y : ↥(ℝ ∙ e)ᗮ) (t : ℝ) :
    (ℝ ∙ e)ᗮ.orthogonalProjectionOnto ((y : E) + t • e) = y := by
  rw [map_add, map_smul, orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero,
    smul_zero, add_zero]
  exact Subtype.ext ((coe_orthogonalProjectionOnto_apply _ _).trans
    ((starProjection_eq_self_iff (K := (ℝ ∙ e)ᗮ)).2 y.2))

private theorem inner_coe_add_smul_unit {e : E} (he : ‖e‖ = 1) (y : ↥(ℝ ∙ e)ᗮ) (t : ℝ) :
    inner ℝ ((y : E) + t • e) e = t := by
  rw [inner_add_left, inner_coe_orthogonal_singleton, zero_add, real_inner_smul_left,
    real_inner_self_eq_norm_sq, he, one_pow, mul_one]

private theorem setOf_inner_eq_eq_range {e : E} (he : ‖e‖ = 1) (φ : ↥(ℝ ∙ e)ᗮ → ℝ) :
    {x : E | inner ℝ x e = φ ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} =
      range fun y : ↥(ℝ ∙ e)ᗮ => (y : E) + φ y • e := by
  ext x; simp only [mem_ofPred_eq, mem_range]
  refine ⟨fun hx => ⟨_, hx ▸ orthogonalProjectionOnto_add_inner_smul he x⟩, ?_⟩
  rintro ⟨y, rfl⟩; simp [orthogonalProjectionOnto_coe_add_smul, inner_coe_add_smul_unit he]

/-- Parametric graph characterization of `IsCCHypersurface`. -/
theorem isCCHypersurface_iff_exists_eq_range {s : Set E} :
    IsCCHypersurface s ↔
      ∃ (e : E) (_ : ‖e‖ = 1) (f g : ↥(ℝ ∙ e)ᗮ → ℝ),
        ConvexOn ℝ univ f ∧ ConvexOn ℝ univ g ∧
        s = range fun y : ↥(ℝ ∙ e)ᗮ => (y : E) + (f y - g y) • e :=
  exists_congr fun _ => exists_congr fun he => exists_congr fun f => exists_congr fun g => by
    simp [setOf_inner_eq_eq_range he (fun y => f y - g y)]

/-- Parametric graph characterization of `IsLipschitzHypersurface`. -/
theorem isLipschitzHypersurface_iff_exists_eq_range {s : Set E} :
    IsLipschitzHypersurface s ↔
      ∃ (e : E) (_ : ‖e‖ = 1) (K : ℝ≥0) (h : ↥(ℝ ∙ e)ᗮ → ℝ),
        LipschitzWith K h ∧ s = range fun y : ↥(ℝ ∙ e)ᗮ => (y : E) + h y • e :=
  exists_congr fun _ => exists_congr fun he => by simp [setOf_inner_eq_eq_range he]

/-- A trivial (zero-dimensional) space contains no `c - c` hypersurface. -/
theorem not_isCCHypersurface_of_subsingleton [Subsingleton E] (s : Set E) :
    ¬ IsCCHypersurface s := by
  rintro ⟨e, he, -⟩; simp [Subsingleton.elim e 0] at he

/-- A trivial (zero-dimensional) space contains no Lipschitz hypersurface. -/
theorem not_isLipschitzHypersurface_of_subsingleton [Subsingleton E] (s : Set E) :
    ¬ IsLipschitzHypersurface s := by
  rintro ⟨e, he, -⟩; simp [Subsingleton.elim e 0] at he

/-- Every `c - c` hypersurface is nonempty. -/
theorem IsCCHypersurface.nonempty {s : Set E} (hs : IsCCHypersurface s) : s.Nonempty := by
  obtain ⟨_, -, _, _, -, -, rfl⟩ := isCCHypersurface_iff_exists_eq_range.1 hs
  exact range_nonempty _

/-- The empty set is not a `c - c` hypersurface. -/
@[simp]
theorem not_isCCHypersurface_empty : ¬ IsCCHypersurface (∅ : Set E) :=
  fun h => h.nonempty.ne_empty rfl

/-- Every Lipschitz hypersurface is nonempty. -/
theorem IsLipschitzHypersurface.nonempty {s : Set E} (hs : IsLipschitzHypersurface s) :
    s.Nonempty := by
  obtain ⟨_, -, _, _, -, rfl⟩ := isLipschitzHypersurface_iff_exists_eq_range.1 hs
  exact range_nonempty _

/-- The empty set is not a Lipschitz hypersurface. -/
@[simp]
theorem not_isLipschitzHypersurface_empty : ¬ IsLipschitzHypersurface (∅ : Set E) :=
  fun h => h.nonempty.ne_empty rfl

/-- Every affine hyperplane `{x | ⟪x, e⟫ = c}` normal to a unit vector `e` is a `c - c`
hypersurface. -/
theorem isCCHypersurface_setOf_inner_eq {e : E} (he : ‖e‖ = 1) (c : ℝ) :
    IsCCHypersurface {x : E | inner ℝ x e = c} :=
  ⟨e, he, fun _ => c, fun _ => 0, convexOn_const c convex_univ, convexOn_const 0 convex_univ,
    by simp⟩

/-- Every affine hyperplane `{x | ⟪x, e⟫ = c}` normal to a unit vector `e` is a Lipschitz
hypersurface. -/
theorem isLipschitzHypersurface_setOf_inner_eq {e : E} (he : ‖e‖ = 1) (c : ℝ) :
    IsLipschitzHypersurface {x : E | inner ℝ x e = c} :=
  ⟨e, he, 0, fun _ => c, LipschitzWith.const c, by simp⟩

/-- Translates of `c - c` hypersurfaces are `c - c` hypersurfaces. -/
theorem IsCCHypersurface.vadd {s : Set E} (hs : IsCCHypersurface s) (v : E) :
    IsCCHypersurface (v +ᵥ s) := by
  obtain ⟨e, he, f, g, hf, hg, rfl⟩ := hs
  let v₀ := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto v
  have hsub {w : ↥(ℝ ∙ e)ᗮ → ℝ} (hw : ConvexOn ℝ univ w) : ConvexOn ℝ univ (fun y => w (y - v₀)) :=
    ⟨convex_univ, fun x _ y _ a b ha hb hab => by
      have hpt : a • x + b • y - v₀ = a • (x - v₀) + b • (y - v₀) := by
        nth_rw 1 [← one_smul ℝ v₀]; rw [← hab, add_smul, smul_sub, smul_sub]; abel
      dsimp only; rw [hpt]; exact hw.2 (mem_univ _) (mem_univ _) ha hb hab⟩
  refine ⟨e, he, fun y => f (y - v₀) + inner ℝ v e, fun y => g (y - v₀),
    (hsub hf).add_const _, hsub hg, Set.ext fun x => ?_⟩
  simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub, mem_ofPred_eq,
    map_sub, inner_sub_left, v₀]
  exact ⟨fun h => by linarith, fun h => by linarith⟩

/-- Translates of Lipschitz hypersurfaces are Lipschitz hypersurfaces. -/
theorem IsLipschitzHypersurface.vadd {s : Set E} (hs : IsLipschitzHypersurface s) (v : E) :
    IsLipschitzHypersurface (v +ᵥ s) := by
  obtain ⟨e, he, K, h, hh, rfl⟩ := hs
  let v₀ := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto v
  refine ⟨e, he, K, fun y => h (y - v₀) + inner ℝ v e, ((hh.comp (LipschitzWith.id.sub
    (.const v₀))).add (.const _)).weaken (by simp), Set.ext fun x => ?_⟩
  simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub, mem_ofPred_eq,
    map_sub, inner_sub_left, v₀]
  exact ⟨fun hx => by linarith, fun hx => by linarith⟩

/-- Linear isometric equivalences preserve `c - c` hypersurfaces. -/
theorem IsCCHypersurface.image_linearIsometryEquiv {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {s : Set E} (hs : IsCCHypersurface s) (L : E ≃ₗᵢ[ℝ] F) :
    IsCCHypersurface (L '' s) := by
  obtain ⟨e, he, f, g, hf, hg, rfl⟩ := hs
  have he' : ‖L e‖ = 1 := by simp [he]
  let ψ : ↥(ℝ ∙ L e)ᗮ →ₗ[ℝ] ↥(ℝ ∙ e)ᗮ :=
    { toFun := fun y => ⟨L.symm (y : F), (Submodule.mem_orthogonal (ℝ ∙ e) _).2 fun z hz => by
        obtain ⟨c, rfl⟩ := mem_span_singleton.1 hz
        rw [real_inner_smul_left, ← L.inner_map_map, L.apply_symm_apply, real_inner_comm,
          inner_coe_orthogonal_singleton, mul_zero]⟩
      map_add' := fun y₁ y₂ => Subtype.ext (map_add L.symm (y₁ : F) (y₂ : F))
      map_smul' := fun c y => Subtype.ext (map_smul L.symm c (y : F)) }
  have hproj (z : F) : ψ ((ℝ ∙ L e)ᗮ.orthogonalProjectionOnto z) =
      (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (L.symm z) := by
    have hz := congrArg L.symm (orthogonalProjectionOnto_add_inner_smul he' z).symm
    simp only [map_add, map_smul, L.symm_apply_apply] at hz
    exact hz ▸ (orthogonalProjectionOnto_coe_add_smul e (ψ _) _).symm
  refine ⟨L e, he', f ∘ ψ, g ∘ ψ, hf.comp_linearMap ψ, hg.comp_linearMap ψ, Set.ext fun z => ?_⟩
  simp only [mem_image, mem_ofPred_eq, Function.comp_apply, hproj]
  refine ⟨?_, fun hz => ⟨L.symm z, ?_, L.apply_symm_apply z⟩⟩
  · rintro ⟨x, hx, rfl⟩; simpa [L.inner_map_map] using hx
  · rwa [← L.inner_map_map, L.apply_symm_apply]

/-- Every Lipschitz hypersurface is closed. -/
theorem IsLipschitzHypersurface.isClosed {s : Set E} (hs : IsLipschitzHypersurface s) :
    IsClosed s := by
  obtain ⟨_, -, _, _, hh, rfl⟩ := hs
  exact isClosed_eq (by fun_prop) (hh.continuous.comp (by fun_prop))

/-- Every Lipschitz hypersurface is Borel measurable. -/
theorem IsLipschitzHypersurface.measurableSet [MeasurableSpace E] [OpensMeasurableSpace E]
    {s : Set E} (hs : IsLipschitzHypersurface s) : MeasurableSet s :=
  hs.isClosed.measurableSet

end Defs

section Coordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem exists_linearIsometryEquiv_of_unit [FiniteDimensional ℝ E] {e : E}
    (he : ‖e‖ = 1) :
    ∃ (Φ : E ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) × ℝ))
      (ψ : ↥(ℝ ∙ e)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))),
      (∀ x, (Φ x).fst = ψ ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)) ∧
      (∀ x, (Φ x).snd = inner ℝ x e) := by
  have he0 : e ≠ 0 := fun h => by simp [h] at he
  have hdim : Module.finrank ℝ ↥(ℝ ∙ e)ᗮ = Module.finrank ℝ E - 1 := by
    have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ e)
    rw [finrank_span_singleton he0] at h1; omega
  let ψ : ↥(ℝ ∙ e)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    (stdOrthonormalBasis ℝ ↥(ℝ ∙ e)ᗮ).repr.trans (.piLpCongrLeft 2 ℝ ℝ (finCongr hdim))
  let Φₗ : E ≃ₗ[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) × ℝ) :=
    { toFun := fun x => .toLp 2 (ψ ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x), inner ℝ x e)
      map_add' := fun x y =>
        (WithLp.equiv 2 _).injective (Prod.ext (by simp) (by simp [inner_add_left]))
      map_smul' := fun c x =>
        (WithLp.equiv 2 _).injective (Prod.ext (by simp) (by simp [real_inner_smul_left]))
      invFun := fun p => (ψ.symm p.fst : E) + p.snd • e
      left_inv := fun x => by simpa using orthogonalProjectionOnto_add_inner_smul he x
      right_inv := fun p => (WithLp.equiv 2 _).injective <| by
        ext <;> simp [orthogonalProjectionOnto_coe_add_smul, inner_coe_add_smul_unit he] }
  refine ⟨{ Φₗ with norm_map' := fun x => ?_ }, ψ, fun _ => rfl, fun _ => rfl⟩
  dsimp only [Φₗ, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2]
  have h1 := (ℝ ∙ e).norm_sq_eq_add_norm_sq_starProjection x
  rw [starProjection_unit_singleton ℝ he, norm_smul, he, mul_one, real_inner_comm,
    Real.norm_eq_abs, sq_abs] at h1
  dsimp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [LinearIsometryEquiv.norm_map, Real.norm_eq_abs, sq_abs, h1, starProjection_apply, norm_coe,
    add_comm]

private theorem exists_unit_of_linearIsometryEquiv
    (Φ : E ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) × ℝ)) :
    ∃ (e : E) (_ : ‖e‖ = 1)
      (ψ : ↥(ℝ ∙ e)ᗮ →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))),
      (∀ x, ψ ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) = (Φ x).fst) ∧
      (∀ x, inner ℝ x e = (Φ x).snd) := by
  let p₀ : WithLp 2 (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) × ℝ) := .toLp 2 (0, 1)
  let e : E := Φ.symm p₀
  have he : ‖e‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, ← sq_eq_sq₀ (norm_nonneg _) zero_le_one,
      WithLp.prod_norm_sq_eq_of_L2]; simp [p₀]
  have hin (x : E) : inner ℝ x e = (Φ x).snd := by
    have h := Φ.inner_map_map x e
    simp only [e, Φ.apply_symm_apply] at h
    rw [← h, WithLp.prod_inner_apply]; simp [p₀]
  let ψ : ↥(ℝ ∙ e)ᗮ →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) :=
    { toFun := fun y => (Φ (y : E)).fst, map_add' := by simp, map_smul' := by simp }
  refine ⟨e, he, ψ, fun x => ?_, hin⟩
  have hx := congrArg (fun z => (Φ z).fst) (orthogonalProjectionOnto_add_inner_smul he x)
  simpa [ψ, e, p₀, map_add, map_smul] using hx

/-- **Orthonormal coordinate characterization of `c - c` hypersurfaces.** In a finite-dimensional
real inner product space `E` of dimension `d`, a subset `s ⊆ E` is a `c - c` hypersurface if and
only if in some orthonormal coordinate splitting `E ≃ₗᵢ[ℝ] ℝ^{d-1} ×₂ ℝ` it is the graph
`{x | (Φ x).snd = f (Φ x).fst - g (Φ x).fst}` of the difference of two convex functions (both sides
are false when `d = 0`). -/
theorem isCCHypersurface_iff_exists_linearIsometryEquiv [FiniteDimensional ℝ E] {s : Set E} :
    IsCCHypersurface s ↔
      ∃ (Φ : E ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) × ℝ))
        (f g : EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1)) → ℝ),
        ConvexOn ℝ univ f ∧ ConvexOn ℝ univ g ∧
        s = {x : E | (Φ x).snd = f (Φ x).fst - g (Φ x).fst} := by
  refine ⟨fun ⟨e, he, f, g, hf, hg, hs⟩ => ?_, fun ⟨Φ, f, g, hf, hg, hs⟩ => ?_⟩
  · obtain ⟨Φ, ψ, hfst, hsnd⟩ := exists_linearIsometryEquiv_of_unit he
    exact ⟨Φ, f ∘ ψ.symm, g ∘ ψ.symm, hf.comp_linearMap ψ.symm.toLinearMap,
      hg.comp_linearMap ψ.symm.toLinearMap, by rw [hs]; ext x; simp [hfst, hsnd]⟩
  · obtain ⟨e, he, ψ, hfst, hsnd⟩ := exists_unit_of_linearIsometryEquiv Φ
    exact ⟨e, he, f ∘ ψ, g ∘ ψ, hf.comp_linearMap ψ, hg.comp_linearMap ψ,
      by rw [hs]; ext x; simp [hfst, hsnd]⟩

/-- **Dimension-one characterization of `c - c` hypersurfaces.** In a one-dimensional real inner
product space, the `c - c` hypersurfaces are precisely the singletons. -/
theorem isCCHypersurface_iff_exists_eq_singleton (hdim : Module.finrank ℝ E = 1) {s : Set E} :
    IsCCHypersurface s ↔ ∃ x : E, s = {x} := by
  have : FiniteDimensional ℝ E := .of_finrank_eq_succ hdim
  have horth {e : E} (he : ‖e‖ = 1) : (ℝ ∙ e)ᗮ = ⊥ := by
    have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ e)
    rw [finrank_span_singleton (fun h => by simp [h] at he), hdim] at h1
    exact Submodule.finrank_eq_zero.1 (by omega)
  refine ⟨fun hs => ?_, fun ⟨x, hx⟩ => ?_⟩
  · obtain ⟨e, he, f, g, -, -, rfl⟩ := isCCHypersurface_iff_exists_eq_range.1 hs
    refine ⟨(f 0 - g 0) • e, Set.ext fun z => ⟨?_, by rintro rfl; exact ⟨0, by simp⟩⟩⟩
    rintro ⟨y, rfl⟩
    have hy0 : y = 0 := Subtype.ext (Submodule.mem_bot ℝ |>.1 (horth he ▸ y.2))
    simp [hy0]
  · subst hx
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    set e : E := ‖v‖⁻¹ • v
    have he : ‖e‖ = 1 := by simp [e, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
    convert isCCHypersurface_setOf_inner_eq he (inner ℝ x e) using 1
    refine Set.ext fun z => ⟨by rintro rfl; simp, fun h => ?_⟩
    have hp (w : E) : ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto w : E) = 0 :=
      Submodule.mem_bot ℝ |>.1 (horth he ▸ ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto w).2)
    have hz := orthogonalProjectionOnto_add_inner_smul he z
    have hx' := orthogonalProjectionOnto_add_inner_smul he x
    rw [hp z, zero_add] at hz; rw [hp x, zero_add] at hx'
    exact mem_singleton_iff.2 (by rw [← hz, ← hx', (h : inner ℝ z e = inner ℝ x e)])

end Coordinates

section MeasureAndLipschitz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Every `c - c` hypersurface in a finite-dimensional real inner product space is closed. -/
theorem IsCCHypersurface.isClosed {s : Set E} (hs : IsCCHypersurface s) : IsClosed s := by
  obtain ⟨_, -, _, _, hf, hg, rfl⟩ := hs
  have := continuousOn_univ.1 (hf.continuousOn isOpen_univ)
  have := continuousOn_univ.1 (hg.continuousOn isOpen_univ)
  exact isClosed_eq (by fun_prop) (by fun_prop)

/-- Every `c - c` hypersurface in a finite-dimensional real inner product space is Borel
measurable. -/
theorem IsCCHypersurface.measurableSet [MeasurableSpace E] [OpensMeasurableSpace E] {s : Set E}
    (hs : IsCCHypersurface s) : MeasurableSet s :=
  hs.isClosed.measurableSet

/-- Every `c - c` hypersurface in a finite-dimensional real inner product space is covered by
countably many Lipschitz hypersurfaces. -/
theorem IsCCHypersurface.subset_iUnion_isLipschitzHypersurface {s : Set E}
    (hs : IsCCHypersurface s) :
    ∃ t : ℕ → Set E, (∀ n, IsLipschitzHypersurface (t n)) ∧ s ⊆ ⋃ n, t n := by
  obtain ⟨e, he, f, g, hf, hg, rfl⟩ := hs
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  choose Kf f' _ hLf hff' using fun n : ℕ =>
    hf.exists_convexOn_lipschitzWith_eqOn (isCompact_closedBall (0 : ↥(ℝ ∙ e)ᗮ) n)
  choose Kg g' _ hLg hgg' using fun n : ℕ =>
    hg.exists_convexOn_lipschitzWith_eqOn (isCompact_closedBall (0 : ↥(ℝ ∙ e)ᗮ) n)
  refine ⟨fun n => {x | inner ℝ x e = (f' n - g' n) (P x)},
    fun n => ⟨e, he, Kf n + Kg n, f' n - g' n, (hLf n).sub (hLg n), rfl⟩, fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_ge ‖P x‖
  have hmem : P x ∈ closedBall (0 : ↥(ℝ ∙ e)ᗮ) n := mem_closedBall_zero_iff.2 hn
  exact mem_iUnion.2 ⟨n, by simpa [← hff' n hmem, ← hgg' n hmem] using hx⟩

/-- Every Lipschitz hypersurface has measure zero for any additive Haar measure on `E`. -/
theorem IsLipschitzHypersurface.addHaar_eq_zero [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {s : Set E} (hs : IsLipschitzHypersurface s) :
    μ s = 0 := by
  have hmeas : MeasurableSet s := hs.measurableSet
  rcases hs with ⟨e, he, _, h, _, hs_eq⟩
  let φ : E ≃L[ℝ] ↥(ℝ ∙ e)ᗮ × ℝ := LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x, inner ℝ x e)
      map_add' := fun x y => by ext <;> simp [inner_add_left]
      map_smul' := fun c x => by ext <;> simp [real_inner_smul_left]
      invFun := fun p => (p.1 : E) + p.2 • e
      left_inv := orthogonalProjectionOnto_add_inner_smul he
      right_inv := fun p => by
        ext <;> simp [orthogonalProjectionOnto_coe_add_smul, inner_coe_add_smul_unit he] }
  refine Measure.addHaar_eq_zero_of_prod_mk_preimage_image_eq_zero μ volume volume φ hmeas
    (Eventually.of_forall fun y => measure_mono_null (t := {h y}) ?_ (by simp))
  rintro r ⟨x, hx, hφx⟩
  rw [hs_eq, mem_ofPred_eq] at hx
  exact mem_singleton_iff.2 ((congrArg Prod.snd hφx : inner ℝ x e = r).symm.trans
    (hx.trans (congrArg h (congrArg Prod.fst hφx))))

/-- Every `c - c` hypersurface has measure zero for any additive Haar measure on `E`. -/
theorem IsCCHypersurface.addHaar_eq_zero [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {s : Set E} (hs : IsCCHypersurface s) :
    μ s = 0 := by
  obtain ⟨t, ht, hsub⟩ := hs.subset_iUnion_isLipschitzHypersurface
  exact measure_mono_null hsub (measure_iUnion_null fun n => (ht n).addHaar_eq_zero μ)

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
  refine ⟨(1 - θ) • p + θ • q,
    convex_subdifferential (innerₗ E) u x hp hq h1θ hθ0 (by ring), ?_, ?_⟩
  · calc ‖(1 - θ) • p + θ • q‖
        ≤ (1 - θ) * ‖p‖ + θ * ‖q‖ := (norm_add_le _ _).trans_eq
            (by rw [norm_smul, norm_smul, Real.norm_of_nonneg h1θ, Real.norm_of_nonneg hθ0])
      _ ≤ (1 - θ) * M + θ * M := by gcongr
      _ = M := by ring
  · simp only [inner_add_left, real_inner_smul_left, θ]
    have hne : inner ℝ q e - inner ℝ p e ≠ 0 := hden.ne'
    field_simp [hne]; ring

private theorem bddAbove_range_subgradient_slice {u : E → EReal} {e : E} (he : ‖e‖ = 1)
    {R M : ℝ} (hM : 0 ≤ M) (c : ℝ) {S : Set E} {x₀ : E} (hx₀S : x₀ ∈ S) (hSR : S ⊆ ball 0 R)
    (α : S → E) (hα : ∀ x : S, ‖α x‖ ≤ M)
    (hsubg : ∀ x₁ x₂ : S, (u x₁).toReal + inner ℝ ((x₂ : E) - x₁) (α x₁) ≤ (u x₂).toReal)
    (y : ↥(ℝ ∙ e)ᗮ) :
    BddAbove (range fun x₁ : S => (u x₁).toReal - c * inner ℝ (x₁ : E) e +
      inner ℝ ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (α x₁))
        (y - (ℝ ∙ e)ᗮ.orthogonalProjectionOnto x₁)) := by
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  refine ⟨(u x₀).toReal + 2 * R * M + |c| * R + M * (‖y‖ + R), forall_mem_range.2 fun x₁ => ?_⟩
  have hx₁R : ‖(x₁ : E)‖ ≤ R := (mem_ball_zero_iff.1 (hSR x₁.2)).le
  have hx₀R : ‖x₀‖ ≤ R := (mem_ball_zero_iff.1 (hSR hx₀S)).le
  have hR : 0 ≤ R := (norm_nonneg x₀).trans hx₀R
  have h2 : |inner ℝ (x₀ - (x₁ : E)) (α x₁)| ≤ 2 * R * M :=
    (abs_real_inner_le_norm _ _).trans <| (mul_le_mul
      ((norm_sub_le _ _).trans (add_le_add hx₀R hx₁R)) (hα x₁) (norm_nonneg _)
        (add_nonneg hR hR)).trans_eq (by ring)
  have h3 : |c * inner ℝ (x₁ : E) e| ≤ |c| * R := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left
      ((abs_real_inner_le_norm _ _).trans (by simp [he, hx₁R])) (abs_nonneg c)
  have h4 : inner ℝ (P (α x₁)) (y - P x₁) ≤ M * (‖y‖ + R) :=
    (real_inner_le_norm _ _).trans <| mul_le_mul
      ((norm_orthogonalProjectionOnto_apply_le _ _).trans (hα x₁))
      ((norm_sub_le _ _).trans (add_le_add le_rfl
        ((norm_orthogonalProjectionOnto_apply_le _ _).trans hx₁R))) (norm_nonneg _) hM
  linarith [hsubg x₁ ⟨x₀, hx₀S⟩, (abs_le.1 h2).1, (abs_le.1 h3).1]

private theorem exists_convexOn_eq_toReal_sub_mul_inner {u : E → EReal} {e : E} (he : ‖e‖ = 1)
    {R M : ℝ} (hM : 0 ≤ M) (c : ℝ) {S : Set E} (hS : S.Nonempty)
    (hSR : S ⊆ ball 0 R) (α : S → E)
    (hα : ∀ x : S, α x ∈ subdifferential (innerₗ E) u x ∧ ‖α x‖ ≤ M ∧ inner ℝ (α x) e = c) :
    ∃ F : ↥(ℝ ∙ e)ᗮ → ℝ, ConvexOn ℝ univ F ∧
      ∀ x : S, F ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) =
        (u x).toReal - c * inner ℝ (x : E) e := by
  have : Nonempty S := hS.to_subtype
  obtain ⟨x₀, hx₀S⟩ := hS
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  let g : S → ↥(ℝ ∙ e)ᗮ → ℝ := fun x₁ y =>
    (u x₁).toReal - c * inner ℝ (x₁ : E) e + inner ℝ (P (α x₁)) (y - P x₁)
  have hsubg (x₁ x₂ : S) : (u x₁).toReal + inner ℝ ((x₂ : E) - x₁) (α x₁) ≤ (u x₂).toReal := by
    obtain ⟨h1b, h1t, h1le⟩ := (mem_subdifferential_iff (innerₗ E)).1 (hα x₁).1
    obtain ⟨h2b, h2t, -⟩ := (mem_subdifferential_iff (innerₗ E)).1 (hα x₂).1
    have h := h1le x₂
    rw [← EReal.coe_toReal h1t h1b, ← EReal.coe_toReal h2t h2b, ← EReal.coe_add,
      EReal.coe_le_coe_iff] at h
    simpa only [innerₗ_apply_apply] using h
  have hbdd : ∀ y, BddAbove (range fun x₁ : S => g x₁ y) :=
    bddAbove_range_subgradient_slice he hM c hx₀S hSR α (fun x => (hα x).2.1) hsubg
  refine ⟨fun y => ⨆ x₁ : S, g x₁ y,
    ⟨convex_univ, fun y₁ _ y₂ _ a b ha hb hab => ciSup_le fun x₁ => ?_⟩,
    fun x => le_antisymm (ciSup_le fun x₁ => ?_)
      (by simpa [g, P] using le_ciSup (hbdd (P x)) x)⟩
  · have haff : g x₁ (a • y₁ + b • y₂) = a * g x₁ y₁ + b * g x₁ y₂ := by
      simp only [g, inner_sub_right, inner_add_right, real_inner_smul_right]
      linear_combination ((u x₁).toReal - c * inner ℝ (x₁ : E) e -
        inner ℝ (P (α x₁)) (P x₁)) * hab.symm
    exact haff.le.trans (add_le_add (mul_le_mul_of_nonneg_left (le_ciSup (hbdd y₁) x₁) ha)
      (mul_le_mul_of_nonneg_left (le_ciSup (hbdd y₂) x₁) hb))
  · have hαeq := (hα x₁).2.2 ▸ (orthogonalProjectionOnto_add_inner_smul he (α x₁)).symm
    have hdec : inner ℝ ((x : E) - x₁) (α x₁) =
        inner ℝ (P (α x₁)) (P x - P x₁) + c * inner ℝ ((x : E) - x₁) e := by
      nth_rw 1 [hαeq]
      rw [inner_add_right, real_inner_smul_right, ← inner_orthogonalProjectionOnto_eq_of_mem_right,
        map_sub, real_inner_comm (P (α x₁))]
    have hle := hsubg x₁ x
    dsimp only [g]; simp only [inner_sub_left] at hdec hle; linarith

/-- **Single-slice subdifferential separation lies in a `c - c` hypersurface.** In any real inner
product space `E`, for any `u : E → EReal`, unit vector `e`, `a < b`, and `R, M : ℝ`, the set of
points `x ∈ ball 0 R` admitting subgradients `p, q ∈ ∂u(x)` of norm at most `M` with `⟪p, e⟫ ≤ a`
and `b ≤ ⟪q, e⟫` is contained in a single `c - c` hypersurface. -/
theorem exists_isCCHypersurface_of_subdifferential_separation {u : E → EReal} {e : E}
    (he : ‖e‖ = 1) {a b : ℝ} (hab : a < b) (R M : ℝ) :
    ∃ s : Set E, IsCCHypersurface s ∧
      {x : E | x ∈ ball 0 R ∧ ∃ p ∈ subdifferential (innerₗ E) u x,
        ∃ q ∈ subdifferential (innerₗ E) u x,
          ‖p‖ ≤ M ∧ ‖q‖ ≤ M ∧ inner ℝ p e ≤ a ∧ b ≤ inner ℝ q e} ⊆ s := by
  set S := {x : E | x ∈ ball 0 R ∧ ∃ p ∈ subdifferential (innerₗ E) u x,
    ∃ q ∈ subdifferential (innerₗ E) u x,
      ‖p‖ ≤ M ∧ ‖q‖ ≤ M ∧ inner ℝ p e ≤ a ∧ b ≤ inner ℝ q e}
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · exact ⟨{x | inner ℝ x e = 0}, isCCHypersurface_setOf_inner_eq he 0, hS0 ▸ empty_subset _⟩
  choose α hα using fun x : S =>
    let ⟨_, _, hp, _, hq, hpM, hqM, hpa, hbq⟩ := x.2
    exists_mem_subdifferential_inner_eq hp hq hpM hqM hpa (hab.le.trans hbq)
  choose β hβ using fun x : S =>
    let ⟨_, _, hp, _, hq, hpM, hqM, hpa, hbq⟩ := x.2
    exists_mem_subdifferential_inner_eq hp hq hpM hqM (hpa.trans hab.le) hbq
  have hM : 0 ≤ M := (norm_nonneg _).trans (hα ⟨hSne.some, hSne.some_mem⟩).2.1
  obtain ⟨Fa, hFa_conv, hFa⟩ :=
    exists_convexOn_eq_toReal_sub_mul_inner he hM a hSne (fun _ hx => hx.1) α hα
  obtain ⟨Fb, hFb_conv, hFb⟩ :=
    exists_convexOn_eq_toReal_sub_mul_inner he hM b hSne (fun _ hx => hx.1) β hβ
  have hba : 0 < b - a := sub_pos.2 hab
  refine ⟨_, ⟨e, he, (b - a)⁻¹ • Fa, (b - a)⁻¹ • Fb, hFa_conv.smul (inv_nonneg.2 hba.le),
    hFb_conv.smul (inv_nonneg.2 hba.le), rfl⟩, fun x hx => ?_⟩
  simp only [mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, hFa ⟨x, hx⟩, hFb ⟨x, hx⟩]
  have hne : b - a ≠ 0 := hba.ne'
  field_simp [hne]; ring

end SubdifferentialSeparation

section SubdifferentialCover

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Subdifferential singular locus is covered by countably many `c - c` hypersurfaces.** For any
extended-real function `u : E → EReal` on a finite-dimensional real inner product space, the set of
points `x` at which `∂u(x)` has more than one element is covered by a countable family of `c - c`
hypersurfaces. -/
theorem exists_countable_isCCHypersurface_cover_not_subsingleton_subdifferential (u : E → EReal) :
    ∃ C : Set (Set E), C.Countable ∧ (∀ s ∈ C, IsCCHypersurface s) ∧
      {x : E | ¬ (subdifferential (innerₗ E) u x).Subsingleton} ⊆ ⋃₀ C := by
  let b := stdOrthonormalBasis ℝ E
  let I := {t : Fin (Module.finrank ℝ E) × ℚ × ℚ × ℕ × ℕ | t.2.1 < t.2.2.1}
  have : Countable I := Subtype.countable
  choose s hs hsub using fun t : I =>
    exists_isCCHypersurface_of_subdifferential_separation (u := u) (b.norm_eq_one t.1.1)
      (Rat.cast_lt.2 t.2) ((t.1.2.2.2.1 : ℝ) + 1) (t.1.2.2.2.2 : ℝ)
  refine ⟨range s, countable_range s, forall_mem_range.2 hs, fun x hx => ?_⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := Set.not_subsingleton_iff.1 hx
  have ⟨i, hi⟩ : ∃ i, inner ℝ p (b i) ≠ inner ℝ q (b i) := by
    by_contra! hall
    exact hpq <| b.repr.injective <| by
      ext i; simpa only [OrthonormalBasis.repr_apply_apply, real_inner_comm] using hall i
  have hstep {p' q' : E} (hp' : p' ∈ subdifferential (innerₗ E) u x)
      (hq' : q' ∈ subdifferential (innerₗ E) u x) (hlt : inner ℝ p' (b i) < inner ℝ q' (b i)) :
      x ∈ ⋃₀ range s := by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    obtain ⟨M, hM⟩ := exists_nat_ge (max ‖p'‖ ‖q'‖)
    obtain ⟨r₁, hr₁, hr₂⟩ := exists_rat_btwn hlt
    obtain ⟨r₂, hr₃, hr₄⟩ := exists_rat_btwn hr₂
    let idx : I := ⟨(i, r₁, r₂, N, M), Rat.cast_lt.1 hr₃⟩
    exact mem_sUnion.2 ⟨s idx, mem_range_self idx, hsub idx
      ⟨mem_ball_zero_iff.2 (hN.trans (lt_add_one _)), p', hp', q', hq',
        (le_max_left _ _).trans hM, (le_max_right _ _).trans hM, hr₁.le, hr₄.le⟩⟩
  exact (lt_or_gt_of_ne hi).elim (hstep hp hq) (hstep hq hp)

/-- For any extended-real function `u : E → EReal` with convex real epigraph, the set of interior
points of its effective domain at which `u.toReal` is not differentiable is covered by countably
many `c - c` hypersurfaces. -/
theorem exists_countable_isCCHypersurface_cover_not_differentiableAt_toReal {u : E → EReal}
    (hu : Convex ℝ {p : E × ℝ | u p.1 ≤ p.2}) :
    ∃ C : Set (Set E), C.Countable ∧ (∀ s ∈ C, IsCCHypersurface s) ∧
      {x : E | x ∈ interior {z | u z ≠ ⊤} ∧ ¬ DifferentiableAt ℝ (fun z => (u z).toReal) x} ⊆
        ⋃₀ C := by
  obtain ⟨C, hC, hs, hsub⟩ :=
    exists_countable_isCCHypersurface_cover_not_subsingleton_subdifferential u
  refine ⟨C, hC, hs, fun x ⟨hx, hnd⟩ => hsub ?_⟩
  rwa [mem_ofPred_eq, ← differentiableAt_toReal_iff_subsingleton_subdifferential hu hx]

end SubdifferentialCover

private theorem not_differentiableAt_of_add_sub_two_mul_ge {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {u : E → ℝ} {x v : E} {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (h : ∀ t ∈ Ioo 0 δ, c * t ≤ u (x + t • v) + u (x - t • v) - 2 * u x) :
    ¬ DifferentiableAt ℝ u x := fun hd => by
  have h₁ : HasDerivAt (fun t : ℝ => u (x + t • v)) (fderiv ℝ u x v) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq 0
      (by simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x) (by simp)
  have h₂ : HasDerivAt (fun t : ℝ => u (x - t • v)) (-fderiv ℝ u x v) 0 :=
    map_neg (fderiv ℝ u x) v ▸ hd.hasFDerivAt.comp_hasDerivAt_of_eq 0
      (by simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_sub x) (by simp)
  have hsum : HasDerivAt (fun t : ℝ => u (x + t • v) + u (x - t • v)) 0 0 := by
    convert h₁.add h₂ using 1; exact (add_neg_cancel _).symm
  refine not_le_of_gt hc (ge_of_tendsto hsum.tendsto_slope_zero_right ?_)
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
  simp only [zero_add, zero_smul, add_zero, sub_zero, smul_eq_mul]
  rw [le_inv_mul_iff₀ ht.1, mul_comm]; linarith [h t ht]

section ConvexFrontier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_countable_isCCHypersurface_cover_closure_of_not_nonempty_interior {K : Set E}
    (hK : Convex ℝ K) (hint : ¬ (interior K).Nonempty) :
    ∃ C : Set (Set E), C.Countable ∧ (∀ s ∈ C, IsCCHypersurface s) ∧ closure K ⊆ ⋃₀ C := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨∅, countable_empty, by simp, by simp⟩
  have hspan : affineSpan ℝ K ≠ ⊤ := mt hK.interior_nonempty_iff_affineSpan_eq_top.2 hint
  have hdir : (affineSpan ℝ K).direction ≠ ⊤ :=
    mt (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨x₀, subset_affineSpan ℝ K hx₀⟩).1 hspan
  obtain ⟨v, hv_mem, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (mt Submodule.orthogonal_eq_bot_iff.1 hdir)
  let e : E := ‖v‖⁻¹ • v
  have he : ‖e‖ = 1 := by simp [e, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)]
  have he_mem : e ∈ (affineSpan ℝ K).directionᗮ := Submodule.smul_mem _ _ hv_mem
  let H : Set E := {x | inner ℝ x e = inner ℝ x₀ e}
  refine ⟨{H}, countable_singleton H, by simpa using isCCHypersurface_setOf_inner_eq he _, ?_⟩
  simpa using closure_minimal (fun x hx => by
    rw [mem_ofPred_eq, ← sub_eq_zero, ← inner_sub_left]
    exact (Submodule.mem_orthogonal _ _).1 he_mem _
      (AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ K hx)
        (subset_affineSpan ℝ K hx₀))) (isClosed_eq (by fun_prop) continuous_const)

/-- **Frontier of a convex set is covered by countably many `c - c` hypersurfaces.** For any convex
subset `K` of a finite-dimensional real inner product space `E`, `frontier K` (and hence also
`K \ interior K`) is covered by a countable family of `c - c` hypersurfaces. -/
theorem _root_.Convex.exists_countable_isCCHypersurface_cover_frontier {K : Set E}
    (hK : Convex ℝ K) :
    ∃ C : Set (Set E), C.Countable ∧ (∀ s ∈ C, IsCCHypersurface s) ∧ frontier K ⊆ ⋃₀ C := by
  by_cases hint : (interior K).Nonempty
  · obtain ⟨z₀, hz₀⟩ := hint
    let K₀ : Set E := (z₀ + ·) ⁻¹' K
    have hK₀ : Convex ℝ K₀ := hK.translate_preimage_right z₀
    have hnhds : K₀ ∈ 𝓝 (0 : E) := (continuous_const.add continuous_id).continuousAt
      |>.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hz₀)
    have habs : Absorbent ℝ K₀ := absorbent_nhds_zero hnhds
    let u : E → ℝ := fun z => max (gauge K₀ (z - z₀)) 1
    have hu : ConvexOn ℝ univ u :=
      ConvexOn.sup ⟨convex_univ, fun x _ y _ a b ha hb hab => by
        have hpt : a • x + b • y - z₀ = a • (x - z₀) + b • (y - z₀) := by
          nth_rw 1 [← one_smul ℝ z₀]; rw [← hab, add_smul, smul_sub, smul_sub]; abel
        dsimp only; rw [hpt]; exact (gauge_add_le hK₀ habs _ _).trans_eq (by
          rw [gauge_smul_of_nonneg ha, gauge_smul_of_nonneg hb, smul_eq_mul, smul_eq_mul])⟩
        (convexOn_const 1 convex_univ)
    obtain ⟨C, hC, hs, hsub⟩ :=
      exists_countable_isCCHypersurface_cover_not_differentiableAt_toReal
        (u := fun z => (u z : EReal)) (by simpa using convexOn_iff_convex_epigraph_ite.1 hu)
    refine ⟨C, hC, hs, fun x hx => hsub ⟨by simp, ?_⟩⟩
    simp only [EReal.toReal_coe]
    have hx₀ : x - z₀ ∈ frontier K₀ := by
      have heq : frontier K₀ = (z₀ + ·) ⁻¹' frontier K :=
        ((Homeomorph.addLeft z₀).preimage_frontier K).symm
      simpa [heq, sub_eq_neg_add] using hx
    have hg1 : gauge K₀ (x - z₀) = 1 := (gauge_eq_one_iff_mem_frontier hK₀ hnhds).2 hx₀
    refine not_differentiableAt_of_add_sub_two_mul_ge (v := x - z₀) zero_lt_one zero_lt_one
      fun t ht => ?_
    have hp : gauge K₀ (x + t • (x - z₀) - z₀) = 1 + t := by
      rw [show x + t • (x - z₀) - z₀ = (1 + t) • (x - z₀) by rw [add_smul, one_smul]; abel,
        gauge_smul_of_nonneg (by linarith [ht.1]), smul_eq_mul, hg1, mul_one]
    have hm : gauge K₀ (x - t • (x - z₀) - z₀) = 1 - t := by
      rw [show x - t • (x - z₀) - z₀ = (1 - t) • (x - z₀) by rw [sub_smul, one_smul]; abel,
        gauge_smul_of_nonneg (by linarith [ht.2]), smul_eq_mul, hg1, mul_one]
    simp only [u, hp, hm, hg1, max_eq_left (by linarith [ht.1] : (1 : ℝ) ≤ 1 + t),
      max_eq_right (by linarith [ht.1] : 1 - t ≤ 1), max_self]
    linarith
  · obtain ⟨C, hC, hs, hcl⟩ :=
      exists_countable_isCCHypersurface_cover_closure_of_not_nonempty_interior hK hint
    exact ⟨C, hC, hs, frontier_subset_closure.trans hcl⟩

end ConvexFrontier

private theorem norm_le_of_forall_add_inner_le_of_lipschitzWith {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ψ : E → ℝ} {K : ℝ≥0} (hlip : LipschitzWith K ψ) {T : E → E}
    (hT : ∀ x z, ψ x + inner ℝ (z - x) (T x) ≤ ψ z) (x : E) : ‖T x‖ ≤ K := by
  by_cases h0 : T x = 0
  · simp [h0]
  have hpos : 0 < ‖T x‖ := norm_pos_iff.2 h0
  have h1 := hT x (x + T x)
  rw [add_sub_cancel_left, real_inner_self_eq_norm_sq] at h1
  have h2 := hlip.dist_le_mul (x + T x) x
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at h2
  nlinarith [(le_abs_self _).trans h2]

private theorem convexOn_and_lipschitzWith_max_orthogonalProjection {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e : E} (he : ‖e‖ = 1)
    [(ℝ ∙ e)ᗮ.HasOrthogonalProjection] {Lf Lg : ℝ≥0} {f' g' : ↥(ℝ ∙ e)ᗮ → ℝ}
    (hf' : ConvexOn ℝ univ f') (hg' : ConvexOn ℝ univ g')
    (hLf' : LipschitzWith Lf f') (hLg' : LipschitzWith Lg g') :
    ConvexOn ℝ univ (fun x : E => max (f' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x))
      (g' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) + inner ℝ x e)) ∧
    LipschitzWith (max Lf (Lg + 1)) (fun x : E => max (f' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x))
      (g' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) + inner ℝ x e)) := by
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  have hlin : ConvexOn ℝ univ (fun x : E => inner ℝ x e) :=
    ⟨convex_univ, fun x _ y _ a b _ _ _ => by simp [inner_add_left, real_inner_smul_left]⟩
  have hlipP : LipschitzWith 1 P := Submodule.lipschitzWith_orthogonalProjectionOnto _
  have hlip_in : LipschitzWith 1 (fun x : E => inner ℝ x e) :=
    LipschitzWith.mk_one fun x₁ x₂ => by
      rw [Real.dist_eq, ← inner_sub_left, dist_eq_norm]
      exact (abs_real_inner_le_norm _ _).trans_eq (by rw [he, mul_one])
  refine ⟨(hf'.comp_linearMap P.toLinearMap).sup ((hg'.comp_linearMap P.toLinearMap).add hlin),
    ((hLf'.comp hlipP).weaken (by simp)).max
      (((hLg'.comp hlipP).weaken (by simp) : LipschitzWith Lg (fun x => g' (P x))).add hlip_in)⟩

private theorem add_inner_subgradient_branch_le_max {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e : E) [(ℝ ∙ e)ᗮ.HasOrthogonalProjection]
    {f' g' : ↥(ℝ ∙ e)ᗮ → ℝ} {Gf Gg : ↥(ℝ ∙ e)ᗮ → ↥(ℝ ∙ e)ᗮ}
    (hGf : ∀ y₁ y₂, f' y₁ + inner ℝ (y₂ - y₁) (Gf y₁) ≤ f' y₂)
    (hGg : ∀ y₁ y₂, g' y₁ + inner ℝ (y₂ - y₁) (Gg y₁) ≤ g' y₂) :
    let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
    let ψ : E → ℝ := fun x => max (f' (P x)) (g' (P x) + inner ℝ x e)
    (∀ x z, g' (P x) + inner ℝ x e ≤ f' (P x) →
      ψ x + inner ℝ (z - x) (Gf (P x) : E) ≤ ψ z) ∧
    (∀ x z, f' (P x) ≤ g' (P x) + inner ℝ x e →
      ψ x + inner ℝ (z - x) ((Gg (P x) : E) + e) ≤ ψ z) := by
  intro P ψ
  refine ⟨fun x z hx => ?_, fun x z hx => ?_⟩
  · dsimp only [ψ]
    rw [max_eq_left hx, ← inner_orthogonalProjectionOnto_eq_of_mem_right, map_sub]
    exact (hGf (P x) (P z)).trans (le_max_left _ _)
  · dsimp only [ψ]
    rw [max_eq_right hx, inner_add_right, ← inner_orthogonalProjectionOnto_eq_of_mem_right,
      map_sub, inner_sub_left z x e]
    linarith [(add_le_add_left (hGg (P x) (P z)) (inner ℝ z e)).trans (le_max_right (f' (P z)) _)]

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
  refine ⟨fun x => if u₂ x ≤ u₁ x then b₁ x else b₂ x,
    fun x => if u₁ x ≤ u₂ x then b₂ x else b₁ x,
    Measurable.ite (isClosed_le hu₂ hu₁).measurableSet hb₁ hb₂,
    Measurable.ite (isClosed_le hu₁ hu₂).measurableSet hb₂ hb₁,
    fun x z => ?_, fun x z => ?_, fun x heq => by simp [heq]⟩
  · dsimp only; split_ifs with hx
    exacts [h₁ x z hx, h₂ x z (le_of_not_ge hx)]
  · dsimp only; split_ifs with hx
    exacts [h₂ x z hx, h₁ x z (le_of_not_ge hx)]

section Zajicek

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Lipschitz convex corner potential along a bounded piece of a `c - c` hypersurface.** Given a
`c - c` hypersurface `s ⊆ E` and `R : ℝ`, there exist `K : ℝ≥0`, a unit vector `e : E`, and a
`K`-Lipschitz convex function `ψ : E → ℝ` with `ψ 0 = 0` and unit second-difference slope
`ψ (x + t • e) + ψ (x - t • e) - 2 * ψ x = t` for every `x ∈ s ∩ closedBall 0 R` and `t ≥ 0`. -/
theorem IsCCHypersurface.exists_convexOn_lipschitzWith_corner {s : Set E}
    (hs : IsCCHypersurface s) (R : ℝ) :
    ∃ (K : ℝ≥0) (e : E) (_ : ‖e‖ = 1) (ψ : E → ℝ),
      ConvexOn ℝ univ ψ ∧ ψ 0 = 0 ∧ LipschitzWith K ψ ∧
      ∀ x ∈ s ∩ closedBall 0 R, ∀ t : ℝ, 0 ≤ t →
        ψ (x + t • e) + ψ (x - t • e) - 2 * ψ x = t := by
  obtain ⟨e, he, f, g, hf, hg, hs_eq⟩ := hs
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  obtain ⟨Lf, f', hf', hLf', hff'⟩ :=
    hf.exists_convexOn_lipschitzWith_eqOn (isCompact_closedBall (0 : ↥(ℝ ∙ e)ᗮ) (max R 0))
  obtain ⟨Lg, g', hg', hLg', hgg'⟩ :=
    hg.exists_convexOn_lipschitzWith_eqOn (isCompact_closedBall (0 : ↥(ℝ ∙ e)ᗮ) (max R 0))
  obtain ⟨hconv₀, hlip₀⟩ :=
    convexOn_and_lipschitzWith_max_orthogonalProjection he hf' hg' hLf' hLg'
  let ψ : E → ℝ := fun x => max (f' (P x)) (g' (P x) + inner ℝ x e) - max (f' 0) (g' 0)
  refine ⟨max Lf (Lg + 1), e, he, ψ, hconv₀.add_const (-max (f' 0) (g' 0)), by simp [ψ, P],
    (hlip₀.sub (LipschitzWith.const _)).weaken (by simp), fun x ⟨hxs, hxR⟩ t ht => ?_⟩
  have hPx : P x ∈ closedBall (0 : ↥(ℝ ∙ e)ᗮ) (max R 0) :=
    mem_closedBall_zero_iff.2 ((norm_orthogonalProjectionOnto_apply_le _ x).trans
      ((mem_closedBall_zero_iff.1 hxR).trans (le_max_left R 0)))
  have heq : g' (P x) + inner ℝ x e = f' (P x) := by
    rw [hs_eq, mem_ofPred_eq] at hxs; rw [← hff' hPx, ← hgg' hPx, hxs]; ring
  have hPe : P e = 0 := orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero e
  have hin_add : inner ℝ (x + t • e) e = inner ℝ x e + t := by
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he, one_pow, mul_one]
  have hin_sub : inner ℝ (x - t • e) e = inner ℝ x e - t := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he, one_pow, mul_one]
  simp only [ψ, map_add, map_sub, map_smul, hPe, smul_zero, add_zero, sub_zero, hin_add, hin_sub]
  rw [show g' (P x) + (inner ℝ x e + t) = f' (P x) + t by linarith,
    show g' (P x) + (inner ℝ x e - t) = f' (P x) - t by linarith, heq,
    max_eq_right (by linarith : f' (P x) ≤ f' (P x) + t),
    max_eq_left (by linarith : f' (P x) - t ≤ f' (P x)), max_self]
  ring

/-- **Borel measurable subgradient splitting along a `c - c` hypersurface.** Given a `c - c`
hypersurface `s ⊆ E` and `R : ℝ`, there exist `K : ℝ≥0`, a `K`-Lipschitz convex function
`ψ : E → ℝ`, and two Borel measurable maps `T₁, T₂ : E → E` bounded in norm by `K` that are
subgradients of `ψ` everywhere and satisfy `T₁ x ≠ T₂ x` at every `x ∈ s ∩ closedBall 0 R`. -/
theorem IsCCHypersurface.exists_convexOn_lipschitzWith_measurable_subgradients
    [MeasurableSpace E] [BorelSpace E] {s : Set E} (hs : IsCCHypersurface s) (R : ℝ) :
    ∃ (K : ℝ≥0) (ψ : E → ℝ) (T₁ T₂ : E → E),
      ConvexOn ℝ univ ψ ∧ LipschitzWith K ψ ∧ Measurable T₁ ∧ Measurable T₂ ∧
      (∀ x z, ψ x + inner ℝ (z - x) (T₁ x) ≤ ψ z) ∧
      (∀ x z, ψ x + inner ℝ (z - x) (T₂ x) ≤ ψ z) ∧
      (∀ x, ‖T₁ x‖ ≤ K) ∧ (∀ x, ‖T₂ x‖ ≤ K) ∧
      (∀ x ∈ s ∩ closedBall 0 R, T₁ x ≠ T₂ x) := by
  obtain ⟨e, he, f, g, hf, hg, hs_eq⟩ := hs
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  obtain ⟨Lf, f', hf', hLf', hff'⟩ :=
    hf.exists_convexOn_lipschitzWith_eqOn (isCompact_closedBall (0 : ↥(ℝ ∙ e)ᗮ) (max R 0))
  obtain ⟨Lg, g', hg', hLg', hgg'⟩ :=
    hg.exists_convexOn_lipschitzWith_eqOn (isCompact_closedBall (0 : ↥(ℝ ∙ e)ᗮ) (max R 0))
  obtain ⟨Gf, hGf_meas, hGf⟩ := hf'.exists_measurable_forall_add_inner_le
  obtain ⟨Gg, hGg_meas, hGg⟩ := hg'.exists_measurable_forall_add_inner_le
  obtain ⟨hconv, hlip⟩ := convexOn_and_lipschitzWith_max_orthogonalProjection he hf' hg' hLf' hLg'
  obtain ⟨hsub₁, hsub₂⟩ := add_inner_subgradient_branch_le_max e hGf hGg
  obtain ⟨T₁, T₂, hT₁m, hT₂m, hT₁, hT₂, hTeq⟩ :=
    exists_measurable_piecewise_subgradient_max (hLf'.continuous.comp P.continuous)
      ((hLg'.continuous.comp P.continuous).add (by fun_prop))
      (measurable_subtype_coe.comp (hGf_meas.comp P.measurable))
      ((measurable_subtype_coe.comp (hGg_meas.comp P.measurable)).add measurable_const) hsub₁ hsub₂
  refine ⟨max Lf (Lg + 1), _, T₁, T₂, hconv, hlip, hT₁m, hT₂m, hT₁, hT₂,
    norm_le_of_forall_add_inner_le_of_lipschitzWith hlip hT₁,
    norm_le_of_forall_add_inner_le_of_lipschitzWith hlip hT₂, fun x ⟨hxs, hxR⟩ hEq => ?_⟩
  have hPx : P x ∈ closedBall (0 : ↥(ℝ ∙ e)ᗮ) (max R 0) :=
    mem_closedBall_zero_iff.2 ((norm_orthogonalProjectionOnto_apply_le _ x).trans
      ((mem_closedBall_zero_iff.1 hxR).trans (le_max_left R 0)))
  obtain ⟨h₁, h₂⟩ := hTeq x (by
    dsimp only [Function.comp_apply, Pi.add_apply]
    rw [hs_eq, mem_ofPred_eq] at hxs; rw [← hff' hPx, ← hgg' hPx, hxs]; ring)
  have hin₁ : inner ℝ (T₁ x) e = 0 := h₁ ▸ inner_coe_orthogonal_singleton e (Gf (P x))
  have hin₂ : inner ℝ (T₂ x) e = 1 := by
    simp [h₂, inner_add_left, inner_coe_orthogonal_singleton, he]
  linarith [congrArg (inner ℝ · e) hEq]

end Zajicek

private theorem summable_and_convexOn_tsum_weighted {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : ℕ → ℝ≥0} {ψ : ℕ → E → ℝ}
    (hconv : ∀ m, ConvexOn ℝ univ (ψ m)) (hψ0 : ∀ m, ψ m 0 = 0)
    (hlip : ∀ m, LipschitzWith (K m) (ψ m)) :
    let w : ℕ → ℝ := fun m => (1 / 2 : ℝ) ^ (m + 1) / ((K m : ℝ) + 1)
    (∀ x, Summable (fun m => w m * ψ m x)) ∧
      ConvexOn ℝ univ (fun x => ∑' m, w m * ψ m x) := by
  intro w
  have hw_pos (m : ℕ) : 0 < w m := by positivity
  have hterm_le (x : E) (m : ℕ) : |w m * ψ m x| ≤ (1 / 2 : ℝ) ^ (m + 1) * ‖x‖ := by
    rw [abs_mul, abs_of_pos (hw_pos m)]
    have hd : |ψ m x| ≤ (K m : ℝ) * ‖x‖ := by
      simpa [hψ0 m, Real.dist_eq, dist_zero_right] using (hlip m).dist_le_mul x 0
    have hK : (K m : ℝ) + 1 ≠ 0 := by positivity
    calc w m * |ψ m x| ≤ w m * (((K m : ℝ) + 1) * ‖x‖) := mul_le_mul_of_nonneg_left
            (hd.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))) (hw_pos m).le
      _ = (1 / 2 : ℝ) ^ (m + 1) * ‖x‖ := by dsimp [w]; field_simp [hK]
  have hsum (x : E) : Summable (fun m => w m * ψ m x) :=
    Summable.of_norm_bounded (((summable_geometric_two.mul_left (1 / 2 : ℝ)).congr
      fun m => by ring).mul_right ‖x‖) (hterm_le x)
  refine ⟨hsum, convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  refine (Summable.tsum_le_tsum (fun m => ?_) (hsum (a • x + b • y))
    (((hsum x).mul_left a).add ((hsum y).mul_left b))).trans_eq ?_
  · have hc := (hconv m).2 (mem_univ x) (mem_univ y) ha hb hab
    simp only [smul_eq_mul] at hc
    linarith [mul_le_mul_of_nonneg_left hc (hw_pos m).le]
  · simp only [smul_eq_mul, Summable.tsum_add ((hsum x).mul_left a) ((hsum y).mul_left b),
      tsum_mul_left]

section ZajicekTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_convexOn_subset_not_differentiableAt_of_seq (s : ℕ → Set E)
    (hs : ∀ n, IsCCHypersurface (s n)) :
    ∃ u : E → ℝ, ConvexOn ℝ univ u ∧ (⋃ n, s n) ⊆ {x | ¬ DifferentiableAt ℝ u x} := by
  choose K e _ ψ hconv hψ0 hlip hcorner using fun m : ℕ =>
    (hs m.unpair.1).exists_convexOn_lipschitzWith_corner (m.unpair.2 : ℝ)
  let w : ℕ → ℝ := fun m => (1 / 2 : ℝ) ^ (m + 1) / ((K m : ℝ) + 1)
  have hw_pos (m : ℕ) : 0 < w m := by positivity
  obtain ⟨hsum, hu_conv⟩ := summable_and_convexOn_tsum_weighted hconv hψ0 hlip
  let u : E → ℝ := fun x => ∑' m, w m * ψ m x
  refine ⟨u, hu_conv, fun x hx => ?_⟩
  obtain ⟨n, hxn⟩ := mem_iUnion.1 hx
  obtain ⟨R, hR⟩ := exists_nat_ge ‖x‖
  let m₀ := Nat.pair n R
  have hm₀ : x ∈ s m₀.unpair.1 ∩ closedBall 0 (m₀.unpair.2 : ℝ) := by
    simpa only [m₀, Nat.unpair_pair] using ⟨hxn, mem_closedBall_zero_iff.2 hR⟩
  refine not_differentiableAt_of_add_sub_two_mul_ge (v := e m₀) (hw_pos m₀) zero_lt_one
    fun t ht => ?_
  have hs₁ := hsum (x + t • e m₀); have hs₂ := hsum (x - t • e m₀); have hs₃ := (hsum x).mul_left 2
  have hs_diff :
      Summable (fun m => w m * (ψ m (x + t • e m₀) + ψ m (x - t • e m₀) - 2 * ψ m x)) :=
    ((hs₁.add hs₂).sub hs₃).congr fun m => by ring
  have hdiff : u (x + t • e m₀) + u (x - t • e m₀) - 2 * u x =
      ∑' m, w m * (ψ m (x + t • e m₀) + ψ m (x - t • e m₀) - 2 * ψ m x) := by
    dsimp only [u]
    rw [← Summable.tsum_add hs₁ hs₂, ← tsum_mul_left, ← Summable.tsum_sub (hs₁.add hs₂) hs₃]
    congr 1; ext m; ring
  rw [hdiff]; nth_rw 1 [← hcorner m₀ x hm₀ t ht.1.le]
  refine Summable.le_tsum hs_diff m₀ fun m _ => mul_nonneg (hw_pos m).le ?_
  have hmid := (hconv m).2 (mem_univ (x + t • e m₀)) (mem_univ (x - t • e m₀))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [show (1 / 2 : ℝ) • (x + t • e m₀) + (1 / 2 : ℝ) • (x - t • e m₀) = x by
    rw [smul_add, smul_sub]; module] at hmid
  simp only [smul_eq_mul] at hmid; linarith

/-- **Zajíček's theorem.** In a finite-dimensional real inner product space `E`, a subset `A ⊆ E`
is contained in the nondifferentiability locus of some real function `u` convex on `E` if and only
if `A` can be covered by countably many `c - c` hypersurfaces. -/
theorem exists_convexOn_subset_not_differentiableAt_iff {A : Set E} :
    (∃ u : E → ℝ, ConvexOn ℝ univ u ∧ A ⊆ {x | ¬ DifferentiableAt ℝ u x}) ↔
      ∃ C : Set (Set E), C.Countable ∧ (∀ s ∈ C, IsCCHypersurface s) ∧ A ⊆ ⋃₀ C := by
  refine ⟨fun ⟨u, hu, hA⟩ => ?_, fun ⟨C, hC, hs, hA⟩ => ?_⟩
  · obtain ⟨C, hC, hs, hsub⟩ :=
      exists_countable_isCCHypersurface_cover_not_differentiableAt_toReal
        (u := fun z => (u z : EReal)) (by simpa using convexOn_iff_convex_epigraph_ite.1 hu)
    exact ⟨C, hC, hs, hA.trans fun x hx => hsub ⟨by simp, by simpa using hx⟩⟩
  · rcases C.eq_empty_or_nonempty with rfl | hCne
    · simp only [sUnion_empty, subset_empty_iff] at hA
      exact ⟨0, convexOn_const 0 convex_univ, hA ▸ empty_subset _⟩
    · obtain ⟨s, rfl⟩ := hC.exists_eq_range hCne
      obtain ⟨u, hu, hsub⟩ :=
        exists_convexOn_subset_not_differentiableAt_of_seq s (forall_mem_range.1 hs)
      exact ⟨u, hu, hA.trans (sUnion_range s ▸ hsub)⟩

/-- **Zajíček's theorem (`ℕ`-indexed sequence form).** In a nontrivial finite-dimensional real inner
product space `E`, a subset `A ⊆ E` is contained in the nondifferentiability locus of some convex
function `u : E → ℝ` if and only if `A` is covered by a sequence `s : ℕ → Set E` of `c - c`
hypersurfaces. -/
theorem exists_convexOn_subset_not_differentiableAt_iff_nat [Nontrivial E] {A : Set E} :
    (∃ u : E → ℝ, ConvexOn ℝ univ u ∧ A ⊆ {x | ¬ DifferentiableAt ℝ u x}) ↔
      ∃ s : ℕ → Set E, (∀ n, IsCCHypersurface (s n)) ∧ A ⊆ ⋃ n, s n := by
  rw [exists_convexOn_subset_not_differentiableAt_iff]
  refine ⟨fun ⟨C, hC, hs, hA⟩ => ?_, fun ⟨s, hs, hA⟩ =>
    ⟨range s, countable_range s, forall_mem_range.2 hs, sUnion_range s ▸ hA⟩⟩
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have he : ‖‖v‖⁻¹ • v‖ = 1 := by simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
    simp only [sUnion_empty, subset_empty_iff] at hA
    exact ⟨fun _ => {x | inner ℝ x (‖v‖⁻¹ • v) = 0},
      fun _ => isCCHypersurface_setOf_inner_eq he 0, hA ▸ empty_subset _⟩
  · obtain ⟨s, rfl⟩ := hC.exists_eq_range hCne
    exact ⟨s, forall_mem_range.1 hs, sUnion_range s ▸ hA⟩

end ZajicekTheorem

end TauCeti
