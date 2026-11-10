/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.StarImmersion

import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Slope
import TauCeti.Analysis.Convex.StdSimplex

/-!
# Small perturbations of embeddings of complexes

Let `f : |K| → E` be a map of the realization of a complex on a finite vertex type into a normed
space which is `Cⁿ` on every closed simplex, `1 ≤ n`. Then `f` is a star immersion (Munkres'
immersion of a complex) exactly when it separates nearby points uniformly in barycentric
coordinates: `c * ‖x - y‖ ≤ ‖f x - f y‖` whenever `‖x - y‖ < δ`, for some `c > 0` and `δ > 0`
(`TauCeti.isStarImmersion_iff_exists_pos_mul_norm_sub_le`). Separation implies injectivity of the
differential: two segments leaving a common point with the same right derivative stay closer
than any fixed multiple of their parameter, so they have the same endpoint.

This characterization makes star immersions stable under perturbations that are small in the
Lipschitz sense. If `f` is moreover injective, it is antilipschitz in barycentric coordinates,
and so is every map `g` for which `g - f` is Lipschitz with a small enough constant. Then `g` is
again an injective star immersion as soon as it is `Cᵐ` on every closed simplex. This is
Munkres' theorem that a `δ`-approximation of an embedding of a finite complex is again an
embedding, with the first-order closeness of `g` to `f` measured by a Lipschitz constant across
all simplices at once.

The approximation may live on a subdivision: `g` may be defined on `|L|` and compared with
`f ∘ φ` for an injective map `φ : |L| → |K|` which separates nearby points uniformly in
barycentric coordinates. The bound on `δ` depends only on `f`, not on `φ`. For the canonical maps
of the edgewise subdivisions of `K` this gives one `δ` for all of them
(`TauCeti.IsStarImmersion.exists_pos_forall_isStarImmersion_and_injective_edgewiseSubdivision`).
The secant maps of `f` on fine edgewise subdivisions are such approximations, and so are their
interpolations with `f` by a smooth cut-off function, which are rectilinear on one part of the
complex and agree with `f` on another.

## Main results

* `TauCeti.isStarImmersion_of_forall_mul_norm_sub_le`: a map which is `Cⁿ` on every closed simplex
  and separates nearby points uniformly is a `Cⁿ` star immersion.
* `TauCeti.isStarImmersion_iff_exists_pos_mul_norm_sub_le`: for maps of a complex on a finite
  vertex type, being a `Cⁿ` star immersion is being `Cⁿ` on every closed simplex and separating
  nearby points uniformly.
* `TauCeti.IsStarImmersion.exists_pos_forall_isStarImmersion_and_injective`: maps whose
  difference with an injective star immersion, read through a reference map `φ`, is Lipschitz with
  a small constant are injective star immersions.
* `TauCeti.IsStarImmersion.exists_pos_forall_isStarImmersion_and_injective_edgewiseSubdivision`:
  the same on all edgewise subdivisions, with a constant independent of the subdivision.

## References

* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Section 8 (`δ`-approximations of immersions and embeddings of complexes) and Theorems 10.5–10.6.
* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
-/

public section

open Set Function Filter Topology AbstractSimplicialComplex PreAbstractSimplicialComplex
  TauCeti.SetLike
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : AbstractSimplicialComplex ι} {n : WithTop ℕ∞} {f : Realization K → E}

/-- Two curves leaving a common point with the same right derivative do not separate linearly:
if `s * a ≤ ‖γ₁ s - γ₂ s‖` for all small `s > 0`, then `a ≤ 0`. -/
private theorem nonpos_of_hasDerivWithinAt_of_mul_le_norm_sub {γ₁ γ₂ : ℝ → E} {u : E} {a : ℝ}
    (h₁ : HasDerivWithinAt γ₁ u (Icc 0 1) 0) (h₂ : HasDerivWithinAt γ₂ u (Icc 0 1) 0)
    (h0 : γ₁ 0 = γ₂ 0) (hle : ∀ᶠ s in 𝓝[>] 0, s * a ≤ ‖γ₁ s - γ₂ s‖) : a ≤ 0 := by
  have hslope := hasDerivWithinAt_iff_tendsto_slope.mp (h₁.sub h₂)
  rw [sub_self, Icc_sdiff_left, nhdsWithin_Ioc_eq_nhdsGT zero_lt_one] at hslope
  refine ge_of_tendsto (by simpa using hslope.norm) ?_
  filter_upwards [hle, self_mem_nhdsWithin] with s hs (hs0 : 0 < s)
  rw [slope_def_module, Pi.sub_apply, Pi.sub_apply, h0, sub_self, sub_zero, sub_zero, norm_smul,
    norm_inv, Real.norm_of_nonneg hs0.le, le_inv_mul_iff₀ hs0]
  exact hs

/-- Along a segment in a closed simplex, a map with a coordinate extension `F` has as right
derivative the derivative of `F` at the starting point applied to the direction of the
segment. -/
private theorem hasDerivWithinAt_lineMap_of_hasFDerivWithinAt {σ : Finset ι}
    {g : StandardSimplex σ → E} {F : (σ → ℝ) → E} {F' : (σ → ℝ) →L[ℝ] E}
    (hFg : ∀ x : StandardSimplex σ, F (fun a => x.1 a) = g x) (b x : StandardSimplex σ)
    (hF : HasFDerivWithinAt F F' (range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights)
      fun a : σ => b.1 a) :
    HasDerivWithinAt (IccExtend zero_le_one (g ∘ StandardSimplex.lineMap b x))
      (F' ((fun a : σ => x.1 a) - fun a : σ => b.1 a)) (Icc 0 1) 0 := by
  have hmem (y : StandardSimplex σ) :
      (fun a : σ => y.1 a) ∈ range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights := by
    rw [← Finset.range_standardSimplex_coordinates]
    exact mem_range_self y
  have hline := hF.comp_hasDerivWithinAt_of_eq (0 : ℝ) AffineMap.hasDerivWithinAt_lineMap
    (fun t ht => (Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ σ).lineMap_mem
      (hmem b) (hmem x) ht) (by simp)
  refine hline.congr_of_mem (fun t ht => ?_) (left_mem_Icc.2 zero_le_one)
  rw [IccExtend_of_mem _ _ ht, comp_apply, comp_apply, ← hFg]
  congr 1
  funext a
  simp [AffineMap.lineMap_apply_module]

variable [Fintype ι]

/-- If `f` separates nearby points uniformly in barycentric coordinates, two segments from a
common point of two closed simplices along which `f` has the same right derivative have the same
endpoint. This is the star condition of `TauCeti.IsStarImmersion`. -/
private theorem eq_of_hasDerivWithinAt_of_forall_mul_norm_sub_le {c δ : ℝ} (hc : 0 < c)
    (hδ : 0 < δ) (hsep : ∀ x y : Realization K, ‖(x.1 : ι → ℝ) - y.1‖ < δ →
      c * ‖(x.1 : ι → ℝ) - y.1‖ ≤ ‖f x - f y‖)
    {σ τ : Face K} {b x : StandardSimplex σ.1} {b' y : StandardSimplex τ.1} {u : E}
    (hb : (b : ι →₀ ℝ) = b')
    (hx : HasDerivWithinAt
      (IccExtend zero_le_one (f ∘ faceInclusion K σ ∘ StandardSimplex.lineMap b x)) u (Icc 0 1) 0)
    (hy : HasDerivWithinAt
      (IccExtend zero_le_one (f ∘ faceInclusion K τ ∘ StandardSimplex.lineMap b' y)) u
        (Icc 0 1) 0) :
    (x : ι →₀ ℝ) = y := by
  set D := ‖((x : ι →₀ ℝ) : ι → ℝ) - y‖
  -- The points at parameter `s` of the two segments are at distance `s * D`.
  have hdist (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖((faceInclusion K σ (StandardSimplex.lineMap b x ⟨s, hs⟩)).1 : ι → ℝ) -
        (faceInclusion K τ (StandardSimplex.lineMap b' y ⟨s, hs⟩)).1‖ = s * D := by
    rw [faceInclusion_val, faceInclusion_val, StandardSimplex.coe_lineMap,
      StandardSimplex.coe_lineMap, hb, AffineMap.lineMap_apply_module,
      AffineMap.lineMap_apply_module, ← Finsupp.coe_sub, add_sub_add_left_eq_sub, ← smul_sub,
      Finsupp.coe_smul, Finsupp.coe_sub, norm_smul, Real.norm_of_nonneg hs.1]
  have hb₀ : faceInclusion K σ b = faceInclusion K τ b' :=
    Subtype.ext (by rw [faceInclusion_val, faceInclusion_val, hb])
  have h0 : IccExtend zero_le_one (f ∘ faceInclusion K σ ∘ StandardSimplex.lineMap b x) 0 =
      IccExtend zero_le_one (f ∘ faceInclusion K τ ∘ StandardSimplex.lineMap b' y) 0 := by
    simp [hb₀]
  have hcD : c * D ≤ 0 := by
    refine nonpos_of_hasDerivWithinAt_of_mul_le_norm_sub hx hy h0 ?_
    have hD1 : 0 < D + 1 := by positivity
    filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos (div_pos hδ hD1))] with s hs
    have hs₁ : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, (hs.2.trans_le (min_le_left _ _)).le⟩
    have hsD : s * D < δ := by
      have h := (lt_div_iff₀ hD1).mp (hs.2.trans_le (min_le_right _ _))
      nlinarith [hs.1]
    rw [IccExtend_of_mem _ _ hs₁, IccExtend_of_mem _ _ hs₁, comp_apply, comp_apply,
      comp_apply, comp_apply, mul_left_comm, ← hdist s hs₁]
    exact hsep _ _ ((hdist s hs₁).trans_lt hsD)
  have hD : D = 0 := le_antisymm (nonpos_of_mul_nonpos_right hcD hc) (norm_nonneg _)
  exact DFunLike.coe_injective (sub_eq_zero.mp (norm_eq_zero.mp hD))

/-- A map which separates nearby points uniformly in barycentric coordinates and is `Cⁿ` on a
closed simplex, `1 ≤ n`, is a `Cⁿ` immersion of that simplex. -/
private theorem isSimplexImmersion_of_forall_mul_norm_sub_le {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hsep : ∀ x y : Realization K, ‖(x.1 : ι → ℝ) - y.1‖ < δ →
      c * ‖(x.1 : ι → ℝ) - y.1‖ ≤ ‖f x - f y‖)
    (σ : Face K) {F : (σ.1 → ℝ) → E}
    (hFg : ∀ x : StandardSimplex σ.1, F (fun a => x.1 a) = f (faceInclusion K σ x))
    (hF : ContDiffOn ℝ n F (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights))
    (hn : 1 ≤ n) :
    IsSimplexImmersion 𝓘(ℝ, E) n (f ∘ faceInclusion K σ) := by
  set S := range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights with hS
  -- The points of the closed simplex with prescribed coordinates.
  have hpt (w : σ.1 → ℝ) (hw : w ∈ S) :
      ∃ x : StandardSimplex σ.1, (fun a : σ.1 => x.1 a) = w := by
    rwa [hS, ← Finset.range_standardSimplex_coordinates] at hw
  refine isSimplexImmersion_iff.mpr ⟨F, hFg, contMDiffOn_iff_contDiffOn.mpr hF, fun t => ?_⟩
  have hFt : HasFDerivWithinAt F (fderivWithin ℝ F S t.weights) S t.weights :=
    ((hF.differentiableOn (by positivity)) _ ⟨t, rfl⟩).hasFDerivWithinAt
  refine ⟨_, hasMFDerivWithinAt_iff_hasFDerivWithinAt.mpr hFt, fun v hv hv0 => ?_⟩
  set F' := fderivWithin ℝ F S t.weights
  -- Write `v` as a multiple of the difference of two points `x` and `y` of the simplex, using
  -- its positive and negative parts, which have the same coordinate sum `s`.
  have hsum : ∑ a, v⁻ a = ∑ a, v⁺ a := by
    have h : ∑ a, (v⁺ a - v⁻ a) = ∑ a, v a :=
      Finset.sum_congr rfl fun a _ => by rw [← Pi.sub_apply, posPart_sub_negPart]
    rw [Finset.sum_sub_distrib, hv] at h
    linarith
  have hpos : ∀ a, 0 ≤ v⁺ a := fun a => (posPart_nonneg v) a
  have hneg : ∀ a, 0 ≤ v⁻ a := fun a => (negPart_nonneg v) a
  rcases (Finset.sum_nonneg fun a _ => hpos a).eq_or_lt with hs0 | hs0
  · -- If the positive part has coordinate sum zero, both parts vanish.
    have hp : v⁺ = 0 := funext fun a =>
      (Finset.sum_eq_zero_iff_of_nonneg fun a _ => hpos a).mp hs0.symm a (Finset.mem_univ a)
    have hn : v⁻ = 0 := funext fun a =>
      (Finset.sum_eq_zero_iff_of_nonneg fun a _ => hneg a).mp (hsum.trans hs0.symm) a
        (Finset.mem_univ a)
    rw [← posPart_sub_negPart v, hp, hn, sub_zero]
  set s := ∑ a, v⁺ a
  have hmem (w : σ.1 → ℝ) (hw : ∀ a, 0 ≤ w a) (hws : ∑ a, w a = s) : s⁻¹ • w ∈ S := by
    refine Convexity.StdSimplex.mem_range_toFun_comp_weights_iff.mpr
      ⟨fun a => mul_nonneg (inv_nonneg.mpr hs0.le) (hw a), ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hws, inv_mul_cancel₀ hs0.ne']
  obtain ⟨x, hx⟩ := hpt _ (hmem _ hpos rfl)
  obtain ⟨y, hy⟩ := hpt _ (hmem _ hneg hsum)
  obtain ⟨b, hb⟩ := hpt t.weights ⟨t, rfl⟩
  rw [← hb] at hFt
  -- `F` has the same derivative along the segments from `b` to `x` and to `y`.
  have hxy := eq_of_hasDerivWithinAt_of_forall_mul_norm_sub_le hc hδ hsep (σ := σ) (τ := σ)
    (b := b) (b' := b) (x := x) (y := y) rfl
    (hasDerivWithinAt_lineMap_of_hasFDerivWithinAt hFg b x hFt)
    ((hasDerivWithinAt_lineMap_of_hasFDerivWithinAt hFg b y hFt).congr_deriv (by
      rw [hx, hy, ← sub_eq_zero, ← map_sub, sub_sub_sub_cancel_right, ← smul_sub, ← neg_sub,
        posPart_sub_negPart, smul_neg, map_neg, map_smul, hv0, smul_zero, neg_zero]))
  have hcoord : s⁻¹ • v⁺ = s⁻¹ • v⁻ := by
    rw [← hx, ← hy, hxy]
  rw [← posPart_sub_negPart v, smul_right_injective _ (inv_ne_zero hs0.ne') hcoord, sub_self]

/-- **Separation gives star immersions.** Let `f` be a map of the realization of a complex on a
finite vertex type into a normed space which is `Cⁿ` on every closed simplex, `1 ≤ n`: in
barycentric coordinates it is the restriction of a map `Cⁿ` within the standard simplex. If `f`
separates nearby points uniformly in barycentric coordinates, `c * ‖x - y‖ ≤ ‖f x - f y‖`
whenever `‖x - y‖ < δ`, then `f` is a `Cⁿ` star immersion. -/
theorem isStarImmersion_of_forall_mul_norm_sub_le
    (hf : ∀ σ : Face K, ∃ F : (σ.1 → ℝ) → E,
      (∀ x : StandardSimplex σ.1, F (fun a => x.1 a) = f (faceInclusion K σ x)) ∧
        ContDiffOn ℝ n F (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights))
    (hn : 1 ≤ n) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hsep : ∀ x y : Realization K, ‖(x.1 : ι → ℝ) - y.1‖ < δ →
      c * ‖(x.1 : ι → ℝ) - y.1‖ ≤ ‖f x - f y‖) :
    IsStarImmersion n f := by
  refine isStarImmersion_iff.mpr ⟨fun σ => ?_, fun σ τ b x b' y u hb hx hy =>
    eq_of_hasDerivWithinAt_of_forall_mul_norm_sub_le hc hδ hsep hb hx hy⟩
  obtain ⟨F, hFg, hF⟩ := hf σ
  exact isSimplexImmersion_of_forall_mul_norm_sub_le hc hδ hsep σ hFg hF hn

/-- **Star immersions are the uniformly separating maps.** A map of the realization of a complex
on a finite vertex type into a normed space is a `Cⁿ` star immersion, `1 ≤ n`, if and only if it
is `Cⁿ` on every closed simplex and separates nearby points uniformly in barycentric
coordinates. -/
theorem isStarImmersion_iff_exists_pos_mul_norm_sub_le (hn : 1 ≤ n) :
    IsStarImmersion n f ↔
      (∀ σ : Face K, ∃ F : (σ.1 → ℝ) → E,
        (∀ x : StandardSimplex σ.1, F (fun a => x.1 a) = f (faceInclusion K σ x)) ∧
          ContDiffOn ℝ n F (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights)) ∧
      ∃ c > 0, ∃ δ > 0, ∀ x y : Realization K, ‖(x.1 : ι → ℝ) - y.1‖ < δ →
        c * ‖(x.1 : ι → ℝ) - y.1‖ ≤ ‖f x - f y‖ := by
  refine ⟨fun h => ⟨fun σ => ?_, h.exists_pos_mul_norm_sub_le_norm_sub hn⟩,
    fun ⟨hf, c, hc, δ, hδ, hsep⟩ => isStarImmersion_of_forall_mul_norm_sub_le hf hn hc hδ hsep⟩
  obtain ⟨F, hFg, hF, -⟩ := isSimplexImmersion_iff.mp (h.isSimplexImmersion σ)
  exact ⟨F, hFg, contMDiffOn_iff_contDiffOn.mp hF⟩

namespace IsStarImmersion

/-- **Small perturbations of embeddings are embeddings** (Munkres' `δ`-approximations). Let `f` be
an injective `Cⁿ` star immersion, `1 ≤ n`, of a complex `K` on a finite vertex type into a normed
space. There is `δ > 0` with the following property. Let `φ : |L| → |K|` be an injective map from
the realization of a complex on a finite vertex type which separates nearby points uniformly in
barycentric coordinates, such as the canonical map of a subdivision, and let `g : |L| → E` be `Cᵐ`
on every closed simplex of `L`, `1 ≤ m`. If `g - f ∘ φ` is `δ`-Lipschitz in the barycentric
coordinates of `K`, then `g` is an injective `Cᵐ` star immersion. The constant `δ` depends only
on `f`. -/
theorem exists_pos_forall_isStarImmersion_and_injective (h : IsStarImmersion n f) (hn : 1 ≤ n)
    (hf : Injective f) :
    ∃ δ > 0, ∀ {κ : Type*} [Fintype κ] {L : AbstractSimplicialComplex κ}
      {φ : Realization L → Realization K} {g : Realization L → E} {m : WithTop ℕ∞},
      Injective φ →
      (∃ c > 0, ∃ δ' > 0, ∀ x y : Realization L, ‖(x.1 : κ → ℝ) - y.1‖ < δ' →
        c * ‖(x.1 : κ → ℝ) - y.1‖ ≤ ‖((φ x).1 : ι → ℝ) - (φ y).1‖) → 1 ≤ m →
      (∀ ρ : Face L, ∃ G : (ρ.1 → ℝ) → E,
        (∀ x : StandardSimplex ρ.1, G (fun a => x.1 a) = g (faceInclusion L ρ x)) ∧
          ContDiffOn ℝ m G (range fun t : Convexity.StdSimplex ℝ ρ.1 => ⇑t.weights)) →
      (∀ x y, ‖(g x - f (φ x)) - (g y - f (φ y))‖ ≤ δ * ‖((φ x).1 : ι → ℝ) - (φ y).1‖) →
      IsStarImmersion m g ∧ Injective g := by
  -- `f` is antilipschitz in barycentric coordinates, with some constant `C`.
  obtain ⟨C, hC, hanti⟩ := h.exists_antilipschitzWith hn hf
  have hCpos : (0 : ℝ) < C := hC
  have hglobal (x y : Realization K) : ‖(x.1 : ι → ℝ) - y.1‖ ≤ C * ‖f x - f y‖ := by
    have h := hanti.le_mul_dist (K.realizationHomeomorphRange (Set.toFinite K.faces) x)
      (K.realizationHomeomorphRange (Set.toFinite K.faces) y)
    rwa [Subtype.dist_eq, dist_eq_norm, dist_eq_norm, comp_apply, comp_apply,
      Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply,
      coe_realizationHomeomorphRange_apply, coe_realizationHomeomorphRange_apply] at h
  refine ⟨(2 * C)⁻¹, by positivity, fun {κ} _ L φ g m hφ hφs hm hg hlip => ?_⟩
  -- Then `g` separates points at least half as well as `f ∘ φ`.
  have hsep (x y : Realization L) :
      ‖((φ x).1 : ι → ℝ) - (φ y).1‖ ≤ 2 * C * ‖g x - g y‖ := by
    have hfg : ‖f (φ x) - f (φ y)‖ ≤
        ‖g x - g y‖ + ‖(g x - f (φ x)) - (g y - f (φ y))‖ := by
      rw [show f (φ x) - f (φ y) = (g x - g y) - ((g x - f (φ x)) - (g y - f (φ y))) by abel]
      exact norm_sub_le _ _
    have h2C : (C : ℝ) * (2 * (C : ℝ))⁻¹ = 1 / 2 := by
      rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hCpos.ne', mul_one, one_div]
    have h := mul_le_mul_of_nonneg_left (hfg.trans (add_le_add le_rfl (hlip x y))) hCpos.le
    rw [mul_add, ← mul_assoc, h2C] at h
    linarith [hglobal (φ x) (φ y)]
  obtain ⟨c, hc, δ, hδ, hφsep⟩ := hφs
  refine ⟨isStarImmersion_of_forall_mul_norm_sub_le hg hm (c := c / (2 * C)) (by positivity) hδ
    fun x y hxy => ?_, fun x y hxy => hφ ?_⟩
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hφsep x y hxy, hsep x y]
  · have h0 := hsep x y
    rw [hxy, sub_self, norm_zero, mul_zero] at h0
    exact Subtype.ext (DFunLike.coe_injective (sub_eq_zero.mp (norm_le_zero_iff.mp h0)))

/-- **Small perturbations of embeddings on edgewise subdivisions.** Let `f` be an injective `Cⁿ`
star immersion, `1 ≤ n`, of a complex `K` on a finite vertex type into a normed space. There is
`δ > 0` such that on every edgewise subdivision of `K`, every map `g` which is `Cᵐ` on every closed
simplex of the subdivision, `1 ≤ m`, and differs from `f` by a `δ`-Lipschitz map, read through
the canonical map onto `|K|` in the barycentric coordinates of `K`, is an injective `Cᵐ` star
immersion. The constant `δ` does not depend on the subdivision. -/
theorem exists_pos_forall_isStarImmersion_and_injective_edgewiseSubdivision [LinearOrder ι]
    (h : IsStarImmersion n f) (hn : 1 ≤ n) (hf : Injective f) :
    ∃ δ > 0, ∀ {k : ℕ} {g : Realization (K.edgewiseSubdivision k) → E} {m : WithTop ℕ∞},
      1 ≤ m →
      (∀ ρ : Face (K.edgewiseSubdivision k), ∃ G : (ρ.1 → ℝ) → E,
        (∀ x : StandardSimplex ρ.1, G (fun a => x.1 a) = g (faceInclusion _ ρ x)) ∧
          ContDiffOn ℝ m G (range fun t : Convexity.StdSimplex ℝ ρ.1 => ⇑t.weights)) →
      (∀ x y, ‖(g x - f (edgewiseSubdivisionRealizationMap K k x)) -
          (g y - f (edgewiseSubdivisionRealizationMap K k y))‖ ≤
        δ * ‖((edgewiseSubdivisionRealizationMap K k x).1 : ι → ℝ) -
          (edgewiseSubdivisionRealizationMap K k y).1‖) →
      IsStarImmersion m g ∧ Injective g := by
  obtain ⟨δ, hδ, hpert⟩ := h.exists_pos_forall_isStarImmersion_and_injective hn hf
  refine ⟨δ, hδ, fun {k} g m hm hg hlip => ?_⟩
  let : Fintype (K.EdgewiseVertex k) := Fintype.ofFinite _
  -- In barycentric coordinates the canonical map is linear on every simplex of the subdivision,
  -- so it is its own secant map. It is injective, so it is a star immersion and separates nearby
  -- points uniformly.
  set p := fun x : Realization (K.edgewiseSubdivision k) =>
    ((edgewiseSubdivisionRealizationMap K k x).1 : ι → ℝ)
  have hp : (K.edgewiseSubdivision k).secantMap p = p := by
    refine secantMap_eq_self_iff.mpr fun ρ x => ?_
    have hsupp : x.1 ∈ Finsupp.supported ℝ ℝ (↑ρ.1 : Set (K.EdgewiseVertex k)) :=
      (Finsupp.mem_supported ℝ x.1).mpr (StandardSimplex.support_subset x)
    simp only [p, edgewiseSubdivisionRealizationMap_val, faceInclusion_val,
      Finsupp.linearCombination_apply_of_mem_supported ℝ hsupp, Finsupp.coe_finsetSum,
      Finsupp.coe_smul, vertex_val, Finsupp.linearCombination_single, one_smul]
    exact (Finset.sum_coe_sort ρ.1 fun u => x.1 u • ⇑(edgewisePoint u.1)).symm
  have hpinj : Injective p := fun x y hxy =>
    edgewiseSubdivisionRealizationMap_injective (Subtype.ext (DFunLike.coe_injective hxy))
  have hps : IsStarImmersion 1 p := by
    rw [← hp]
    exact isStarImmersion_secantMap (hp.symm ▸ hpinj)
  exact hpert edgewiseSubdivisionRealizationMap_injective
    (hps.exists_pos_mul_norm_sub_le_norm_sub le_rfl) hm hg hlip

end IsStarImmersion

end TauCeti
