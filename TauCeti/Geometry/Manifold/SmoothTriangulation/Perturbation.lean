/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.StarImmersion

import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.ContDiff
import TauCeti.Geometry.Manifold.SmoothTriangulation.Lipschitz.Basic

/-!
# Small perturbations of embeddings of complexes

A map `f : |K| → E` of the realization of a complex on a finite vertex type into a normed space
which is `Cⁿ` on every closed simplex, `1 ≤ n`, is a star immersion (Munkres' immersion of a
complex) exactly when it separates nearby points uniformly in barycentric coordinates
(`TauCeti.isStarImmersion_iff_exists_pos_mul_norm_sub_le`, in `SmoothTriangulation.StarImmersion`).

This characterization makes star immersions stable under perturbations that are small in the
Lipschitz sense. If `f` is moreover injective, it is antilipschitz in barycentric coordinates,
and by `AntilipschitzWith.add_sub_lipschitzWith` so is every map `g` for which `g - f` is
Lipschitz with a small enough constant. Then `g` is again an injective star immersion as soon as
it is `Cᵐ` on every closed simplex. This is Munkres' theorem that a `δ`-approximation of an
embedding of a finite complex is again an embedding, with the first-order closeness of `g` to `f`
measured by a Lipschitz constant across all simplices at once.

The approximation may live on a subdivision: `g` may be defined on `|L|` and compared with
`f ∘ φ` for an injective map `φ : |L| → |K|` which separates nearby points uniformly in
barycentric coordinates. The bound on `δ` depends only on `f`, not on `φ`. For the canonical maps
of the edgewise subdivisions of `K` this gives one `δ` for all of them
(`TauCeti.IsStarImmersion.exists_pos_forall_isStarImmersion_and_injective_edgewiseSubdivision`).
The secant maps of `f` on fine edgewise subdivisions are such approximations, and so are their
interpolations with `f` by a cut-off function `φ` which is `Cᵐ` on every closed simplex:
`AffineMap.lineMap (f (π x)) (s x) (φ (π x))`, with `s` the secant map and `π` the canonical map
onto `|K|`. Such an interpolation is rectilinear on the simplices of the subdivision where
`φ = 1` and agrees with `f` where `φ = 0`, and it is again an injective star immersion on every
fine enough edgewise subdivision. This is how an embedding is made rectilinear near a compact set
while it is kept fixed away from it, when local rectilinear triangulations are fitted together.

## Main results

* `TauCeti.IsStarImmersion.exists_pos_forall_isStarImmersion_and_injective`: maps whose
  difference with an injective star immersion, read through a reference map `φ`, is Lipschitz with
  a small constant are injective star immersions.
* `TauCeti.IsStarImmersion.exists_pos_forall_isStarImmersion_and_injective_edgewiseSubdivision`:
  the same on all edgewise subdivisions, with a constant independent of the subdivision.
* `TauCeti.IsStarImmersion.eventually_isStarImmersion_and_injective_lineMap_secantMap`:
  the interpolation of an injective star immersion with its secant map by a cut-off function is
  an injective star immersion on all sufficiently fine edgewise subdivisions.

## References

* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Section 8 (`δ`-approximations of immersions and embeddings of complexes) and Theorems 10.5–10.6.
* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
-/

public section

open Set Function Filter Topology AbstractSimplicialComplex PreAbstractSimplicialComplex
  TauCeti.SetLike
open scoped Manifold ContDiff NNReal

namespace TauCeti

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : AbstractSimplicialComplex ι} {n : WithTop ℕ∞} {f : Realization K → E} [Fintype ι]

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
  set e := K.realizationHomeomorphRange (Set.toFinite K.faces)
  have hCδ : (2 * C)⁻¹ < C⁻¹ := inv_strictAnti₀ hC (lt_two_mul_self hC)
  refine ⟨((2 * C)⁻¹ : ℝ≥0), NNReal.coe_pos.2 (inv_pos.2 (mul_pos two_pos hC)),
    fun {κ} _ L φ g m hφ hφs hm hg hlip => ?_⟩
  -- Measure distances on `|L|` in the barycentric coordinates of `K` through `φ`. Then `f ∘ φ` is
  -- antilipschitz and `g - f ∘ φ` is Lipschitz with a small constant, so `g` is antilipschitz.
  let : PseudoMetricSpace (Realization L) := .induced (fun x => e (φ x)) inferInstance
  have hdist (x y : Realization L) : dist x y = ‖((φ x).1 : ι → ℝ) - (φ y).1‖ := by
    change dist (e (φ x)) (e (φ y)) = _
    simp [e, Subtype.dist_eq, dist_eq_norm]
  have hfφ : AntilipschitzWith C (f ∘ φ) := .of_le_mul_dist fun x y =>
    (hanti.le_mul_dist (e (φ x)) (e (φ y))).trans_eq (by simp [e])
  have hgφ : LipschitzWith (2 * C)⁻¹ (g - f ∘ φ) := .of_dist_le_mul fun x y => by
    simpa [hdist, dist_eq_norm] using hlip x y
  obtain ⟨C', hC', hsep⟩ : ∃ C' > (0 : ℝ),
      ∀ x y : Realization L, ‖((φ x).1 : ι → ℝ) - (φ y).1‖ ≤ C' * ‖g x - g y‖ :=
    ⟨_, NNReal.coe_pos.2 (inv_pos.2 (tsub_pos_iff_lt.2 hCδ)), fun x y => by
      simpa only [hdist, dist_eq_norm] using (hfφ.add_sub_lipschitzWith hgφ hCδ).le_mul_dist x y⟩
  obtain ⟨c, hc, δ, hδ, hφsep⟩ := hφs
  refine ⟨isStarImmersion_of_forall_mul_norm_sub_le hg hm (c := c / C') (div_pos hc hC') hδ
    fun x y hxy => ?_, fun x y hxy => hφ ?_⟩
  · rw [div_mul_eq_mul_div, div_le_iff₀ hC']
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

omit [Fintype ι] in
/-- **Making an embedding rectilinear where a cut-off is one.** Let `f` be an injective `Cⁿ` star
immersion, `1 ≤ n`, of a complex `K` on a finite vertex type into a normed space, and let
`φ : |K| → ℝ` be `Cᵐ` on every closed simplex, `1 ≤ m`. For all sufficiently large `k`, the
interpolation `AffineMap.lineMap (f (π x)) (s x) (φ (π x))` on the `k`-th edgewise subdivision is
an injective `C^(min n m)` star immersion, where `s` is the secant map of `f` on the subdivision
and `π` is the canonical map onto `|K|`. It is linear on every closed simplex of the subdivision
on which `φ = 1`, and agrees with `f ∘ π` where `φ = 0`. -/
theorem eventually_isStarImmersion_and_injective_lineMap_secantMap
    [Finite ι] [LinearOrder ι] {m : WithTop ℕ∞} {φ : Realization K → ℝ} (h : IsStarImmersion n f)
    (hn : 1 ≤ n) (hf : Injective f) (hm : 1 ≤ m)
    (hφ : ∀ σ : Face K, ∃ Φ : (σ.1 → ℝ) → ℝ,
      (∀ x : StandardSimplex σ.1, Φ (fun a => x.1 a) = φ (faceInclusion K σ x)) ∧
        ContDiffOn ℝ m Φ (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights)) :
    ∀ᶠ k in atTop,
      IsStarImmersion (min n m) (fun x : Realization (K.edgewiseSubdivision k) =>
        AffineMap.lineMap (f (edgewiseSubdivisionRealizationMap K k x))
          ((K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k) x)
          (φ (edgewiseSubdivisionRealizationMap K k x))) ∧
      Injective (fun x : Realization (K.edgewiseSubdivision k) =>
        AffineMap.lineMap (f (edgewiseSubdivisionRealizationMap K k x))
          ((K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k) x)
          (φ (edgewiseSubdivisionRealizationMap K k x))) := by
  have := Fintype.ofFinite ι
  obtain ⟨δ, hδ, hpert⟩ := h.exists_pos_forall_isStarImmersion_and_injective_edgewiseSubdivision
    hn hf
  -- On every closed simplex, `f` is the restriction of a `Cⁿ` map in barycentric coordinates.
  have hCn (σ : Face K) : ∃ F : (σ.1 → ℝ) → E,
      (∀ x : StandardSimplex σ.1, F (fun a => x.1 a) = f (faceInclusion K σ x)) ∧
        ContDiffOn ℝ n F (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights) := by
    obtain ⟨F, hFg, hF, -⟩ := isSimplexImmersion_iff.mp (h.isSimplexImmersion σ)
    exact ⟨F, hFg, contMDiffOn_iff_contDiffOn.mp hF⟩
  have hC1 (σ : Face K) : ∃ F : (σ.1 → ℝ) → E,
      (∀ x : StandardSimplex σ.1, F (fun a => x.1 a) = f (faceInclusion K σ x)) ∧
        ContDiffOn ℝ 1 F (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights) :=
    (hCn σ).imp fun _ hF => ⟨hF.1, hF.2.of_le hn⟩
  have hφ1 (σ : Face K) : ∃ Φ : (σ.1 → ℝ) → ℝ,
      (∀ x : StandardSimplex σ.1, Φ (fun a => x.1 a) = φ (faceInclusion K σ x)) ∧
        ContDiffOn ℝ 1 Φ (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights) :=
    (hφ σ).imp fun _ hΦ => ⟨hΦ.1, hΦ.2.of_le hm⟩
  filter_upwards [eventually_norm_lineMap_secantMap_sub_sub_le_edgewiseSubdivision hC1 hφ1 hδ]
    with k hk
  refine hpert (le_min hn hm) (fun ρ => ?_) hk
  -- On a closed simplex of the subdivision, `f ∘ π` and `φ ∘ π` are smooth and the secant map is
  -- linear, so their interpolation is smooth.
  obtain ⟨Gf, hGf, hGfc⟩ := exists_contDiffOn_edgewiseSubdivisionRealizationMap_faceInclusion hCn ρ
  obtain ⟨Gφ, hGφ, hGφc⟩ := exists_contDiffOn_edgewiseSubdivisionRealizationMap_faceInclusion hφ ρ
  let Gs : (ρ.1 → ℝ) →L[ℝ] E := (Fintype.linearCombination ℝ fun a : ρ.1 =>
    f (edgewiseSubdivisionRealizationMap K k (vertex _ a))).toContinuousLinearMap
  have hGs (x : StandardSimplex ρ.1) : Gs (fun a => x.1 a) =
      (K.edgewiseSubdivision k).secantMap (f ∘ edgewiseSubdivisionRealizationMap K k)
        (faceInclusion _ ρ x) := by
    rw [secantMap_faceInclusion]
    simp [Gs, Fintype.linearCombination_apply]
  refine ⟨fun w => AffineMap.lineMap (Gf w) (Gs w) (Gφ w), fun x => by
    simp only [hGf, hGs, hGφ], ?_⟩
  simp_rw [AffineMap.lineMap_apply_module']
  exact ((hGφc.of_le (min_le_right _ _)).smul
    (Gs.contDiff.contDiffOn.sub (hGfc.of_le (min_le_left _ _)))).add
    (hGfc.of_le (min_le_left _ _))

end IsStarImmersion

end TauCeti
