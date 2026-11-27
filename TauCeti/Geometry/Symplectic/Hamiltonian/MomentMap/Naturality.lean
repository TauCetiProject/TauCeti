/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Tangent.Prod
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.RankTwo
public import TauCeti.GroupTheory.GroupAction.FixedPoints
public import TauCeti.GroupTheory.GroupAction.Hom

/-!
# Moment polytopes under subtori, translations, equivariant maps and products

Let a torus `G` act on a compact manifold `M` with a nondegenerate two-form `σ` and moment map
`μ : M → 𝔤*`, and write `M^G` for the fixed-point set. The convexity theorem of Atiyah and
Guillemin–Sternberg says that the image `μ(M)` is the polytope `conv μ(M^G)`; the inclusion
`μ(M) ⊆ conv μ(M^G)` holds in general
(`TauCeti.SmoothTwoForm.IsMomentMap.range_subset_convexHull_image_fixedPoints`), and the equality
is known for tori of dimension at most two and for actions that are locally free off their fixed
points. This file records how the polytope and the equality behave under the standard operations
on Hamiltonian torus actions.

* **Subtori.** A homomorphism `φ : K →* G` restricts the action to `K`, with moment map
  `x ↦ μ x ∘ dφ` (`TauCeti.SmoothTwoForm.HamiltonianTorusData.comp_monoidHom`). For any linear map
  `L` into `𝔤`, the image of `x ↦ μ x ∘ L` lies in the convex hull of its values at the points
  fixed by the whole torus `G`
  (`TauCeti.SmoothTwoForm.IsMomentMap.range_comp_subset_convexHull_image_fixedPoints`), so the
  polytope of a subtorus is the projection of the polytope of `G`
  (`TauCeti.SmoothTwoForm.IsMomentMap.convexHull_range_comp_eq_convexHull_image_fixedPoints`). If
  `μ(M) = conv μ(M^G)`, then also `μ_K(M) = conv μ_K(M^K)` for every `K` acting through `G`
  (`TauCeti.range_comp_eq_convexHull_image_fixedPoints_of_smul_eq`).
* **Translations.** The equality `μ(M) = conv μ(M^G)` holds for `μ + ν` exactly when it holds for
  `μ` (`TauCeti.range_add_const_eq_convexHull_image_fixedPoints_iff`).
* **Naturality.** Along an equivariant bijection `f : N → M`, such as an equivariant
  symplectomorphism, it holds for `μ ∘ f` exactly when it holds for `μ`
  (`TauCeti.range_comp_eq_convexHull_image_fixedPoints_iff`).
* **Products.** Let `G` act on `M` with moment map `μ` and `G₂` act on `N` with moment map `ν`,
  and let `G × G₂` act on `M × N` componentwise, with moment map `(x, y) ↦ e (μ x, ν y)`, where
  `e : 𝔤* × 𝔤₂* ≃ Lie(G × G₂)*` is `TauCeti.Lie.groupLieAlgebraDualProdDualEquivDual`
  (`TauCeti.SmoothTwoForm.HamiltonianTorusData.prodMap`). The fixed points of the product action
  are the pairs of fixed points, so the polytope of the product is the product of the polytopes,
  `e (conv μ(M^G) × conv ν(N^G₂))`
  (`TauCeti.convexHull_image_fixedPoints_prod`). If `μ(M) = conv μ(M^G)`
  and `ν(N) = conv ν(N^G₂)`, the product satisfies the same equality
  (`TauCeti.range_prod_eq_convexHull_image_fixedPoints`), and if the
  fibres of `μ` and `ν` are connected, so are those of the product moment map
  (`TauCeti.isPreconnected_preimage_singleton_prod`).

Combined with the convexity theorem for tori of dimension at most two, the product statement gives
`μ(M × N) = conv μ((M × N)^(G × G₂))` for the product of two such actions, a torus of dimension up
to four
(`TauCeti.SmoothTwoForm.IsMomentMap.range_prod_eq_convexHull_image_fixedPoints_of_finrank_le_two`).
When the product has dimension more than two, neither of those convexity theorems applies to it
directly: its isotropy algebra at a point `(x, y)` with `x` fixed and `y` free is the Lie algebra of
the first factor, neither `0` nor everything.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15.
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 27.
-/

public section

open Set
open scoped ContDiff Manifold Pointwise

namespace TauCeti

/-! ### Transfer of the convexity theorem -/

section Transfer

variable {𝔤 : Type*} [AddCommGroup 𝔤] [Module ℝ 𝔤] {G : Type*} [Monoid G]
  {M : Type*} [MulAction G M] {μ : M → Module.Dual ℝ 𝔤}

/-- **The convexity theorem passes to subtori.** If a moment map `μ` of an action of `G` on `M`
satisfies `μ(M) = conv μ(M^G)`, and `K` acts on `M` through a map `f : K → G`, then for every
linear map `L : V → 𝔤`, such as the differential of a homomorphism `K →* G`, the map
`μ_K = (x ↦ μ x ∘ L)` satisfies `μ_K(M) = conv μ_K(M^K)`. -/
theorem range_comp_eq_convexHull_image_fixedPoints_of_smul_eq
    (hμ : range μ = convexHull ℝ (μ '' MulAction.fixedPoints G M))
    {V : Type*} [AddCommGroup V] [Module ℝ V] (L : V →ₗ[ℝ] 𝔤) {K : Type*} [Monoid K]
    [MulAction K M] (f : K → G) (hf : ∀ (k : K) (x : M), k • x = f k • x) :
    range (fun x ↦ (μ x).comp L) =
      convexHull ℝ ((fun x ↦ (μ x).comp L) '' MulAction.fixedPoints K M) := by
  have hL : (fun x ↦ (μ x).comp L) = L.dualMap ∘ μ := funext fun x ↦ (L.dualMap_apply' _).symm
  -- The image is the convex set `dφ^*(conv μ(M^G))`, which contains `μ_K(M^K)` and is spanned
  -- by the smaller set `μ_K(M^G)`.
  have hG : range (fun x ↦ (μ x).comp L) =
      convexHull ℝ ((fun x ↦ (μ x).comp L) '' MulAction.fixedPoints G M) := by
    rw [hL, range_comp, hμ, L.dualMap.image_convexHull, image_comp]
  refine le_antisymm ?_ ?_
  · rw [hG]
    exact convexHull_mono (image_mono (fixedPoints_subset_fixedPoints_of_smul_eq f hf))
  · rw [hG]
    exact convexHull_min ((image_subset_range _ _).trans hG.le) (convex_convexHull ℝ _)

/-- **The convexity theorem is invariant under translation.** For `ν ∈ 𝔤*`, the shifted moment
map `μ + ν` satisfies `(μ + ν)(M) = conv (μ + ν)(M^G)` exactly when `μ(M) = conv μ(M^G)`. -/
theorem range_add_const_eq_convexHull_image_fixedPoints_iff (ν : Module.Dual ℝ 𝔤) :
    (range fun x ↦ μ x + ν) = convexHull ℝ ((fun x ↦ μ x + ν) '' MulAction.fixedPoints G M) ↔
      range μ = convexHull ℝ (μ '' MulAction.fixedPoints G M) := by
  -- Both sides are images of the corresponding sets for `μ` under the translation by `ν`.
  have hA : (fun x ↦ μ x + ν) = (ν +ᵥ ·) ∘ μ :=
    funext fun x ↦ (add_comm _ _).trans (vadd_eq_add ν (μ x)).symm
  rw [hA, range_comp, image_comp, image_vadd, image_vadd, convexHull_vadd]
  exact (AddAction.injective ν).eq_iff

/-- **Naturality of the convexity theorem.** If `f : N → M` is a `G`-equivariant bijection, for
instance an equivariant symplectomorphism, then `μ ∘ f` satisfies
`(μ ∘ f)(N) = conv (μ ∘ f)(N^G)` exactly when `μ(M) = conv μ(M^G)`. -/
theorem range_comp_eq_convexHull_image_fixedPoints_iff {N : Type*} [MulAction G N] {f : N → M}
    (hf : Function.Bijective f) (hfg : ∀ (g : G) (y : N), f (g • y) = g • f y) :
    range (μ ∘ f) = convexHull ℝ ((μ ∘ f) '' MulAction.fixedPoints G N) ↔
      range μ = convexHull ℝ (μ '' MulAction.fixedPoints G M) := by
  rw [range_comp, hf.2.range_eq, image_univ, image_comp,
    MulAction.image_fixedPoints_of_bijective hf hfg]

variable {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] {G₂ : Type*} [Monoid G₂]
  {N : Type*} [MulAction G₂ N] {ν : N → Module.Dual ℝ E₂}
  {W : Type*} [AddCommGroup W] [Module ℝ W] (e : (Module.Dual ℝ 𝔤 × Module.Dual ℝ E₂) ≃ₗ[ℝ] W)

/-- The product moment map `(x, y) ↦ e (μ x, ν y)` is `e ∘ Prod.map μ ν`. -/
private theorem comp_prodMap_eq :
    e ∘ Prod.map μ ν = fun p : M × N ↦ e (μ p.1, ν p.2) :=
  funext fun p ↦ by rw [Function.comp_apply, Prod.map_apply]

/-- The image of the points fixed by a componentwise product action under a product moment map
`(x, y) ↦ e (μ x, ν y)` is the image under `e` of the product of the fixed-point images. -/
theorem image_fixedPoints_prod [MulAction (G × G₂) (M × N)]
    (hsmul : ∀ (g : G × G₂) (p : M × N), g • p = (g.1 • p.1, g.2 • p.2)) :
    (fun p : M × N ↦ e (μ p.1, ν p.2)) '' MulAction.fixedPoints (G × G₂) (M × N) =
      e '' ((μ '' MulAction.fixedPoints G M) ×ˢ (ν '' MulAction.fixedPoints G₂ N)) := by
  rw [fixedPoints_prod_of_smul_eq hsmul, ← prodMap_image_prod, ← image_comp,
    comp_prodMap_eq e]

/-- **The product polytope.** For a componentwise product action with product moment map
`(x, y) ↦ e (μ x, ν y)`, the convex hull of the images of the fixed points is the image under `e`
of the product of the convex hulls of the fixed-point images of the factors. -/
theorem convexHull_image_fixedPoints_prod [MulAction (G × G₂) (M × N)]
    (hsmul : ∀ (g : G × G₂) (p : M × N), g • p = (g.1 • p.1, g.2 • p.2)) :
    convexHull ℝ ((fun p : M × N ↦ e (μ p.1, ν p.2)) ''
        MulAction.fixedPoints (G × G₂) (M × N)) =
      e '' (convexHull ℝ (μ '' MulAction.fixedPoints G M) ×ˢ
        convexHull ℝ (ν '' MulAction.fixedPoints G₂ N)) := by
  have he := e.toLinearMap.image_convexHull
    ((μ '' MulAction.fixedPoints G M) ×ˢ (ν '' MulAction.fixedPoints G₂ N))
  rw [LinearEquiv.coe_coe] at he
  rw [image_fixedPoints_prod e hsmul, ← he, convexHull_prod]

/-- **The convexity theorem passes to products.** If `μ(M) = conv μ(M^G)` and
`ν(N) = conv ν(N^G₂)`, then the product moment map `(x, y) ↦ e (μ x, ν y)` of the componentwise
action of `G × G₂` on `M × N` satisfies the same equality, and its image is the product polytope
`e (conv μ(M^G) × conv ν(N^G₂))`. -/
theorem range_prod_eq_convexHull_image_fixedPoints [MulAction (G × G₂) (M × N)]
    (hμ : range μ = convexHull ℝ (μ '' MulAction.fixedPoints G M))
    (hν : range ν = convexHull ℝ (ν '' MulAction.fixedPoints G₂ N))
    (hsmul : ∀ (g : G × G₂) (p : M × N), g • p = (g.1 • p.1, g.2 • p.2)) :
    (range fun p : M × N ↦ e (μ p.1, ν p.2)) =
      convexHull ℝ ((fun p : M × N ↦ e (μ p.1, ν p.2)) ''
        MulAction.fixedPoints (G × G₂) (M × N)) := by
  rw [convexHull_image_fixedPoints_prod e hsmul, ← hμ, ← hν, ← range_prodMap, ← range_comp,
    comp_prodMap_eq e]

/-- **Connected fibres pass to products.** If every fibre of `μ` and every fibre of `ν` is
preconnected, then so is every fibre of the product moment map `(x, y) ↦ e (μ x, ν y)`. -/
theorem isPreconnected_preimage_singleton_prod [TopologicalSpace M] [TopologicalSpace N]
    (hμ : ∀ a, IsPreconnected (μ ⁻¹' {a})) (hν : ∀ b, IsPreconnected (ν ⁻¹' {b})) (c : W) :
    IsPreconnected ((fun p : M × N ↦ e (μ p.1, ν p.2)) ⁻¹' {c}) := by
  -- The fibre over `c = e (a, b)` is the product of the fibres of `μ` over `a` and `ν` over `b`.
  obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective c
  have : (fun p : M × N ↦ e (μ p.1, ν p.2)) ⁻¹' {e (a, b)} = (μ ⁻¹' {a}) ×ˢ (ν ⁻¹' {b}) := by
    ext p
    simp [e.injective.eq_iff]
  rw [this]
  exact (hμ a).prod (hν b)

end Transfer

end TauCeti

namespace TauCeti.SmoothTwoForm.IsMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-! ### Subtori -/

section Subtorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [IsMulCommutative G] [CompactSpace G] [PreconnectedSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [T2Space M]
  [BoundarylessManifold I' M] [CompactSpace M] [MulAction G M] [ContMDiffSMul I I' ∞ G M]
  {σ : SmoothTwoForm I' M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The polytope of a subtorus is the projection of the polytope of the torus.** Let `μ` be a
moment map of a smooth action of a compact connected commutative Lie group `G` on a compact
boundaryless manifold `M` with a nondegenerate two-form, and let `L : V → 𝔤` be linear, for
instance the differential of a homomorphism `K →* G`. Then the convex hull of the image of
`x ↦ μ x ∘ L` is spanned by its values at the points fixed by all of `G`. -/
theorem convexHull_range_comp_eq_convexHull_image_fixedPoints
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    (L : V →ₗ[ℝ] GroupLieAlgebra I G) :
    convexHull ℝ (range fun x ↦ (μ x).comp L) =
      convexHull ℝ ((fun x ↦ (μ x).comp L) '' MulAction.fixedPoints G M) := by
  have hL : (fun x ↦ (μ x).comp L) = L.dualMap ∘ μ := funext fun x ↦ (L.dualMap_apply' _).symm
  rw [hL, range_comp, image_comp, ← L.dualMap.image_convexHull, ← L.dualMap.image_convexHull,
    h.convexHull_range_eq_convexHull_image_fixedPoints hσ]

/-- **The image of a subtorus moment map lies in the projected polytope.** Let `μ` be a moment map
of a smooth action of a compact connected commutative Lie group `G` on a compact boundaryless
manifold `M` with a nondegenerate two-form, and let `L : V → 𝔤` be linear, for instance the
differential of a homomorphism `K →* G`. Then the image of `x ↦ μ x ∘ L` lies in the convex hull
of its values at the points fixed by all of `G`. -/
theorem range_comp_subset_convexHull_image_fixedPoints
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G I' M) μ) (hσ : σ.IsNondegenerate)
    (L : V →ₗ[ℝ] GroupLieAlgebra I G) :
    range (fun x ↦ (μ x).comp L) ⊆
      convexHull ℝ ((fun x ↦ (μ x).comp L) '' MulAction.fixedPoints G M) :=
  (subset_convexHull ℝ _).trans (h.convexHull_range_comp_eq_convexHull_image_fixedPoints hσ L).le

end Subtorus

/-! ### Products of tori of dimension at most two -/

section RankTwo

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [IsMulCommutative G] [CompactSpace G] [PreconnectedSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {M : Type*} [TopologicalSpace M] [ChartedSpace E' M] [IsManifold 𝓘(ℝ, E') ∞ M] [T2Space M]
  [CompactSpace M] [PreconnectedSpace M] [MulAction G M] [ContMDiffSMul I 𝓘(ℝ, E') ∞ G M]
  {σ : SmoothTwoForm 𝓘(ℝ, E') M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {G₂ : Type*} [TopologicalSpace G₂] [ChartedSpace H₂ G₂] [Group G₂] [LieGroup I₂ ∞ G₂]
  [T2Space G₂] [IsTopologicalGroup G₂] [IsMulCommutative G₂] [CompactSpace G₂]
  [PreconnectedSpace G₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N] [T2Space N]
  [CompactSpace N] [PreconnectedSpace N] [MulAction G₂ N] [ContMDiffSMul I₂ 𝓘(ℝ, F) ∞ G₂ N]
  {τ : SmoothTwoForm 𝓘(ℝ, F) N} {ν : N → Module.Dual ℝ (GroupLieAlgebra I₂ G₂)}

/-- **The convexity theorem for products of tori of dimension at most two.** Let tori `G` and
`G₂` of dimension at most two act smoothly on compact connected boundaryless finite-dimensional
manifolds `M` and `N`, preserving nondegenerate two-forms, with moment maps `μ` and `ν`. Then the
product moment map `(x, y) ↦ (μ x, ν y)` of the componentwise action of `G × G₂` on `M × N`, read
in the dual of the Lie algebra of `G × G₂`, has image the convex hull of its values at the fixed
points. -/
theorem range_prod_eq_convexHull_image_fixedPoints_of_finrank_le_two
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsNondegenerate)
    (hσG : ∀ (a : G) (x : M) (u v : TangentSpace 𝓘(ℝ, E') x),
      σ.eval₂ (a • x) (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (a • ·) x u)
        (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (a • ·) x v) = σ.eval₂ x u v)
    (hE : Module.finrank ℝ E ≤ 2)
    (h₂ : τ.IsMomentMap (InfinitesimalAction.fundamental I₂ G₂ 𝓘(ℝ, F) N) ν)
    (hτ : τ.IsNondegenerate)
    (hτG : ∀ (a : G₂) (y : N) (u v : TangentSpace 𝓘(ℝ, F) y),
      τ.eval₂ (a • y) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (a • ·) y u)
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (a • ·) y v) = τ.eval₂ y u v)
    (hE₂ : Module.finrank ℝ E₂ ≤ 2) [MulAction (G × G₂) (M × N)]
    (hsmul : ∀ (g : G × G₂) (p : M × N), g • p = (g.1 • p.1, g.2 • p.2)) :
    (range fun p : M × N ↦ Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I₂ G₂ (μ p.1, ν p.2)) =
      convexHull ℝ ((fun p : M × N ↦
          Lie.groupLieAlgebraDualProdDualEquivDual ℝ I G I₂ G₂ (μ p.1, ν p.2)) ''
        MulAction.fixedPoints (G × G₂) (M × N)) :=
  range_prod_eq_convexHull_image_fixedPoints _
    (h.range_eq_convexHull_image_fixedPoints_of_finrank_le_two hσ hσG hE)
    (h₂.range_eq_convexHull_image_fixedPoints_of_finrank_le_two hτ hτG hE₂) hsmul

end RankTwo

end TauCeti.SmoothTwoForm.IsMomentMap
