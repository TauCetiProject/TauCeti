/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Incidence.Basic
public import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Coprod

/-!
# Transversality of a map to a map

Let `g : M → V` and `j : N → V` be maps from charted spaces over models with corners `I` and `J`
into a normed space `V`. The map `g` is *transverse to* `j` at `x : M`
(`TauCeti.IsTransverseAt I J g j x`) when for every `y : N` with `g x = j y` the map
`(u, v) ↦ dg_x u - dj_y v` from `T_x M × T_y N` onto `V` is surjective; equivalently, the images
of the two differentials together span `V` (`TauCeti.isTransverseAt_iff_range_sup_eq_top`). The
condition holds vacuously when `g x` is not in the range of `j`, and `j` need not be an embedding.
Derivatives are read through `mvfderiv`, which is zero where a map is not differentiable, so the
predicate is meant for differentiable maps.

On normed spaces the differentials are Fréchet derivatives
(`TauCeti.isTransverseAt_modelWithCornersSelf_iff`), and for a parametrized family
`F : E × P → V` the slice `F(·, p)` is transverse to `j` at every point exactly when `p` is a
regular incidence parameter (`TauCeti.isRegularIncidenceParameter_iff_forall_isTransverseAt`).
Transversality at `x` depends only on the germ of `g` at `x`
(`Filter.EventuallyEq.isTransverseAt_iff`); it is unchanged when `g` and `j` are both followed by
one diffeomorphism of `V`, in particular by an affine isomorphism
(`Diffeomorph.isTransverseAt_comp_iff`), and when either source is reparametrized by a
diffeomorphism (`Diffeomorph.isTransverseAt_comp_diffeomorph_iff`,
`Diffeomorph.isTransverseAt_comp_diffeomorph_right_iff`). When the model dimensions satisfy
`dim E + dim F < dim V`, transversality at `x` means that `g x` avoids the range of `j`
(`TauCeti.isTransverseAt_iff_notMem_range`).

## Main declarations

* `TauCeti.IsTransverseAt`: transversality of `g` to `j` at a point of the source of `g`.
* `TauCeti.isTransverseAt_of_notMem_range`, `TauCeti.isTransverseAt_of_surjective_mvfderiv_left`,
  `TauCeti.isTransverseAt_of_surjective_mvfderiv_right`: the vacuous case and submersions.
* `TauCeti.isRegularIncidenceParameter_iff_forall_isTransverseAt`: agreement with regular
  incidence parameters on normed spaces.
* `Diffeomorph.isTransverseAt_comp_iff`, `Diffeomorph.isTransverseAt_comp_diffeomorph_iff`,
  `Diffeomorph.isTransverseAt_comp_diffeomorph_right_iff`: invariance under diffeomorphisms.
* `TauCeti.isTransverseAt_iff_notMem_range`: dimension-counting avoidance.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 6, *Transversality*.
-/

public section

open Function Set Filter Module
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

section Definition

variable (I J) in
/-- A map `g : M → V` is *transverse to* `j : N → V` at `x : M` when for every `y : N` with
`g x = j y` the map `(u, v) ↦ dg_x u - dj_y v` from `T_x M × T_y N` to `V` is surjective. This
holds vacuously when no `y` has `g x = j y`. The differentials are `mvfderiv`, which is zero
where a map is not differentiable. -/
def IsTransverseAt (g : M → V) (j : N → V) (x : M) : Prop :=
  ∀ y, g x = j y → Surjective ((mvfderiv I g x).coprod (-mvfderiv J j y))

variable {g : M → V} {j : N → V} {x : M}

/-- Unfold `TauCeti.IsTransverseAt`. -/
theorem isTransverseAt_iff :
    IsTransverseAt I J g j x ↔
      ∀ y, g x = j y → Surjective ((mvfderiv I g x).coprod (-mvfderiv J j y)) :=
  Iff.rfl

/-- `g` is transverse to `j` at `x` exactly when, at every `y` with `g x = j y`, the ranges of the
two differentials together span `V`. -/
theorem isTransverseAt_iff_range_sup_eq_top :
    IsTransverseAt I J g j x ↔
      ∀ y, g x = j y → (mvfderiv I g x).range ⊔ (mvfderiv J j y).range = ⊤ := by
  simp only [isTransverseAt_iff, ContinuousLinearMap.surjective_coprod_neg_iff]

/-- At an incidence `g x = j y` of a transverse pair, the ranges of the two differentials together
span `V`. -/
theorem IsTransverseAt.range_sup_eq_top (h : IsTransverseAt I J g j x) {y : N}
    (hy : g x = j y) : (mvfderiv I g x).range ⊔ (mvfderiv J j y).range = ⊤ :=
  isTransverseAt_iff_range_sup_eq_top.1 h y hy

/-- If `g x` is not in the range of `j`, then `g` is transverse to `j` at `x`, vacuously. -/
theorem isTransverseAt_of_notMem_range (h : g x ∉ range j) : IsTransverseAt I J g j x :=
  fun y hy ↦ (h ⟨y, hy.symm⟩).elim

/-- A map whose differential at `x` is surjective is transverse at `x` to every map. -/
theorem isTransverseAt_of_surjective_mvfderiv_left (h : Surjective (mvfderiv I g x)) :
    IsTransverseAt I J g j x :=
  isTransverseAt_iff_range_sup_eq_top.2 fun _ _ ↦
    eq_top_mono le_sup_left (LinearMap.range_eq_top.2 h)

/-- If the differential of `j` is surjective at every `y` with `g x = j y`, then `g` is transverse
to `j` at `x`, whatever the differential of `g`. -/
theorem isTransverseAt_of_surjective_mvfderiv_right
    (h : ∀ y, g x = j y → Surjective (mvfderiv J j y)) : IsTransverseAt I J g j x :=
  isTransverseAt_iff_range_sup_eq_top.2 fun y hy ↦
    eq_top_mono le_sup_right (LinearMap.range_eq_top.2 (h y hy))

/-- **Locality.** For a fixed `j`, transversality of `g` to `j` at `x` depends only on the germ of
`g` at `x`. -/
theorem _root_.Filter.EventuallyEq.isTransverseAt_iff {g₁ g₂ : M → V} (h : g₁ =ᶠ[𝓝 x] g₂) :
    IsTransverseAt I J g₁ j x ↔ IsTransverseAt I J g₂ j x := by
  simp only [TauCeti.isTransverseAt_iff, h.eq_of_nhds, h.mvfderiv_eq]

/-- **Dimension-counting avoidance.** If the model dimensions satisfy `dim E + dim F < dim V`, then
`g` is transverse to `j` at `x` exactly when `g x` is not in the range of `j`. -/
theorem isTransverseAt_iff_notMem_range [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (hdim : finrank 𝕜 E + finrank 𝕜 F < finrank 𝕜 V) :
    IsTransverseAt I J g j x ↔ g x ∉ range j := by
  refine ⟨fun h ⟨y, hy⟩ ↦ ?_, isTransverseAt_of_notMem_range⟩
  have hd := LinearMap.finrank_le_finrank_of_surjective
    (f := ((mvfderiv I g x).coprod (-mvfderiv J j y) : TangentSpace I x × TangentSpace J y →ₗ[𝕜] V))
    (isTransverseAt_iff.1 h y hy.symm)
  rw [finrank_prod] at hd
  -- The tangent spaces `TangentSpace I x` and `TangentSpace J y` are the model spaces `E` and `F`.
  exact hd.not_gt hdim

end Definition

section NormedSpace

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']

/-- On normed spaces, `g` is transverse to `j` at `x` when `(u, v) ↦ Dg(x) u - Dj(y) v` is
surjective at every `y` with `g x = j y`, with Fréchet derivatives. -/
theorem isTransverseAt_modelWithCornersSelf_iff {g : E' → V} {j : F' → V} {x : E'} :
    IsTransverseAt 𝓘(𝕜, E') 𝓘(𝕜, F') g j x ↔
      ∀ y, g x = j y → Surjective ((fderiv 𝕜 g x).coprod (-fderiv 𝕜 j y)) := by
  simp only [isTransverseAt_iff, mvfderiv_eq_fderiv]
  refine forall₂_congr fun y _ ↦ ?_
  -- The tangent spaces of `E'` and `F'` are identified with `E'` and `F'` by
  -- `NormedSpace.fromTangentSpace`, and precomposing with a bijection preserves surjectivity.
  have hcomp : ⇑((fderiv 𝕜 g x ∘L (NormedSpace.fromTangentSpace (𝕜 := 𝕜) x : _ →L[𝕜] E')).coprod
      (-(fderiv 𝕜 j y ∘L (NormedSpace.fromTangentSpace (𝕜 := 𝕜) y : _ →L[𝕜] F')))) =
        (fderiv 𝕜 g x).coprod (-fderiv 𝕜 j y) ∘
          Prod.map (NormedSpace.fromTangentSpace (𝕜 := 𝕜) x)
            (NormedSpace.fromTangentSpace (𝕜 := 𝕜) y) := by
    ext ⟨u, v⟩
    simp
  rw [hcomp, Surjective.of_comp_iff _ ((NormedSpace.fromTangentSpace x).surjective.prodMap
    (NormedSpace.fromTangentSpace y).surjective)]

end NormedSpace

section Incidence

variable {E' W P V' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V'] [NormedSpace ℝ V']

/-- **Agreement with regular incidence parameters.** If the family `F : E × P → V` and the map
`j` are differentiable at the incidence points of the slice at `p`, then `p` is a regular
incidence parameter exactly when the slice `F(·, p)` is transverse to `j` at every point. -/
theorem isRegularIncidenceParameter_iff_forall_isTransverseAt {F : E' × P → V'} {j : W → V'}
    {p : P} (hF : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ F (x, p))
    (hj : ∀ x y, F (x, p) = j y → DifferentiableAt ℝ j y) :
    IsRegularIncidenceParameter F j p ↔
      ∀ x, IsTransverseAt 𝓘(ℝ, E') 𝓘(ℝ, W) (fun x' ↦ F (x', p)) j x := by
  simp only [isRegularIncidenceParameter_iff_surjective_coprod hF hj,
    isTransverseAt_modelWithCornersSelf_iff]

end Incidence

end TauCeti

namespace Diffeomorph

open TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {g : M → V} {j : N → V} {x : M} {n : ℕ∞ω}

/-- **Invariance under diffeomorphisms of the target.** Following `g` and `j` by one
diffeomorphism `χ : V → V'` does not change transversality. This applies in particular to affine
isomorphisms `v ↦ L v + b` of `V`. -/
theorem isTransverseAt_comp_iff {V' : Type*} [NormedAddCommGroup V'] [NormedSpace 𝕜 V']
    (χ : V ≃ₘ^n⟮𝓘(𝕜, V), 𝓘(𝕜, V')⟯ V') (hn : n ≠ 0) :
    IsTransverseAt I J (χ ∘ g) (χ ∘ j) x ↔ IsTransverseAt I J g j x := by
  have hχ : Injective χ := χ.toHomeomorph.injective
  simp only [isTransverseAt_iff, comp_apply, hχ.eq_iff, χ.mvfderiv_diffeomorph_comp hn]
  refine forall₂_congr fun y hy ↦ ?_
  rw [← hy, ← ContinuousLinearMap.comp_neg, ← ContinuousLinearMap.comp_coprod,
    ContinuousLinearMap.coe_comp]
  exact Surjective.of_comp_iff' (χ.bijective_fderiv hn (g x)) _

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- **Invariance under diffeomorphisms of the first source.** For a diffeomorphism `ψ : M' → M`,
`g ∘ ψ` is transverse to `j` at `x` exactly when `g` is transverse to `j` at `ψ x`. -/
theorem isTransverseAt_comp_diffeomorph_iff (ψ : M' ≃ₘ^n⟮I', I⟯ M) (hn : n ≠ 0) {x : M'} :
    IsTransverseAt I' J (g ∘ ψ) j x ↔ IsTransverseAt I J g j (ψ x) := by
  simp only [isTransverseAt_iff_range_sup_eq_top, comp_apply,
    ψ.range_mvfderiv_comp_diffeomorph hn]

/-- **Invariance under diffeomorphisms of the second source.** For a diffeomorphism `ψ : N' → N`,
`g` is transverse to `j ∘ ψ` at `x` exactly when it is transverse to `j` at `x`. -/
theorem isTransverseAt_comp_diffeomorph_right_iff {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'}
    {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N'] (ψ : N' ≃ₘ^n⟮J', J⟯ N) (hn : n ≠ 0) :
    IsTransverseAt I J' g (j ∘ ψ) x ↔ IsTransverseAt I J g j x := by
  simp only [isTransverseAt_iff_range_sup_eq_top, comp_apply,
    ψ.range_mvfderiv_comp_diffeomorph hn]
  refine ⟨fun h y hy ↦ ?_, fun h y' hy ↦ h (ψ y') hy⟩
  have hψ := h (ψ.symm y) (by rwa [ψ.apply_symm_apply])
  rwa [ψ.apply_symm_apply] at hψ

end Diffeomorph
