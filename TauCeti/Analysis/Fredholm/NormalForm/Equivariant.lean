/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.NormalForm.Basic
import TauCeti.Analysis.Calculus.FDeriv.Comp
import TauCeti.Topology.Algebra.Module.Complement

/-!
# The equivariant Lyapunov–Schmidt reduction

Let `f : E → F` be a map whose derivative `T` at a point `a` is Fredholm, and let
`ContinuousLinearMap.FredholmPackage.obstructionMap` be its finite-dimensional obstruction in the
normal-form coordinates of a Fredholm package `pkg` of `T`. This file shows that the reduction
inherits the symmetries of `f`.

Suppose that continuous linear maps `σ : E → E` and `τ : F → F` intertwine `f` near `a`,
`f (σ x) = τ (f x)`, that `σ` fixes `a`, and that `σ` preserves the two summands of the domain
splitting of `pkg` and `τ` the two summands of its codomain splitting. Write `σ₀` and `τ₀`, `τ₁`
for the restrictions of `σ` and `τ` to the finite-dimensional summands and to the essential
codomain summand. Then near the coordinate of `a`:

* the normal-form coordinates intertwine `σ` with `τ₁ × σ₀`
  (`ContinuousLinearMap.FredholmPackage.normalFormMap_map`), and so does the inverse chart
  (`ContinuousLinearMap.FredholmPackage.eventually_normalFormOpenPartialHomeomorph_symm_prodMap`);
* the obstruction map intertwines `τ₁ × σ₀` with `τ₀`
  (`ContinuousLinearMap.FredholmPackage.eventually_obstructionMap_prodMap`), and its slice through
  the base point intertwines `σ₀` with `τ₀`
  (`ContinuousLinearMap.FredholmPackage.eventually_obstructionSlice_map`).

Two of these four invariance conditions hold automatically: differentiating `f ∘ σ = τ ∘ f` at `a`
gives `T ∘ σ = τ ∘ T`, so `σ` preserves the kernel of `T` and `τ` its range
(`ContinuousLinearMap.FredholmPackage.mapsTo_decDom_X₀`,
`ContinuousLinearMap.FredholmPackage.mapsTo_decCodom_X₁`), so the statements about the inverse
chart, the obstruction map and its slice assume only the invariance of the essential domain summand
and of the finite-dimensional codomain summand. Splittings with all four invariance
properties exist: if a finite group `G` of invertible order acts on
`E` and `F` by continuous linear maps and `T` intertwines the two actions, then `T` has a Fredholm
package whose four summands are `G`-invariant
(`ContinuousLinearMap.IsFredholm.exists_fredholmPackage_forall_mapsTo` in
`TauCeti.Analysis.Fredholm.Equivariant`), obtained by averaging projections over `G`.

The case of an involution acting by `-1` on the kernel and on the cokernel of `T` is the source of
odd obstruction maps (`ContinuousLinearMap.FredholmPackage.eventually_obstructionSlice_neg`). In
Taubes's count of pseudoholomorphic curves this is the expected situation at a period-doubling
bifurcation of a torus: the deformation problem of its double cover commutes with the deck
involution, the double cover itself is a fixed solution, and at the bifurcation the kernel of the
linearization consists of sections that are odd under the involution. The reduced obstruction slice
is then an odd function. This is the oddness at a single parameter value only: before the pitchfork
model `TauCeti.eventually_pitchfork` of `TauCeti.Analysis.Calculus.Bifurcation` applies, one still
needs a reduction of the whole one-parameter family, identifications of the kernel and cokernel
with the scalars, and the conditions on the parameter derivatives that the pitchfork model
requires. A pair of opposite nonzero zeros of the slice is one orbit of the involution, which would
correspond to one embedded torus in twice the class of the original one. This file proves only the
abstract reduction at a fixed parameter, not these further steps or geometric identifications.

## Main results

* `ContinuousLinearMap.FredholmPackage.mapsTo_decDom_X₀`,
  `ContinuousLinearMap.FredholmPackage.mapsTo_decCodom_X₁`: the symmetries of an equivariant map
  preserve the kernel and the range of its derivative at a fixed point.
* `ContinuousLinearMap.FredholmPackage.normalFormMap_map`,
  `ContinuousLinearMap.FredholmPackage.eventually_normalFormOpenPartialHomeomorph_symm_prodMap`:
  the normal-form chart and its inverse are equivariant.
* `ContinuousLinearMap.FredholmPackage.eventually_obstructionMap_prodMap`: the obstruction map of
  an equivariant map is equivariant.
* `ContinuousLinearMap.FredholmPackage.eventually_obstructionSlice_map`: so is its slice through the
  base point.
* `ContinuousLinearMap.FredholmPackage.eventually_obstructionSlice_neg`: for an involution acting by
  `-1` on the kernel and the cokernel, the slice is odd.

## References

* M. Golubitsky and D. G. Schaeffer, *Singularities and Groups in Bifurcation Theory, Vol. I*,
  Applied Mathematical Sciences 51, Springer, 1985, Chapter VII, §3 (the equivariant
  Lyapunov–Schmidt reduction).
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893.
-/

public section

open Set Filter Topology

namespace ContinuousLinearMap

namespace FredholmPackage

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {T : E →L[𝕜] F} (pkg : ContinuousLinearMap.FredholmPackage T)
  {σ : E →L[𝕜] E} {τ : F →L[𝕜] F}
  (hσ₀ : MapsTo σ pkg.decDom.X₀ pkg.decDom.X₀) (hσ₁ : MapsTo σ pkg.decDom.X₁ pkg.decDom.X₁)
  (hτ₀ : MapsTo τ pkg.decCodom.X₀ pkg.decCodom.X₀)
  (hτ₁ : MapsTo τ pkg.decCodom.X₁ pkg.decCodom.X₁)
  {f : E → F} {a : E}

include hτ₀ hτ₁ in
/-- The projection of the codomain onto its essential summand commutes with a map preserving both
codomain summands. -/
private theorem proj_map (y : F) :
    pkg.decCodom.proj (τ y) = τ.restrict (fun _ hx ↦ hτ₁ hx) (pkg.decCodom.proj y) := by
  rw [FredholmDecomposition.proj]
  exact Submodule.projectionOntoL_apply_of_mapsTo pkg.decCodom.isTopCompl hτ₁ hτ₀ y

include hσ₀ hσ₁ hτ₀ hτ₁ in
/-- **The normal-form coordinates are equivariant.** If `σ` fixes the base point `a`, preserves both
domain summands, `τ` preserves both codomain summands and `f (σ x) = τ (f x)`, then the normal-form
coordinates of `σ x` are those of `x` moved by the restrictions of `τ` and `σ`. -/
theorem normalFormMap_map (ha : σ a = a) {x : E} (hx : f (σ x) = τ (f x)) :
    pkg.normalFormMap f a (σ x) =
      Prod.map (τ.restrict fun _ hy ↦ hτ₁ hy) (σ.restrict fun _ hy ↦ hσ₀ hy)
        (pkg.normalFormMap f a x) := by
  rw [normalFormMap_apply, normalFormMap_apply, Prod.map_apply, hx, ← pkg.proj_map hτ₀ hτ₁,
    ← Submodule.projectionOntoL_apply_of_mapsTo pkg.decDom.isTopCompl.symm hσ₀ hσ₁, map_sub σ, ha]

/-- If `f` intertwines `σ` with `τ` near a point `a` fixed by `σ`, then `σ` preserves the kernel
of the derivative `T` of `f` at `a`, which is the finite-dimensional domain summand. -/
theorem mapsTo_decDom_X₀ (hf : HasFDerivAt f T a) (ha : σ a = a)
    (hfσ : ∀ᶠ x in 𝓝 a, f (σ x) = τ (f x)) : MapsTo σ pkg.decDom.X₀ pkg.decDom.X₀ := by
  rw [← pkg.ker_eq]
  have h := hf.comp_eq_comp_of_eventuallyEq σ.hasFDerivAt τ.hasFDerivAt ha hfσ
  exact Function.Semiconj.mapsTo_preimage (s := {0}) (t := {0})
    (fun x ↦ congr($h x) : Function.Semiconj T σ τ) (by simp)

/-- If `f` intertwines `σ` with `τ` near a point `a` fixed by `σ`, then `τ` preserves the range of
the derivative `T` of `f` at `a`, which is the essential codomain summand. -/
theorem mapsTo_decCodom_X₁ (hf : HasFDerivAt f T a) (ha : σ a = a)
    (hfσ : ∀ᶠ x in 𝓝 a, f (σ x) = τ (f x)) : MapsTo τ pkg.decCodom.X₁ pkg.decCodom.X₁ := by
  rw [← pkg.range_eq]
  have h := hf.comp_eq_comp_of_eventuallyEq σ.hasFDerivAt τ.hasFDerivAt ha hfσ
  rw [LinearMap.coe_range, coe_coe]
  exact Function.Semiconj.mapsTo_range fun x ↦ congr($h x)

section Chart

variable [CompleteSpace E]

include hσ₁ hτ₀ in
/-- **The inverse normal-form chart is equivariant.** Near the coordinate of the base point, the
inverse normal-form chart intertwines the restrictions of `τ` and `σ` with `σ`. Only the invariance
of the complementary summands is assumed: `σ` preserves the finite-dimensional domain summand by
`mapsTo_decDom_X₀` and `τ` the essential codomain summand by `mapsTo_decCodom_X₁`. -/
theorem eventually_normalFormOpenPartialHomeomorph_symm_prodMap (hf : HasStrictFDerivAt f T a)
    (ha : σ a = a) (hfσ : ∀ᶠ x in 𝓝 a, f (σ x) = τ (f x)) :
    ∀ᶠ y in 𝓝 (pkg.decCodom.proj (f a), (0 : pkg.decDom.X₀)),
      (pkg.normalFormOpenPartialHomeomorph hf).symm
          (Prod.map (τ.restrict fun _ hy ↦ pkg.mapsTo_decCodom_X₁ hf.hasFDerivAt ha hfσ hy)
            (σ.restrict fun _ hy ↦ pkg.mapsTo_decDom_X₀ hf.hasFDerivAt ha hfσ hy) y) =
        σ ((pkg.normalFormOpenPartialHomeomorph hf).symm y) := by
  have hσ₀ := pkg.mapsTo_decDom_X₀ hf.hasFDerivAt ha hfσ
  have hτ₁ := pkg.mapsTo_decCodom_X₁ hf.hasFDerivAt ha hfσ
  set Φ := pkg.normalFormOpenPartialHomeomorph hf
  -- Near `a`, `f` is equivariant and `σ` maps into the source of the chart.
  have hσsrc : ∀ᶠ x in 𝓝 a, σ x ∈ Φ.source :=
    σ.continuous.continuousAt.preimage_mem_nhds
      (by rw [ha]; exact Φ.open_source.mem_nhds (pkg.mem_normalFormOpenPartialHomeomorph_source hf))
  filter_upwards [Φ.open_target.mem_nhds (pkg.normalFormOpenPartialHomeomorph_self_mem_target hf),
    pkg.eventually_normalFormOpenPartialHomeomorph_symm hf (hfσ.and hσsrc)] with y hy ⟨hfy, hsrc⟩
  have hΦ : Φ (σ (Φ.symm y)) =
      Prod.map (τ.restrict fun _ hy ↦ hτ₁ hy) (σ.restrict fun _ hy ↦ hσ₀ hy) y := by
    rw [pkg.normalFormOpenPartialHomeomorph_apply, pkg.normalFormMap_map hσ₀ hσ₁ hτ₀ hτ₁ ha hfy,
      ← pkg.normalFormOpenPartialHomeomorph_apply hf, Φ.right_inv hy]
  rw [← hΦ, Φ.left_inv hsrc]

include hσ₁ hτ₀ in
/-- **The obstruction map is equivariant.** If `σ` fixes the base point `a` and preserves the
essential domain summand, `τ` preserves the finite-dimensional codomain summand and `f` intertwines
`σ` with `τ` near `a`, then near the coordinate of `a` the obstruction map intertwines the
restrictions of `τ` and `σ` with the restriction of `τ` to the finite-dimensional codomain summand.
The other two summands are preserved by `mapsTo_decDom_X₀` and `mapsTo_decCodom_X₁`. -/
theorem eventually_obstructionMap_prodMap (hf : HasStrictFDerivAt f T a) (ha : σ a = a)
    (hfσ : ∀ᶠ x in 𝓝 a, f (σ x) = τ (f x)) :
    ∀ᶠ y in 𝓝 (pkg.decCodom.proj (f a), (0 : pkg.decDom.X₀)),
      pkg.obstructionMap hf
          (Prod.map (τ.restrict fun _ hy ↦ pkg.mapsTo_decCodom_X₁ hf.hasFDerivAt ha hfσ hy)
            (σ.restrict fun _ hy ↦ pkg.mapsTo_decDom_X₀ hf.hasFDerivAt ha hfσ hy) y) =
        τ.restrict (fun _ hy ↦ hτ₀ hy) (pkg.obstructionMap hf y) := by
  filter_upwards [pkg.eventually_normalFormOpenPartialHomeomorph_symm_prodMap hσ₁ hτ₀ hf ha hfσ,
    pkg.eventually_normalFormOpenPartialHomeomorph_symm hf hfσ] with y hy hfy
  rw [obstructionMap_apply, obstructionMap_apply, hy, hfy]
  exact Submodule.projectionOntoL_apply_of_mapsTo pkg.decCodom.isTopCompl.symm hτ₀
    (pkg.mapsTo_decCodom_X₁ hf.hasFDerivAt ha hfσ) _

include hσ₁ hτ₀ in
/-- **The obstruction slice through the base point is equivariant.** Under the hypotheses of
`eventually_obstructionMap_prodMap`, the essential coordinate `pkg.decCodom.proj (f a)` of the base
point is fixed by `τ`, and near `0` the slice of the obstruction map through it intertwines the
restrictions of `σ` and `τ` to the finite-dimensional summands. -/
theorem eventually_obstructionSlice_map (hf : HasStrictFDerivAt f T a) (ha : σ a = a)
    (hfσ : ∀ᶠ x in 𝓝 a, f (σ x) = τ (f x)) :
    ∀ᶠ z in 𝓝 (0 : pkg.decDom.X₀),
      pkg.obstructionSlice hf (pkg.decCodom.proj (f a))
          (σ.restrict (fun _ hy ↦ pkg.mapsTo_decDom_X₀ hf.hasFDerivAt ha hfσ hy) z) =
        τ.restrict (fun _ hy ↦ hτ₀ hy) (pkg.obstructionSlice hf (pkg.decCodom.proj (f a)) z) := by
  have hτ₁ := pkg.mapsTo_decCodom_X₁ hf.hasFDerivAt ha hfσ
  have hfa : τ (f a) = f a := by rw [← hfσ.self_of_nhds, ha]
  have hy₁ :
      τ.restrict (fun _ hy ↦ hτ₁ hy) (pkg.decCodom.proj (f a)) = pkg.decCodom.proj (f a) := by
    rw [← pkg.proj_map hτ₀ hτ₁, hfa]
  have hslice : Tendsto (fun z : pkg.decDom.X₀ ↦ (pkg.decCodom.proj (f a), z)) (𝓝 0)
      (𝓝 (pkg.decCodom.proj (f a), 0)) :=
    (continuous_const.prodMk continuous_id).tendsto' _ _ rfl
  filter_upwards [hslice.eventually (pkg.eventually_obstructionMap_prodMap hσ₁ hτ₀ hf ha hfσ)]
    with z hz
  rw [obstructionSlice_apply, obstructionSlice_apply, ← hz, Prod.map_apply, hy₁]

/-- **Odd obstruction slices.** Suppose that `σ` fixes the base point `a`, acts by `-1` on the
finite-dimensional domain summand (the kernel of `T`) and preserves the essential one, that `τ` acts
by `-1` on the finite-dimensional codomain summand, and that `f` intertwines `σ` with `τ` near `a`.
Then near `0` the slice of the obstruction map through the base point is odd. -/
theorem eventually_obstructionSlice_neg (hf : HasStrictFDerivAt f T a)
    (hσ₀ : ∀ x ∈ pkg.decDom.X₀, σ x = -x) (hσ₁ : MapsTo σ pkg.decDom.X₁ pkg.decDom.X₁)
    (hτ₀ : ∀ y ∈ pkg.decCodom.X₀, τ y = -y) (ha : σ a = a) (hfσ : ∀ᶠ x in 𝓝 a, f (σ x) = τ (f x)) :
    ∀ᶠ z in 𝓝 (0 : pkg.decDom.X₀),
      pkg.obstructionSlice hf (pkg.decCodom.proj (f a)) (-z) =
        -pkg.obstructionSlice hf (pkg.decCodom.proj (f a)) z := by
  have hσ₀' := pkg.mapsTo_decDom_X₀ hf.hasFDerivAt ha hfσ
  have hτ₀' : MapsTo τ pkg.decCodom.X₀ pkg.decCodom.X₀ := fun y hy ↦ by
    rw [SetLike.mem_coe, hτ₀ y hy]
    exact neg_mem hy
  filter_upwards [pkg.eventually_obstructionSlice_map hσ₁ hτ₀' hf ha hfσ] with z hz
  have hσz : σ.restrict (fun _ hy ↦ hσ₀' hy) z = -z :=
    Subtype.ext <| by rw [coe_restrict_apply, Submodule.coe_neg]; exact hσ₀ z z.property
  rw [← hσz, hz]
  exact Subtype.ext <| by
    rw [coe_restrict_apply, Submodule.coe_neg]
    exact hτ₀ _ (Subtype.property _)

end Chart

end FredholmPackage

end ContinuousLinearMap
