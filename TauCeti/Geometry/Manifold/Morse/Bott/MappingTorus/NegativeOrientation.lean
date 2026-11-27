/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.MappingTorus.Basic
public import TauCeti.Geometry.Manifold.Morse.Bott.NormalSubbundle
public import TauCeti.Topology.VectorBundle.Orientation.Cover
import TauCeti.Geometry.Manifold.Instances.MappingTorus.Vertical
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.VectorBundle.Quotient
import TauCeti.Topology.FiberBundle.Pullback

/-!
# Monodromy of the negative normal bundle of a critical circle in a mapping torus

Let `φ` be a diffeomorphism of a manifold `M`, `h : M → ℝ` a `φ`-invariant function and `x` a
nondegenerate critical point of `h` fixed by `φ`. On the mapping torus
`Y_φ = (ℝ × M) / ((t + 1, y) ∼ (t, φ y))` the circle `c : t ↦ [t, x]` is a Morse–Bott critical
submanifold of the induced function `f [t, y] = h y`
(`TauCeti.SmoothMappingTorus.isNondegenerateCriticalSubmanifold_closedOrbitEmbedding`), whose
negative normal bundle `ν⁻` has the rank `r` of the Morse index of `h` at `x`. Going once around the
circle, the fibre of `ν⁻` over `[0, x]` comes back to itself through the differential `dφₓ`. This
file shows that this monodromy can be read off from `dφₓ`: if `dφₓ` reverses the orientation of an
`r`-dimensional space of directions at `x` on which the Hessian of `h` is negative definite, then
`ν⁻` is not orientable
(`TauCeti.SmoothMappingTorus.isEmpty_vectorBundleOrientation_negativeNormalSpace_of_det_neg`).

The space of directions is given as the image of a linear map `j : V → TₓM` intertwining a linear
map `A` of `V` with `dφₓ`, so that `dφₓ` acts on it by `A`, with `det A < 0`. The vertical vectors
`d[t, ·]ₓ (j v)` along the circle have normal classes on which the normal Hessian is negative
definite, so projecting them onto the negative normal space of a fibre metric `g`, along its
positive normal space, is injective. A basis of `V` therefore gives a frame of `ν⁻` along the
circle, depending continuously on `t`. The identification `[1, y] = [0, φ y]` carries the frame at
`t = 1` to the frame at `t = 0` composed with `A`, so the orientations of the two frames are
opposite. The continuous path of orientations then ends at the opposite of its start, which no
orientation of `ν⁻` allows (`TauCeti.VectorBundleOrientation.isEmpty_of_continuous_basis`).

Only the negative space at the single point `x` enters, not the whole normal bundle: in the
mapping torus of `S² × S¹` by a pair of reflections, `dφₓ` reverses the negative plane of the
circle `(N, π)` while preserving the orientation of its whole normal space
(`TauCeti.Geometry.Manifold.Morse.Bott.Examples.SphereCircle`).

## Main results

* `TauCeti.SmoothMappingTorus.isEmpty_vectorBundleOrientation_negativeNormalSpace_of_det_neg`: if
  `dφₓ` acts with negative determinant on a space of directions of dimension the Morse index on
  which the Hessian of `h` is negative definite, the negative normal bundle of the critical circle
  through `x` is not orientable, for every `C^k` fibre metric.
* `TauCeti.SmoothMappingTorus.continuous_normalClass_mfderiv_mk`: the normal classes of the
  vertical vectors `d[t, ·]ₓ w` along a circle `t ↦ [t, x]` form a continuous path in its normal
  bundle.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 6.2 (orientations of Morse–Bott trajectory spaces).
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

noncomputable section

open Bundle Function Module Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [LocallyCompactSpace M] {φ : M ≃ₘ⟮I, I⟯ M} {x : M}

variable [FiniteDimensional ℝ E] (hn : (∞ : ℕ∞ω) ≠ 0)
  {c : SmoothEmbedding 𝓘(ℝ) (𝓘(ℝ).prod I) ∞ (AddCircle ((1 : ℕ) : ℝ)) (SmoothMappingTorus φ)}

/-- The normal classes of the vertical vectors `d[t, ·]ₓ w` at the points `c t = [t, x]` of a
circle `c` form a continuous path in the normal bundle of `c`. -/
theorem continuous_normalClass_mfderiv_mk (hc : ∀ t : ℝ, c t = mk φ t x)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (hdim : finrank ℝ P = finrank ℝ (ℝ × E) - finrank ℝ ℝ) (w : TangentSpace I x) :
    letI := c.normalSpaceFiberBundle hn hdim
    Continuous fun t : ℝ ↦ (⟨(t : AddCircle ((1 : ℕ) : ℝ)),
      c.isImmersion.normalClass t hn (mfderiv I (𝓘(ℝ).prod I) (mk φ t) x w)⟩ :
      TotalSpace P fun s ↦ c.isImmersion.NormalSpace s hn) := by
  let := c.normalSpaceFiberBundle hn hdim
  -- The vertical vectors form a continuous path in the pulled-back tangent bundle.
  have hq : Continuous fun t : ℝ ↦ (⟨(t : AddCircle ((1 : ℕ) : ℝ)),
      mfderiv I (𝓘(ℝ).prod I) (mk φ t) x w⟩ :
        TotalSpace (ℝ × E) (⇑c *ᵖ (TangentSpace (𝓘(ℝ).prod I)))) :=
    Pullback.continuous_iff.2 ⟨AddCircle.continuous_mk' (p := ((1 : ℕ) : ℝ)),
      (continuous_mfderiv_mk φ x w).congr fun t ↦ TotalSpace.ext (hc t).symm HEq.rfl⟩
  refine ((c.contMDiff_normalQuotientMap hn (m := 0) (by simp) hdim).continuous.comp hq).congr
    fun t ↦ ?_
  rw [Function.comp_apply, SmoothEmbedding.normalQuotientMap_apply]

variable [I.Boundaryless]

omit [FiniteDimensional ℝ E] in
/-- Along a critical circle `c : t ↦ [t, x]` of the function induced by `h`, the normal Hessian on
the normal class of a vertical vector `d[t, ·]ₓ w` is the Hessian of `h` at `x` on `w`. -/
private theorem normalHessian_normalClass_mfderiv_mk {h : M → ℝ} {hh : ∀ y, h (φ y) = h y}
    (hc : ∀ t : ℝ, c t = mk φ t x)
    (hs : c.IsNondegenerateCriticalSubmanifold (liftOfInvariant φ h hh)) (t : ℝ)
    (w : TangentSpace I x) :
    hs.normalHessian hn t (c.isImmersion.normalClass t hn (mfderiv I (𝓘(ℝ).prod I) (mk φ t) x w))
        (c.isImmersion.normalClass t hn (mfderiv I (𝓘(ℝ).prod I) (mk φ t) x w)) =
      criticalHessian I h x w w := by
  have hcomp : liftOfInvariant φ h hh ∘ mk φ t = h := funext fun y ↦ liftOfInvariant_mk φ _ t y
  have hH := criticalHessian_comp_apply (hc t).symm (hs.contMDiffAt t)
    ((contMDiff_mk φ t).contMDiffAt.of_le (by simp)) (hs.mem_criticalPoints t) w w
  rw [hcomp] at hH
  rw [hH]
  exact hs.normalHessian_normalClass hn t _ _

/-- **The seam of a critical circle.** At `[1, x] = [0, φ x] = [0, x]`, the projection to the
negative normal space of the normal class of the vertical vector `d[1, ·]ₓ w` is that of
`d[0, ·]ₓ (dφₓ w)`, as vectors of the total space of the negative normal bundle. -/
private theorem totalSpaceMk_negativeNormalProjection_one {f : SmoothMappingTorus φ → ℝ}
    (hc : ∀ t : ℝ, c t = mk φ t x) (hs : c.IsNondegenerateCriticalSubmanifold f)
    (g : RiemannianMetric fun s ↦ c.isImmersion.NormalSpace s hn) (F' : Type*)
    {w w' : TangentSpace I x} (hw : mfderiv I I φ x w = w') (hu hu') :
    (⟨((1 : ℝ) : AddCircle ((1 : ℕ) : ℝ)), ⟨hs.negativeNormalProjection hn g _
      (c.isImmersion.normalClass _ hn (mfderiv I (𝓘(ℝ).prod I) (mk φ 1) x w)), hu⟩⟩ :
        TotalSpace F' fun s ↦ hs.negativeNormalSpace hn g s) =
      ⟨((0 : ℝ) : AddCircle ((1 : ℕ) : ℝ)), ⟨hs.negativeNormalProjection hn g _
        (c.isImmersion.normalClass _ hn (mfderiv I (𝓘(ℝ).prod I) (mk φ 0) x w')), hu'⟩⟩ := by
  -- `x` is fixed by `φ`, since `[1, x] = c 1 = c 0 = [0, x]`, so `d[1, ·]ₓ w = d[0, ·]ₓ w'`.
  have hx : φ x = x := (mk_add_one_eq_mk_iff φ 0 x).1 (by
    rw [zero_add, ← hc, ← hc]
    exact congrArg c (by simp))
  have hvec : mfderiv I (𝓘(ℝ).prod I) (mk φ 1) x w = mfderiv I (𝓘(ℝ).prod I) (mk φ 0) x w' := by
    rw [← hw, ← mfderiv_mk_add_one_of_apply_eq φ (by simp) hx, zero_add]
  -- Projected normal classes over equal points of the circle with the same representative agree.
  have hmk {s s' : AddCircle ((1 : ℕ) : ℝ)} (hss : s = s') (u : ℝ × E) (hu hu') :
      (⟨s, ⟨hs.negativeNormalProjection hn g s (c.isImmersion.normalClass s hn u), hu⟩⟩ :
        TotalSpace F' fun s ↦ hs.negativeNormalSpace hn g s) =
        ⟨s', ⟨hs.negativeNormalProjection hn g s' (c.isImmersion.normalClass s' hn u), hu'⟩⟩ := by
    subst hss
    rfl
  exact (hmk (by simp) _ hu (hs.negativeNormalProjection_apply_mem hn _ _)).trans
    (congrArg (TotalSpace.mk _) (Subtype.ext
      (congrArg (fun u ↦ hs.negativeNormalProjection hn g _ (c.isImmersion.normalClass _ hn u))
        hvec)))

/-- **A negative space reversed by `dφₓ` makes the negative normal bundle of the critical circle
nonorientable.** Let `h` be a `φ`-invariant function and `c` an embedded circle `t ↦ [t, x]` in the
mapping torus of `φ` which is a Morse–Bott critical submanifold of the induced function
`f [t, y] = h y`, of Morse index `r`, with `f` of class `C^{k+2}` along it. Let `g` be a `C^k` fibre
metric on the normal bundle of `c`, with negative normal bundle `ν⁻`
(`hasLocalContMDiffSubbundleFrames_negativeNormalSpace`, in the namespace
`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`).
Suppose that `j : V → TₓM`, from an `r`-dimensional space `V`, takes values on which the Hessian of
`h` at `x` is negative definite, and that `dφₓ ∘ j = j ∘ A` for a linear map `A` of `V` with
`det A < 0`. Then `ν⁻` is not orientable.

The point `x` is fixed by `φ`, since `[1, x] = [0, x]`, so `dφₓ` acts on the tangent space at `x`.
The vertical vectors `d[t, ·]ₓ (j v)` project to a frame of `ν⁻` along the circle, and at the seam
`[1, y] = [0, φ y]` the frame at `t = 1` is the frame at `t = 0` composed with `A`: the orientation
of `ν⁻` has monodromy the sign of `det A`. -/
theorem isEmpty_vectorBundleOrientation_negativeNormalSpace_of_det_neg {h : M → ℝ}
    {hh : ∀ y, h (φ y) = h y} (hc : ∀ t : ℝ, c t = mk φ t x)
    (hs : c.IsNondegenerateCriticalSubmanifold (liftOfInvariant φ h hh)) {k : ℕ∞}
    (hf : ∀ s, ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) ((k : ℕ∞ω) + 2) (liftOfInvariant φ h hh) (c s))
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (hdim : finrank ℝ P = finrank ℝ (ℝ × E) - finrank ℝ ℝ)
    (g : letI := c.normalSpaceFiberBundle hn hdim
      letI := c.normalSpaceVectorBundle hn hdim
      ContMDiffRiemannianMetric 𝓘(ℝ) k P fun s ↦ c.isImmersion.NormalSpace s hn) {r : ℕ}
    (hr : ∀ s, manifoldMorseIndex (𝓘(ℝ).prod I) (liftOfInvariant φ h hh) (c s) = r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (hV : finrank ℝ V = r)
    (j : V →ₗ[ℝ] TangentSpace I x) (A : V →ₗ[ℝ] V) (hA : ∀ v, mfderiv I I φ x (j v) = j (A v))
    (hdet : LinearMap.det A < 0) (hneg : ∀ v ≠ 0, criticalHessian I h x (j v) (j v) < 0) :
    haveI : IsManifold (𝓘(ℝ).prod I) ((k : ℕ∞ω) + 2) (SmoothMappingTorus φ) :=
      .of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
    haveI : IsManifold 𝓘(ℝ) ((k : ℕ∞ω) + 1) (AddCircle ((1 : ℕ) : ℝ)) :=
      .of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
    letI := c.normalSpaceFiberBundle hn hdim
    letI := c.normalSpaceVectorBundle hn hdim
    letI := subbundleTopology P (F' := Fin r → ℝ) (hs.negativeNormalSpace hn g.toRiemannianMetric)
    letI := (hs.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn
      (WithTop.coe_le_coe.2 le_top : (k : ℕ∞ω) + 1 ≤ ∞) hf hdim g hr).fiberBundle
    haveI := (hs.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn
      (WithTop.coe_le_coe.2 le_top : (k : ℕ∞ω) + 1 ≤ ∞) hf hdim g hr).vectorBundle
    IsEmpty (VectorBundleOrientation (Fin r → ℝ)
      (fun s ↦ hs.negativeNormalSpace hn g.toRiemannianMetric s) (Fin r)) := by
  have : IsManifold (𝓘(ℝ).prod I) ((k : ℕ∞ω) + 2) (SmoothMappingTorus φ) :=
    .of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
  have : IsManifold 𝓘(ℝ) ((k : ℕ∞ω) + 1) (AddCircle ((1 : ℕ) : ℝ)) :=
    .of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
  have hk : (k : ℕ∞ω) + 1 ≤ ∞ := WithTop.coe_le_coe.2 le_top
  let := c.normalSpaceFiberBundle hn hdim
  let := c.normalSpaceVectorBundle hn hdim
  have hF := hs.hasLocalContMDiffSubbundleFrames_negativeNormalSpace hn hk hf hdim g hr
  let := subbundleTopology P (F' := Fin r → ℝ) (hs.negativeNormalSpace hn g.toRiemannianMetric)
  let := hF.fiberBundle
  have := hF.vectorBundle
  set ν := fun s ↦ hs.negativeNormalSpace hn g.toRiemannianMetric s
  set p := hs.negativeNormalProjection hn g.toRiemannianMetric
  -- Project the normal class of the vertical vector `d[t, ·]ₓ (j v)` to the negative normal space.
  let L (t : ℝ) : V →ₗ[ℝ] ν t :=
    (p t ∘ₗ c.isImmersion.normalClass t hn ∘ₗ
      ((mfderiv I (𝓘(ℝ).prod I) (mk φ t) x).toLinearMap ∘ₗ j)).codRestrict (ν t)
      fun v ↦ hs.negativeNormalProjection_apply_mem hn _ _
  -- This is injective: the normal Hessian is negative definite on the normal classes and
  -- nonnegative on the positive normal space, the kernel of the projection.
  have hL (t : ℝ) : Injective (L t) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv0
    have hpos := hs.normalHessian_apply_self_nonneg_of_mem_positiveNormalSpace hn
      g.toRiemannianMetric ((hs.negativeNormalProjection_apply_eq_zero_iff hn _).1
        (congrArg Subtype.val hv))
    exact (hneg v hv0).not_ge
      (le_of_le_of_eq hpos (normalHessian_normalClass_mfderiv_mk hn hc hs t (j v)))
  -- So a basis of `V` gives a frame of `ν⁻` at every point `[t, x]` of the circle.
  let b := Module.finBasisOfFinrankEq ℝ V hV
  let e (t : ℝ) : V ≃ₗ[ℝ] ν t := (L t).linearEquivOfInjective (hL t)
    (by rw [hV, hs.finrank_negativeNormalSpace, hr])
  let A' := A.equivOfDetNeZero hdet.ne
  refine VectorBundleOrientation.isEmpty_of_continuous_basis (by simp)
    (g := ((↑) : ℝ → AddCircle ((1 : ℕ) : ℝ))) (AddCircle.continuous_mk' (p := ((1 : ℕ) : ℝ)))
    (fun t ↦ b.map (e t)) (fun i ↦ ?_)
    (x := 0) (y := 1) (by simp) ((b.map A').map (e 0)) (fun i ↦ ?_) ?_
  · -- The frames vary continuously.
    refine (isEmbedding_totalSpace_subbundle P (Fin r → ℝ) ν).isInducing.continuous_iff.2 ?_
    exact (SmoothEmbedding.IsNondegenerateCriticalSubmanifold.contMDiff_negativeNormalProjection
      hn hs hk hf hdim g).continuous.comp (continuous_normalClass_mfderiv_mk hn hc hdim (j (b i)))
  · -- At the seam the frame at `t = 1` is the frame at `t = 0` composed with `A`.
    exact totalSpaceMk_negativeNormalProjection_one hn hc hs g.toRiemannianMetric _ (hA (b i)) _ _
  · -- Composing with `A`, of negative determinant, reverses the orientation.
    rw [Basis.orientation_map, (b.orientation_comp_linearEquiv_eq_neg_iff_det_neg A').2 hdet,
      Orientation.map_neg, ← Basis.orientation_map]

end TauCeti.SmoothMappingTorus
