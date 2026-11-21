/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus.ClosedOrbit
public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Manifold.Morse.Prod
public import TauCeti.Geometry.Manifold.Morse.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Morse.Submersion
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Morse functions of the fibre coordinate on mapping tori

Let `φ : M ≃ₘ⟮I, I⟯ M` be a diffeomorphism and `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` its
smooth mapping torus (`TauCeti.SmoothMappingTorus φ`). This file studies a function `f` on `Y_φ`
which depends only on the fibre coordinate: `f [t, x] = g x` for a function `g` on `M`, which is
then invariant under `φ`. In the coordinates `(t, x)` such an `f` is the function `g ∘ Prod.snd`
of the second factor of `ℝ × M`, and the quotient map `ℝ × M → Y_φ` is a local diffeomorphism.
So `f` is `C^m` exactly when `g` is (`TauCeti.SmoothMappingTorus.contMDiff_iff_of_forall_mk_eq`),
its critical points are the points `[t, x]` over critical points `x` of `g`, and at such a point
its Morse index is the Morse index of `g` at `x`; at a nondegenerate critical point of `g`, the
kernel of the Hessian of `f` is spanned by the time direction `∂_t`.

If `x` is a fixed point of `φ`, the curve `[t] ↦ [t, x]` is an embedded circle in `Y_φ`, the closed
orbit of the suspension flow through `[0, x]` (`TauCeti.SmoothMappingTorus.fixedPtCircle`, whose
velocity is `∂_t` by `TauCeti.SmoothMappingTorus.hasMFDerivAt_fixedPtCircle`). When
`x` is a nondegenerate critical point of `g`, the time direction is the whole kernel of the Hessian
of `f` along this circle, which is therefore a Morse–Bott critical submanifold of `f`, of the
Morse index of `g` at `x`. Hence, if `g` is a Morse function whose critical points are all fixed by
`φ`, the circles through them exhibit `f` as a Morse–Bott function
(`TauCeti.IsMorse.isMorseBottFamily_fixedPtCircle`).

This is how Morse–Bott functions with critical circles are built on mapping tori. The example
in `TauCeti.Geometry.Manifold.Morse.Bott.Examples.SphereCircleMappingTorus` is the mapping torus of
`(p, w) ↦ (ρ p, conj w)` on `S² × S¹`, with `ρ` a reflection of the sphere, and the function
`[t, p, w] ↦ z(p) + ε Re w`, which has four critical circles.

## Main results

In the namespace `TauCeti.SmoothMappingTorus`, for `f` with `f [t, x] = g x`:

* `mk_mem_criticalPoints_iff_of_forall_mk_eq`: `[t, x]` is a critical point of `f` exactly when
  `x` is a critical point of `g`.
* `manifoldMorseIndex_mk_of_forall_mk_eq`: the Morse index of `f` at `[t, x]` is that of `g` at
  `x`.
* `ker_criticalHessian_mk_le_of_forall_mk_eq`: at a nondegenerate critical point, the kernel of the
  Hessian of `f` lies in the line spanned by `∂_t`.
* `isNondegenerateCriticalSubmanifold_fixedPtCircle`: the circle through a fixed nondegenerate
  critical point of `g` is a Morse–Bott critical submanifold of `f`.

Finally, `TauCeti.IsMorse.isMorseBottFamily_fixedPtCircle`: if `g` is Morse and `φ` fixes its
critical points, the circles through them exhibit `f` as a Morse–Bott function.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 6.2 (Morse–Bott functions and the orientations of
  their trajectory spaces).
-/

public section

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ### Critical points and Morse indices of functions of the fibre coordinate -/

section Critical

variable [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] (φ : M ≃ₘ⟮I, I⟯ M)
  {f : SmoothMappingTorus φ → ℝ} {g : M → ℝ} (hfg : ∀ t x, f (mk φ t x) = g x)

include hfg in
/-- **Critical points of a function of the fibre coordinate.** If `f [t, x] = g x` for all `t` and
`x`, then `[t, x]` is a critical point of `f` exactly when `x` is a critical point of `g`. -/
theorem mk_mem_criticalPoints_iff_of_forall_mk_eq {t : ℝ} {x : M} :
    mk φ t x ∈ criticalPoints (𝓘(ℝ).prod I) f ↔ x ∈ criticalPoints I g := by
  -- Along the local diffeomorphism `(t, x) ↦ [t, x]`, `f` reads as `g ∘ Prod.snd`.
  have h := (isLocalDiffeomorph_uncurry_mk φ (t, x)).mem_criticalPoints_comp_iff (by simp) (f := f)
  rw [comp_uncurry_mk_eq_comp_snd φ hfg] at h
  exact h.symm.trans mem_criticalPoints_comp_snd_iff

include hfg in
/-- **The Morse index of a function of the fibre coordinate.** If `f [t, x] = g x` for all `t` and
`x`, then at a critical point `x` of `g` at which `g` is `C²`, the Morse index of `f` at `[t, x]`
is the Morse index of `g` at `x`. -/
theorem manifoldMorseIndex_mk_of_forall_mk_eq [I.Boundaryless] {t : ℝ} {x : M}
    (hgx : ContMDiffAt I 𝓘(ℝ) 2 g x) (hx : x ∈ criticalPoints I g) :
    manifoldMorseIndex (𝓘(ℝ).prod I) f (mk φ t x) = manifoldMorseIndex I g x := by
  have hf := (contMDiffAt_mk_iff_of_forall_mk_eq φ hfg (by simp : (2 : ℕ∞ω) ≤ ∞) (t := t)).2 hgx
  have h := (isLocalDiffeomorph_uncurry_mk φ (t, x)).manifoldMorseIndex_comp (by simp) hf
    ((mk_mem_criticalPoints_iff_of_forall_mk_eq φ hfg).2 hx)
  rw [comp_uncurry_mk_eq_comp_snd φ hfg, manifoldMorseIndex_comp_snd] at h
  exact h.symm

include hfg in
/-- **The kernel of the Hessian of a function of the fibre coordinate.** If `f [t, x] = g x` for
all `t` and `x`, then at a nondegenerate critical point `x` of `g` the kernel of the critical
Hessian of `f` at `[t, x]` lies in the line spanned by the time direction `∂_t`
(`TauCeti.SmoothMappingTorus.timeVectorField`). -/
theorem ker_criticalHessian_mk_le_of_forall_mk_eq [I.Boundaryless] {t : ℝ} {x : M}
    (hx : IsManifoldNondegenerateCriticalPoint I g x) :
    (criticalHessian (𝓘(ℝ).prod I) f (mk φ t x)).ker ≤ ℝ ∙ timeVectorField φ (mk φ t x) := by
  intro v hv
  obtain ⟨b, w, rfl⟩ := exists_mfderiv_uncurry_mk_eq φ t x v
  have hf := (contMDiffAt_mk_iff_of_forall_mk_eq φ hfg (by simp : (2 : ℕ∞ω) ≤ ∞) (t := t)).2
    hx.contMDiffAt
  have hcrit := (mk_mem_criticalPoints_iff_of_forall_mk_eq φ hfg (t := t)).2
    hx.mem_criticalPoints
  -- Pull the kernel back along `(t, x) ↦ [t, x]`, where `f` reads as `g ∘ Prod.snd`, and then
  -- along the second projection, to the kernel of the Hessian of `g`, which is zero.
  have hker := ((isLocalDiffeomorph_uncurry_mk φ (t, x)).isRegularPoint (by simp))
    |>.ker_criticalHessian_comp hf ((contMDiff_uncurry_mk φ (t, x)).of_le (by simp)) hcrit
  rw [comp_uncurry_mk_eq_comp_snd φ hfg,
    ker_criticalHessian_comp_snd (p := (t, x)) hx.contMDiffAt hx.mem_criticalPoints] at hker
  have hw : (Manifold.tangentSpaceProdEquiv (t, x)).symm (b, w) ∈
      (criticalHessian (𝓘(ℝ).prod I) f (uncurry (mk φ) (t, x))).ker.comap
        (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)).toLinearMap :=
    Submodule.mem_comap.2 hv
  have hsw : mfderiv (𝓘(ℝ).prod I) I Prod.snd (t, x)
      ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, w)) = w := by
    rw [mfderiv_snd_apply, Manifold.tangentSpaceProdEquiv_symm_apply]
  have hw' : criticalHessian I g x w = 0 := by
    rw [← hker, Submodule.mem_comap, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hw
    -- `hw` is this statement at `(t, x).2 = x`, with `w` written as its image under `d Prod.snd`.
    rw [← hsw]
    exact hw
  obtain rfl : w = 0 := hx.isInvertible_criticalHessian.injective (hw'.trans (map_zero _).symm)
  refine Submodule.mem_span_singleton.2 ⟨b, ?_⟩
  have hb : (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := I) (t, x)).symm (b, 0) =
      b • (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := I) (t, x)).symm (1, 0) := by
    rw [← map_smul, Prod.smul_mk, smul_zero]
    congr 2
    exact (mul_one b).symm
  rw [timeVectorField_mk, hb]
  exact (map_smul _ b _).symm

/-! ### The circle through a fixed point -/

variable [FiniteDimensional ℝ E] [I.Boundaryless] {φ} {x : M} (hx : IsFixedPt φ x)

include hfg in
/-- **The circle through a fixed nondegenerate critical point is Morse–Bott.** Let `f` be a
function on the mapping torus with `f [t, x] = g x` for all `t` and `x`. If `x` is a fixed point
of `φ` and a nondegenerate critical point of `g`, the circle `[t] ↦ [t, x]` is a nondegenerate
critical submanifold of `f`: the kernel of the Hessian of `f` along it is the time direction,
which is its tangent line. -/
theorem isNondegenerateCriticalSubmanifold_fixedPtCircle
    (hgx : IsManifoldNondegenerateCriticalPoint I g x) :
    (fixedPtCircle φ hx).IsNondegenerateCriticalSubmanifold f where
  contMDiffAt θ := by
    induction θ using QuotientAddGroup.induction_on with | H t => ?_
    rw [fixedPtCircle_coe]
    exact (contMDiffAt_mk_iff_of_forall_mk_eq φ hfg (by simp)).2 hgx.contMDiffAt
  mem_criticalPoints θ := by
    induction θ using QuotientAddGroup.induction_on with | H t => ?_
    rw [fixedPtCircle_coe]
    exact (mk_mem_criticalPoints_iff_of_forall_mk_eq φ hfg).2 hgx.mem_criticalPoints
  ker_criticalHessian_le θ := by
    induction θ using QuotientAddGroup.induction_on with | H t => ?_
    rw [(hasMFDerivAt_fixedPtCircle hx _).mfderiv, fixedPtCircle_coe]
    intro v hv
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1
      (ker_criticalHessian_mk_le_of_forall_mk_eq φ hfg hgx hv)
    -- `smulRight 1 T` sends `b` to `1 b • T = b • T`.
    exact ⟨b, (ContinuousLinearMap.smulRight_apply (c := (1 : ℝ →L[ℝ] ℝ)) (x := b)).trans
      (by rw [one_apply_eq_self])⟩

include hfg in
/-- **A Morse function of the fibre coordinate is Morse–Bott on the mapping torus.** Let `g` be a
Morse function on `M` whose critical points are all fixed by `φ`, and let `f` be the function on
the mapping torus with `f [t, x] = g x`. Then the circles `[t] ↦ [t, x]` through the critical
points `x` of `g` exhibit `f` as a Morse–Bott function. Along the circle through `x` the Morse
index is that of `g` at `x` (`TauCeti.SmoothMappingTorus.manifoldMorseIndex_mk_of_forall_mk_eq`).
-/
theorem _root_.TauCeti.IsMorse.isMorseBottFamily_fixedPtCircle (hg : IsMorse I g)
    (hfix : ∀ x ∈ criticalPoints I g, IsFixedPt φ x) :
    IsMorseBottFamily (fun x : criticalPoints I g ↦ fixedPtCircle φ (hfix x x.property)) f := by
  refine .of_pairwise_disjoint (by simp)
    ((contMDiff_iff_of_forall_mk_eq φ hfg le_rfl).2 hg.contMDiff)
    (fun x ↦ isNondegenerateCriticalSubmanifold_fixedPtCircle hfg (hfix x x.property)
      (hg.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints x.property)) ?_ ?_
  · -- Circles through distinct fixed points are disjoint.
    intro x y hxy
    refine disjoint_left.2 ?_
    rintro _ ⟨θ, rfl⟩ hθ
    induction θ using QuotientAddGroup.induction_on with | H t => ?_
    rw [fixedPtCircle_coe, mk_mem_range_fixedPtCircle_iff] at hθ
    exact hxy (Subtype.ext hθ)
  · -- A critical point `[t, x]` of `f` lies on the circle through the critical point `x`.
    intro z hz
    obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
    exact mem_iUnion.2 ⟨⟨x, (mk_mem_criticalPoints_iff_of_forall_mk_eq φ hfg).1 hz⟩, t,
      fixedPtCircle_coe _ t⟩

end Critical

end SmoothMappingTorus

end TauCeti
