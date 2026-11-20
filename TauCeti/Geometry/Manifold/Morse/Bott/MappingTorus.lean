/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus.ClosedOrbit
public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Manifold.Morse.Prod
public import TauCeti.Geometry.Manifold.Morse.Submersion
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph

/-!
# Morse functions of the fibre coordinate on mapping tori

Let `φ : M ≃ₘ⟮I, I⟯ M` be a diffeomorphism and `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` its
smooth mapping torus (`TauCeti.SmoothMappingTorus φ`). This file studies a function `f` on `Y_φ`
which depends only on the fibre coordinate: `f [t, x] = g x` for a function `g` on `M`, which is
then invariant under `φ`. In the coordinates `(t, x)` such an `f` is the function `g ∘ Prod.snd`
of the second factor of `ℝ × M`, and the quotient map `ℝ × M → Y_φ` is a local diffeomorphism.
So `f` is `C^m` exactly when `g` is, its critical points are the points `[t, x]` over critical
points `x` of `g`, and at such a point its Morse index is the Morse index of `g` at `x`; at a
nondegenerate critical point of `g`, the kernel of the Hessian of `f` is spanned by the time
direction `∂_t`.

If `x` is a fixed point of `φ`, the curve `[t] ↦ [t, x]` is an embedded circle in `Y_φ`, the closed
orbit of the suspension flow through `[0, x]` (`TauCeti.SmoothMappingTorus.fixedPtCircle`). When
`x` is a nondegenerate critical point of `g`, the time direction is the whole kernel of the Hessian
of `f` along this circle, which is therefore a Morse–Bott critical submanifold of `f`, of the
Morse index of `g` at `x`. Hence, if `g` is a Morse function whose critical points are all fixed by
`φ`, the circles through them exhibit `f` as a Morse–Bott function
(`TauCeti.IsMorse.isMorseBottFamily_fixedPtCircle`).

This is how Morse–Bott functions with critical circles are built on mapping tori. The example
in `TauCeti.Geometry.Manifold.Morse.Bott.Examples.SphereCircleMappingTorus` is the mapping torus of
`(p, w) ↦ (ρ p, conj w)` on `S² × S¹`, with `ρ` a reflection of the sphere, and the function
`[t, p, w] ↦ z(p) + ε Re w`, which has four critical circles.

## Main definitions

* `TauCeti.SmoothMappingTorus.fixedPtCircle φ hx`: the circle `[t] ↦ [t, x]` through a fixed point
  `x` of `φ`, as a smooth embedding of `ℝ / ℤ`.

## Main results

In the namespace `TauCeti.SmoothMappingTorus`, for `f` with `f [t, x] = g x`:

* `contMDiff_iff_of_forall_mk_eq`: `f` is `C^m` exactly when `g` is.
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
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-! ### Functions of the fibre coordinate -/

section Smooth

variable [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] (φ : M ≃ₘ^n⟮I, I⟯ M)
  {F G β : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace β] [ChartedSpace G β] {m : ℕ∞ω}
  {f : SmoothMappingTorus φ → β} {g : M → β}

omit [T2Space M] [LocallyCompactSpace M] [IsManifold I n M] [TopologicalSpace β] in
/-- A function `f` with `f [t, x] = g x` reads, in the coordinates `(t, x)`, as the function
`g ∘ Prod.snd` of the second factor. -/
private theorem comp_uncurry_mk_eq (hfg : ∀ t x, f (mk φ t x) = g x) :
    f ∘ uncurry (mk φ) = g ∘ Prod.snd :=
  funext fun p ↦ hfg p.1 p.2

/-- **A function of the fibre coordinate is `C^m` at `[t, x]` exactly when it is so on `M`**: if
`f [t, x] = g x` for all `t` and `x`, then `f` is `C^m` at `[t, x]` exactly when `g` is `C^m` at
`x`, for `m` at most the smoothness of `φ`. The quotient map `(t, x) ↦ [t, x]` is a local
diffeomorphism, along which `f` reads as `g ∘ Prod.snd`. -/
theorem contMDiffAt_mk_iff_of_forall_mk_eq (hfg : ∀ t x, f (mk φ t x) = g x) (hm : m ≤ n)
    {t : ℝ} {x : M} :
    ContMDiffAt (𝓘(ℝ).prod I) J m f (mk φ t x) ↔ ContMDiffAt I J m g x := by
  have h := (isLocalDiffeomorph_uncurry_mk φ (t, x)).contMDiffAt_comp_iff (g := f) (I' := J) hm
  rw [comp_uncurry_mk_eq φ hfg] at h
  refine h.symm.trans ⟨fun h ↦ ?_, fun h ↦ h.comp (t, x) contMDiffAt_snd⟩
  -- `g` is `g ∘ Prod.snd` on the slice `x ↦ (t, x)`.
  exact h.comp x (contMDiffAt_const.prodMk contMDiffAt_id)

/-- **A function of the fibre coordinate is `C^m` exactly when it is so on `M`**: if
`f [t, x] = g x` for all `t` and `x`, then `f` is `C^m` exactly when `g` is, for `m` at most the
smoothness of `φ`. -/
theorem contMDiff_iff_of_forall_mk_eq (hfg : ∀ t x, f (mk φ t x) = g x) (hm : m ≤ n) :
    ContMDiff (𝓘(ℝ).prod I) J m f ↔ ContMDiff I J m g := by
  refine ⟨fun h x ↦ (contMDiffAt_mk_iff_of_forall_mk_eq φ hfg hm (t := 0)).1 (h _),
    fun h z ↦ ?_⟩
  obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
  exact (contMDiffAt_mk_iff_of_forall_mk_eq φ hfg hm).2 (h x)

end Smooth

/-! ### Critical points and Morse indices -/

section Critical

variable [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] (φ : M ≃ₘ⟮I, I⟯ M)
  {f : SmoothMappingTorus φ → ℝ} {g : M → ℝ} (hfg : ∀ t x, f (mk φ t x) = g x)

/-- The quotient map `(t, x) ↦ [t, x]` has onto derivative everywhere. -/
private theorem isRegularPoint_uncurry_mk (p : ℝ × M) :
    IsRegularPoint (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) p :=
  isRegularPoint_iff.2
    ((isLocalDiffeomorph_uncurry_mk φ).isInvertible_mfderiv (by simp) p).surjective

include hfg in
/-- **Critical points of a function of the fibre coordinate.** If `f [t, x] = g x` for all `t` and
`x`, then `[t, x]` is a critical point of `f` exactly when `x` is a critical point of `g`. -/
theorem mk_mem_criticalPoints_iff_of_forall_mk_eq {t : ℝ} {x : M} :
    mk φ t x ∈ criticalPoints (𝓘(ℝ).prod I) f ↔ x ∈ criticalPoints I g := by
  -- Along the local diffeomorphism `(t, x) ↦ [t, x]`, `f` reads as `g ∘ Prod.snd`.
  have h := (isLocalDiffeomorph_uncurry_mk φ (t, x)).mfderiv_comp (by simp) f (I' := 𝓘(ℝ))
  rw [comp_uncurry_mk_eq φ hfg] at h
  refine Iff.trans ?_ (mem_criticalPoints_comp_snd_iff (I := 𝓘(ℝ)) (I' := I) (p := (t, x)))
  rw [mem_criticalPoints_iff_mfderiv_eq_zero, mem_criticalPoints_iff_mfderiv_eq_zero, h]
  refine ⟨fun h0 ↦ ContinuousLinearMap.ext fun u ↦
    congr($h0 (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x) u)), fun h0 ↦ ?_⟩
  -- The differential of the quotient map is onto.
  refine ContinuousLinearMap.ext fun w ↦ ?_
  obtain ⟨u, rfl⟩ := isRegularPoint_iff.1 (isRegularPoint_uncurry_mk φ (t, x)) w
  exact congr($h0 u)

include hfg in
/-- **The Morse index of a function of the fibre coordinate.** If `f [t, x] = g x` for all `t` and
`x`, then at a critical point `x` of `g` at which `g` is `C²`, the Morse index of `f` at `[t, x]`
is the Morse index of `g` at `x`. -/
theorem manifoldMorseIndex_mk_of_forall_mk_eq [FiniteDimensional ℝ E] [I.Boundaryless] {t : ℝ}
    {x : M} (hgx : ContMDiffAt I 𝓘(ℝ) 2 g x) (hx : x ∈ criticalPoints I g) :
    manifoldMorseIndex (𝓘(ℝ).prod I) f (mk φ t x) = manifoldMorseIndex I g x := by
  have hf := (contMDiffAt_mk_iff_of_forall_mk_eq φ hfg (by simp : (2 : ℕ∞ω) ≤ ∞) (t := t)).2 hgx
  have h := (isRegularPoint_uncurry_mk φ (t, x)).manifoldMorseIndex_comp hf
    ((contMDiff_uncurry_mk φ (t, x)).of_le (by simp))
    ((mk_mem_criticalPoints_iff_of_forall_mk_eq φ hfg).2 hx)
  rw [comp_uncurry_mk_eq φ hfg, manifoldMorseIndex_comp_snd] at h
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
  have hker := (isRegularPoint_uncurry_mk φ (t, x)).ker_criticalHessian_comp hf
    ((contMDiff_uncurry_mk φ (t, x)).of_le (by simp)) hcrit
  have hsnd : IsRegularPoint (𝓘(ℝ).prod I) I (Prod.snd : ℝ × M → M) (t, x) := by
    rw [isRegularPoint_iff, mfderiv_snd]
    exact fun w ↦ ⟨(0, w), rfl⟩
  rw [comp_uncurry_mk_eq φ hfg, hsnd.ker_criticalHessian_comp hx.contMDiffAt contMDiffAt_snd
    hx.mem_criticalPoints] at hker
  have hw : (Manifold.tangentSpaceProdEquiv (t, x)).symm (b, w) ∈ (criticalHessian I g
      (t, x).2).ker.comap (mfderiv (𝓘(ℝ).prod I) I Prod.snd (t, x)).toLinearMap := by
    rw [hker]
    exact hv
  have hsw : mfderiv (𝓘(ℝ).prod I) I Prod.snd (t, x)
      ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, w)) = w := by
    rw [mfderiv_snd, Manifold.tangentSpaceProdEquiv_symm_apply]
    rfl
  have hw' : criticalHessian I g x w = 0 := by
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

variable [FiniteDimensional ℝ E] [I.Boundaryless]

/-- **The circle through a fixed point** `x` of `φ`: the closed orbit `[t] ↦ [t, x]` of the
suspension flow, as a smooth embedding of `ℝ / ℤ` into the mapping torus. It is the closed orbit
`TauCeti.SmoothMappingTorus.closedOrbit` of period one, read on `ℝ / ℤ`
(`TauCeti.SmoothMappingTorus.fixedPtCircle_coe`). -/
def fixedPtCircle {x : M} (hx : IsFixedPt φ x) :
    SmoothEmbedding 𝓘(ℝ) (𝓘(ℝ).prod I) ∞ UnitAddCircle (SmoothMappingTorus φ) :=
  haveI : Fact (0 < ((1 : ℕ) : ℝ)) := ⟨Nat.cast_pos.2 one_pos⟩
  .ofIsSmoothEmbedding
    (closedOrbit φ (hx.isPeriodicPt 1) ∘ AddCircle.diffeomorphAddCircle 1 ((1 : ℕ) : ℝ) ∞)
    (isSmoothEmbedding_comp_diffeomorph _
      ((isSmoothEmbedding_closedOrbit_iff _ (by simp)).2
        (minimalPeriod_eq_one_iff_isFixedPt.2 hx)))

variable {φ} {x : M} (hx : IsFixedPt φ x)

/-- The circle through a fixed point `x` sends the class of `t` to `[t, x]`. -/
@[simp]
theorem fixedPtCircle_coe (t : ℝ) : fixedPtCircle φ hx t = mk φ t x := by
  simp [fixedPtCircle]

/-- The point `[t, y]` lies on the circle through the fixed point `x` exactly when `y = x`. -/
theorem mk_mem_range_fixedPtCircle_iff {t : ℝ} {y : M} :
    mk φ t y ∈ range (fixedPtCircle φ hx) ↔ y = x := by
  have : Fact (0 < ((1 : ℕ) : ℝ)) := ⟨Nat.cast_pos.2 one_pos⟩
  -- The circle has the image of the closed orbit of period one through `x`.
  rw [fixedPtCircle, SmoothEmbedding.coe_ofIsSmoothEmbedding,
    EquivLike.range_comp,
    mk_mem_range_closedOrbit_iff]
  exact ⟨fun ⟨j, hj⟩ ↦ hj.symm.trans (hx.iterate j).eq, fun h ↦ ⟨0, h.symm⟩⟩

/-- **The circle through a fixed point is an orbit of the suspension flow**: its velocity at `θ`
is the time direction `T = ∂_t` at its point `θ`. -/
theorem hasMFDerivAt_fixedPtCircle (θ : UnitAddCircle) :
    HasMFDerivAt 𝓘(ℝ) (𝓘(ℝ).prod I) (fixedPtCircle φ hx) θ
      ((1 : ℝ →L[ℝ] ℝ).smulRight (timeVectorField φ (fixedPtCircle φ hx θ))) := by
  have : Fact (0 < ((1 : ℕ) : ℝ)) := ⟨Nat.cast_pos.2 one_pos⟩
  induction θ using QuotientAddGroup.induction_on with | H t => ?_
  -- The rescaling `ℝ / ℤ → ℝ / 1ℤ` is the identity on representatives, so it has derivative one.
  have hD : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) (AddCircle.diffeomorphAddCircle 1 ((1 : ℕ) : ℝ) ∞)
      (t : UnitAddCircle) (ContinuousLinearMap.id ℝ ℝ) :=
    AddCircle.hasMFDerivAt_of_comp_coe_eq (f := id) (funext fun s ↦ by simp) (hasFDerivAt_id t)
  have h := (hasMFDerivAt_closedOrbit (hx.isPeriodicPt 1) _).comp (t : UnitAddCircle) hD
  rw [fixedPtCircle, SmoothEmbedding.coe_ofIsSmoothEmbedding]
  exact h.congr_mfderiv (ContinuousLinearMap.ext fun _ ↦ rfl)

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
    exact ⟨b, rfl⟩

include hfg in
/-- **A Morse function of the fibre coordinate is Morse–Bott on the mapping torus.** Let `g` be a
Morse function on `M` whose critical points are all fixed by `φ`, and let `f` be the function on
the mapping torus with `f [t, x] = g x`. Then the circles `[t] ↦ [t, x]` through the critical
points `x` of `g` exhibit `f` as a Morse–Bott function. Along the circle through `x` the Morse
index is that of `g` at `x` (`TauCeti.SmoothMappingTorus.manifoldMorseIndex_mk_of_forall_mk_eq`).
-/
theorem _root_.TauCeti.IsMorse.isMorseBottFamily_fixedPtCircle (hg : IsMorse I g)
    (hfix : ∀ x ∈ criticalPoints I g, IsFixedPt φ x) :
    IsMorseBottFamily (fun x : criticalPoints I g ↦ fixedPtCircle φ (hfix x x.2)) f := by
  refine .of_pairwise_disjoint (by simp)
    ((contMDiff_iff_of_forall_mk_eq φ hfg le_rfl).2 hg.contMDiff)
    (fun x ↦ isNondegenerateCriticalSubmanifold_fixedPtCircle hfg (hfix x x.2)
      (hg.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints x.2)) ?_ ?_
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
