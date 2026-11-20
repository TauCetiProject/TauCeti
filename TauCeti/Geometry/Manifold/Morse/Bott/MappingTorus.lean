/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus.ClosedOrbit
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.Lift
public import TauCeti.Geometry.Manifold.Morse.Bott.Family
public import TauCeti.Geometry.Manifold.VectorField.MappingTorus
import TauCeti.Geometry.Manifold.Morse.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Morse.Prod

/-!
# Morse–Bott functions on mapping tori

Let `φ` be a diffeomorphism of a boundaryless finite-dimensional manifold `M`, with smooth mapping
torus `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))`, and let `g : M → ℝ` be invariant under `φ`. Then
`g` descends to the function `G [t, x] = g x` on `Y_φ` (`TauCeti.SmoothMappingTorus.lift`). This
file computes the critical points, the critical Hessian and the Morse indices of `G`, and shows
that when `g` is Morse, `G` is Morse–Bott, its critical submanifolds being the closed orbits of the
suspension flow through the critical points of `g`.

Pulled back along the quotient map `π (t, x) = [t, x]`, a local diffeomorphism, `G` is
`g ∘ Prod.snd`. Hence:

* `[t, x]` is a critical point of `G` exactly when `x` is a critical point of `g`
  (`TauCeti.SmoothMappingTorus.mem_criticalPoints_lift_mk_iff`);
* at a critical point, `Hess G (dπ (b, v), dπ (b', v')) = Hess g (v, v')`
  (`TauCeti.SmoothMappingTorus.criticalHessian_lift_mk_apply`): the circle direction is null, and
  the Morse index of `G` at `[t, x]` is that of `g` at `x`
  (`TauCeti.SmoothMappingTorus.manifoldMorseIndex_lift_mk`);
* at a nondegenerate critical point `x` of `g`, the kernel of the Hessian of `G` at `[t, x]` is the
  line spanned by the suspension vector field `T = dπ (1, 0)`
  (`TauCeti.SmoothMappingTorus.ker_criticalHessian_lift_mk`).

A critical point `x` of `g` of least period `d > 0` under `φ` gives the closed orbit
`γ [t] = [t, x]` of the suspension flow (`TauCeti.SmoothMappingTorus.closedOrbit`), a smooth
embedding of the circle `ℝ / dℤ` whose velocity is `T`. Its image consists of critical points of
`G`, and its tangent line is the kernel of the Hessian, so it is a Morse–Bott critical
submanifold (`TauCeti.SmoothMappingTorus.isNondegenerateCriticalSubmanifold_lift_closedOrbit`),
of index the Morse index of `g` at `x`. When `g` is a smooth Morse function whose critical points
are periodic under `φ`, choosing one critical point on each `φ`-orbit of critical points, these
closed orbits exhibit `G` as a Morse–Bott function
(`TauCeti.SmoothMappingTorus.isMorseBottFamily_lift`).

This is a source of Morse–Bott functions whose critical circles may have nonorientable negative
normal bundles: at a fixed critical point `x`, going once around the circle `t ↦ [t, x]` returns
the normal space `T_x M` to itself by `dφ_x`, which may reverse the orientation of the negative
eigenspace of the Hessian of `g` at `x`. The normal bundles themselves are not constructed in this
file.

## Main results

In the namespace `TauCeti.SmoothMappingTorus`:

* `mem_criticalPoints_lift_mk_iff`: the critical points of `G`.
* `criticalHessian_lift_mk_apply`: the critical Hessian of `G`.
* `manifoldMorseIndex_lift_mk`: the Morse index of `G`.
* `ker_criticalHessian_lift_mk`: the kernel of the Hessian of `G` at a nondegenerate critical point
  of `g` is spanned by the suspension vector field.
* `isNondegenerateCriticalSubmanifold_lift_closedOrbit`: the closed orbit through a nondegenerate
  periodic critical point of `g` is a Morse–Bott critical submanifold of `G`.
* `isMorseBottFamily_lift`: for a smooth `g`, the closed orbits through periodic nondegenerate
  representatives of the `φ`-orbits of critical points exhibit `G` as a Morse–Bott function.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 6.2 (Morse–Bott trajectory spaces and the orientation
  local systems of their negative bundles).
-/

public section

open Set Function
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [LocallyCompactSpace M]

section Finite

variable {n : ℕ∞ω} [IsManifold I n M] (φ : M ≃ₘ^n⟮I, I⟯ M) {g : M → ℝ}
  (hg : ∀ x, g (φ x) = g x)

/-- **The critical points of an invariant function on the mapping torus.** For `n ≥ 1`, the point
`[t, x]` is a critical point of `G` exactly when `x` is a critical point of `g`. -/
theorem mem_criticalPoints_lift_mk_iff (hn : 1 ≤ n) (t : ℝ) (x : M) :
    mk φ t x ∈ criticalPoints (𝓘(ℝ).prod I) (lift φ g hg) ↔ x ∈ criticalPoints I g := by
  have h := (isLocalDiffeomorph_uncurry_mk φ (t, x)).mem_criticalPoints_comp_iff hn
    (f := lift φ g hg)
  rw [lift_comp_uncurry_mk, criticalPoints_comp_snd] at h
  simpa using h.symm

variable [I.Boundaryless]

/-- **The critical Hessian of an invariant function on the mapping torus.** At a critical point
`x` of `g` where `g` is `C²`, and for `n ≥ 2`, the critical Hessian of `G` at `[t, x]` evaluated
on the images under `dπ` of `(b, v)` and `(b', v')` is the critical Hessian of `g` at `x`
evaluated on `v` and `v'`. In particular the direction of the circle is null. -/
theorem criticalHessian_lift_mk_apply (hn : 2 ≤ n) {t : ℝ} {x : M}
    (hgx : ContMDiffAt I 𝓘(ℝ) 2 g x) (hx : x ∈ criticalPoints I g) (b b' : ℝ)
    (v v' : TangentSpace I x) :
    criticalHessian (𝓘(ℝ).prod I) (lift φ g hg) (mk φ t x)
        (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v)))
        (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b', v'))) =
      criticalHessian I g x v v' := by
  have : IsManifold I 2 M := IsManifold.of_le hn
  have hπ := isLocalDiffeomorph_uncurry_mk φ (t, x)
  have hcomp := criticalHessian_comp_apply (φ := uncurry (mk φ)) (y := (t, x)) rfl
    ((contMDiffAt_lift_mk_iff φ hg hn t x).2 hgx) (hπ.contMDiffAt.of_le hn)
    ((mem_criticalPoints_lift_mk_iff φ hg (one_le_two.trans hn) t x).2 hx)
    ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v))
    ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b', v'))
  -- `g ∘ Prod.snd` is the separated sum of the zero function on `ℝ` and of `g`.
  have key : criticalHessian (𝓘(ℝ).prod I) (lift φ g hg ∘ uncurry (mk φ)) (t, x) =
      criticalHessian (𝓘(ℝ).prod I) ((fun _ : ℝ ↦ (0 : ℝ)) ∘ Prod.fst + g ∘ Prod.snd) (t, x) := by
    rw [lift_comp_uncurry_mk]
    congr 1
    ext
    simp
  have hsum := criticalHessian_comp_fst_add_comp_snd_apply (I := 𝓘(ℝ)) (x := t) (y := x)
    (f := fun _ : ℝ ↦ (0 : ℝ)) (g := g) contDiffAt_const hgx.contDiffAt_comp_extChartAt_symm
    ((Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := I) (t, x)).symm (b, v))
    ((Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := I) (t, x)).symm (b', v'))
  have h₁ := congrArg Prod.snd
    (Manifold.tangentSpaceProdEquiv_symm_apply (I := 𝓘(ℝ)) (J := I) (t, x) (b, v))
  have h₂ := congrArg Prod.snd
    (Manifold.tangentSpaceProdEquiv_symm_apply (I := 𝓘(ℝ)) (J := I) (t, x) (b', v'))
  refine hcomp.symm.trans ((DFunLike.congr_fun (DFunLike.congr_fun key _) _).trans
    (hsum.trans ?_))
  rw [h₁, h₂]
  simp only [criticalHessian_modelSpace, fderiv_fun_const, fderiv_zero, Pi.zero_apply,
    add_eq_right]
  -- The zero bilinear map applied to vectors of `TangentSpace 𝓘(ℝ) t`, which is `ℝ` by
  -- definition; `ContinuousLinearMap.zero_apply` does not match these types syntactically.
  exact rfl

/-- **The Morse index of an invariant function on the mapping torus.** At a critical point `x` of
`g` where `g` is `C²`, and for `n ≥ 2`, the Morse index of `G` at `[t, x]` is the Morse index of
`g` at `x`. -/
theorem manifoldMorseIndex_lift_mk [FiniteDimensional ℝ E] (hn : 2 ≤ n) {t : ℝ} {x : M}
    (hgx : ContMDiffAt I 𝓘(ℝ) 2 g x) (hx : x ∈ criticalPoints I g) :
    manifoldMorseIndex (𝓘(ℝ).prod I) (lift φ g hg) (mk φ t x) = manifoldMorseIndex I g x := by
  have hπ := isLocalDiffeomorph_uncurry_mk φ (t, x)
  -- Read `[t, x]` as the quotient map `(t, x) ↦ [t, x]` evaluated at `(t, x)`.
  rw [show mk φ t x = uncurry (mk φ) (t, x) from rfl,
    ← hπ.manifoldMorseIndex_comp hn ((contMDiffAt_lift_mk_iff φ hg hn t x).2 hgx)
      ((mem_criticalPoints_lift_mk_iff φ hg (one_le_two.trans hn) t x).2 hx),
    lift_comp_uncurry_mk]
  exact manifoldMorseIndex_comp_snd hgx.contDiffAt_comp_extChartAt_symm

end Finite

variable [IsManifold I ∞ M] [I.Boundaryless] (φ : M ≃ₘ⟮I, I⟯ M) {g : M → ℝ}
  (hg : ∀ x, g (φ x) = g x)

/-- **The kernel of the Hessian on the mapping torus.** At a nondegenerate critical point `x` of
`g`, the kernel of the critical Hessian of `G` at `[t, x]` is the line spanned by the suspension
vector field `T = ∂_t`. -/
theorem ker_criticalHessian_lift_mk {x : M} (hx : IsManifoldNondegenerateCriticalPoint I g x)
    (t : ℝ) :
    (criticalHessian (𝓘(ℝ).prod I) (lift φ g hg) (mk φ t x)).ker =
      Submodule.span ℝ {timeVectorField φ (mk φ t x)} := by
  obtain ⟨hgx, hcrit, hinv⟩ := isManifoldNondegenerateCriticalPoint_iff_criticalHessian.1 hx
  have hx' : x ∈ criticalPoints I g := mem_criticalPoints.2 hcrit
  have hH := criticalHessian_lift_mk_apply φ hg (by simp) (t := t) hgx hx'
  -- The image of `(c, 0)` under the differential of the quotient map is `c • T`.
  have hsmul (c : ℝ) : mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
      ((Manifold.tangentSpaceProdEquiv (t, x)).symm (c, 0)) =
        c • timeVectorField φ (mk φ t x) := by
    -- Scalar multiplication on `TangentSpace 𝓘(ℝ) t`, which is `ℝ` by definition, is the
    -- product of reals.
    have hc : ((c, 0) : TangentSpace 𝓘(ℝ) t × TangentSpace I x) =
        c • ((1 : ℝ), (0 : TangentSpace I x)) :=
      Prod.ext (mul_one c).symm (smul_zero c).symm
    exact (congrArg (fun u ↦ mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
      ((Manifold.tangentSpaceProdEquiv (t, x)).symm u)) hc).trans
        ((congrArg _ (map_smul _ c _)).trans
          ((map_smul _ c _).trans (congrArg (c • ·) (timeVectorField_mk φ t x).symm)))
  ext w
  obtain ⟨b, v, rfl⟩ := exists_mfderiv_uncurry_mk_eq φ t x w
  constructor
  · intro hw
    -- Pairing with `(0, v')` shows that `v` lies in the kernel of the Hessian of `g`, so `v = 0`.
    have hv : criticalHessian I g x v = 0 := ContinuousLinearMap.ext fun v' ↦ by
      have h0 := DFunLike.congr_fun (LinearMap.mem_ker.1 hw)
        (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm (0, v')))
      exact (hH b 0 v v').symm.trans h0
    obtain rfl : v = 0 := hinv.injective (hv.trans (map_zero _).symm)
    exact Submodule.mem_span_singleton.2 ⟨b, (hsmul b).symm⟩
  · intro hw
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hw
    refine LinearMap.mem_ker.2 (ContinuousLinearMap.ext fun w' ↦ ?_)
    obtain ⟨b', v', rfl⟩ := exists_mfderiv_uncurry_mk_eq φ t x w'
    have h0 := hH c b' 0 v'
    rw [hsmul, hc, map_zero] at h0
    exact h0

variable {d : ℕ} [Fact (0 < (d : ℝ))] {x : M} (h : IsPeriodicPt φ d x)

/-- **Closed orbits through nondegenerate critical points are Morse–Bott.** If `x` is a periodic
point of `φ` with period `d > 0` and a nondegenerate critical point of `g`, and the closed orbit
`γ [t] = [t, x]` is a smooth embedding of the circle `ℝ / dℤ` (that is, `d` is the least period of
`x`, by `TauCeti.SmoothMappingTorus.isSmoothEmbedding_closedOrbit_iff`), then `γ` is a
nondegenerate critical submanifold of `G`. -/
theorem isNondegenerateCriticalSubmanifold_lift_closedOrbit
    (he : Manifold.IsSmoothEmbedding 𝓘(ℝ) (𝓘(ℝ).prod I) ∞ (closedOrbit φ h))
    (hx : IsManifoldNondegenerateCriticalPoint I g x) :
    (SmoothEmbedding.ofIsSmoothEmbedding _ he).IsNondegenerateCriticalSubmanifold
      (lift φ g hg) := by
  obtain ⟨hgx, hcrit, -⟩ := isManifoldNondegenerateCriticalPoint_iff_criticalHessian.1 hx
  have hcoe : ⇑(SmoothEmbedding.ofIsSmoothEmbedding (closedOrbit φ h) he) = closedOrbit φ h :=
    SmoothEmbedding.coe_ofIsSmoothEmbedding _ _
  refine ⟨⟨fun θ ↦ ?_, fun θ ↦ ?_⟩, fun θ ↦ ?_⟩ <;> rw [hcoe] <;>
    induction θ using QuotientAddGroup.induction_on with | H t => ?_
  · rw [closedOrbit_coe]
    exact (contMDiffAt_lift_mk_iff φ hg (by simp) t x).2 hgx
  · rw [closedOrbit_coe]
    exact (mem_criticalPoints_lift_mk_iff φ hg (by simp) t x).2 (mem_criticalPoints.2 hcrit)
  · -- The kernel is spanned by `T`, which is the velocity of the closed orbit.
    rw [mfderiv_closedOrbit h, closedOrbit_coe h t, ker_criticalHessian_lift_mk φ hg hx t]
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨c, ContinuousLinearMap.smulRight_apply⟩

omit [Fact (0 < (d : ℝ))] in
/-- **Invariant Morse functions descend to Morse–Bott functions.** Let `g` be a smooth function on
`M`, invariant under `φ`. Choose points `c a`, each periodic under `φ` with least period `d a > 0`
and a nondegenerate critical point of `g`, one on each `φ`-orbit of critical points of `g`. Then
the closed orbits `[t] ↦ [t, c a]` of the suspension flow exhibit `G` as a Morse–Bott function on
the mapping torus. Since `g` is invariant, every critical point is then nondegenerate, so `g` is
a Morse function. -/
theorem isMorseBottFamily_lift [FiniteDimensional ℝ E] (hgs : ContMDiff I 𝓘(ℝ) ∞ g)
    {ι : Type*} {c : ι → M} {d : ι → ℕ} [∀ a, Fact (0 < (d a : ℝ))]
    (hmin : ∀ a, minimalPeriod φ (c a) = d a)
    (hnd : ∀ a, IsManifoldNondegenerateCriticalPoint I g (c a))
    (hdisj : Pairwise fun a b ↦ ¬∃ j : ℕ, (⇑φ)^[j] (c a) = c b)
    (hcover : ∀ y ∈ criticalPoints I g, ∃ a, ∃ j : ℕ, (⇑φ)^[j] (c a) = y) :
    IsMorseBottFamily (fun a ↦ SmoothEmbedding.ofIsSmoothEmbedding _
      ((isSmoothEmbedding_closedOrbit_iff (d := d a)
        (hmin a ▸ isPeriodicPt_minimalPeriod φ (c a)) (by simp)).2 (hmin a))) (lift φ g hg) := by
  have hc (a : ι) : IsPeriodicPt φ (d a) (c a) := hmin a ▸ isPeriodicPt_minimalPeriod φ (c a)
  have hrange (a : ι) : range (SmoothEmbedding.ofIsSmoothEmbedding _
      ((isSmoothEmbedding_closedOrbit_iff (hc a) (by simp)).2 (hmin a))) =
        range (closedOrbit φ (hc a)) := by
    rw [SmoothEmbedding.coe_ofIsSmoothEmbedding]
  refine .of_pairwise_disjoint (by simp) ((contMDiff_lift_iff φ hg le_rfl).2 hgs)
    (fun a ↦ isNondegenerateCriticalSubmanifold_lift_closedOrbit φ hg (hc a) _ (hnd a))
    (fun a b hab ↦ ?_) ?_
  · rw [onFun, hrange, hrange]
    exact (disjoint_range_closedOrbit_iff (hc a) (hc b)).2 (hdisj hab)
  · intro z hz
    obtain ⟨⟨t, y⟩, rfl⟩ := uncurry_mk_surjective φ z
    obtain ⟨a, j, rfl⟩ := hcover y ((mem_criticalPoints_lift_mk_iff φ hg (by simp) t y).1 hz)
    exact mem_iUnion.2 ⟨a, (hrange a).symm ▸ (mk_mem_range_closedOrbit_iff (hc a)).2 ⟨j, rfl⟩⟩

end SmoothMappingTorus

end TauCeti
