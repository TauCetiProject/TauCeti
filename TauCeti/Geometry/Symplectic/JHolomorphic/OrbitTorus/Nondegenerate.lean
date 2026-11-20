/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.Geometry.Manifold.TwoForm.Basic
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.Trivialization

/-!
# Nondegeneracy of the orbit tori of a surface map up to a period cutoff

Let `φ : M ≃ₘ⟮I, I⟯ M` be a diffeomorphism of a surface preserving a two-form `σ`, and let
`K_((s, t), y)` be a *vertical family* of almost complex structures on the tangent spaces of `M`
satisfying the seam identity

`dφ⁻¹ ∘ K_((s, t), y) = K_((s, t + 1), φ⁻¹ y) ∘ dφ⁻¹`,

the data from which a block almost complex structure on the symplectic suspension
`(ℝ / ℤ)_s × Y_φ` descends (`TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure`).
A periodic point `x` of period `d` gives the orbit torus `S¹ × γ_x`. Along it, for a family not
depending on `s` (such as `TauCeti.SmoothMappingTorus.seamFamily`), the normal operator in vertical
directions is `D v = ∂s v + K(t) ∂t v` with `K(t) = K_((s₀, t), x)`
(`TauCeti.orbitTorusVerticalOperator`, `TauCeti.hasDerivAt_cauchyRiemannOperator_vertical`), and
the normal sections twisted by a real sign character are the maps `v : ℝ × ℝ → T_x M` with
`v (s + k, t) = ε₁ v (s, t)` and `P ^ n v (s + a, t + n d) = ε₂ v (s, t)`, on the finite cover with
deck group spanned by `(k, 0)` and `(a, n d)`. Here `P = dφ^d_x` is the linearized return map.

This file supplies the hypotheses of the kernel criteria of
`TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.Trivialization` from these geometric data:

* the seam identity iterates along orbits: `dφ⁻ʲ ∘ K_((s, t), y) = K_((s, t + j), φ⁻ʲ y) ∘ dφ⁻ʲ`
  (`TauCeti.mfderiv_iterate_symm_apply_eq_apply_mfderiv`);
* at a periodic point of period `d` it becomes the seam identity of the return map,
  `P ∘ K(t + d) = K(t) ∘ P` (`TauCeti.apply_apply_add_eq_apply_apply_of_hasMFDerivAt_iterate`);
* a smooth vertical family is smooth in `t` along each orbit
  (`TauCeti.contDiff_toContinuousLinearMap_of_contMDiff`);
* the return map preserves `σ`, because every iterate of `φ` does.

The main theorem combines these with the dynamics of the return map. If `φ` is nondegenerate up to
period `2 N` (no return map of a periodic orbit of period at most `2 N` has the eigenvalue `1`),
then `det (1 - P ^ (2 n)) ≠ 0` for every periodic point of period `d` and every `n` with
`d n ≤ N`, since the return map of the `2 n`-fold cover is `P ^ (2 n)`
(`TauCeti.IsNondegenerateUpToPeriod.det_smul_one_sub_pow_ne_zero`). Hence all four twisted
vertical operators on every cover of the orbit torus whose period along the orbit is at most `N`
have no nonzero `C²` kernel element
(`TauCeti.forall_eq_zero_of_orbitTorusVerticalOperator_eq_zero_of_isNondegenerateUpToPeriod`).
The eigenvalue `-1` of `P ^ n`, which governs the sign character twisted along the orbit, is
excluded by nondegeneracy of the `2 n`-fold cover; so nondegeneracy up to period `N` alone does not
control the twisted operators on the covers of period `N`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* E.-N. Ionel and T. H. Parker, *Gromov invariants and symplectic maps*, Math. Ann. 314 (1999),
  127--158.
* M. Hutchings and M. Sullivan, *The periodic Floer homology of a Dehn twist*,
  Algebraic & Geometric Topology 5 (2005), 301--354.
-/

public section

open Bundle Function
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {φ : M ≃ₘ⟮I, I⟯ M}
  {K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)}

/-- **The seam identity along an orbit.** If a vertical family `K` satisfies the seam identity
`dφ⁻¹ ∘ K_((s, t), y) = K_((s, t + 1), φ⁻¹ y) ∘ dφ⁻¹`, then for every `j : ℕ` the differential of
`φ⁻ʲ` intertwines `K_((s, t), y)` with `K_((s, t + j), φ⁻ʲ y)`. -/
theorem mfderiv_iterate_symm_apply_eq_apply_mfderiv
    (ht : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K p v) = K (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    (j : ℕ) (s t : ℝ) (y : M) (v : TangentSpace I y) :
    mfderiv I I (⇑φ.symm)^[j] y (K ((s, t), y) v) =
      K ((s, t + j), (⇑φ.symm)^[j] y) (mfderiv I I (⇑φ.symm)^[j] y v) := by
  induction j generalizing t y v with
  | zero =>
    rw [Nat.cast_zero, add_zero]
    simp only [iterate_zero, mfderiv_id]
    -- The two sides agree up to the eta-expansion of the point `((s, t), y)`.
    rfl
  | succ j ih =>
    have hg : MDifferentiableAt I I (⇑φ.symm)^[j] (φ.symm y) :=
      (φ.symm.contMDiff.iterate j).mdifferentiableAt (by simp)
    have hh : MDifferentiableAt I I φ.symm y := φ.symm.contMDiff.mdifferentiableAt (by simp)
    have h := ht ((s, t), y) v
    rw [show ((s, t) + (0, 1) : ℝ × ℝ) = (s, t + 1) by simp] at h
    rw [iterate_succ, mfderiv_comp y hg hh, ContinuousLinearMap.comp_apply, h, ih,
      ContinuousLinearMap.comp_apply, Nat.cast_succ, add_assoc, add_comm 1 (j : ℝ)]
    -- The two sides agree up to the eta-expansion of the point.
    rfl

/-- **The seam identity of the return map.** Let `K` be a vertical family satisfying the seam
identity, let `x` be a periodic point of `φ` of period `d`, and let `P` be the differential of
`φ^d` at `x`, the linearized return map of the orbit of `x`. Then
`P ∘ K_((s, t + d), x) = K_((s, t), x) ∘ P`. -/
theorem apply_apply_add_eq_apply_apply_of_hasMFDerivAt_iterate
    (ht : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K p v) = K (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    {d : ℕ} {x : M} (hx : IsPeriodicPt φ d x) {P : E →L[ℝ] E}
    (hP : HasMFDerivAt I I (⇑φ)^[d] x P) (s t : ℝ) (v : E) :
    P (K ((s, t + d), x) v) = K ((s, t), x) (P v) := by
  have hl : LeftInverse (⇑φ.symm)^[d] (⇑φ)^[d] := LeftInverse.iterate φ.symm_apply_apply d
  have hr : LeftInverse (⇑φ)^[d] (⇑φ.symm)^[d] := LeftInverse.iterate φ.apply_symm_apply d
  have hxs : (⇑φ.symm)^[d] x = x := by simpa [hx.eq] using hl x
  -- `P` and the differential of `φ⁻ᵈ` at `x` are mutually inverse, by the chain rule.
  have hQ : HasMFDerivAt I I (⇑φ.symm)^[d] x (mfderiv I I (⇑φ.symm)^[d] x) :=
    ((φ.symm.contMDiff.iterate d).mdifferentiableAt (by simp)).hasMFDerivAt
  have hPQ : ∀ w, P (mfderiv I I (⇑φ.symm)^[d] x w) = w := by
    have h := (hxs.symm ▸ hP : HasMFDerivAt I I (⇑φ)^[d] ((⇑φ.symm)^[d] x) P).comp x hQ
    rw [show (⇑φ)^[d] ∘ (⇑φ.symm)^[d] = id from funext hr] at h
    exact fun w ↦ congrArg (· w) (h.mfderiv.symm.trans (mfderiv_id (I := I)))
  have hQP : ∀ w, mfderiv I I (⇑φ.symm)^[d] x (P w) = w := by
    have h := (hx.eq.symm ▸ hQ : HasMFDerivAt I I (⇑φ.symm)^[d] ((⇑φ)^[d] x)
      (mfderiv I I (⇑φ.symm)^[d] x)).comp x hP
    rw [show (⇑φ.symm)^[d] ∘ (⇑φ)^[d] = id from funext hl] at h
    exact fun w ↦ congrArg (· w) (h.mfderiv.symm.trans (mfderiv_id (I := I)))
  have h := mfderiv_iterate_symm_apply_eq_apply_mfderiv ht d s t x (P v)
  rw [hQP, hxs] at h
  rw [← h]
  exact hPQ _

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

/-- **Smoothness of a vertical family along an orbit.** If the vertical family `K` is a smooth
section of the endomorphism bundle of `T M` along the projection `(ℝ × ℝ) × M → M`, then for fixed
`s` and `x` the map `t ↦ K_((s, t), x)` into the endomorphisms of `T_x M` is smooth. -/
theorem contDiff_toContinuousLinearMap_of_contMDiff
    (hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (K p).toLinearMap.toContinuousLinearMap))
    (s : ℝ) (x : M) :
    ContDiff ℝ ∞ fun t : ℝ ↦
      show E →L[ℝ] E from (K ((s, t), x)).toLinearMap.toContinuousLinearMap := by
  rw [← contMDiff_iff_contDiff]
  intro t₀
  have hc : ContMDiff 𝓘(ℝ) (𝓘(ℝ, ℝ × ℝ).prod I) ∞ (fun t : ℝ ↦ ((s, t), x)) :=
    (contDiff_const.prodMk contDiff_id).contMDiff.prodMk contMDiff_const
  -- Read in the chart at `x`, the section over the constant base point `x` is `K` itself: both
  -- coordinate changes are coordinate changes from the chart at `x` to itself.
  have h := (contMDiffAt_hom_bundle _).1 (hK.comp hc t₀)
  refine h.2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
  have := inTangentCoordinates_eq (I := I) (I' := I) (fun _ : ℝ ↦ x) (fun _ : ℝ ↦ x)
    (fun t : ℝ ↦ ((K ((s, t), x)).toLinearMap.toContinuousLinearMap :
      TangentSpace I x →L[ℝ] TangentSpace I x)) (x₀ := t₀) (x := t)
    (mem_chart_source H x) (mem_chart_source H x)
  refine Eq.trans ?_ this.symm
  ext v
  have hc := (tangentBundleCore I M).coordChange_self (achart H x) x (mem_achart_source H x)
  exact (congrArg _ (hc v)).symm.trans (hc _).symm

/-- **The orbit tori of a surface map are nondegenerate through half the period cutoff.** Let
`φ` be a diffeomorphism of a surface preserving a two-form `σ`, and let `K` be a vertical family
satisfying the seam identity. Let `x` be a periodic point of period `d > 0`, with return map
`P = dφ^d_x`, and suppose that along the orbit, at the circle coordinate `s₀`, the structures
`K(t) = K_((s₀, t), x)` depend `C²` on `t`, preserve `σ_x`, and that `σ_x` tames `K(0)`. If `φ`
is nondegenerate up to period `2 N`, then for `n > 0` with `d n ≤ N`, `k > 0` and `a ∈ ℤ`, the
vertical operator `∂s + K(t) ∂t`, twisted by any signs `ε₁` along `(k, 0)` and `ε₂` along
`(a, n d)` through `P`, has no nonzero `C²` kernel element. -/
theorem forall_eq_zero_of_orbitTorusVerticalOperator_eq_zero_of_isNondegenerateUpToPeriod
    (hE : Module.finrank ℝ E = 2) {σ : SmoothTwoForm I M}
    (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ)
    (ht : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K p v) = K (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))
    {x : M} (s₀ : ℝ)
    (hK2 : ContDiff ℝ 2 fun t : ℝ ↦
      show E →L[ℝ] E from (K ((s₀, t), x)).toLinearMap.toContinuousLinearMap)
    (hKσ : ∀ (t : ℝ) (v w : TangentSpace I x),
      σ.eval₂ x (K ((s₀, t), x) v) (K ((s₀, t), x) w) = σ.eval₂ x v w)
    (htame : ∀ v : TangentSpace I x, v ≠ 0 → 0 < σ.eval₂ x v (K ((s₀, 0), x) v))
    {N d n k : ℕ} (hφ : IsNondegenerateUpToPeriod I φ (2 * N)) (hx : IsPeriodicPt φ d x)
    (hd : 0 < d) (hn : 0 < n) (hdn : d * n ≤ N) (hk : 0 < k) {P : E →L[ℝ] E}
    (hP : HasMFDerivAt I I (⇑φ)^[d] x P) (a : ℤ) :
    ∀ ε₁ ε₂ : ℝ, ε₁ ^ 2 = 1 → ε₂ ^ 2 = 1 → ∀ v : ℝ × ℝ → E, ContDiff ℝ 2 v →
      (∀ s t, v (s + k, t) = ε₁ • v (s, t)) →
      (∀ s t, (P ^ n) (v (s + a, t + n * d)) = ε₂ • v (s, t)) →
      (∀ z, orbitTorusVerticalOperator (fun t : ℝ ↦
        show E →L[ℝ] E from (K ((s₀, t), x)).toLinearMap.toContinuousLinearMap) v z = 0) →
      v = 0 := by
  -- The form `σ` at `x`, as a continuous bilinear map.
  let σx : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
      (show LinearMap.BilinForm ℝ E from σ.bilinFormAt x))
  have hσx (v w : E) : σx v w = σ.eval₂ x v w := by
    simp only [σx, LinearMap.coe_toContinuousLinearMap']
    exact SmoothForm.bilinFormAt_apply σ x v w
  have hσanti (v w : E) : σx v w = -σx w v := by
    rw [hσx, hσx]
    exact SmoothBundleForm.eval₂_swap σ x v w
  have hσK (t : ℝ) (v w : E) : σx (K ((s₀, t), x) v) (K ((s₀, t), x) w) = σx v w :=
    (hσx _ _).trans ((hKσ t v w).trans (hσx v w).symm)
  have hσtame (v : E) (hv : v ≠ 0) : 0 < σx v (K ((s₀, 0), x) v) :=
    (htame v hv).trans_eq (hσx _ _).symm
  -- The return map preserves `σ` at `x`, since every iterate of `φ` preserves `σ`.
  have hPσ (v w : E) : σx (P v) (P w) = σx v w := by
    have h := SmoothForm.eval₂_mpullback _ (φ.contMDiff.iterate d) σ x v w
    rw [SmoothForm.mpullback_iterate_eq_self φ.contMDiff hσ d, hP.mfderiv, hx.eq] at h
    rw [hσx, hσx]
    exact h.symm
  have hPK (t : ℝ) : P ∘L (show E →L[ℝ] E from
      (K ((s₀, t + d), x)).toLinearMap.toContinuousLinearMap) =
      (show E →L[ℝ] E from (K ((s₀, t), x)).toLinearMap.toContinuousLinearMap) ∘L P := by
    ext v
    exact apply_apply_add_eq_apply_apply_of_hasMFDerivAt_iterate ht hx hP s₀ t v
  -- The return map `P ^ (2 n)` of the `2 n`-fold cover, of period `2 d n ≤ 2 N`, fixes no vector.
  have hdet := hφ.det_smul_one_sub_pow_ne_zero (m := 2 * n) (j := 1) hd (by omega) one_pos
    (by nlinarith) hx hP (one_pow 1)
  rw [one_smul] at hdet
  intro ε₁ ε₂ hε₁ hε₂ v hv hv₁ hv₂ hDv
  refine (forall_eq_zero_of_orbitTorusVerticalOperator_eq_zero_iff_of_finrank_eq_two hE hK2
    (fun t w ↦ (K ((s₀, t), x)).apply_apply w) hσanti hσK hσtame hPσ hPK one_pos
    (Nat.cast_pos.2 hd) hk hn a).2 hdet ε₁ ε₂ hε₁ hε₂ v hv (by simpa using hv₁)
    (by simpa using hv₂) hDv

end TauCeti
