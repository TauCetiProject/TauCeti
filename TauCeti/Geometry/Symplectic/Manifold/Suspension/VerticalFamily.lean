/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Suspension.BlockCurve
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic

/-!
# Block almost complex structures on a symplectic suspension come from vertical families

Let `φ` be a diffeomorphism of a finite-dimensional locally compact Hausdorff smooth manifold `M`,
let `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its smooth mapping torus, with vector field
`T = ∂_t`, and let `X_φ = (ℝ / ℤ)_s × Y_φ`, with covering map
`q : (ℝ × ℝ) × M → X_φ`, `((s, t), x) ↦ ([s], [t, x])`
(`TauCeti.SmoothMappingTorus.suspensionCover`) and vertical subbundle `V = pr_Y^* ker dp`
(`TauCeti.SmoothMappingTorus.suspensionVerticalSubspace`).

A smooth vertical family `K_((s,t),x)` of complex structures on `T_x M`, periodic in `s` and
satisfying the seam identity `dφ⁻¹ ∘ K_((s, t), x) = K_((s, t + 1), φ⁻¹ x) ∘ dφ⁻¹`, descends to
the block almost complex structure `TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure` on
`X_φ`, which sends `∂_s` to `T` and preserves `V`. This file proves the converse: every smooth
almost complex structure `J` on `X_φ` with

`J ∂_s = T` and `J V ⊆ V` at every point

is the descent of exactly such a family. The family is read off from the pullback `q^* J` of `J`
along the covering map (`TauCeti.SmoothAlmostComplexStructure.localPullback`): since `dq` sends the
vertical vectors `0 ∂_s + 0 ∂_t + v` of `(ℝ × ℝ) × M` onto `V`, the structure `q^* J` preserves
them, and its vertical block

`K_((s,t),x) v = (q^* J (0 ∂_s + 0 ∂_t + v))_M`

(`TauCeti.SmoothMappingTorus.verticalFamily`) is a complex structure on `T_x M`, so that
`J (0, [0, v]) = (0, [0, K v])` in the coordinates `(s, t, x)`
(`TauCeti.SmoothMappingTorus.apply_mk_eq_verticalFamily`). It is smooth because `q^* J` is. It is
periodic and satisfies the seam identity because the deck transformations
`((s, t), x) ↦ ((s + 1, t), x)` and `((s, t), x) ↦ ((s, t + 1), φ⁻¹ x)` of `q` are complex linear
for `q^* J`. Finally `J ∂_s = T` makes `q^* J` the standard structure `∂_s ↦ ∂_t ↦ -∂_s` on the
`(s, t)`-plane, so `q^* J` is the block structure of `K`, and its descent is `J`.

The structure `J` is compatible with `Ω = ds ∧ dt + σ_v` exactly when every member of its
vertical family is compatible with `σ`, and similarly for tameness. Hence the `Ω`-compatible block
structures on `X_φ`, which the classification of curves of zero vertical area takes as input, are
exactly the descents of the `σ`-compatible seam-compatible vertical families. In particular,
spatial data on `X_φ` given by a block structure pull back to deck-compatible tensors on
`(ℝ × ℝ) × M`.

## Main definitions

* `TauCeti.SmoothMappingTorus.verticalFamily J hJV`: the vertical family of an almost complex
  structure `J` on `X_φ` preserving `V`.

## Main results

* `TauCeti.SmoothMappingTorus.apply_mk_eq_verticalFamily`,
  `TauCeti.SmoothMappingTorus.verticalFamily_eq_iff`: `J` acts on `V` through its vertical family,
  which is determined by this action.
* `TauCeti.SmoothMappingTorus.verticalFamily_suspensionAlmostComplexStructure`: the vertical family
  of the descent of a vertical family `K` is `K`.
* `TauCeti.SmoothMappingTorus.contMDiff_verticalFamily`,
  `TauCeti.SmoothMappingTorus.verticalFamily_add_fst`,
  `TauCeti.SmoothMappingTorus.mfderiv_symm_verticalFamily`: the vertical family is smooth,
  periodic in `s` and satisfies the seam identity.
* `TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure_verticalFamily`: if also
  `J ∂_s = T`, then `J` is the descent of its vertical family.
* `TauCeti.SmoothMappingTorus.exists_suspensionAlmostComplexStructure_eq_iff`: the descended block
  structures are exactly the smooth almost complex structures with `J ∂_s = T` and `J V ⊆ V`.
* `TauCeti.SmoothMappingTorus.tames_suspensionForm_iff_verticalFamily`,
  `TauCeti.SmoothMappingTorus.compatible_suspensionForm_iff_verticalFamily`: `J` is tamed by, or
  compatible with, `Ω` exactly when every member of its vertical family is tamed by, or compatible
  with, `σ`.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (admissible almost complex structures on
  symplectic mapping tori).
-/

public noncomputable section

open Bundle Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] {φ : M ≃ₘ⟮I, I⟯ M}

/-! ### The pullback of a structure on `X_φ` -/

variable (J : SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
  (UnitAddCircle × SmoothMappingTorus φ))

/-- The pullback `q^* J` of `J` along the covering map `q : (ℝ × ℝ) × M → X_φ`. -/
private def coverStructure : SmoothAlmostComplexStructure (𝓘(ℝ, ℝ × ℝ).prod I) ((ℝ × ℝ) × M) :=
  SmoothAlmostComplexStructure.localPullback (isLocalDiffeomorph_suspensionCover φ) J

private theorem mfderiv_coverStructure_apply (p : (ℝ × ℝ) × M)
    (w : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) p) :
    mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionCover φ) p
        (coverStructure J p w) =
      J (suspensionCover φ p)
        (mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (suspensionCover φ) p w) :=
  SmoothAlmostComplexStructure.mfderiv_localPullback_apply _ J p w

/-- The vertical block `v ↦ (q^* J (0 ∂_s + 0 ∂_t + v))_M` of the pullback of `J`. -/
private def verticalEndomorphism (p : (ℝ × ℝ) × M) :
    TangentSpace I p.2 →L[ℝ] TangentSpace I p.2 :=
  ContinuousLinearMap.snd ℝ (TangentSpace 𝓘(ℝ, ℝ × ℝ) p.1) (TangentSpace I p.2) ∘L
    ((Manifold.tangentSpaceProdEquiv p).toContinuousLinearMap ∘L
      ((coverStructure J).toEndomorphism p ∘L
        ((Manifold.tangentSpaceProdEquiv p).symm.toContinuousLinearMap ∘L
          ContinuousLinearMap.inr ℝ (TangentSpace 𝓘(ℝ, ℝ × ℝ) p.1) (TangentSpace I p.2))))

private theorem verticalEndomorphism_apply (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2) :
    verticalEndomorphism J p v =
      (Manifold.tangentSpaceProdEquiv p
        (coverStructure J p ((Manifold.tangentSpaceProdEquiv p).symm (0, v)))).2 :=
  (rfl)

variable {J}
variable (hJV : ∀ (y : UnitAddCircle × SmoothMappingTorus φ)
  (ξ : TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) y),
    ξ ∈ suspensionVerticalSubspace φ y → J y ξ ∈ suspensionVerticalSubspace φ y)

include hJV in
/-- If `J` preserves `V`, then `q^* J` preserves the vertical vectors `0 ∂_s + 0 ∂_t + v`. -/
private theorem coverStructure_symm_zero (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2) :
    coverStructure J p ((Manifold.tangentSpaceProdEquiv p).symm (0, v)) =
      (Manifold.tangentSpaceProdEquiv p).symm (0, verticalEndomorphism J p v) := by
  obtain ⟨⟨s, t⟩, x⟩ := p
  -- `J` sends the vertical vector `dq (0, v)` to a vertical vector `dq (0, v')`.
  obtain ⟨v', hv'⟩ := mem_suspensionVerticalSubspace_mk_iff.1
    (hJV ((s : UnitAddCircle), mk φ t x) _
      ((mem_suspensionVerticalSubspace_mk_iff (φ := φ) (θ := (s : UnitAddCircle)) (t := t)
        (x := x)).2 ⟨v, rfl⟩))
  have hw : coverStructure J ((s, t), x) ((Manifold.tangentSpaceProdEquiv _).symm (0, v)) =
      (Manifold.tangentSpaceProdEquiv _).symm (0, v') := by
    apply ((isLocalDiffeomorph_suspensionCover φ).isInvertible_mfderiv (by simp) _).injective
    rw [mfderiv_coverStructure_apply, mfderiv_suspensionCover_mk_zero,
      mfderiv_suspensionCover_mk_zero, suspensionCover_apply]
    exact hv'
  rw [verticalEndomorphism_apply, hw, ContinuousLinearEquiv.apply_symm_apply]

include hJV in
private theorem verticalEndomorphism_comp_square (p : (ℝ × ℝ) × M) :
    (verticalEndomorphism J p).comp (verticalEndomorphism J p) = -ContinuousLinearMap.id ℝ _ := by
  ext v
  rw [ContinuousLinearMap.comp_apply, _root_.neg_apply,
    ContinuousLinearMap.id_apply]
  have h := (coverStructure J).apply_apply p ((Manifold.tangentSpaceProdEquiv p).symm (0, v))
  rw [coverStructure_symm_zero hJV, coverStructure_symm_zero hJV] at h
  simpa only [ContinuousLinearEquiv.apply_symm_apply, map_neg, Prod.snd_neg] using
    congrArg (fun w ↦ (Manifold.tangentSpaceProdEquiv p w).2) h

variable (J) in
/-- The vertical family of a smooth almost complex structure `J` on `X_φ` preserving the vertical
subbundle `V`: the complex structure `K_((s,t),x)` on `T_x M` through which `J` acts on the
vertical vectors at `([s], [t, x])`, `J (0, [0, v]) = (0, [0, K v])`
(`TauCeti.SmoothMappingTorus.apply_mk_eq_verticalFamily`). It is the vertical block of the pullback
of `J` along the covering map `(ℝ × ℝ) × M → X_φ`. -/
def verticalFamily (p : (ℝ × ℝ) × M) : AlmostComplexStructure (TangentSpace I p.2) where
  toLinearMap := (verticalEndomorphism J p).toLinearMap
  square_neg := by
    ext v
    exact congrArg (fun A : TangentSpace I p.2 →L[ℝ] TangentSpace I p.2 ↦ A v)
      (verticalEndomorphism_comp_square hJV p)

private theorem verticalFamily_apply (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2) :
    verticalFamily J hJV p v = verticalEndomorphism J p v :=
  (rfl)

/-- The vertical family read without the canonical identification of product tangent spaces. -/
private theorem verticalFamily_apply' (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2) :
    verticalFamily J hJV p v = (coverStructure J p (0, v)).2 := by
  rw [verticalFamily_apply, verticalEndomorphism_apply, Manifold.tangentSpaceProdEquiv_apply,
    Manifold.tangentSpaceProdEquiv_symm_apply]
  -- The zero of `T_c (ℝ × ℝ)` is the zero of `ℝ × ℝ`.
  rfl

/-- **`J` acts on the vertical subbundle through its vertical family.** In the coordinates
`(s, t, x)`, `J` sends the vertical vector `0 ∂_s + 0 T + v` at `([s], [t, x])` to
`0 ∂_s + 0 T + K_((s,t),x) v`. -/
theorem apply_mk_eq_verticalFamily (s t : ℝ) (x : M) (v : TangentSpace I x) :
    J ((s : UnitAddCircle), mk φ t x)
        ((Manifold.tangentSpaceProdEquiv _).symm
          ((0 : ℝ), mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
            ((Manifold.tangentSpaceProdEquiv (t, x)).symm ((0 : ℝ), v)))) =
      (Manifold.tangentSpaceProdEquiv _).symm
        ((0 : ℝ), mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm
            ((0 : ℝ), verticalFamily J hJV ((s, t), x) v))) := by
  rw [← mfderiv_suspensionCover_mk_zero, ← mfderiv_suspensionCover_mk_zero,
    verticalFamily_apply, ← coverStructure_symm_zero hJV, mfderiv_coverStructure_apply,
    suspensionCover_apply]

/-- The vertical family of `J` is uniquely determined by the action of `J` on the vertical
subbundle. -/
theorem verticalFamily_eq_iff (K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)) :
    verticalFamily J hJV = K ↔
      ∀ (s t : ℝ) (x : M) (v : TangentSpace I x),
        J ((s : UnitAddCircle), mk φ t x)
            ((Manifold.tangentSpaceProdEquiv _).symm
              ((0 : ℝ), mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
                ((Manifold.tangentSpaceProdEquiv (t, x)).symm ((0 : ℝ), v)))) =
          (Manifold.tangentSpaceProdEquiv _).symm
            ((0 : ℝ), mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
              ((Manifold.tangentSpaceProdEquiv (t, x)).symm ((0 : ℝ), K ((s, t), x) v))) := by
  refine ⟨fun h ↦ h ▸ apply_mk_eq_verticalFamily hJV, fun h ↦ ?_⟩
  funext ⟨⟨s, t⟩, x⟩
  ext v
  have h' := (apply_mk_eq_verticalFamily hJV s t x v).symm.trans (h s t x v)
  -- The vertical vectors `0 ∂_s + 0 T + u` are images of `0 ∂_s + 0 ∂_t + u` under the
  -- injective differential of the covering map, so they determine `u`.
  rw [← mfderiv_suspensionCover_mk_zero, ← mfderiv_suspensionCover_mk_zero] at h'
  have h'' := congrArg (fun w ↦ (Manifold.tangentSpaceProdEquiv ((s, t), x) w).2)
    (((isLocalDiffeomorph_suspensionCover φ).isInvertible_mfderiv (by simp) _).injective h')
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h''

omit hJV in
/-- The vertical family of the block structure descended from a vertical family `K` is `K`. -/
@[simp]
theorem verticalFamily_suspensionAlmostComplexStructure
    {K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)}
    (hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (K p).toLinearMap.toContinuousLinearMap))
    (hs : ∀ p : (ℝ × ℝ) × M, K (p.1 + (1, 0), p.2) = K p)
    (ht : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K p v) = K (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) :
    verticalFamily (suspensionAlmostComplexStructure φ hK hs ht)
        (fun y _ hξ ↦
          suspensionAlmostComplexStructure_apply_mem_suspensionVerticalSubspace hK hs ht y hξ) =
      K :=
  (verticalFamily_eq_iff _ K).2 fun s t x v ↦ by
    have h := suspensionAlmostComplexStructure_mk φ hK hs ht s t x 0 0 v
    rwa [neg_zero] at h

/-! ### Smoothness, periodicity and the seam identity -/

include hJV in
/-- The vertical family of `J` is smooth: it is a smooth section of the tangent endomorphism
bundle along the projection `(ℝ × ℝ) × M → M`. -/
theorem contMDiff_verticalFamily :
    ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (verticalFamily J hJV p).toLinearMap.toContinuousLinearMap) := by
  refine (TauCeti.contMDiff_hom_bundle_prod_iff _).2 ?_
  -- Read the vertical block through `(c, v) ↦ (0 ∂_s + 0 ∂_t + v) ↦ q^* J (…) ↦ its `M`-part.
  have hin : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I.tangent) (𝓘(ℝ, ℝ × ℝ).prod I).tangent ∞
      (fun r : (ℝ × ℝ) × TangentBundle I M ↦
        (equivTangentBundleProd 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) I M).symm
          (zeroSection (ℝ × ℝ) (TangentSpace 𝓘(ℝ, ℝ × ℝ)) r.1, r.2)) :=
    contMDiff_equivTangentBundleProd_symm.comp
      (((contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, ℝ × ℝ))).comp contMDiff_fst).prodMk
        contMDiff_snd)
  have hJ' : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I).tangent (𝓘(ℝ, ℝ × ℝ).prod I).tangent ∞
      (fun w : TangentBundle (𝓘(ℝ, ℝ × ℝ).prod I) ((ℝ × ℝ) × M) ↦
        TotalSpace.mk' ((ℝ × ℝ) × E) w.proj (coverStructure J w.proj w.snd)) :=
    ((coverStructure J).toEndomorphism.contMDiff.comp
      (Bundle.contMDiff_proj (TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I)))).clm_bundle_apply contMDiff_id
  refine ((contMDiff_snd.comp contMDiff_equivTangentBundleProd).comp (hJ'.comp hin)).congr ?_
  rintro ⟨c, x, v⟩
  simp only [Function.comp_apply, equivTangentBundleProd_apply,
    equivTangentBundleProd_symm_apply_snd, zeroSection_snd]
  exact congrArg (fun u ↦ (⟨x, u⟩ : TangentBundle I M)) (verticalFamily_apply' hJV (c, x) v)

include hJV in
/-- A deck transformation `((s, t), x) ↦ ((s, t) + c, g x)` of the covering map is complex linear
for the vertical family of `J`. -/
private theorem mfderiv_verticalFamily_of_deck (c : ℝ × ℝ) (g : M ≃ₘ⟮I, I⟯ M)
    (hg : suspensionCover φ ∘ Prod.map (fun r ↦ r + c) g = suspensionCover φ)
    (p : (ℝ × ℝ) × M) (w : TangentSpace I p.2) :
    mfderiv I I g p.2 (verticalFamily J hJV p w) =
      verticalFamily J hJV (p.1 + c, g p.2) (mfderiv I I g p.2 w) := by
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (fun r ↦ r + c) p.1 :=
    (differentiableAt_id.add_const c).mdifferentiableAt
  have hgd : MDifferentiableAt I I g p.2 := g.mdifferentiable (by simp) p.2
  have h : mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℝ × ℝ).prod I) (Prod.map (fun r ↦ r + c) g) p
        (coverStructure J p ((Manifold.tangentSpaceProdEquiv p).symm (0, w))) =
      coverStructure J (p.1 + c, g p.2)
        (mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℝ × ℝ).prod I) (Prod.map (fun r ↦ r + c) g) p
          ((Manifold.tangentSpaceProdEquiv p).symm (0, w))) :=
    SmoothAlmostComplexStructure.mfderiv_localPullback_apply_of_comp_eq _ J (hf.prodMap hgd) hg _
  have hd (u : TangentSpace I p.2) :
      mfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℝ × ℝ).prod I) (Prod.map (fun r ↦ r + c) g) p
          ((Manifold.tangentSpaceProdEquiv p).symm (0, u)) =
        (Manifold.tangentSpaceProdEquiv (p.1 + c, g p.2)).symm (0, mfderiv I I g p.2 u) := by
    rw [Manifold.mfderiv_prodMap_apply hf hgd, map_zero]
  rw [coverStructure_symm_zero hJV, hd, hd, coverStructure_symm_zero hJV] at h
  have h' := congrArg (fun u ↦ (Manifold.tangentSpaceProdEquiv (p.1 + c, g p.2) u).2) h
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h'
  exact h'

include hJV in
/-- The vertical family of `J` is periodic in `s`. -/
theorem verticalFamily_add_fst (p : (ℝ × ℝ) × M) :
    verticalFamily J hJV (p.1 + (1, 0), p.2) = verticalFamily J hJV p := by
  ext w
  have h := mfderiv_verticalFamily_of_deck hJV (1, 0) (Diffeomorph.refl I M ∞)
    (funext fun p ↦ suspensionCover_add_fst φ p) p w
  simp only [Diffeomorph.coe_refl, mfderiv_id, id_eq] at h
  exact h.symm

include hJV in
/-- The vertical family of `J` satisfies the seam identity
`dφ⁻¹ ∘ K_((s, t), x) = K_((s, t + 1), φ⁻¹ x) ∘ dφ⁻¹`. -/
theorem mfderiv_symm_verticalFamily (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2) :
    mfderiv I I φ.symm p.2 (verticalFamily J hJV p v) =
      verticalFamily J hJV (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v) :=
  mfderiv_verticalFamily_of_deck hJV (0, 1) φ.symm
    (funext fun p ↦ suspensionCover_add_snd_symm φ p) p v

/-! ### Recovering `J` from its vertical family -/

variable (hJs : ∀ y : UnitAddCircle × SmoothMappingTorus φ,
  J y ((Manifold.tangentSpaceProdEquiv y).symm ((1 : ℝ), 0)) =
    (Manifold.tangentSpaceProdEquiv y).symm ((0 : ℝ), timeVectorField φ y.2))

include hJs in
/-- If `J ∂_s = T`, then `q^* J` sends `∂_s` to `∂_t`. -/
private theorem coverStructure_symm_one_zero (p : (ℝ × ℝ) × M) :
    coverStructure J p ((Manifold.tangentSpaceProdEquiv p).symm
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p.1).symm (1, 0), 0)) =
      (Manifold.tangentSpaceProdEquiv p).symm
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) p.1).symm (0, 1), 0) := by
  obtain ⟨⟨s, t⟩, x⟩ := p
  apply ((isLocalDiffeomorph_suspensionCover φ).isInvertible_mfderiv (by simp) _).injective
  rw [mfderiv_coverStructure_apply, mfderiv_suspensionCover_mk, mfderiv_suspensionCover_mk,
    suspensionCover_apply]
  have h0 : mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
      ((Manifold.tangentSpaceProdEquiv (t, x)).symm ((0 : ℝ), (0 : TangentSpace I x))) = 0 :=
    -- The pair `(0, 0)` is the zero of the product of the tangent spaces.
    (congrArg _ (map_zero _)).trans (map_zero _)
  have h := hJs ((s : UnitAddCircle), mk φ t x)
  rw [timeVectorField_mk] at h
  rw [h0]
  exact h

include hJs hJV in
/-- If `J ∂_s = T` and `J V ⊆ V`, then `q^* J` is the block structure of the vertical family of
`J`. -/
private theorem coverStructure_eq_prodFamily :
    coverStructure J = SmoothAlmostComplexStructure.prodFamily
      (AlmostComplexStructure.product ℝ).constSmooth (verticalFamily J hJV)
      (contMDiff_verticalFamily hJV) := by
  refine SmoothAlmostComplexStructure.ext fun p w ↦ ?_
  set F := NormedSpace.fromTangentSpace (𝕜 := ℝ) p.1
  set e := Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ, ℝ × ℝ)) (J := I) p
  -- Write `w = a ∂_s + b ∂_t + v`.
  obtain ⟨a, b, v, rfl⟩ : ∃ (a b : ℝ) (v : TangentSpace I p.2), w = e.symm (F.symm (a, b), v) :=
    ⟨(F (e w).1).1, (F (e w).1).2, (e w).2, by simp⟩
  have hw : e.symm (F.symm (a, b), v) =
      a • e.symm (F.symm (1, 0), 0) + b • e.symm (F.symm (0, 1), 0) + e.symm (0, v) := by
    simp only [← map_smul, ← map_add]
    congr 1
    ext
    · apply F.injective
      simp [map_add, map_smul]
    · simp
  have h₁ : coverStructure J p (e.symm (F.symm (1, 0), 0)) = e.symm (F.symm (0, 1), 0) :=
    coverStructure_symm_one_zero hJs p
  have h₂ : coverStructure J p (e.symm (F.symm (0, 1), 0)) = -e.symm (F.symm (1, 0), 0) := by
    rw [← h₁, SmoothAlmostComplexStructure.apply_apply]
  have hstd : (AlmostComplexStructure.product ℝ).constSmooth p.1 (F.symm (a, b)) =
      F.symm (-b, a) := by
    apply F.injective
    rw [AlmostComplexStructure.fromTangentSpace_constSmooth_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
      AlmostComplexStructure.product_apply]
  rw [SmoothAlmostComplexStructure.prodFamily_apply, ContinuousLinearEquiv.apply_symm_apply, hstd,
    hw]
  have h₃ : coverStructure J p (e.symm (0, v)) = e.symm (0, verticalEndomorphism J p v) :=
    coverStructure_symm_zero hJV p v
  simp only [map_add, map_smul, h₁, h₂, h₃, verticalFamily_apply]
  apply e.injective
  simp only [e, F, map_add, map_smul, map_neg, ContinuousLinearEquiv.apply_symm_apply]
  refine Prod.ext ?_ ?_
  · apply F.injective
    simp [F]
  · simp

include hJs hJV in
/-- **A block almost complex structure on `X_φ` is the descent of its vertical family.** If `J`
sends `∂_s` to the suspension vector field `T` and preserves the vertical subbundle `V`, then `J`
is the block structure `TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure` descended from
its vertical family. -/
theorem suspensionAlmostComplexStructure_verticalFamily :
    suspensionAlmostComplexStructure φ (contMDiff_verticalFamily hJV)
      (verticalFamily_add_fst hJV) (mfderiv_symm_verticalFamily hJV) = J := by
  refine SmoothAlmostComplexStructure.ext fun y ξ ↦ ?_
  obtain ⟨p, rfl⟩ := suspensionCover_surjective φ y
  obtain ⟨w, rfl⟩ :=
    ((isLocalDiffeomorph_suspensionCover φ).isInvertible_mfderiv (by simp) p).surjective ξ
  rw [suspensionAlmostComplexStructure_apply_mfderiv, ← coverStructure_eq_prodFamily hJV hJs,
    mfderiv_coverStructure_apply]

variable (J) in
/-- **The descended block structures on `X_φ` are exactly the block almost complex structures.** A
smooth almost complex structure `J` on `X_φ` is the descent of a smooth vertical family, periodic in
`s` and satisfying the seam identity in `t`, exactly when it sends `∂_s` to the suspension vector
field `T` and preserves the vertical subbundle `V`. -/
theorem exists_suspensionAlmostComplexStructure_eq_iff :
    (∃ (K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2))
      (hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun p ↦ TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
          p.2 (K p).toLinearMap.toContinuousLinearMap))
      (hs : ∀ p : (ℝ × ℝ) × M, K (p.1 + (1, 0), p.2) = K p)
      (ht : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
        mfderiv I I φ.symm p.2 (K p v) =
          K (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)),
      suspensionAlmostComplexStructure φ hK hs ht = J) ↔
    (∀ y : UnitAddCircle × SmoothMappingTorus φ,
      J y ((Manifold.tangentSpaceProdEquiv y).symm ((1 : ℝ), 0)) =
        (Manifold.tangentSpaceProdEquiv y).symm ((0 : ℝ), timeVectorField φ y.2)) ∧
    ∀ (y : UnitAddCircle × SmoothMappingTorus φ)
      (ξ : TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) y),
        ξ ∈ suspensionVerticalSubspace φ y → J y ξ ∈ suspensionVerticalSubspace φ y := by
  refine ⟨?_, fun ⟨hJs, hJV⟩ ↦
    ⟨_, _, _, _, suspensionAlmostComplexStructure_verticalFamily hJV hJs⟩⟩
  rintro ⟨K, hK, hs, ht, rfl⟩
  exact ⟨suspensionAlmostComplexStructure_apply_symm_one_zero φ hK hs ht,
    fun y _ hξ ↦
      suspensionAlmostComplexStructure_apply_mem_suspensionVerticalSubspace hK hs ht y hξ⟩

/-! ### Tameness and compatibility -/

variable {σ : SmoothTwoForm I M} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}

include hJs hJV in
/-- A block almost complex structure on `X_φ` is tamed by `Ω = ds ∧ dt + σ_v` exactly when `σ`
tames every member of its vertical family. -/
theorem tames_suspensionForm_iff_verticalFamily :
    (suspensionForm φ σ hσ).Tames J ↔
      ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2), v ≠ 0 →
        0 < σ.eval₂ p.2 v (verticalFamily J hJV p v) := by
  refine ⟨fun h ⟨⟨s, t⟩, x⟩ v hv ↦ ?_, fun h ↦ ?_⟩
  · have hpos := (SmoothTwoForm.tames_iff.1 h) ((s : UnitAddCircle), mk φ t x)
      ((Manifold.tangentSpaceProdEquiv _).symm
        ((0 : ℝ), mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm ((0 : ℝ), v))))
      fun h0 ↦ hv ((symm_tangentSpaceProdEquiv_eq_zero_iff _ _ _ _ _ _).1 h0).2.2
    rw [apply_mk_eq_verticalFamily hJV, eval₂_suspensionForm_mk] at hpos
    simpa only [mul_zero, sub_zero, zero_add] using hpos
  · rw [← suspensionAlmostComplexStructure_verticalFamily hJV hJs]
    exact tames_suspensionAlmostComplexStructure φ _ _ _ h

include hJs hJV in
/-- A block almost complex structure on `X_φ` is compatible with `Ω = ds ∧ dt + σ_v` exactly when
every member of its vertical family is compatible with the nondegenerate form `σ`. -/
theorem compatible_suspensionForm_iff_verticalFamily (hσn : σ.IsNondegenerate) :
    (suspensionForm φ σ hσ).Compatible J ↔
      ∀ p : (ℝ × ℝ) × M, (hσn.symplecticFormAt p.2).Compatible (verticalFamily J hJV p) := by
  refine ⟨fun h ⟨⟨s, t⟩, x⟩ ↦ .of_tames ?_ fun v hv ↦ ?_, fun h ↦ ?_⟩
  · refine (SymplecticForm.invariant_iff _ _).2 fun v w ↦ ?_
    have hinv := (SmoothTwoForm.invariant_iff.1 h.invariant) ((s : UnitAddCircle), mk φ t x)
      ((Manifold.tangentSpaceProdEquiv _).symm
        ((0 : ℝ), mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm ((0 : ℝ), v))))
      ((Manifold.tangentSpaceProdEquiv _).symm
        ((0 : ℝ), mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm ((0 : ℝ), w))))
    rw [apply_mk_eq_verticalFamily hJV, apply_mk_eq_verticalFamily hJV, eval₂_suspensionForm_mk,
      eval₂_suspensionForm_mk] at hinv
    simpa only [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply, mul_zero, sub_zero,
      zero_add] using hinv
  · rw [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply]
    exact (tames_suspensionForm_iff_verticalFamily hJV hJs).1 h.tames ((s, t), x) v hv
  · rw [← suspensionAlmostComplexStructure_verticalFamily hJV hJs]
    exact compatible_suspensionAlmostComplexStructure φ _ _ _ hσn h

end TauCeti.SmoothMappingTorus
