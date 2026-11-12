/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Orientation
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.SeamFamily

/-!
# Curves of zero vertical area for the descended block structures of a symplectic suspension

Let `φ` be a diffeomorphism of a locally compact Hausdorff smooth manifold `M` preserving a
two-form `σ`, let `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its smooth mapping torus, with
projection `p : Y_φ → ℝ / ℤ` and vector field `T = ∂_t`, and let `X_φ = (ℝ / ℤ)_s × Y_φ`, with
`ω_v` the fiber form `σ_v` pulled back to `X_φ` and `V = pr_Y^* ker dp` the vertical subbundle
(`TauCeti.SmoothMappingTorus.suspensionVerticalSubspace`).

The classification of compact pseudoholomorphic curves of zero `ω_v`-area as the tori
`(ℝ / ℤ) × γ` over primitive closed orbits `γ`, in
`TauCeti.Geometry.Symplectic.Manifold.Suspension.Leaf` and
`TauCeti.Geometry.Symplectic.Manifold.Suspension.Orientation`, takes three pointwise hypotheses
on the almost complex structure `J` of `X_φ`: `J ∂_s = T`, `J` preserves `V`, and `ω_v` tames the
restriction of `J` to `V`. This file shows that the block structures descended from vertical
families satisfy all three, and states the classification for them with hypotheses on the
vertical family alone.

In the coordinates `(s, t, x)`, the tangent vector `a ∂_s + b ∂_t + v` at `([s], [t, x])` is
vertical exactly when `a = b = 0`
(`TauCeti.SmoothMappingTorus.symm_tangentSpaceProdEquiv_mem_suspensionVerticalSubspace_iff`), and
`ω_v` pairs `a ∂_s + b ∂_t + v` with `a' ∂_s + b' ∂_t + v'` to `σ(v, v')`
(`TauCeti.SmoothMappingTorus.eval₂_mpullback_snd_fiberForm_mk`). The block structure
`TauCeti.SmoothMappingTorus.suspensionAlmostComplexStructure` descended from a vertical family
`K_((s,t),x)`, periodic in `s` and satisfying the seam identity in `t`, sends `∂_s` to `T` by
construction and sends `0 ∂_s + 0 ∂_t + v` to `0 ∂_s + 0 ∂_t + K v`. So it preserves `V`, and for
a vertical vector `ξ = 0 ∂_s + 0 ∂_t + v` the value `ω_v(ξ, J ξ)` is `σ(v, K v)`, positive for
`v ≠ 0` when `σ` tames every `K_((s,t),x)`. Hence for such a structure a compact connected
nonconstant pseudoholomorphic curve of zero vertical area has image the orbit torus
`(ℝ / ℤ) × γ` over a primitive closed orbit, and an embedded one has `Ω`-area the least period of
that orbit.

The same holds for the seam structure `TauCeti.SmoothMappingTorus.seamAlmostComplexStructure`
built from a single `σ`-compatible almost complex structure `J₀` on `M`, with no further
hypothesis, since every member of its vertical family is `σ`-compatible. No `φ`-invariant almost
complex structure on `M` and no compactness of `M` is needed.

## Main results

All declarations are in the namespace `TauCeti.SmoothMappingTorus`.

* `suspensionAlmostComplexStructure_apply_mem_suspensionVerticalSubspace`,
  `seamAlmostComplexStructure_apply_mem_suspensionVerticalSubspace`: the descended block
  structures preserve `V`.
* `eval₂_mpullback_snd_fiberForm_suspensionAlmostComplexStructure_pos`,
  `eval₂_mpullback_snd_fiberForm_seamAlmostComplexStructure_pos`: their restrictions to `V` are
  tamed by `ω_v`.
* `range_eq_range_orbitTorus_of_suspensionAlmostComplexStructure`,
  `range_eq_range_orbitTorus_of_seamAlmostComplexStructure`: a compact connected nonconstant
  pseudoholomorphic curve of zero vertical area fills an orbit torus.
* `integralTopForm_mpullback_suspensionForm_of_suspensionAlmostComplexStructure`,
  `integralTopForm_mpullback_suspensionForm_of_seamAlmostComplexStructure`: an embedded one has
  `Ω`-area the least period of its closed orbit.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (admissible almost complex structures on
  `ℝ × Y_φ` and holomorphic curves on which `ω_φ` vanishes).
* Eleny-Nicoleta Ionel and Thomas H. Parker, *Gromov invariants and symplectic maps*,
  Mathematische Annalen 314 (1999), 127–158 (pseudoholomorphic tori over periodic orbits in
  `S¹ × Y_φ`).
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] {φ : M ≃ₘ⟮I, I⟯ M}

/-! ### The descended block structures -/

section Descended

variable [FiniteDimensional ℝ E]
  {K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)}
  (hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
    (fun p ↦ Bundle.TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 (K p).toLinearMap.toContinuousLinearMap))
  (hs : ∀ p : (ℝ × ℝ) × M, K (p.1 + (1, 0), p.2) = K p)
  (ht : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
    mfderiv I I φ.symm p.2 (K p v) = K (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v))

/-- The block structure descended from a vertical family preserves the vertical subspace
`V = pr_Y^* ker dp` of `X_φ`. -/
theorem suspensionAlmostComplexStructure_apply_mem_suspensionVerticalSubspace
    (q : UnitAddCircle × SmoothMappingTorus φ) {ξ : TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) q}
    (hξ : ξ ∈ suspensionVerticalSubspace φ q) :
    suspensionAlmostComplexStructure φ hK hs ht q ξ ∈ suspensionVerticalSubspace φ q := by
  obtain ⟨⟨⟨s, t⟩, x⟩, rfl⟩ := suspensionCover_surjective φ q
  rw [suspensionCover_apply] at hξ ⊢
  obtain ⟨v, rfl⟩ := mem_suspensionVerticalSubspace_mk_iff.1 hξ
  rw [suspensionAlmostComplexStructure_mk, neg_zero]
  exact mem_suspensionVerticalSubspace_mk_iff.2 ⟨_, rfl⟩

/-- If `σ` tames every member of the vertical family, then `ω_v` tames the restriction to the
vertical subspace of the descended block structure. -/
theorem eval₂_mpullback_snd_fiberForm_suspensionAlmostComplexStructure_pos
    {σ : SmoothTwoForm I M} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}
    (htame : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ σ p.2 v (K p v))
    (q : UnitAddCircle × SmoothMappingTorus φ) {ξ : TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) q}
    (hξ : ξ ∈ suspensionVerticalSubspace φ q) (hξ₀ : ξ ≠ 0) :
    0 < SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))
      q ξ (suspensionAlmostComplexStructure φ hK hs ht q ξ) := by
  obtain ⟨⟨⟨s, t⟩, x⟩, rfl⟩ := suspensionCover_surjective φ q
  rw [suspensionCover_apply] at hξ hξ₀ ⊢
  obtain ⟨v, rfl⟩ := mem_suspensionVerticalSubspace_mk_iff.1 hξ
  have hv : v ≠ 0 := fun hv ↦ hξ₀ ((symm_tangentSpaceProdEquiv_eq_zero_iff _ _ _ _ _ _).2
    ⟨rfl, rfl, hv⟩)
  rw [suspensionAlmostComplexStructure_mk, neg_zero, eval₂_mpullback_snd_fiberForm_mk]
  exact htame ((s, t), x) v hv

section Curves

variable [I.Boundaryless] {E' H' C : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  [TopologicalSpace C] [ChartedSpace H' C] [IsManifold I' ∞ C] [CompactSpace C]
  {j : SmoothAlmostComplexStructure I' C}
  {o : Manifold.Orientation I' C (Fin 2)} {u : C → UnitAddCircle × SmoothMappingTorus φ}

/-- **Curves of zero vertical area for a descended block structure fill an orbit torus.** Let `J`
be the block structure on `X_φ` descended from a vertical family `K`, periodic in `s`, satisfying
the seam identity in `t`, and tamed by `σ`. Let `u` be a smooth `J`-holomorphic map from a compact
connected boundaryless surface `C`, oriented so that the frames `(e, j e)` are positive, that is
not constant. If the vertical area `∫_C u^* ω_v` vanishes, then for every value `(s, [t, x])` of
`u`, the image of `u` is the orbit torus `(ℝ / ℤ) × γ` of the primitive closed orbit `γ` through
`[0, x]`. -/
theorem range_eq_range_orbitTorus_of_suspensionAlmostComplexStructure [T2Space C]
    [PreconnectedSpace C] {σ : SmoothTwoForm I M} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}
    (htame : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ σ p.2 v (K p v))
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (ho : ∀ c (b : Module.Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j (suspensionAlmostComplexStructure φ hK hs ht) u c)
    (h0 : integralTopForm o (SmoothForm.mpullback u hu
      (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))).1 = 0)
    {c₀ : C} (hne : mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c₀ ≠ 0)
    {c : C} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) :
    Set.range u = Set.range (orbitTorus φ (isPeriodicPt_minimalPeriod φ x)) :=
  range_eq_range_orbitTorus_of_integralTopForm_eq_zero_of_mfderiv_ne_zero hu ho hhol
    (fun c ↦ suspensionAlmostComplexStructure_apply_symm_one_zero φ hK hs ht (u c))
    (fun c _ hv ↦
      suspensionAlmostComplexStructure_apply_mem_suspensionVerticalSubspace hK hs ht (u c) hv)
    (fun c _ hv hv₀ ↦
      eval₂_mpullback_snd_fiberForm_suspensionAlmostComplexStructure_pos hK hs ht htame (u c) hv
        hv₀)
    h0 hne hc

/-- **The `Ω`-area of an embedded curve of zero vertical area for a descended block structure.**
Let `J` be the block structure on `X_φ` descended from a vertical family `K`, periodic in `s`,
satisfying the seam identity in `t`, and tamed by `σ`. Let `u` be an injective smooth
`J`-holomorphic map with injective differential from a compact connected boundaryless surface `C`,
oriented so that the frames `(e, j e)` are positive. If the vertical area `∫_C u^* ω_v` vanishes,
then for every value `(s, [t, x])` of `u`, the `Ω`-area `∫_C u^* Ω` is the least period of `x`. -/
theorem integralTopForm_mpullback_suspensionForm_of_suspensionAlmostComplexStructure
    [ConnectedSpace C] {σ : SmoothTwoForm I M} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}
    (htame : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ σ p.2 v (K p v))
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u) (hu₁ : Injective u)
    (ho : ∀ c (b : Module.Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j (suspensionAlmostComplexStructure φ hK hs ht) u c)
    (h0 : integralTopForm o (SmoothForm.mpullback u hu
      (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))).1 = 0)
    (hinj : ∀ c, Injective (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c))
    {c : C} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) :
    integralTopForm o (SmoothForm.mpullback u hu (suspensionForm φ σ hσ)).1 =
      minimalPeriod φ x :=
  integralTopForm_mpullback_suspensionForm_of_integralTopForm_eq_zero hu hu₁ ho hhol
    (fun c ↦ suspensionAlmostComplexStructure_apply_symm_one_zero φ hK hs ht (u c))
    (fun c _ hv ↦
      suspensionAlmostComplexStructure_apply_mem_suspensionVerticalSubspace hK hs ht (u c) hv)
    (fun c _ hv hv₀ ↦
      eval₂_mpullback_snd_fiberForm_suspensionAlmostComplexStructure_pos hK hs ht htame (u c) hv
        hv₀)
    h0 hinj hc

end Curves

end Descended

section Seam

variable [FiniteDimensional ℝ E] {σ : SmoothTwoForm I M}
  (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ) {J₀ : SmoothAlmostComplexStructure I M}
  (hJ₀ : σ.Compatible J₀)

omit [T2Space M] [LocallyCompactSpace M] in
/-- Every member of the seam family built from a `σ`-compatible structure `J₀` is tamed by `σ`. -/
private theorem eval₂_seamFamily_pos (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2) (hv : v ≠ 0) :
    0 < SmoothBundleForm.eval₂ σ p.2 v (seamFamily hσ hJ₀ p v) := by
  simpa only [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply] using
    (compatible_seamFamily hσ hJ₀ hJ₀.isNondegenerate p).tames v hv

/-- The seam structure built from a `σ`-compatible structure `J₀` preserves the vertical subspace
`V = pr_Y^* ker dp` of `X_φ`. -/
theorem seamAlmostComplexStructure_apply_mem_suspensionVerticalSubspace
    (q : UnitAddCircle × SmoothMappingTorus φ) {ξ : TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) q}
    (hξ : ξ ∈ suspensionVerticalSubspace φ q) :
    seamAlmostComplexStructure hσ hJ₀ q ξ ∈ suspensionVerticalSubspace φ q := by
  rw [seamAlmostComplexStructure_def]
  exact suspensionAlmostComplexStructure_apply_mem_suspensionVerticalSubspace _ _ _ q hξ

/-- The restriction of the seam structure built from a `σ`-compatible structure `J₀` to the
vertical subspace of `X_φ` is tamed by `ω_v`. -/
theorem eval₂_mpullback_snd_fiberForm_seamAlmostComplexStructure_pos
    (q : UnitAddCircle × SmoothMappingTorus φ) {ξ : TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) q}
    (hξ : ξ ∈ suspensionVerticalSubspace φ q) (hξ₀ : ξ ≠ 0) :
    0 < SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))
      q ξ (seamAlmostComplexStructure hσ hJ₀ q ξ) := by
  rw [seamAlmostComplexStructure_def]
  exact eval₂_mpullback_snd_fiberForm_suspensionAlmostComplexStructure_pos _ _ _
    (eval₂_seamFamily_pos hσ hJ₀) q hξ hξ₀

section Curves

variable [I.Boundaryless] {E' H' C : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  [TopologicalSpace C] [ChartedSpace H' C] [IsManifold I' ∞ C] [CompactSpace C]
  {j : SmoothAlmostComplexStructure I' C}
  {o : Manifold.Orientation I' C (Fin 2)} {u : C → UnitAddCircle × SmoothMappingTorus φ}

/-- **Curves of zero vertical area for the seam structure fill an orbit torus.** Let `J` be the
seam structure on `X_φ` built from a `σ`-compatible structure `J₀` on `M`, and let `u` be a smooth
`J`-holomorphic map from a compact connected boundaryless surface `C`, oriented so that the frames
`(e, j e)` are positive, that is not constant. If the vertical area `∫_C u^* ω_v` vanishes, then
for every value `(s, [t, x])` of `u`, the image of `u` is the orbit torus `(ℝ / ℤ) × γ` of the
primitive closed orbit `γ` through `[0, x]`. -/
theorem range_eq_range_orbitTorus_of_seamAlmostComplexStructure [T2Space C] [PreconnectedSpace C]
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (ho : ∀ c (b : Module.Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j (seamAlmostComplexStructure hσ hJ₀) u c)
    (h0 : integralTopForm o (SmoothForm.mpullback u hu
      (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))).1 = 0)
    {c₀ : C} (hne : mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c₀ ≠ 0)
    {c : C} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) :
    Set.range u = Set.range (orbitTorus φ (isPeriodicPt_minimalPeriod φ x)) := by
  rw [seamAlmostComplexStructure_def] at hhol
  exact range_eq_range_orbitTorus_of_suspensionAlmostComplexStructure _ _ _
    (eval₂_seamFamily_pos hσ hJ₀) hu ho hhol h0 hne hc

/-- **The `Ω`-area of an embedded curve of zero vertical area for the seam structure.** Let `J` be
the seam structure on `X_φ` built from a `σ`-compatible structure `J₀` on `M`, and let `u` be an
injective smooth `J`-holomorphic map with injective differential from a compact connected
boundaryless surface `C`, oriented so that the frames `(e, j e)` are positive. If the vertical area
`∫_C u^* ω_v` vanishes, then for every value `(s, [t, x])` of `u`, the `Ω`-area `∫_C u^* Ω` is the
least period of `x`. -/
theorem integralTopForm_mpullback_suspensionForm_of_seamAlmostComplexStructure [ConnectedSpace C]
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u) (hu₁ : Injective u)
    (ho : ∀ c (b : Module.Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : ∀ c, IsPseudoholomorphicAt j (seamAlmostComplexStructure hσ hJ₀) u c)
    (h0 : integralTopForm o (SmoothForm.mpullback u hu
      (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))).1 = 0)
    (hinj : ∀ c, Injective (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c))
    {c : C} {t : ℝ} {x : M} (hc : (u c).2 = mk φ t x) :
    integralTopForm o (SmoothForm.mpullback u hu (suspensionForm φ σ hσ)).1 =
      minimalPeriod φ x := by
  rw [seamAlmostComplexStructure_def] at hhol
  exact integralTopForm_mpullback_suspensionForm_of_suspensionAlmostComplexStructure _ _ _
    (eval₂_seamFamily_pos hσ hJ₀) hu hu₁ ho hhol h0 hinj hc

end Curves

end Seam

end TauCeti.SmoothMappingTorus
