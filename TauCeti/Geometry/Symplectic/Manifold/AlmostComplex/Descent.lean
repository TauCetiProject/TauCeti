/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Descending almost complex structures along local diffeomorphisms

Let `q : M → N` be a surjective smooth local diffeomorphism, for instance the projection of a
covering space onto its base, and let `J` be a smooth almost complex structure on `M`. Suppose that
`J` is consistent with `q`: whenever two tangent vectors `v ∈ T_x M` and `w ∈ T_y M` have the same
image under `dq`, so do `J v` and `J w`. Then there is exactly one smooth almost complex structure
`J'` on `N` with `dq ∘ J = J' ∘ dq`. At `q x` it is `dq_x ∘ J_x ∘ (dq_x)⁻¹`; consistency makes
this independent of the point `x` over `q x`, and near each point of `N` it is read through a
smooth local inverse of `q`, which gives smoothness.

Consistency holds in particular when every two points of a fiber of `q` are related by a
deck transformation `g` (`q ∘ g = q`) whose differential intertwines `J`
(`TauCeti.SmoothAlmostComplexStructure.mfderiv_apply_eq_of_deck`). This is how an
almost complex structure built on a cover, invariant under the deck transformations, is put on the
quotient. Tameness, invariance and compatibility with a two-form descend along with `J`: they hold
for `J'` and a form `Ω` on `N` exactly when they hold for `J` and the pullback `q^* Ω`.

## Main definitions

* `TauCeti.SmoothAlmostComplexStructure.descend J hq hsurj hJ`: the descent of `J` along a
  surjective local diffeomorphism `q`.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.descend_apply_mfderiv`: `J' (q x) (dq_x v) = dq_x (J x v)`.
* `TauCeti.SmoothAlmostComplexStructure.eq_descend_iff`: the descent is the only almost complex
  structure on `N` with this property.
* `TauCeti.SmoothAlmostComplexStructure.mfderiv_apply_eq_of_deck`: deck transformations
  intertwining `J` make `J` consistent with `q`.
* `TauCeti.SmoothAlmostComplexStructure.tames_descend_iff`,
  `TauCeti.SmoothAlmostComplexStructure.invariant_descend_iff`,
  `TauCeti.SmoothAlmostComplexStructure.compatible_descend_iff`: a two-form `Ω` on `N` tames, is
  invariant under or is compatible with the descent exactly when `q^* Ω` has the same relation
  with `J`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.2 (almost complex structures).
-/

public section

noncomputable section

open Bundle Function Filter
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M E' H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  {q : M → N}

section Descend

variable (J : SmoothAlmostComplexStructure I M) (hq : IsLocalDiffeomorph I I' ∞ q)
  (hsurj : Surjective q)

/-- The endomorphism `dq_x ∘ J_x ∘ (dq_x)⁻¹` of `T_z N`, at a chosen point `x` over `z`. The casts
identify the tangent spaces at `q x` and `z`, which are equal. -/
private def descendEndomorphism (z : N) : TangentSpace I' z →L[ℝ] TangentSpace I' z :=
  (tangentSpaceCast I' (q (surjInv hsurj z)) z : TangentSpace I' (q (surjInv hsurj z)) →L[ℝ] _) ∘L
    mfderiv I I' q (surjInv hsurj z) ∘L J.toEndomorphism (surjInv hsurj z) ∘L
    (mfderiv I I' q (surjInv hsurj z)).inverse ∘L
    (tangentSpaceCast I' z (q (surjInv hsurj z)) : TangentSpace I' z →L[ℝ] _)

variable {J hsurj}
variable (hJ : ∀ (x y : M), q x = q y → ∀ (v : TangentSpace I x) (w : TangentSpace I y),
  mfderiv I I' q x v = mfderiv I I' q y w → mfderiv I I' q x (J x v) = mfderiv I I' q y (J y w))

omit [IsManifold I' ∞ N] in
include hq hJ in
private theorem descendEndomorphism_apply_mfderiv (x : M) (v : TangentSpace I x) :
    descendEndomorphism J hsurj (q x) (mfderiv I I' q x v) = mfderiv I I' q x (J x v) := by
  set y := surjInv hsurj (q x)
  have hy : q y = q x := surjInv_eq hsurj (q x)
  have hinv := hq.isInvertible_mfderiv (by simp) y
  -- The vector `(dq_y)⁻¹ (dq_x v)` has the same image as `v`.
  exact hJ y x hy _ v (hinv.self_apply_inverse _)

variable [FiniteDimensional ℝ E'] [T2Space N]

include hq hJ in
private theorem contMDiff_descendEndomorphism :
    ContMDiff I' (I'.prod 𝓘(ℝ, E' →L[ℝ] E')) ∞
      (fun z ↦ TotalSpace.mk' (E' →L[ℝ] E')
        (E := fun z : N ↦ TangentSpace I' z →L[ℝ] TangentSpace I' z) z
        (descendEndomorphism J hsurj z)) := by
  refine (Manifold.contMDiff_hom_iff _).2 fun V hV z₀ ↦ ?_
  obtain ⟨x₀, rfl⟩ := hsurj z₀
  have hx₀ := hq x₀
  set s := hx₀.localInverse
  have hs : ContMDiffAt I' I ∞ s (q x₀) := hx₀.contMDiffAt_localInverse
  -- Read near `q x₀` through the local inverse `s`: `J' z (V z) = dq (J (ds (V z)))`.
  have hA : ContMDiffAt I' I.tangent ∞ (fun z ↦ tangentMap I' I s ⟨z, V z⟩) (q x₀) :=
    (hs.contMDiffAt_tangentMap (X := ⟨q x₀, V (q x₀)⟩) (by simp)).comp (q x₀) (hV (q x₀))
  have hB : ContMDiffAt I' I.tangent ∞
      (fun z ↦ TotalSpace.mk' E (s z) (J (s z) (mfderiv I' I s z (V z)))) (q x₀) :=
    ((J.toEndomorphism.contMDiff (s (q x₀))).comp (q x₀) hs).clm_bundle_apply hA
  have hC := ((hq.contMDiff.contMDiff_tangentMap (m := ∞) (by simp)).contMDiffAt).comp (q x₀) hB
  refine hC.congr_of_eventuallyEq ?_
  have hev : ∀ᶠ z in 𝓝 (q x₀), z ∈ hx₀.localInverse.source :=
    hx₀.localInverse_open_source.mem_nhds hx₀.localInverse_mem_source
  filter_upwards [hev] with z hz
  have hqs : q (s z) = z := hx₀.localInverse_right_inv hz
  -- The chain rule for `q ∘ s = id` near `z`: `dq_(s z) (ds_z (V z)) = V z`.
  have hchain : mfderiv I I' q (s z) (mfderiv I' I s z (V z)) = V z := by
    have hid : q ∘ s =ᶠ[𝓝 z] id :=
      eventuallyEq_of_mem (hx₀.localInverse_open_source.mem_nhds hz)
        hx₀.localInverse_eqOn_right
    have hsz : MDifferentiableAt I' I s z :=
      (hx₀.contMDiffOn_localInverse.contMDiffAt
        (hx₀.localInverse_open_source.mem_nhds hz)).mdifferentiableAt (by simp)
    have h := mfderiv_comp_apply z ((hq.contMDiff (s z)).mdifferentiableAt (by simp)) hsz (V z)
    rw [hid.mfderiv_eq, mfderiv_id] at h
    -- The base points `q (s z)` and `z` agree, so `h` is the claim.
    exact h.symm
  have key (y : M) (v : TangentSpace I y) (hy : q y = z) (hv : mfderiv I I' q y v = V z) :
      (⟨z, descendEndomorphism J hsurj z (V z)⟩ : TangentBundle I' N) =
        ⟨q y, mfderiv I I' q y (J y v)⟩ := by
    subst hy
    rw [← hv, descendEndomorphism_apply_mfderiv hq hJ]
  exact key (s z) _ hqs hchain

variable (J hsurj) in
/-- The descent of a smooth almost complex structure `J` on `M` along a surjective smooth local
diffeomorphism `q : M → N`, when `J` is consistent with `q`: tangent vectors with the same image
under `dq` have `J`-images with the same image. It is the unique almost complex structure `J'` on
`N` with `J' (q x) (dq_x v) = dq_x (J x v)` (`TauCeti.SmoothAlmostComplexStructure.eq_descend_iff`).
-/
def descend : SmoothAlmostComplexStructure I' N where
  toEndomorphism := ⟨descendEndomorphism J hsurj, contMDiff_descendEndomorphism hq hJ⟩
  square_neg z := by
    obtain ⟨x, rfl⟩ := hsurj z
    ext u
    obtain ⟨v, rfl⟩ := (hq.isInvertible_mfderiv (by simp) x).surjective u
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, _root_.neg_apply,
      ContinuousLinearMap.id_apply, ContMDiffSection.coeFn_mk]
    rw [descendEndomorphism_apply_mfderiv hq hJ, descendEndomorphism_apply_mfderiv hq hJ,
      apply_apply, map_neg]

variable {hq hJ}

/-- The descent of `J` intertwines the differential of `q`: `J' (q x) (dq_x v) = dq_x (J x v)`. -/
@[simp]
theorem descend_apply_mfderiv (x : M) (v : TangentSpace I x) :
    descend J hq hsurj hJ (q x) (mfderiv I I' q x v) = mfderiv I I' q x (J x v) :=
  descendEndomorphism_apply_mfderiv hq hJ x v

/-- The descent of `J` is the only almost complex structure `K` on `N` with
`K (q x) (dq_x v) = dq_x (J x v)`. -/
theorem eq_descend_iff {K : SmoothAlmostComplexStructure I' N} :
    K = descend J hq hsurj hJ ↔
      ∀ (x : M) (v : TangentSpace I x),
        K (q x) (mfderiv I I' q x v) = mfderiv I I' q x (J x v) := by
  refine ⟨fun h x v ↦ h ▸ descend_apply_mfderiv x v, fun h ↦ ext fun z u ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hsurj z
  obtain ⟨v, rfl⟩ := (hq.isInvertible_mfderiv (by simp) x).surjective u
  rw [h, descend_apply_mfderiv]

end Descend

omit [IsManifold I' ∞ N] in
/-- A smooth almost complex structure is consistent with a smooth map `q` when every two points of
each fiber of `q` are related by a deck transformation `g`, a map with `q ∘ g = q`, whose
differential intertwines `J`. -/
theorem mfderiv_apply_eq_of_deck {J : SmoothAlmostComplexStructure I M}
    (hq : MDifferentiable I I' q)
    (hdeck : ∀ x y : M, q x = q y → ∃ g : M → M, g x = y ∧ q ∘ g = q ∧
      MDifferentiableAt I I g x ∧
        ∀ v : TangentSpace I x, mfderiv I I g x (J x v) = J y (mfderiv I I g x v))
    (hinj : ∀ y : M, Injective (mfderiv I I' q y))
    (x y : M) (hxy : q x = q y) (v : TangentSpace I x) (w : TangentSpace I y)
    (hvw : mfderiv I I' q x v = mfderiv I I' q y w) :
    mfderiv I I' q x (J x v) = mfderiv I I' q y (J y w) := by
  obtain ⟨g, rfl, hqg, hg, hgJ⟩ := hdeck x y hxy
  -- The chain rule for `q ∘ g = q`: `dq_(g x) ∘ dg_x = dq_x`.
  have hchain (u : TangentSpace I x) :
      mfderiv I I' q (g x) (mfderiv I I g x u) = mfderiv I I' q x u := by
    rw [← mfderiv_comp_apply x (hq (g x)) hg, hqg]
  have hw : mfderiv I I g x v = w := hinj (g x) ((hchain v).trans hvw)
  rw [← hchain, hgJ, hw]

section Forms

variable {J : SmoothAlmostComplexStructure I M} {hq : IsLocalDiffeomorph I I' ∞ q}
  {hsurj : Surjective q} [FiniteDimensional ℝ E'] [T2Space N]
  {hJ : ∀ (x y : M), q x = q y → ∀ (v : TangentSpace I x) (w : TangentSpace I y),
    mfderiv I I' q x v = mfderiv I I' q y w → mfderiv I I' q x (J x v) = mfderiv I I' q y (J y w)}
  {Ω : SmoothTwoForm I' N}

/-- A two-form `Ω` on `N` tames the descent of `J` exactly when its pullback `q^* Ω` tames `J`. -/
theorem tames_descend_iff :
    Ω.Tames (descend J hq hsurj hJ) ↔
      SmoothTwoForm.Tames (SmoothForm.mpullback q hq.contMDiff Ω) J := by
  simp only [SmoothTwoForm.tames_iff, SmoothForm.eval₂_mpullback]
  refine ⟨fun h x v hv ↦ ?_, fun h z u hu ↦ ?_⟩
  · rw [← descend_apply_mfderiv]
    exact h (q x) _ ((hq.isInvertible_mfderiv (by simp) x).injective.ne_iff' (map_zero _) |>.2 hv)
  · obtain ⟨x, rfl⟩ := hsurj z
    obtain ⟨v, rfl⟩ := (hq.isInvertible_mfderiv (by simp) x).surjective u
    simp only [descend_apply_mfderiv]
    exact h x v fun hv ↦ hu (by rw [hv, map_zero])

/-- A two-form `Ω` on `N` is invariant under the descent of `J` exactly when its pullback `q^* Ω`
is invariant under `J`. -/
theorem invariant_descend_iff :
    Ω.Invariant (descend J hq hsurj hJ) ↔
      SmoothTwoForm.Invariant (SmoothForm.mpullback q hq.contMDiff Ω) J := by
  simp only [SmoothTwoForm.invariant_iff, SmoothForm.eval₂_mpullback]
  refine ⟨fun h x v w ↦ ?_, fun h z u u' ↦ ?_⟩
  · rw [← descend_apply_mfderiv, ← descend_apply_mfderiv]
    exact h (q x) _ _
  · obtain ⟨x, rfl⟩ := hsurj z
    obtain ⟨v, rfl⟩ := (hq.isInvertible_mfderiv (by simp) x).surjective u
    obtain ⟨w, rfl⟩ := (hq.isInvertible_mfderiv (by simp) x).surjective u'
    simp only [descend_apply_mfderiv]
    exact h x v w

/-- A two-form `Ω` on `N` is compatible with the descent of `J` exactly when its pullback `q^* Ω`
is compatible with `J`. -/
theorem compatible_descend_iff :
    Ω.Compatible (descend J hq hsurj hJ) ↔
      SmoothTwoForm.Compatible (SmoothForm.mpullback q hq.contMDiff Ω) J :=
  ⟨fun h ↦ ⟨invariant_descend_iff.1 h.invariant, tames_descend_iff.1 h.tames⟩,
    fun h ↦ ⟨invariant_descend_iff.2 h.invariant, tames_descend_iff.2 h.tames⟩⟩

end Forms

end TauCeti.SmoothAlmostComplexStructure
