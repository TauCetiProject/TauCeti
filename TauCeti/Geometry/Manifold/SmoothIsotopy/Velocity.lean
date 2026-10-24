/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Extension
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
public import TauCeti.Topology.Homotopy.Isotopy.Track
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# The ambient velocity field of a smooth isotopy

A compact boundaryless manifold `M` moving through a boundaryless manifold `N` by smooth
embeddings has a velocity at every point of the moving image. This file extends that velocity to
a compactly supported time-dependent vector field on `N`: a field `X t` on `N` for each time `t`,
jointly smooth in time and space and vanishing outside a fixed compact set, such that each point
of `M` moves along an integral curve of `X`. This is the vector field in the proof of the isotopy
extension theorem, which integrates it to an ambient diffeotopy carrying the initial embedding
along the isotopy.

The motion is a jointly smooth `G : ℝ × M → N`, defined for all real times and stationary before
a time `a` and after a time `b`. Its track `(t, x) ↦ (t, G (t, x))` is a closed embedding of
`ℝ × M` into `ℝ × N`, by compactness of `M`, and an immersion, since the time slices are
immersions. The velocity of the track, the image of the unit time vector under its differential,
is therefore a smooth section of the tangent bundle of `ℝ × N` along an embedded submanifold, and
extends from the compact portion of the track over `[a - 1, b + 1]` to a compactly supported
smooth section of that bundle. Its spatial part, cut off in time outside `(a - 1, b + 1)`, is the
required field. A smooth isotopy on the unit interval is run over the real line by the smooth
time change `Real.smoothTransition`, which is stationary near both ends of the interval.

The field is stated in the form taken by time-dependent flows on manifolds: joint smoothness of
`(t, y) ↦ X t y` as a map into the tangent bundle, and the curves `t ↦ G (t, x)` solving
`γ' t = X t (γ t)`.

## Main results

* `TauCeti.exists_ambientVelocityField`: under a motion of a compact manifold by smooth
  embeddings, stationary outside a compact time interval, every point moves along an integral
  curve of one compactly supported smooth time-dependent vector field.
* `TauCeti.SmoothIsotopy.exists_ambientVelocityField`: the same for a smooth isotopy run at the
  time `Real.smoothTransition t`.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §1: the isotopy
  extension theorem (Theorem 1.3) and its proof.
-/

public section

noncomputable section

open Set Function Topology Manifold Bundle
open scoped Manifold ContDiff

namespace TauCeti

/-- The time derivative of a motion `G : ℝ × M → N` vanishes before a time `a` after which it is
stationary. -/
private theorem mfderiv_eq_zero_of_lt {E' H' M N : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N]
    [ChartedSpace H' N] {G : ℝ × M → N} {a t : ℝ}
    (ha : ∀ s ≤ a, ∀ x, G (s, x) = G (a, x)) (ht : t < a) (x : M) :
    mfderiv 𝓘(ℝ, ℝ) J (fun s => G (s, x)) t = 0 :=
  ((hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := J) (G (a, x)) t).congr_of_eventuallyEq
    (by filter_upwards [Iio_mem_nhds ht] with s hs using ha s hs.le x)).mfderiv

/-- The time derivative of a motion `G : ℝ × M → N` vanishes after a time `b` from which on it is
stationary. -/
private theorem mfderiv_eq_zero_of_gt {E' H' M N : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N]
    [ChartedSpace H' N] {G : ℝ × M → N} {b t : ℝ}
    (hb : ∀ s, b ≤ s → ∀ x, G (s, x) = G (b, x)) (ht : b < t) (x : M) :
    mfderiv 𝓘(ℝ, ℝ) J (fun s => G (s, x)) t = 0 :=
  ((hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := J) (G (b, x)) t).congr_of_eventuallyEq
    (by filter_upwards [Ioi_mem_nhds ht] with s hs using hb s hs.le x)).mfderiv

variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  [I.Boundaryless] [J.Boundaryless] [IsManifold J ∞ N]
  [CompactSpace M] [T2Space N] [SigmaCompactSpace N]

/-- The velocity of the track of a motion of a compact manifold by smooth embeddings extends from
the part of the track over a compact time interval to a compactly supported smooth section of the
tangent bundle of `ℝ × N`. Its spatial part at a point `(t, G (t, x))` of that part of the track is
the time derivative of `s ↦ G (s, x)` at `t`. -/
private theorem exists_section_eq_velocity {n m : ℕ∞} [IsManifold I n M] {G : ℝ × M → N}
    (hG : ContMDiff (𝓘(ℝ, ℝ).prod I) J n G)
    (hslice : ∀ t, IsSmoothEmbedding I J n fun x => G (t, x)) (hm : 1 ≤ m) (hmn : m + 1 ≤ n)
    (c d : ℝ) :
    ∃ Y : Cₛ^m⟮𝓘(ℝ, ℝ).prod J; ℝ × E', TangentSpace (𝓘(ℝ, ℝ).prod J)⟯, ∃ U : Set (ℝ × N),
      IsCompact (closure U) ∧ (∀ p ∉ U, Y p = 0) ∧
      ∀ t ∈ Icc c d, ∀ x, (Y (t, G (t, x))).2 = mfderiv 𝓘(ℝ, ℝ) J (fun s => G (s, x)) t 1 := by
  have hmn' : (m : ℕ∞ω) ≤ n := by exact_mod_cast le_trans le_self_add hmn
  have hm' : (1 : ℕ∞ω) ≤ m := by exact_mod_cast hm
  have hn0 : (n : ℕ∞ω) ≠ 0 := fun h => absurd (hm'.trans hmn') (by simp [h])
  have : IsManifold I m M := .of_le hmn'
  have : IsManifold I 1 M := .of_le (hm'.trans hmn')
  -- The track of the motion, a closed embedding with an immersion normal form everywhere.
  let Γ : ℝ × M → ℝ × N := fun q => (q.1, G q)
  have hΓ : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) n Γ := contMDiff_fst.prodMk hG
  have hΓemb : IsClosedEmbedding Γ :=
    hG.continuous.isClosedEmbedding_fst_prod fun t => (hslice t).isEmbedding.injective
  have hΓimm : ∀ q, IsImmersionAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) m Γ q := fun q => by
    have hq := ((hslice q.1).isImmersion.isImmersionAt q.2).isDiffImmersionAt hn0
    -- An immersion into a finite-dimensional model has a finite-dimensional source model.
    have : FiniteDimensional ℝ E := FiniteDimensional.of_injective
      (mfderiv I J (fun x => G (q.1, x)) q.2).toLinearMap hq.mfderiv_injective
    have : CompleteSpace E := FiniteDimensional.complete ℝ E
    exact (hG.of_le hmn').isImmersionAt_fst_prod hm' hq
  -- The velocity of the track: the image of the unit time vector under its differential.
  let v : (q : ℝ × M) → TangentSpace (𝓘(ℝ, ℝ).prod J) (Γ q) := fun q =>
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) Γ q ((1 : ℝ), (0 : E))
  have hclock : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent m
      (fun s : ℝ => (⟨s, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.2 contDiff_const
  have hunit : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent m
      (fun q : ℝ × M => (⟨q, ((1 : ℝ), (0 : E))⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
    (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ)) (M := ℝ) (I' := I) (M' := M)).comp
      ((hclock.comp contMDiff_fst).prodMk
        ((Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _)).comp contMDiff_snd))
  have hv : ContMDiff (𝓘(ℝ, ℝ).prod I) ((𝓘(ℝ, ℝ).prod J).prod 𝓘(ℝ, ℝ × E')) m
      (fun q => TotalSpace.mk' (ℝ × E') (Γ q) (v q)) :=
    (hΓ.contMDiff_tangentMap (by exact_mod_cast hmn)).comp hunit
  -- Extend the velocity from the compact part of the track over `[c, d]`.
  have hK : IsCompact (Γ '' (Icc c d ×ˢ univ)) :=
    (isCompact_Icc.prod isCompact_univ).image hΓ.continuous
  have : LocallyCompactSpace H' := J.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace H' N
  obtain ⟨U, hU, hKU, -, hcU⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_univ (subset_univ _)
  obtain ⟨Y, hYK, hYU⟩ := hΓemb.isEmbedding.exists_contMDiffSection_extension
    (fun q _ => hΓimm q) hK.isClosed hU hKU v hv
  refine ⟨Y, U, hcU, hYU, fun t ht x => ?_⟩
  -- The spatial part of the track velocity is the time derivative of the motion.
  have hGd : MDifferentiable (𝓘(ℝ, ℝ).prod I) J G := hG.mdifferentiable hn0
  have hpath : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun s : ℝ => (s, x)) t :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hcomp : (fun s => G (s, x)) = G ∘ fun s => (s, x) := rfl
  rw [hYK (t, x) ⟨ht, mem_univ x⟩, hcomp, mfderiv_comp t (hGd _) hpath, mfderiv_prod_left]
  simp only [v, Γ, mfderiv_prodMk mdifferentiableAt_fst (hGd _)]
  -- Both sides are `mfderiv G (t, x) (1, 0)`: `ContinuousLinearMap.prod_apply` and
  -- `ContinuousLinearMap.inl_apply` hold by `rfl`, but do not fire through the instances of the
  -- tangent spaces of the products, which are only definitionally the products of model spaces.
  rfl

/-- **The ambient velocity field of a motion.** Let a compact boundaryless manifold `M` move
through a boundaryless manifold `N` by a `C^n` motion `G : ℝ × M → N` through smooth embeddings,
stationary up to time `a` and from time `b` on. For `1 ≤ m` and `m + 1 ≤ n` there is a
time-dependent vector field `X` on `N`, jointly `C^m` in time and space and vanishing outside a
compact set, along which every point of `M` moves: `∂ₜ G (t, x) = X t (G (t, x))`. -/
theorem exists_ambientVelocityField {n m : ℕ∞} [IsManifold I n M] {G : ℝ × M → N}
    (hG : ContMDiff (𝓘(ℝ, ℝ).prod I) J n G)
    (hslice : ∀ t, IsSmoothEmbedding I J n fun x => G (t, x)) {a b : ℝ}
    (ha : ∀ t ≤ a, ∀ x, G (t, x) = G (a, x)) (hb : ∀ t, b ≤ t → ∀ x, G (t, x) = G (b, x))
    (hm : 1 ≤ m) (hmn : m + 1 ≤ n) :
    ∃ X : ℝ → (y : N) → TangentSpace J y, ∃ K : Set N, IsCompact K ∧
      (∀ t, ∀ y ∉ K, X t y = 0) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod J) J.tangent m
        (fun p : ℝ × N => (⟨p.2, X p.1 p.2⟩ : TangentBundle J N)) ∧
      ∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) J (fun s => G (s, x)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (G (t, x)))) := by
  obtain ⟨Y, U, hcU, hYU, hY⟩ := exists_section_eq_velocity hG hslice hm hmn (a - 1) (b + 1)
  -- A time cutoff equal to `1` on `[a, b]` and vanishing outside `(a - 1, b + 1)`.
  let χ : ℝ → ℝ := fun t =>
    Real.smoothTransition (t - (a - 1)) * Real.smoothTransition (b + 1 - t)
  have hχ : ContDiff ℝ m χ := by fun_prop
  let X : ℝ → (y : N) → TangentSpace J y := fun t y => χ t • (Y (t, y)).2
  refine ⟨X, Prod.snd '' closure U, hcU.image continuous_snd, fun t y hy => ?_, ?_, fun t x => ?_⟩
  · have hty : (t, y) ∉ U := fun h => hy ⟨(t, y), subset_closure h, rfl⟩
    simp only [X, hYU _ hty]
    -- The spatial part of the zero tangent vector of `ℝ × N` is zero by definition.
    exact smul_eq_zero_of_right _ rfl
  · -- `X` is the spatial part of the smooth section `χ • Y` of the tangent bundle of `ℝ × N`.
    have hZ : ContMDiff (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod J).tangent m
        (fun p : ℝ × N => TotalSpace.mk' (ℝ × E') p (χ p.1 • Y p)) :=
      (hχ.contMDiff.comp contMDiff_fst).smul_section Y.contMDiff
    exact contMDiff_snd.comp ((contMDiff_equivTangentBundleProd (I := 𝓘(ℝ, ℝ)) (M := ℝ)
      (I' := J) (M' := N)).comp hZ)
  have hmn' : (m : ℕ∞ω) ≤ n := by exact_mod_cast le_trans le_self_add hmn
  have hm' : (1 : ℕ∞ω) ≤ m := by exact_mod_cast hm
  have hn0 : (n : ℕ∞ω) ≠ 0 := fun h => absurd (hm'.trans hmn') (by simp [h])
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ) J (fun s => G (s, x)) t :=
    (hG.mdifferentiable hn0 (t, x)).comp t (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  suffices key : mfderiv 𝓘(ℝ, ℝ) J (fun s => G (s, x)) t 1 = X t (G (t, x)) by
    refine hc.hasMFDerivAt.congr_mfderiv (ContinuousLinearMap.ext_ring ?_)
    exact key.trans (one_smul ℝ _).symm
  simp only [X]
  by_cases ht : t ∈ Icc (a - 1) (b + 1)
  · rw [hY t ht x]
    by_cases hab : t ∈ Icc a b
    · have hχ1 : χ t = 1 := by
        simp only [χ]
        rw [Real.smoothTransition.one_of_one_le (by linarith [hab.1]),
          Real.smoothTransition.one_of_one_le (by linarith [hab.2]), one_mul]
      rw [hχ1]
      exact (one_smul ℝ _).symm
    · simp only [mem_Icc, not_and_or, not_le] at hab
      rw [hab.elim (mfderiv_eq_zero_of_lt ha · x) (mfderiv_eq_zero_of_gt hb · x)]
      exact (smul_zero _).symm
  · simp only [mem_Icc, not_and_or, not_le] at ht
    have hχ0 : χ t = 0 := by
      rcases ht with ht | ht
      · simp only [χ, Real.smoothTransition.zero_of_nonpos (by linarith : t - (a - 1) ≤ 0),
          zero_mul]
      · simp only [χ, Real.smoothTransition.zero_of_nonpos (by linarith : b + 1 - t ≤ 0),
          mul_zero]
    rw [hχ0, zero_smul, ht.elim (fun ht => mfderiv_eq_zero_of_lt ha (by linarith) x)
      (fun ht => mfderiv_eq_zero_of_gt hb (by linarith) x)]
    -- The zero map applied to `1`; `ContinuousLinearMap.zero_apply` does not fire through the
    -- tangent-space instances.
    rfl

/-- **The ambient velocity field of a smooth isotopy.** A `C^n` isotopy `F` of a compact
boundaryless manifold through smooth embeddings into a boundaryless manifold, run at the time
`Real.smoothTransition t`, which is stationary before time `0` and after time `1`, moves every
point along a compactly supported time-dependent vector field, jointly `C^m` in time and space
for `1 ≤ m` and `m + 1 ≤ n`. -/
theorem SmoothIsotopy.exists_ambientVelocityField {n m : ℕ∞} [IsManifold I n M]
    {f₀ f₁ : C^n⟮I, M; J, N⟯}
    (F : SmoothIsotopy f₀ f₁) (hm : 1 ≤ m) (hmn : m + 1 ≤ n) :
    ∃ X : ℝ → (y : N) → TangentSpace J y, ∃ K : Set N, IsCompact K ∧
      (∀ t, ∀ y ∉ K, X t y = 0) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod J) J.tangent m
        (fun p : ℝ × N => (⟨p.2, X p.1 p.2⟩ : TangentBundle J N)) ∧
      ∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) J
        (fun s => F (⟨Real.smoothTransition s, Real.smoothTransition.nonneg _,
          Real.smoothTransition.le_one _⟩, x)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (F (⟨Real.smoothTransition t,
          Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, x)))) := by
  let σ : ℝ → unitInterval := fun s =>
    ⟨Real.smoothTransition s, Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hσ : ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 1) n σ :=
    contMDiff_id.smoothTransition (by exact_mod_cast le_top)
  have hσ₀ : ∀ t ≤ 0, σ t = σ 0 := fun t ht => Subtype.ext <| by
    simp only [σ, Real.smoothTransition.zero_of_nonpos ht, Real.smoothTransition.zero]
  have hσ₁ : ∀ t, 1 ≤ t → σ t = σ 1 := fun t ht => Subtype.ext <| by
    simp only [σ, Real.smoothTransition.one_of_one_le ht, Real.smoothTransition.one]
  exact TauCeti.exists_ambientVelocityField (G := fun q => F (σ q.1, q.2))
    (F.contMDiff.comp ((hσ.comp contMDiff_fst).prodMk contMDiff_snd))
    (fun t => F.isSmoothEmbedding (σ t)) (fun t ht x => by rw [hσ₀ t ht])
    (fun t ht x => by rw [hσ₁ t ht]) hm hmn

end TauCeti
