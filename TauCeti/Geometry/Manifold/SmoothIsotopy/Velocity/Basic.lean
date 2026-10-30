/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Extension
public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# Ambient velocity on a compact part of a smooth motion

Let a boundaryless manifold `M` move through a finite-dimensional boundaryless manifold `N`
by smooth embeddings. On any compact subset `A` of `M`, the velocity extends to a smooth
ambient time-dependent vector field with support in a fixed compact subset of `N`, provided
that the motion of `A` is stationary outside a bounded time interval. The source itself need
not be compact. In particular, `A` can be a closed disc in an open-disc source.

The time-preserving track is an injective immersion. Its restriction to a precompact open
neighbourhood of the compact portion under consideration is a topological embedding: it
is a restriction of a continuous injection from the compact closure into a Hausdorff space.
Extend the track velocity using `Topology.IsEmbedding.exists_contMDiffSection_extension`
and cut off in time. This is the velocity-extension step in the proof of isotopy extension;
integration of the field is separate.

`TauCeti.exists_ambientVelocityField` allows arbitrary codimension and loses one derivative.
It requires stationarity only on the compact subset whose velocity is extended.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §1,
  Theorems 1.3--1.4 and their proof.
-/

public section

noncomputable section

open Set Function Topology Manifold Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  [I.Boundaryless] [J.Boundaryless] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

/-- The velocity of a motion by smooth embeddings extends from the track of a compact subset
over a compact time interval to a compactly supported smooth section of the
tangent bundle of `ℝ × N`. Its spatial part at a point `(t, G (t, x))` of that part of the track is
the time derivative of `s ↦ G (s, x)` at `t`. -/
private theorem exists_section_eq_velocity {n m : ℕ∞} [IsManifold I n M] {G : ℝ × M → N}
    (hG : ContMDiff (𝓘(ℝ, ℝ).prod I) J n G)
    (hslice : ∀ t, IsSmoothEmbedding I J n fun x => G (t, x)) (hm : 1 ≤ m) (hmn : m + 1 ≤ n)
    {A : Set M} (hA : IsCompact A) (c d : ℝ) :
    ∃ Y : Cₛ^m⟮𝓘(ℝ, ℝ).prod J; ℝ × E', TangentSpace (𝓘(ℝ, ℝ).prod J)⟯, ∃ U : Set (ℝ × N),
      IsCompact (closure U) ∧ (∀ p ∉ U, Y p = 0) ∧
      ∀ t ∈ Icc c d, ∀ x ∈ A, (Y (t, G (t, x))).2 = mfderiv 𝓘(ℝ, ℝ) J (fun s => G (s, x)) t 1 := by
  have hmn' : (m : ℕ∞ω) ≤ n := by exact_mod_cast le_trans le_self_add hmn
  have hm' : (1 : ℕ∞ω) ≤ m := by exact_mod_cast hm
  have hn0 : (n : ℕ∞ω) ≠ 0 := fun h => absurd (hm'.trans hmn') (by simp [h])
  have : IsManifold I m M := .of_le hmn'
  have : IsManifold I 1 M := .of_le (hm'.trans hmn')
  rcases isEmpty_or_nonempty M with hM | hM
  · have := hM
    exact ⟨0, ∅, by simp, fun _ _ => rfl, fun _ _ x _ => isEmptyElim x⟩
  obtain ⟨x₀⟩ := hM
  have : FiniteDimensional ℝ E := FiniteDimensional.of_injective
    (mfderiv I J (fun x => G (0, x)) x₀).toLinearMap
    (((hslice 0).isImmersion.isImmersionAt x₀).isDiffImmersionAt hn0).mfderiv_injective
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : T2Space M := (hslice 0).isEmbedding.t2Space
  -- Restrict the injective track to a precompact open neighbourhood of the compact portion.
  let Γ : ℝ × M → ℝ × N := fun q => (q.1, G q)
  have hΓ : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) n Γ := contMDiff_fst.prodMk hG
  have hΓinj : Injective Γ := by
    rintro ⟨t, x⟩ ⟨s, y⟩ h
    obtain rfl : t = s := congrArg Prod.fst h
    exact Prod.ext rfl ((hslice t).isEmbedding.injective (congrArg Prod.snd h))
  obtain ⟨W₀, hW₀, hAW, -, hcW⟩ := exists_open_between_and_isCompact_closure
    (isCompact_Icc.prod hA : IsCompact (Icc c d ×ˢ A)) isOpen_univ (subset_univ _)
  let W : TopologicalSpace.Opens (ℝ × M) := ⟨W₀, hW₀⟩
  have : CompactSpace (closure W₀) := isCompact_iff_compactSpace.mp hcW
  have hΓcl : IsEmbedding (fun q : closure W₀ => Γ q) :=
    ((hΓ.continuous.comp continuous_subtype_val).isClosedEmbedding
      (hΓinj.comp Subtype.val_injective)).isEmbedding
  have hΓW : IsEmbedding (fun q : W => Γ q) :=
    hΓcl.comp (IsEmbedding.inclusion (subset_closure : W₀ ⊆ closure W₀))
  have hΓimm : ∀ q, IsImmersionAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) m Γ q := fun q => by
    have hq := ((hslice q.1).isImmersion.isImmersionAt q.2).isDiffImmersionAt hn0
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
  have hK : IsCompact (Γ '' (Icc c d ×ˢ A)) :=
    (isCompact_Icc.prod hA).image hΓ.continuous
  have himage : (fun q : W => Γ q) '' (Subtype.val ⁻¹' (Icc c d ×ˢ A)) =
      Γ '' (Icc c d ×ˢ A) := by
    rw [← image_image]
    exact congrArg (image Γ) (image_preimage_eq_of_subset (by simpa [W] using hAW))
  have : LocallyCompactSpace H' := J.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace H' N
  obtain ⟨U, hU, hKU, -, hcU⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_univ (subset_univ _)
  obtain ⟨Y, hYK, hYU⟩ := hΓW.exists_contMDiffSection_extension
    (I := 𝓘(ℝ, ℝ).prod I) (J := 𝓘(ℝ, ℝ).prod J)
    (fun q _ => isImmersionAt_comp_isLocalDiffeomorphAt
      (isLocalDiffeomorph_subtype_val q) (hΓimm q))
    (himage.symm ▸ hK.isClosed) hU (himage.symm ▸ hKU)
    (fun q : W => v q) (hv.comp contMDiff_subtype_val)
  refine ⟨Y, U, hcU, hYU, fun t ht x hx => ?_⟩
  -- The spatial part of the track velocity is the time derivative of the motion.
  have hGd : MDifferentiable (𝓘(ℝ, ℝ).prod I) J G := hG.mdifferentiable hn0
  have hpath : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun s : ℝ => (s, x)) t :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hcomp : (fun s => G (s, x)) = G ∘ fun s => (s, x) := rfl
  rw [hYK ⟨(t, x), hAW ⟨ht, hx⟩⟩ ⟨ht, hx⟩, hcomp, mfderiv_comp t (hGd _) hpath, mfderiv_prod_left]
  simp only [v, Γ, mfderiv_prodMk mdifferentiableAt_fst (hGd _)]
  -- Both sides are `mfderiv G (t, x) (1, 0)`: `ContinuousLinearMap.prod_apply` and
  -- `ContinuousLinearMap.inl_apply` hold by `rfl`, but do not fire through the instances of the
  -- tangent spaces of the products, which are only definitionally the products of model spaces.
  rfl

/-- A compact part of a motion through smooth embeddings moves along a compactly supported
smooth ambient vector field. The source need not be compact, and stationarity outside the time
interval `[a, b]` is required only on `A`. The field is jointly `C^m` in time and space when the
motion is `C^n`, with `1 ≤ m` and `m + 1 ≤ n`. -/
theorem exists_ambientVelocityField {n m : ℕ∞} [IsManifold I n M] {G : ℝ × M → N}
    (hG : ContMDiff (𝓘(ℝ, ℝ).prod I) J n G)
    (hslice : ∀ t, IsSmoothEmbedding I J n fun x => G (t, x))
    {A : Set M} (hA : IsCompact A) {a b : ℝ}
    (ha : ∀ t ≤ a, ∀ x ∈ A, G (t, x) = G (a, x))
    (hb : ∀ t, b ≤ t → ∀ x ∈ A, G (t, x) = G (b, x))
    (hm : 1 ≤ m) (hmn : m + 1 ≤ n) :
    ∃ X : ℝ → (y : N) → TangentSpace J y, ∃ K : Set N, IsCompact K ∧
      (∀ t, ∀ y ∉ K, X t y = 0) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod J) J.tangent m
        (fun p : ℝ × N => (⟨p.2, X p.1 p.2⟩ : TangentBundle J N)) ∧
      ∀ t, ∀ x ∈ A, HasMFDerivAt 𝓘(ℝ, ℝ) J (fun s => G (s, x)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (G (t, x)))) := by
  obtain ⟨Y, U, hcU, hYU, hY⟩ := exists_section_eq_velocity hG hslice hm hmn hA (a - 1) (b + 1)
  -- A time cutoff equal to `1` on `[a, b]` and vanishing outside `(a - 1, b + 1)`.
  let χ : ℝ → ℝ := fun t =>
    Real.smoothTransition (t - (a - 1)) * Real.smoothTransition (b + 1 - t)
  have hχ : ContDiff ℝ m χ := by fun_prop
  let X : ℝ → (y : N) → TangentSpace J y := fun t y => χ t • (Y (t, y)).2
  refine ⟨X, Prod.snd '' closure U, hcU.image continuous_snd,
    fun t y hy => ?_, ?_, fun t x hx => ?_⟩
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
  · rw [hY t ht x hx]
    by_cases hab : t ∈ Icc a b
    · have hχ1 : χ t = 1 := by
        simp only [χ]
        rw [Real.smoothTransition.one_of_one_le (by linarith [hab.1]),
          Real.smoothTransition.one_of_one_le (by linarith [hab.2]), one_mul]
      rw [hχ1]
      exact (one_smul ℝ _).symm
    · simp only [mem_Icc, not_and_or, not_le] at hab
      rw [hab.elim (Manifold.mfderiv_eq_zero_of_eqOn_Iic (fun s hs => ha s hs x hx))
        (Manifold.mfderiv_eq_zero_of_eqOn_Ici (fun s hs => hb s hs x hx))]
      exact (smul_zero _).symm
  · simp only [mem_Icc, not_and_or, not_le] at ht
    have hχ0 : χ t = 0 := by
      rcases ht with ht | ht
      · simp only [χ, Real.smoothTransition.zero_of_nonpos (by linarith : t - (a - 1) ≤ 0),
          zero_mul]
      · simp only [χ, Real.smoothTransition.zero_of_nonpos (by linarith : b + 1 - t ≤ 0),
          mul_zero]
    rw [hχ0, zero_smul,
      ht.elim (fun ht => Manifold.mfderiv_eq_zero_of_eqOn_Iic
        (fun s hs => ha s hs x hx) (by linarith))
        (fun ht => Manifold.mfderiv_eq_zero_of_eqOn_Ici
          (fun s hs => hb s hs x hx) (by linarith))]
    -- The zero map applied to `1`; `ContinuousLinearMap.zero_apply` does not fire through the
    -- tangent-space instances.
    rfl

end TauCeti
