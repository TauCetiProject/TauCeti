/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Transport of distributions through diffeomorphisms

A partial diffeomorphism transports local frames on its source, while a global diffeomorphism
transports smooth constant-rank distributions and involutivity. This allows regularity and
involutivity to be checked in local or global coordinate models when constructing integral
manifolds. In particular, the pullback of a smooth distribution is smooth, and a distribution is
involutive if and only if its pullback by a diffeomorphism is involutive.

The vector-field pullback and Lie-bracket naturality APIs are provided by Mathlib.

`TauCeti.IsDistributionFrameOn.comap_mfderivWithin` pulls a local frame back through partial
coordinates. `TauCeti.IsDistributionFrameOn.comap_mfderiv` is its global specialization, and
`TauCeti.IsContMDiffDistribution.comap_mfderiv` pulls back a smooth distribution.
`TauCeti.IsInvolutiveDistribution.diffeomorph` gives the forward transport theorem, and
`Diffeomorph.isInvolutiveDistribution_iff` gives the equivalence for identified distributions.
`Diffeomorph.isInvolutiveDistribution_comap_mfderiv_iff` gives the pullback characterization.

The distributions remain families of tangent subspaces, and their pullback is expressed by
`Submodule.comap` along the differential. Pulling back a `C^m` frame through a `C^n`
diffeomorphism requires `m + 1 ≤ n`, because the vector-field pullback contains the inverse
differential. Involutivity requires the diffeomorphism to be at least `C²` over the reals
(`minSmoothness 𝕜 2` over a general scalar field), so that pullbacks of differentiable vector
fields are differentiable and their Lie brackets transform naturally.
-/

public section

noncomputable section

open Set Bundle VectorField
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω}
  {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}
  {D' : Π y : N, Submodule 𝕜 (TangentSpace J y)}

namespace TauCeti

section Regularity

variable [IsManifold I 1 M] [IsManifold J 1 N]

private theorem isDistributionFrameOn_comap_mfderivWithin_of_isInvertible {m : ℕ∞ω}
    {ι : Type*} {X : ι → Π y : N, TangentSpace J y} {U : Set N}
    (hX : IsDistributionFrameOn J m D' X U) (f : M → N) (s : Set M)
    (hf : CMDiff[s] n f) (hfinv : ∀ x ∈ s, (mfderivWithin I J f s x).IsInvertible)
    (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n) :
    IsDistributionFrameOn I m
      (fun x ↦ (D' (f x)).comap (mfderivWithin I J f s x).toLinearMap)
      (fun i ↦ mpullbackWithin I J f (X i) s) (s ∩ f ⁻¹' U) := by
  refine ⟨fun i ↦ (hX.contMDiffOn i).mpullbackWithin_vectorField_inter hf
      (fun x hx ↦ hfinv x hx.1) hs hmn, fun {x} hx ↦ ?_, fun {x} hx ↦ ?_⟩
  · apply LinearIndependent.of_comp (mfderivWithin I J f s x).toLinearMap
    convert hX.linearIndependent hx.2 using 1
    funext i
    exact (hfinv x hx.1).self_apply_inverse _
  · apply Submodule.map_injective_of_injective (hfinv x hx.1).injective
    rw [Submodule.map_comap_eq_of_surjective (hfinv x hx.1).surjective]
    rw [Submodule.map_span, ← hX.span_eq hx.2, ← Set.range_comp]
    congr 2
    funext i
    exact (hfinv x hx.1).self_apply_inverse _

/-- Pulling a local frame back through partial coordinates gives a frame on the part of the
coordinate source mapping into the original frame domain. The loss of one derivative comes from
the inverse differential in the vector-field pullback. -/
theorem IsDistributionFrameOn.comap_mfderivWithin {m : ℕ∞ω} {ι : Type*}
    {X : ι → Π y : N, TangentSpace J y} {U : Set N}
    (hX : IsDistributionFrameOn J m D' X U) (Φ : PartialDiffeomorph I J M N n)
    (hmn : m + 1 ≤ n) :
    IsDistributionFrameOn I m
      (fun x ↦ (D' (Φ x)).comap (mfderivWithin I J Φ Φ.source x).toLinearMap)
      (fun i ↦ mpullbackWithin I J Φ (X i) Φ.source) (Φ.source ∩ Φ ⁻¹' U) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hmn
  have hΦinv (x : M) (hx : x ∈ Φ.source) :
      (mfderivWithin I J Φ Φ.source x).IsInvertible := by
    rw [mfderivWithin_eq_mfderiv (Φ.open_source.uniqueMDiffOn x hx)
      (Φ.mdifferentiableAt hn0 hx)]
    exact (_root_.PartialDiffeomorph.isLocalDiffeomorphAt I J n Φ hx).isInvertible_mfderiv hn0
  exact isDistributionFrameOn_comap_mfderivWithin_of_isInvertible hX Φ Φ.source
    Φ.contMDiffOn hΦinv Φ.open_source.uniqueMDiffOn hmn

/-- Pulling a local frame back through a diffeomorphism gives a local frame for the pullback
distribution. The loss of one derivative comes from the inverse differential in the vector-field
pullback. -/
theorem IsDistributionFrameOn.comap_mfderiv {m : ℕ∞ω} {ι : Type*}
    {X : ι → Π y : N, TangentSpace J y} {U : Set N}
    (hX : IsDistributionFrameOn J m D' X U) (h : M ≃ₘ^n⟮I, J⟯ N) (hmn : m + 1 ≤ n) :
    IsDistributionFrameOn I m
      (fun x ↦ (D' (h x)).comap (mfderiv I J h x).toLinearMap)
      (fun i ↦ mpullback I J h (X i)) (h ⁻¹' U) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hmn
  simpa only [univ_inter, mfderivWithin_univ, mpullbackWithin_univ] using
    isDistributionFrameOn_comap_mfderivWithin_of_isInvertible hX h Set.univ
      h.contMDiff.contMDiffOn
      (fun x _ ↦ by simpa only [mfderivWithin_univ] using h.isInvertible_mfderiv hn0)
      uniqueMDiffOn_univ hmn

/-- The pullback of a `C^m` distribution through a `C^n` diffeomorphism is a `C^m`
distribution of the same rank when `m + 1 ≤ n`. -/
theorem IsContMDiffDistribution.comap_mfderiv {m : ℕ∞ω} {k : ℕ}
    (hD' : IsContMDiffDistribution J m k D') (h : M ≃ₘ^n⟮I, J⟯ N) (hmn : m + 1 ≤ n) :
    IsContMDiffDistribution I m k
      (fun x ↦ (D' (h x)).comap (mfderiv I J h x).toLinearMap) := by
  rw [isContMDiffDistribution_iff] at hD' ⊢
  intro x
  obtain ⟨U, hU, hx, X, hX⟩ := hD' (h x)
  exact ⟨h ⁻¹' U, hU.preimage h.continuous, hx, fun i ↦ mpullback I J h (X i),
    hX.comap_mfderiv h hmn⟩

end Regularity

section Involutive

variable [IsManifold I (minSmoothness 𝕜 2) M]
  [IsManifold J (minSmoothness 𝕜 2) N]

/-- A diffeomorphism whose differential identifies two distributions transports involutivity.
The tangent-space identification is stated as membership equivalence, so it applies directly
to both images and preimages of subspaces under the differential. -/
theorem IsInvolutiveDistribution.diffeomorph (hD : IsInvolutiveDistribution I D)
    (h : M ≃ₘ^n⟮I, J⟯ N) (hn : minSmoothness 𝕜 2 ≤ n)
    (hDD' : ∀ x v, v ∈ D x ↔ mfderiv I J h x v ∈ D' (h x)) :
    IsInvolutiveDistribution J D' := by
  have hn0 : n ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num : (0 : ℕ∞ω) < 2) (le_minSmoothness.trans hn))
  rw [isInvolutiveDistribution_iff]
  intro U hU V W hV hW hVD hWD y hy
  let V₀ := mpullback I J h V
  let W₀ := mpullback I J h W
  have hU₀ : IsOpen (h ⁻¹' U) := hU.preimage h.continuous
  have hV₀ : MDiff[h ⁻¹' U] (T% V₀) :=
    hV.mpullback_vectorField_preimage h.contMDiff
      (fun _ _ ↦ h.isInvertible_mfderiv hn0) (le_minSmoothness.trans hn)
  have hW₀ : MDiff[h ⁻¹' U] (T% W₀) :=
    hW.mpullback_vectorField_preimage h.contMDiff
      (fun _ _ ↦ h.isInvertible_mfderiv hn0) (le_minSmoothness.trans hn)
  have hV₀D : ∀ x ∈ h ⁻¹' U, V₀ x ∈ D x := by
    intro x hx
    apply (hDD' x _).mpr
    simpa only [V₀, h.mfderiv_apply_mpullback hn0] using hVD (h x) hx
  have hW₀D : ∀ x ∈ h ⁻¹' U, W₀ x ∈ D x := by
    intro x hx
    apply (hDD' x _).mpr
    simpa only [W₀, h.mfderiv_apply_mpullback hn0] using hWD (h x) hx
  have hx : h.symm y ∈ h ⁻¹' U := by simpa using hy
  have hbr := hD.mlieBracket_mem hU₀ hV₀ hW₀ hV₀D hW₀D hx
  have hVy : MDiffAt (T% V) (h (h.symm y)) :=
    (hV _ hx).mdifferentiableAt (hU.mem_nhds hx)
  have hWy : MDiffAt (T% W) (h (h.symm y)) :=
    (hW _ hx).mdifferentiableAt (hU.mem_nhds hx)
  rw [← mpullback_mlieBracket hVy hWy (h.contMDiff.contMDiffAt) hn] at hbr
  have hmem := (hDD' (h.symm y) _).mp hbr
  rw [h.mfderiv_apply_mpullback hn0, h.apply_symm_apply] at hmem
  exact hmem

end Involutive

end TauCeti

namespace Diffeomorph

open TauCeti

variable [CompleteSpace F] [IsManifold I (minSmoothness 𝕜 2) M]
  [IsManifold J (minSmoothness 𝕜 2) N]

/-- Involutivity is invariant under a diffeomorphism identifying tangent distributions. -/
theorem isInvolutiveDistribution_iff (h : M ≃ₘ^n⟮I, J⟯ N)
    (hn : minSmoothness 𝕜 2 ≤ n)
    (hDD' : ∀ x v, v ∈ D x ↔ mfderiv I J h x v ∈ D' (h x)) :
    IsInvolutiveDistribution I D ↔ IsInvolutiveDistribution J D' := by
  have hn0 : n ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num : (0 : ℕ∞ω) < 2) (le_minSmoothness.trans hn))
  refine ⟨fun hD ↦ hD.diffeomorph h hn hDD', fun hD' ↦ ?_⟩
  apply hD'.diffeomorph h.symm hn
  intro y v
  have hss : h.symm.symm = h := Diffeomorph.ext fun _ ↦ rfl
  have hder : mfderiv I J h (h.symm y) (mfderiv J I h.symm y v) = v := by
    have hh := h.symm.mfderiv_symm_apply_mfderiv_apply hn0 y v
    rw [hss] at hh
    exact hh
  have hh := (hDD' (h.symm y) (mfderiv J I h.symm y v)).symm
  rw [hder, h.apply_symm_apply] at hh
  exact hh

/-- A distribution is involutive exactly when its pullback by a diffeomorphism is involutive.
This form expresses the transported distribution directly as the preimage of each tangent
subspace under the differential. -/
@[simp]
theorem isInvolutiveDistribution_comap_mfderiv_iff (h : M ≃ₘ^n⟮I, J⟯ N)
    (hn : minSmoothness 𝕜 2 ≤ n) (D' : Π y : N, Submodule 𝕜 (TangentSpace J y)) :
    IsInvolutiveDistribution I
      (fun x ↦ (D' (h x)).comap (mfderiv I J h x).toLinearMap) ↔
        IsInvolutiveDistribution J D' :=
  h.isInvolutiveDistribution_iff hn (fun _ _ ↦ Iff.rfl)

end Diffeomorph
