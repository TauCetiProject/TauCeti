/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Transport of involutive distributions

A diffeomorphism whose differential identifies two distributions preserves involutivity.
The proof transports local differentiable sections by Mathlib's vector-field pullback and uses
the naturality of the Lie bracket. In particular, a distribution is involutive if and only if
its pullback by a diffeomorphism is involutive.

`TauCeti.IsInvolutiveDistribution.diffeomorph` gives the forward transport theorem, and
`Diffeomorph.isInvolutiveDistribution_iff` gives the equivalence for identified distributions.
`Diffeomorph.isInvolutiveDistribution_comap_mfderiv_iff` gives the pullback characterization.

The distributions remain families of tangent subspaces, and their pullback is expressed using
`Submodule.comap`. No regularity or constant-rank assumption on the distribution is needed.
The diffeomorphism must be at least `C²` over the reals (`minSmoothness 𝕜 2` over a general
scalar field), so that pullbacks of differentiable vector fields are differentiable and their
Lie brackets transform naturally.
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
  [IsManifold I (minSmoothness 𝕜 2) M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J (minSmoothness 𝕜 2) N]
  {n : ℕ∞ω}
  {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}
  {D' : Π y : N, Submodule 𝕜 (TangentSpace J y)}

namespace TauCeti

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

end TauCeti

namespace Diffeomorph

open TauCeti

variable [CompleteSpace F]

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
