/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.ZeroSection
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible

/-!
# Maps out of a vector bundle sending the zero section onto a submanifold

Let `i : S → M` be a smooth embedding, and let `Φ` be a map out of the total space of a vector
bundle `V → S` with model fibre `P` which sends the zero section onto the submanifold,
`Φ (0_s) = i s`, with injective derivative at `0_s`, as a tubular neighbourhood does. If the rank
of `V` is the codimension of `S`, the fibre of `Φ` over `s` is a transverse slice through the
submanifold: read in the preferred trivialization at `s`, its derivative at `0` followed by the
quotient onto the normal space of `i` at `s` is bijective
(`TauCeti.SmoothEmbedding.bijective_normalClass_mfderiv_comp_mk_trivializationAt_symm`). If the
derivative of `Φ` at `0_s` is invertible, as for a tubular neighbourhood, the rank condition holds
automatically, since the derivative identifies the tangent space `E' × P` of the total space with
the tangent space `E` of `M`
(`bijective_normalClass_mfderiv_comp_mk_trivializationAt_symm_of_isInvertible`, in the namespace
`TauCeti.SmoothEmbedding`).

The tangent space of the total space at `0_s` splits into horizontal and vertical parts
(`TauCeti.Geometry.Manifold.VectorBundle.ZeroSection`). The derivative of `Φ` agrees with that of
`i` on horizontal vectors, so a vertical vector sent into the tangent space of the submanifold is
sent to the image of a horizontal vector, and must vanish by injectivity.
-/

public section

open Bundle Function Topology
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {n : ℕ∞ω} {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)
  {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  {V : S → Type*} [∀ s, AddCommMonoid (V s)] [∀ s, Module 𝕜 (V s)]
  [∀ s, TopologicalSpace (V s)] [TopologicalSpace (TotalSpace P V)]
  [FiberBundle P V] [VectorBundle 𝕜 P V]
  {Φ : TotalSpace P V → M} {s : S}

/-- **The fibres of a map out of a vector bundle are transverse to the image of its zero
section.** Let `Φ` send the zero section of a vector bundle `V → S` onto the embedded submanifold
`i` near `s`, `Φ (0_s') = i s'`, with injective derivative at `0_s`. If the rank of `V` is the
codimension of `S`, then the fibre of `Φ` over `s`, read in the trivialization at `s`, has
bijective normal derivative at `0`: its derivative at `0` followed by the quotient onto the
normal space of `i` at `s` is bijective. -/
theorem bijective_normalClass_mfderiv_comp_mk_trivializationAt_symm
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 E - Module.finrank 𝕜 E')
    (hΦi : ∀ᶠ s' in 𝓝 s, Φ (zeroSection P V s') = i s')
    (hΦ' : Injective (mfderiv (J.prod 𝓘(𝕜, P)) I Φ (zeroSection P V s))) :
    Bijective fun w : P ↦ i.normalClass s hn (mfderiv 𝓘(𝕜, P) I
      (fun w : P ↦ Φ ⟨s, (trivializationAt P V s).symm s w⟩) 0 w) := by
  have hΦ := mdifferentiableAt_of_mfderiv_injective hΦ'
  have hζd := TauCeti.Bundle.hasMFDerivAt_zeroSection (I := J) (F := P) (V := V) s
  -- Along the zero section, the derivative of `Φ` is that of `i` on horizontal vectors.
  have hhor (ξ : TangentSpace J s) : mfderiv J I i s ξ =
      mfderiv (J.prod 𝓘(𝕜, P)) I Φ (zeroSection P V s) (ξ, 0) := by
    have hi : Φ ∘ zeroSection P V =ᶠ[𝓝 s] i := hΦi
    have h₁ : mfderiv J I i s ξ = mfderiv J I (Φ ∘ zeroSection P V) s ξ := by
      rw [hi.mfderiv_eq]
      -- `tangentSpaceCast` is by definition the identity of the model space.
      rfl
    have h₂ : mfderiv J I (Φ ∘ zeroSection P V) s ξ =
        mfderiv (J.prod 𝓘(𝕜, P)) I Φ (zeroSection P V s) (ξ, 0) := by
      rw [mfderiv_comp s hΦ hζd.mdifferentiableAt, hζd.mfderiv]
      rfl
    exact h₁.trans h₂
  -- The normal derivative is a linear map between spaces of the same finite dimension.
  let L : P →ₗ[𝕜] i.NormalSpace s hn :=
    (i.normalClass s hn).comp (mfderiv 𝓘(𝕜, P) I
      (fun w : P ↦ Φ ⟨s, (trivializationAt P V s).symm s w⟩) 0 :
        P →L[𝕜] TangentSpace I (i s)).toLinearMap
  have hinj : Injective L := by
    refine (injective_iff_map_eq_zero L).mpr fun w hw ↦ ?_
    -- A vertical vector sent into the tangent space of the submanifold is horizontal, so zero.
    obtain ⟨ξ, hξ⟩ : mfderiv 𝓘(𝕜, P) I
        (fun w : P ↦ Φ ⟨s, (trivializationAt P V s).symm s w⟩) 0 w ∈ i.tangentRange s hn := by
      rw [← normalClass_ker]
      exact hw
    have h' := hΦ' ((hhor ξ).symm.trans
      (hξ.trans (TauCeti.Bundle.mfderiv_comp_mk_trivializationAt_symm_zero_apply hΦ w)))
    exact (congrArg Prod.snd h').symm
  have : FiniteDimensional 𝕜 P := Module.Finite.of_injective L hinj
  have hfin : Module.finrank 𝕜 P = Module.finrank 𝕜 (i.NormalSpace s hn) := by
    have hsum := i.finrank_normalSpace_add_finrank s hn
    -- The tangent spaces of `S` and `M` are by definition the model spaces `E'` and `E`.
    have hE : Module.finrank 𝕜 (TangentSpace I (i s)) = Module.finrank 𝕜 E := rfl
    have hE' : Module.finrank 𝕜 (TangentSpace J s) = Module.finrank 𝕜 E' := rfl
    omega
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj⟩

/-- **The fibres of a local diffeomorphism out of a vector bundle are transverse to the image of
its zero section.** Let `Φ` send the zero section of a vector bundle `V → S` onto the embedded
submanifold `i` near `s`, `Φ (0_s') = i s'`, with invertible derivative at `0_s`. Then the fibre of
`Φ` over `s`, read in the trivialization at `s`, has bijective normal derivative at `0`. -/
theorem bijective_normalClass_mfderiv_comp_mk_trivializationAt_symm_of_isInvertible
    (hΦi : ∀ᶠ s' in 𝓝 s, Φ (zeroSection P V s') = i s')
    (hΦ' : (mfderiv (J.prod 𝓘(𝕜, P)) I Φ (zeroSection P V s)).IsInvertible) :
    Bijective fun w : P ↦ i.normalClass s hn (mfderiv 𝓘(𝕜, P) I
      (fun w : P ↦ Φ ⟨s, (trivializationAt P V s).symm s w⟩) 0 w) := by
  refine bijective_normalClass_mfderiv_comp_mk_trivializationAt_symm hn ?_ hΦi hΦ'.injective
  -- The tangent space `E' × P` of the total space is isomorphic to the tangent space `E` of `M`.
  have hdim := finrank_eq_of_isInvertible_mfderiv hΦ'
  obtain ⟨e, -⟩ := hΦ'
  have : FiniteDimensional 𝕜 (E' × P) := (e.toLinearEquiv : (E' × P) ≃ₗ[𝕜] E).symm.finiteDimensional
  have : FiniteDimensional 𝕜 E' :=
    Module.Finite.of_injective (LinearMap.inl 𝕜 E' P) LinearMap.inl_injective
  have : FiniteDimensional 𝕜 P :=
    Module.Finite.of_injective (LinearMap.inr 𝕜 E' P) LinearMap.inr_injective
  rw [Module.finrank_prod] at hdim
  omega

end TauCeti.SmoothEmbedding
