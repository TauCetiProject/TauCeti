/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Transition
public import TauCeti.Geometry.Symplectic.Liouville.Graph.Basic
import TauCeti.Geometry.Contact.ClosedOrbit.Rescale

/-!
# Every contact form defining the boundary contact structure, through a Liouville graph

Let `W` be a Liouville domain in a manifold `M`, with primitive `α` and complete Liouville field
`Z`, and let `ι : S → M` be a smooth embedding of a compact manifold onto its boundary. Then
`α₀ = ι^* α` is a contact form, with contact structure `ξ = ker α₀`. For a smooth `f > 1` on `S`,
the Liouville graph `j_f(s) = φ_{log f(s)}(ι s)` (`TauCeti.liouvilleGraph`) restricts `α` to the
contact form `f α₀` (`TauCeti.mpullback_liouvilleGraph_apply`), and a contractible closed
characteristic on it, if the graph is a regular level, gives a closed Reeb orbit of `f α₀` whose
loop on the boundary is contractible in `M`
(`IsLiouvilleDomain.exists_isMIntegralCurve_reebVectorField_of_hasContractibleClosedCharacteristic`
in `TauCeti`).

This file reaches every contact form `β` on `S` with `ker β = ξ`, not only the forms `f α₀` with
`f > 1`. Multiplying `β` by a nonzero constant on each connected component of `S` turns it into
some `f α₀` with a smooth `f > 1`
(`TauCeti.SmoothForm.exists_isLocallyConstant_smul_eq_smul`), and such a rescaling keeps
the closed Reeb orbits as subsets of `S`, changing only their speed and, where the constant is
negative, their direction
(`TauCeti.SmoothForm.IsContactForm.isMIntegralCurve_comp_mul_of_eq_smul_of_isLocallyConstant`).
So there is a smooth `f > 1` such that a contractible closed characteristic on the graph of `f`,
as a regular level, gives a closed Reeb orbit of `β` itself, contractible in `M`
(`TauCeti.IsLiouvilleDomain.exists_one_lt_forall_exists_isMIntegralCurve_reebVectorField`).

This is the step of the proof of Corollary E of Barraud–Damian–Humilière–Oancea that passes from
an arbitrary contact form `α` defining `ξ` to the factor `f_α > 1` with `α = f_α α₀`, up to a
constant on each component. The constant may be negative: `-α₀` defines `ξ`, its Reeb field is
`-R_{α₀}`, and its closed Reeb orbits are those of `α₀`, reversed.

## Main results

* `TauCeti.IsLiouvilleDomain.exists_one_lt_forall_exists_isMIntegralCurve_reebVectorField`: for
  every contact form `β` defining the contact structure of the boundary, some Liouville graph turns
  contractible closed characteristics into contractible closed Reeb orbits of `β`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Corollary E and its proof.
-/

public section

open Function Set
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {Z : (x : M) → TangentSpace I x} {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {ι : S → M} [TopologicalSpace S]
  [ChartedSpace H' S] [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
  [IsManifold I (⊤ : ℕ∞) M] [BoundarylessManifold J S] [CompactSpace S]
  [IsManifold J (⊤ : ℕ∞) S] {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {W : Set M}

namespace IsLiouvilleDomain

/-- **Closed Reeb orbits of every contact form defining the boundary contact structure.** Let `ι`
be a smooth injective immersion of a compact manifold `S`, of one dimension less than `M`, into the
frontier of a Liouville domain `W` with primitive `α` and complete Liouville field `Z`, and let `β`
be a contact form on `S` with the same kernel as `ι^* α`. Then there is a smooth `f > 1` on `S`
with the following property: if the Liouville graph of `f` over `ι` is the regular level
`K⁻¹(c)` of a `C²` function `K`, and this level carries a closed characteristic contractible in
some set `V`, then `β` has a closed Reeb orbit `γ` whose loop `ι ∘ γ`, run at another speed, is
contractible in `M`.

This is the step of the proof of Corollary E of Barraud–Damian–Humilière–Oancea that reaches every
contact form defining `ξ`. -/
theorem exists_one_lt_forall_exists_isMIntegralCurve_reebVectorField [FiniteDimensional ℝ E']
    (h : IsLiouvilleDomain ω α W) (hZ : RoughForm.interior Z ω.val = α.val)
    (hc : IsCompleteVectorField Z) (hι : ContMDiff J I (⊤ : ℕ∞) ι) (hιi : Injective ι)
    (hιs : ∀ s, Injective (mfderiv J I ι s)) (hιW : ∀ s, ι s ∈ frontier W)
    (hdim : Module.finrank ℝ E' + 1 = Module.finrank ℝ E) {β : SmoothForm J S ℝ 1}
    (hβ : β.IsContactForm)
    (hker : β.kerDistribution = (SmoothForm.mpullback ι hι α).kerDistribution) :
    ∃ f : S → ℝ, ContMDiff J 𝓘(ℝ) (⊤ : ℕ∞) f ∧ (∀ s, 1 < f s) ∧
      ∀ {K : M → ℝ} {c : ℝ} {V : Set M}, ContMDiff I 𝓘(ℝ) 2 K → IsRegularValue I 𝓘(ℝ) K c →
        {x | K x = c} = range (liouvilleGraph Z ι f) →
        ω.HasContractibleClosedCharacteristic V K c →
        ∃ γ : ℝ → S, IsMIntegralCurve γ β.reebVectorField ∧ (∃ τ, τ ≠ 0 ∧ Periodic γ τ) ∧
          ∃ (T : ℝ) (ψ : ℝ ≃ₜ ℝ), 0 < T ∧
            ∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = ι (γ (ψ t)) := by
  have hα₀ (s : S) : (SmoothForm.mpullback ι hι α).val s ≠ 0 := fun h₀ ↦
    hβ.apply_ne_zero s ((SmoothForm.apply_eq_zero_iff_of_kerDistribution_eq hker s).2 h₀)
  -- Take `f` with `a β = f ι^* α` for a nonzero constant `a` on each connected component of `S`;
  -- the closed Reeb orbits of `f ι^* α = a β` are those of `β`, reparametrized.
  obtain ⟨a, f, ha, ha₀, hf, hf₁, haf⟩ :=
    SmoothForm.exists_isLocallyConstant_smul_eq_smul hα₀ hker 1
  refine ⟨f, hf, hf₁, fun hK hreg hlevel hV ↦ ?_⟩
  have hf₀ (s : S) : 0 < f s := zero_lt_one.trans (hf₁ s)
  obtain ⟨γ, hγ, ⟨τ, hτ, hper⟩, T, ψ, hT, g, hg, hgγ⟩ :=
    h.exists_isMIntegralCurve_reebVectorField_of_hasContractibleClosedCharacteristic hZ hc hι
      hιi hιs hιW hf hf₀ hdim hK hreg hlevel hV
  -- The graph restricts `α` to `f ι^* α = a β`.
  have hθ (s : S) : (SmoothForm.mpullback (liouvilleGraph Z ι f)
      (contMDiff_liouvilleGraph le_top (h.contMDiff_of_interior_eq hZ) hc hι hf
        fun s ↦ (hf₀ s).ne') α).val s = a s • β.val s := by
    rw [haf, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
      mpullback_liouvilleGraph_apply ((h.contMDiff_of_interior_eq hZ).of_le (by simp))
        α.mdifferentiable h.mextDeriv_eq hZ (hc.mem_flowDomain _ _)
        ((hι s).mdifferentiableAt (by simp)) ((hf s).mdifferentiableAt (by simp)) (hf₀ s)]
  -- Along `γ` the constant is `a₀`, and `t ↦ γ (t a₀)` is a closed Reeb orbit of `β`.
  set a₀ := a (γ 0)
  refine ⟨γ ∘ (· * a₀),
    hβ.isMIntegralCurve_comp_mul_of_eq_smul_of_isLocallyConstant ha hθ hγ (ha₀ _),
    ⟨τ / a₀, div_ne_zero hτ (ha₀ _), hper.mul_const' a₀⟩, T,
    ψ.trans (Homeomorph.mulRight₀ a₀⁻¹ (inv_ne_zero (ha₀ _))), hT, g, hg, fun t ↦ ?_⟩
  simp [hgγ, a₀, inv_mul_cancel_right₀ (ha₀ (γ 0))]

end IsLiouvilleDomain

end TauCeti
