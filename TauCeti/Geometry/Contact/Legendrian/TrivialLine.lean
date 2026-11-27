/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Legendrian.Neighborhood
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Annihilator
import TauCeti.Geometry.Contact.Coorientation
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph

/-!
# Legendrian neighbourhoods of a contact structure with trivial contact line

Let `ξ` be a contact structure on a manifold `M` of dimension `2 n + 1`, given by its hyperplanes
alone, and let `ι : Λ → M` be a Legendrian embedding of an `n`-manifold. The contact structure need
not be coorientable, so there may be no contact form with kernel `ξ` on all of `M`. Suppose that
the contact line `TM ⧸ ξ` is trivial along `Λ`, in the form of a continuous choice of nonzero
covectors `σ q` annihilating `ξ (ι q)`: a trivialization of the dual line `ξ⁰` along `Λ`.

The one-jet space `J¹Λ = T^* Λ × ℝ` carries the contact form `dz - λ`, for the Liouville form `λ`
of `T^* Λ` (`TauCeti.SmoothForm.contactization`). This file proves that a neighbourhood of `ι(Λ)`
is contactomorphic to a neighbourhood of the zero section of `J¹Λ`
(`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_kerDistribution_eq_contactization`): there is
a partial diffeomorphism `φ` from `J¹Λ` to `M`, defined on an open neighbourhood of the zero
section, with `φ(0_q, 0) = ι q` for every `q`, whose differential carries the hyperplanes
`ker (dz - λ)` onto the hyperplanes of `ξ` at every point of its source. Along the zero section it
matches the given trivialization of the contact line with that of `J¹Λ` up to positive factors:
`σ q ∘ dφ = c q • (dz - λ)` at `(0_q, 0)` with `c q > 0`. Neither compactness of `Λ` nor
closedness of its image is assumed.

This is the trivial-line case of the Legendrian neighbourhood theorem for contact structures. The
proof reduces it to the strict theorem for contact forms
(`TauCeti.SmoothEmbedding.exists_partialDiffeomorph_mpullback_eq_contactization`). The
trivialization `σ` gives a contact form `α` with kernel `ξ` on an open neighbourhood `W` of
`ι(Λ)`, a positive multiple of `σ` along `ι`
(`TauCeti.IsContactDistribution.exists_opens_isContactForm_pos_smul`). The embedding `ι` is
Legendrian for `ker α` as a map into `W`, the strict theorem on `W` gives `φ` with `φ^* α = dz - λ`,
and `φ` is read in `M` through the inclusion of `W`.

## Main results

* `TauCeti.SmoothEmbedding.exists_partialDiffeomorph_kerDistribution_eq_contactization`: the
  Legendrian neighbourhood theorem for a contact structure whose contact line is trivial along the
  Legendrian submanifold.

## References

* A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*, Mathematical Surveys and
  Monographs 53, AMS (1997), Proposition 43.18.
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.5.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti

variable {F G M : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]
  {D : Π x : M, Submodule ℝ (TangentSpace J x)}

namespace SmoothEmbedding

variable {E H Λ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace Λ] [ChartedSpace H Λ] [IsManifold I ∞ Λ] [J.Boundaryless]
  [SecondCountableTopology M]

/-- **The Legendrian neighbourhood theorem for a contact structure with trivial contact line.**
Let `D` be a contact structure on a Hausdorff second-countable manifold `M` and `ι : Λ → M` a
smooth embedding of a nonempty manifold which is Legendrian for `D`. Suppose the contact line is
trivial along `Λ`: `σ q` is a nonzero covector annihilating `D (ι q)`, depending continuously on
`q`. Then there is a partial diffeomorphism `φ` from the one-jet space `J¹Λ = T^* Λ × ℝ` to `M`,
whose source contains the zero section, with `φ(0_q, 0) = ι q` for every `q`, whose differential
carries the kernel of `dz - λ` onto `D` at every point of its source, and which pulls `σ q` back to
a positive multiple of `dz - λ` at `(0_q, 0)`. Neither compactness of `Λ` nor closedness of `ι(Λ)`
nor coorientability of `D` is needed. -/
theorem exists_partialDiffeomorph_kerDistribution_eq_contactization [Nonempty Λ]
    (hD : IsContactDistribution J ∞ D) (ι : SmoothEmbedding I J ∞ Λ M)
    (hι : IsLegendrianImmersion I D ι) {σ : Π q : Λ, TangentSpace J (ι q) →L[ℝ] ℝ}
    (hσ : Continuous fun q ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace J x →L[ℝ] ℝ) (ι q) (σ q))
    (hσ₀ : ∀ q, σ q ≠ 0) (hσD : ∀ q, σ q ∈ CotangentBundle.annihilatorSpace J D (ι q)) :
    ∃ φ : PartialDiffeomorph ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J
        (CotangentBundle I Λ × ℝ) M ∞,
      (∀ q, (zeroSection (E →L[ℝ] ℝ) (fun x : Λ ↦ TangentSpace I x →L[ℝ] ℝ) q, (0 : ℝ)) ∈
        φ.source) ∧
      (∀ q, φ (zeroSection (E →L[ℝ] ℝ) (fun x : Λ ↦ TangentSpace I x →L[ℝ] ℝ) q, 0) = ι q) ∧
      (∀ x ∈ φ.source, (CotangentBundle.liouvilleForm I Λ).contactization.kerDistribution x =
        (D (φ x)).comap (mfderiv _ J φ x).toLinearMap) ∧
      ∀ q, ∃ c : ℝ, 0 < c ∧ ∀ w, σ q (mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J φ
          (zeroSection (E →L[ℝ] ℝ) (fun x : Λ ↦ TangentSpace I x →L[ℝ] ℝ) q, 0) w) =
        c * (CotangentBundle.liouvilleForm I Λ).contactization.val
          (zeroSection (E →L[ℝ] ℝ) (fun x : Λ ↦ TangentSpace I x →L[ℝ] ℝ) q, 0) ![w] := by
  obtain ⟨W, hιW, α, -, hker, hpos⟩ :=
    hD.exists_opens_isContactForm_pos_smul ι.isEmbedding.isInducing hσ hσ₀ hσD
  have hιW' : ∀ q, ι q ∈ W := fun q ↦ hιW ⟨q, rfl⟩
  let ι' := ι.codRestrict W hιW'
  have hι'_val : ∀ q, (ι' q : M) = ι q := ι.val_codRestrict_apply W hιW'
  -- The restricted embedding is Legendrian for `ker α`.
  have hι' : IsLegendrianImmersion I α.kerDistribution ι' := by
    rw [hker, show (ι' : Λ → W) = fun q ↦ ⟨ι q, hιW' q⟩ from funext fun q ↦ Subtype.ext (hι'_val q)]
    exact hι.codRestrict W hιW'
  have : Nonempty W := ⟨ι' (Classical.arbitrary Λ)⟩
  obtain ⟨φ, hsrc, hval, hφ⟩ := exists_partialDiffeomorph_mpullback_eq_contactization ι' hι'
  -- Read `φ` in `M` through the inclusion of `W`.
  let Ψ := φ.trans (PartialDiffeomorph.subtypeVal J ∞ W this)
  have hΨsrc : Ψ.source = φ.source := by
    rw [PartialDiffeomorph.trans_source, PartialDiffeomorph.subtypeVal_source, preimage_univ,
      inter_univ]
  have hdΨ : ∀ x w, mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J Ψ x w =
      mfderiv ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) J φ x w := fun x w ↦ by
    rw [PartialDiffeomorph.coe_trans, PartialDiffeomorph.coe_subtypeVal]
    exact Manifold.mfderiv_subtype_val_comp_apply w
  have hΨ : ∀ x, Ψ x = (φ x : M) := fun x ↦ by
    rw [PartialDiffeomorph.coe_trans, PartialDiffeomorph.coe_subtypeVal, Function.comp_apply]
  refine ⟨Ψ, fun q ↦ hΨsrc ▸ hsrc q, fun q ↦ ?_, fun x hx ↦ ?_, fun q ↦ ?_⟩
  · rw [hΨ, hval q, hι'_val]
  · rw [hΨsrc] at hx
    ext v
    rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, hdΨ, hΨ, ← congrFun hker (φ x)]
    simp only [SmoothForm.mem_kerDistribution, ← hφ x hx, TauCeti.mpullback_apply_one]
    exact SmoothForm.mem_kerDistribution.symm
  obtain ⟨c, hc, hce⟩ := hpos q (hιW' q)
  refine ⟨c⁻¹, inv_pos.2 hc, fun w ↦ ?_⟩
  have hx := hsrc q
  have key : ∀ y : W, (y : M) = ι q → ∀ v : TangentSpace J y, α.val y ![v] = c * σ q v := by
    rintro ⟨y, hyW⟩ hy v
    dsimp only at hy
    subst hy
    rw [← SmoothForm.degreeOneEquiv_apply_apply_vec, hce]
    exact (smul_apply (σ q) c v).trans (smul_eq_mul c (σ q v))
  rw [hdΨ, ← hφ _ hx, TauCeti.mpullback_apply_one, key _ (by rw [hval q, hι'_val]),
    ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

end SmoothEmbedding

end TauCeti
