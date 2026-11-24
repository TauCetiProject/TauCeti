/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Symplectization.Annihilator
public import TauCeti.Geometry.Manifold.Diffeomorph.Annihilator
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.VectorBundle.Submersion
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift

/-!
# Lifting contactomorphisms to the symplectization

Let `ξ` on `M` and `ξ'` on `N` be contact structures, with no defining one-forms or
coorientations chosen, and let `h : M → N` be a **contactomorphism**: a smooth diffeomorphism whose
differential carries `ξ` onto `ξ'`. The symplectization of `ξ` is the complement `ξ⁰ ∖ 0` of the
zero section in the annihilator line `ξ⁰ ⊂ T*M`, with the tautological one-form
`θ_z(v) = z(dπ v)` (`TauCeti.IsContactDistribution.annihilatorLiouvilleForm`), whose exterior
derivative is symplectic there.

The lift of `h` to the annihilator lines is the diffeomorphism
`Diffeomorph.annihilatorLift`, `(x, p) ↦ (h x, p ∘ (dh_x)⁻¹)`, the restriction of the cotangent
lift of `h`. This file proves that it is the lift of `h` to the symplectizations:

* it preserves the tautological one-form, `Φ^* θ' = θ`
  (`Diffeomorph.mpullback_annihilatorLift_annihilatorLiouvilleForm`), hence the symplectic form
  `dθ` (`Diffeomorph.mpullback_annihilatorLift_mextDerivₗ_annihilatorLiouvilleForm`);
* it maps the symplectization `ξ⁰ ∖ 0` onto `ξ'⁰ ∖ 0`
  (`Diffeomorph.annihilatorLift_mem_annihilatorPunctured_iff`);
* it is the only smooth map covering `h` that preserves the tautological one-form
  (`Diffeomorph.eq_annihilatorLift_of_mpullback_annihilatorLiouvilleForm`); pointwise, a map
  differentiable at `z`, covering `h` near `z` and preserving `θ` at `z` agrees with the lift at
  `z` (`Diffeomorph.apply_eq_annihilatorLift_of_annihilatorLiouvilleForm`).

No coorientation enters: the statements hold equally for contactomorphisms reversing a chosen
coorientation, which exchange the two halves of the punctured line over each point, and for
contact structures that are not the kernel of any global one-form. For a contact form `α` and a
contactomorphism with `h^* α' = f α`, `f > 0`, the trivialized form of this lift is
`(t, x) ↦ (t - log f(x), h x)` on `ℝ × M`
(`TauCeti.SmoothForm.mpullback_symplectizationLift_symplectization`).

The preservation of `θ` is the naturality of the Liouville form under cotangent lifts
(`Diffeomorph.mpullback_cotangent_liouvilleForm`), pulled back along the inclusions of the
annihilator lines. Uniqueness holds because `θ` determines a covector `z` from its values
`θ_z(v) = z(dπ v)`, the derivative of the projection being surjective.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer, 1989,
  Appendix 4 (the symplectification of a contact manifold, and the lift of contact
  diffeomorphisms to it).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 and Appendix B (symplectization of a contact structure).
-/

public section

noncomputable section

open Bundle Function Manifold Module Set
open scoped Manifold ContDiff

open TauCeti TauCeti.CotangentBundle

namespace Diffeomorph

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [Nonempty M] {ξ : Π x : M, Submodule ℝ (TangentSpace I x)}
  {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [Nonempty N] {ξ' : Π y : N, Submodule ℝ (TangentSpace J y)}
  (h : M ≃ₘ⟮I, J⟯ N) (hhξ : ∀ x v, v ∈ ξ x ↔ mfderiv I J h x v ∈ ξ' (h x))
  (hξ : IsContactDistribution I ∞ ξ) (hξ' : IsContactDistribution J ∞ ξ')

/-- `C^(∞ + 1)` charts, needed by the annihilator bundle construction of
`TauCeti.IsContMDiffDistribution.annihilatorContMDiffVectorBundle` at smoothness `∞`. -/
local instance instIsManifoldSymplectizationLiftSource : IsManifold I ((∞ : WithTop ℕ∞) + 1) M :=
  IsManifold.of_le (n := ∞) (by simp)

/-- `C^(∞ + 1)` charts on the target, as for the source. -/
local instance instIsManifoldSymplectizationLiftTarget : IsManifold J ((∞ : WithTop ℕ∞) + 1) N :=
  IsManifold.of_le (n := ∞) (by simp)

/-- **The lift of a contactomorphism preserves the tautological one-form.** The lift of `h` to the
annihilator lines pulls the tautological one-form `θ'` of `ξ'⁰` back to that of `ξ⁰`. -/
theorem mpullback_annihilatorLift_annihilatorLiouvilleForm :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
    haveI := hξ'.isContMDiffDistribution.annihilatorVectorBundle hξ'.finrank_sub_one_add_one
    haveI := hξ'.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ'.finrank_sub_one_add_one
    SmoothForm.mpullback
        (h.annihilatorLift hhξ hξ.isContMDiffDistribution hξ'.isContMDiffDistribution
          hξ.finrank_sub_one_add_one hξ'.finrank_sub_one_add_one)
        (h.annihilatorLift hhξ hξ.isContMDiffDistribution hξ'.isContMDiffDistribution
          hξ.finrank_sub_one_add_one hξ'.finrank_sub_one_add_one).contMDiff
        hξ'.annihilatorLiouvilleForm =
      hξ.annihilatorLiouvilleForm :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
  haveI := hξ'.isContMDiffDistribution.annihilatorVectorBundle hξ'.finrank_sub_one_add_one
  haveI := hξ'.isContMDiffDistribution.annihilatorContMDiffVectorBundle
    hξ'.finrank_sub_one_add_one
  by
  rw [IsContactDistribution.annihilatorLiouvilleForm_def,
    IsContactDistribution.annihilatorLiouvilleForm_def,
    SmoothForm.mpullback_mpullback_of_comp_eq _ _
      (hξ.isContMDiffDistribution.contMDiff_annihilatorInclusion hξ.finrank_sub_one_add_one)
      h.cotangent.contMDiff
      (by rw [coe_annihilatorLift]; exact funext (h.annihilatorInclusion_annihilatorMap _ hhξ)),
    mpullback_cotangent_liouvilleForm]

/-- **The lift of a contactomorphism is symplectic.** The lift of `h` to the annihilator lines
pulls the exterior derivative `dθ'` of the tautological one-form of `ξ'⁰`, the symplectic form of
the symplectization of `ξ'`, back to `dθ`. -/
theorem mpullback_annihilatorLift_mextDerivₗ_annihilatorLiouvilleForm :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
    haveI := hξ'.isContMDiffDistribution.annihilatorVectorBundle hξ'.finrank_sub_one_add_one
    haveI := hξ'.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ'.finrank_sub_one_add_one
    SmoothForm.mpullback
        (h.annihilatorLift hhξ hξ.isContMDiffDistribution hξ'.isContMDiffDistribution
          hξ.finrank_sub_one_add_one hξ'.finrank_sub_one_add_one)
        (h.annihilatorLift hhξ hξ.isContMDiffDistribution hξ'.isContMDiffDistribution
          hξ.finrank_sub_one_add_one hξ'.finrank_sub_one_add_one).contMDiff
        (mextDerivₗ (J.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 hξ'.annihilatorLiouvilleForm) =
      mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 hξ.annihilatorLiouvilleForm :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
  haveI := hξ'.isContMDiffDistribution.annihilatorVectorBundle hξ'.finrank_sub_one_add_one
  haveI := hξ'.isContMDiffDistribution.annihilatorContMDiffVectorBundle
    hξ'.finrank_sub_one_add_one
  by
  rw [← SmoothForm.mextDerivₗ_mpullback,
    h.mpullback_annihilatorLift_annihilatorLiouvilleForm hhξ hξ hξ']

/-- **The lift of a contactomorphism maps the symplectization onto the symplectization.** A
covector annihilating `ξ` is nonzero exactly when its lift is. -/
theorem annihilatorLift_mem_annihilatorPunctured_iff
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x} :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
    h.annihilatorLift hhξ hξ.isContMDiffDistribution hξ'.isContMDiffDistribution
        hξ.finrank_sub_one_add_one hξ'.finrank_sub_one_add_one z ∈ hξ'.annihilatorPunctured ↔
      z ∈ hξ.annihilatorPunctured := by
  simp

/-- **The lift of a contactomorphism is determined pointwise by the tautological one-form.** Let
`G : ξ⁰ → ξ'⁰` be differentiable at `z`, cover `h` near `z`, and pull the tautological one-form
`θ'` of `ξ'⁰` back at `z` to that of `ξ⁰`. Then `G z` is the lift of `h` at `z`. Only the
behaviour of `G` near `z` enters, so this also applies to lifts defined on the symplectization
`ξ⁰ ∖ 0` alone. -/
theorem apply_eq_annihilatorLift_of_annihilatorLiouvilleForm
    {G : (TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x) →
      TotalSpace (Fin 1 → ℝ) fun y ↦ annihilatorSpace J ξ' y}
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x} :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
    haveI := hξ'.isContMDiffDistribution.annihilatorVectorBundle hξ'.finrank_sub_one_add_one
    haveI := hξ'.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ'.finrank_sub_one_add_one
    MDifferentiableAt (I.prod 𝓘(ℝ, Fin 1 → ℝ)) (J.prod 𝓘(ℝ, Fin 1 → ℝ)) G z →
      TotalSpace.proj ∘ G =ᶠ[nhds z] h ∘ TotalSpace.proj →
      (∀ v, hξ'.annihilatorLiouvilleForm.val (G z)
          ![mfderiv (I.prod 𝓘(ℝ, Fin 1 → ℝ)) (J.prod 𝓘(ℝ, Fin 1 → ℝ)) G z v] =
        hξ.annihilatorLiouvilleForm.val z ![v]) →
      G z = h.annihilatorLift hhξ hξ.isContMDiffDistribution hξ'.isContMDiffDistribution
        hξ.finrank_sub_one_add_one hξ'.finrank_sub_one_add_one z :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
  haveI := hξ'.isContMDiffDistribution.annihilatorVectorBundle hξ'.finrank_sub_one_add_one
  haveI := hξ'.isContMDiffDistribution.annihilatorContMDiffVectorBundle
    hξ'.finrank_sub_one_add_one
  by
  intro hG hproj hθ
  have hGz : (G z).proj = h z.proj := hproj.eq_of_nhds
  -- `θ' (dG v) = θ v` reads `(G z) (dh (dπ v)) = z (dπ v)`, since `π' ∘ G = h ∘ π` near `z`.
  have key (v : TangentSpace (I.prod 𝓘(ℝ, Fin 1 → ℝ)) z) :
      ((G z).snd : TangentSpace J (G z).proj →L[ℝ] ℝ)
          (mfderiv I J h z.proj (mfderiv (I.prod 𝓘(ℝ, Fin 1 → ℝ)) I TotalSpace.proj z v)) =
        (z.snd : TangentSpace I z.proj →L[ℝ] ℝ)
          (mfderiv (I.prod 𝓘(ℝ, Fin 1 → ℝ)) I TotalSpace.proj z v) := by
    have hπ' := mfderiv_comp_apply z
      ((contMDiff_proj (fun y ↦ annihilatorSpace J ξ' y) (G z)).mdifferentiableAt one_ne_zero)
      hG v
    have hπ := mfderiv_comp_apply z (h.mdifferentiable (by simp) z.proj)
      ((contMDiff_proj (fun x ↦ annihilatorSpace I ξ x) z).mdifferentiableAt one_ne_zero) v
    have hchain := hπ'.symm.trans ((DFunLike.congr_fun hproj.mfderiv_eq v).trans hπ)
    have hz := hθ v
    rw [IsContactDistribution.annihilatorLiouvilleForm_apply,
      IsContactDistribution.annihilatorLiouvilleForm_apply] at hz
    rw [← hz, ← hchain]
  rw [coe_annihilatorLift]
  refine totalSpace_annihilatorSpace_ext (hGz.trans (proj_annihilatorMap _ h hhξ z).symm)
    fun w ↦ ?_
  -- Every tangent vector at `h x` is `dh (dπ v)` for some tangent vector `v` of `ξ⁰` at `z`.
  obtain ⟨v, hv⟩ := mfderiv_proj_surjective (IB := I) z (mfderiv J I h.symm (h z.proj) w)
  have hw : mfderiv I J h z.proj (mfderiv (I.prod 𝓘(ℝ, Fin 1 → ℝ)) I TotalSpace.proj z v) = w := by
    rw [hv]
    exact h.mfderiv_apply_mfderiv_symm_apply (by simp) z.proj w
  rw [← hw, key, annihilatorMap_snd_apply_mfderiv]

/-- **The lift of a contactomorphism is the unique lift preserving the tautological one-form.** A
smooth map `Ψ : ξ⁰ → ξ'⁰` covering `h` and pulling the tautological one-form `θ'` of `ξ'⁰` back to
that of `ξ⁰` is the lift of `h` to the annihilator lines. In particular, there is no freedom to
rescale the fibres. -/
theorem eq_annihilatorLift_of_mpullback_annihilatorLiouvilleForm
    {Ψ : (TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x) →
      TotalSpace (Fin 1 → ℝ) fun y ↦ annihilatorSpace J ξ' y}
    (hproj : ∀ z, (Ψ z).proj = h z.proj) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
    haveI := hξ'.isContMDiffDistribution.annihilatorVectorBundle hξ'.finrank_sub_one_add_one
    haveI := hξ'.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ'.finrank_sub_one_add_one
    ∀ hΨ : ContMDiff (I.prod 𝓘(ℝ, Fin 1 → ℝ)) (J.prod 𝓘(ℝ, Fin 1 → ℝ)) ∞ Ψ,
      SmoothForm.mpullback Ψ hΨ hξ'.annihilatorLiouvilleForm = hξ.annihilatorLiouvilleForm →
        Ψ = h.annihilatorLift hhξ hξ.isContMDiffDistribution hξ'.isContMDiffDistribution
          hξ.finrank_sub_one_add_one hξ'.finrank_sub_one_add_one :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
  haveI := hξ'.isContMDiffDistribution.annihilatorVectorBundle hξ'.finrank_sub_one_add_one
  haveI := hξ'.isContMDiffDistribution.annihilatorContMDiffVectorBundle
    hξ'.finrank_sub_one_add_one
  fun hΨ hθ ↦ funext fun z ↦
    h.apply_eq_annihilatorLift_of_annihilatorLiouvilleForm hhξ hξ hξ'
      ((hΨ z).mdifferentiableAt (by simp)) (Filter.Eventually.of_forall hproj) fun v ↦ by
        rw [← SmoothForm.mpullback_apply_one Ψ hΨ, hθ]

end Diffeomorph
