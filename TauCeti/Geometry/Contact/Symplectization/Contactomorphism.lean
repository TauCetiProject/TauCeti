/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactomorphism
public import TauCeti.Geometry.Contact.Symplectization.Annihilator
public import TauCeti.Geometry.Contact.Symplectization.Trivialization
public import TauCeti.Geometry.Manifold.Diffeomorph.Annihilator
import TauCeti.Geometry.Contact.Symplectization.Components
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
contact structures that are not the kernel of any global one-form.

In the trivializations `κ_α : (t, x) ↦ eᵗ α_x` of the annihilator lines by one-forms `α` and `α'`
with kernels `ξ` and `ξ'` (`TauCeti.SmoothForm.symplectizationToAnnihilator`), the lift of a
diffeomorphism `h` with `h^* α' = f α`, written `Φ`, is explicit. Where `f > 0` it is the lift
`(t, x) ↦ (t - log f(x), h x)` of `TauCeti.symplectizationLift`:

`Φ (κ_α (t, x)) = κ_α' (t - log f(x), h x)`

(`Diffeomorph.annihilatorLift_symplectizationToAnnihilator`), so on the positive halves `Φ` is the
lift of the cooriented symplectizations, which pulls `eᵗ α'` back to `eᵗ α`
(`TauCeti.SmoothForm.mpullback_symplectizationLift_symplectization`). Where `f < 0` the lift
reverses the coorientation and lands in the other half,

`Φ (κ_α (t, x)) = κ_(-α') (t - log(-f(x)), h x)`

(`Diffeomorph.annihilatorLift_symplectizationToAnnihilator_of_neg`). These identities only use
that `ξ` and `ξ'` are smooth hyperplane fields. So for `f > 0` the lift maps the image of `κ_α`
onto that of `κ_α'`, and for `f < 0` onto that of `κ_(-α')`
(`Diffeomorph.image_annihilatorLift_range_symplectizationToAnnihilator`,
`Diffeomorph.image_annihilatorLift_range_symplectizationToAnnihilator_of_neg`).

On a connected manifold these images are the two connected components of `ξ⁰ ∖ 0`
(`TauCeti.IsContactDistribution.connectedComponentIn_annihilatorPunctured_eq_range`). Hence a
contactomorphism `g` of `ξ = ker α` with `g^* α = f α`, `f < 0`, exchanges the two components: its
lift sends every covector of `ξ⁰ ∖ 0` to the component not containing it
(`Diffeomorph.disjoint_connectedComponentIn_annihilatorLift`), while it still preserves `θ`. In
the trivialization by `α`, by contrast, no map `(t, x) ↦ (φ(t, x), g x)` covering `g` preserves
`eᵗ α` (`TauCeti.SmoothForm.eq_symplectizationLift_of_mpullback_symplectization_eq`).

On the standard contact space `V × V × ℝ` with `α = dz - ⟪p, dq⟫`, the diffeomorphism
`e : (q, p, z) ↦ (q, c p, c z)` pulls `α` back to `c α`. A map `(t, x) ↦ (φ(t, x), e x)` preserves
`eᵗ α` exactly when `c > 0` and `φ(t, x) = t - log c`
(`TauCeti.mpullback_symplectization_innerProductContactForm_eq_iff_of_coe_eq`), and for `c < 0` the
lift of `e` exchanges the components of `ξ⁰ ∖ 0`
(`TauCeti.disjoint_connectedComponentIn_annihilatorLift_innerProductContactForm_of_coe_eq`). For
`V = ℝ` and `c = -1` this is the map `(x, y, z) ↦ (-x, y, -z)` of `ℝ³` with the form `dz - x dy`,
in the coordinates `(q, p, z) = (y, x, z)` of `TauCeti.mpullback_innerProductContactForm_real`.

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

/-! ### The lift in contact-form trivializations -/

section Trivialization

variable {k k' : ℕ} {D : Π x : M, Submodule ℝ (TangentSpace I x)}
  {D' : Π y : N, Submodule ℝ (TangentSpace J y)}
  (hDD' : ∀ x v, v ∈ D x ↔ mfderiv I J h x v ∈ D' (h x)) (hD : IsContMDiffDistribution I ∞ k D)
  (hD' : IsContMDiffDistribution J ∞ k' D') (hk : k + 1 = finrank ℝ E) (hk' : k' + 1 = finrank ℝ F)
  {α : SmoothForm I M ℝ 1} {α' : SmoothForm J N ℝ 1} (hα : α.kerDistribution = D)
  (hα' : α'.kerDistribution = D') {f : M → ℝ}
  (hf : ∀ x, (SmoothForm.mpullback h h.contMDiff α').val x = f x • α.val x)

omit [Nonempty M] [Nonempty N] in
include hf in
/-- **The lift of a contactomorphism in contact-form trivializations.** If `h` pulls `α'` back to
`f α`, then at a point where `f` is positive the lift of `h` to the annihilator lines sends the
covector `κ_α (t, x) = eᵗ α_x` to `κ_α' (t - log f(x), h x)`: in the trivializations by `α` and
`α'` it is the lift `TauCeti.symplectizationLift` of the cooriented symplectizations. -/
theorem annihilatorLift_symplectizationToAnnihilator {p : ℝ × M} (hp : 0 < f p.2) :
    letI := hD.annihilatorFiberBundle hk
    letI := hD'.annihilatorFiberBundle hk'
    h.annihilatorLift hDD' hD hD' hk hk' (α.symplectizationToAnnihilator hα p) =
      α'.symplectizationToAnnihilator hα' (symplectizationLift h f p) :=
  letI := hD.annihilatorFiberBundle hk
  letI := hD'.annihilatorFiberBundle hk'
  annihilatorInclusion_injective J D' (Fin 1 → ℝ) <| by
    rw [coe_annihilatorLift, annihilatorInclusion_annihilatorMap,
      SmoothForm.annihilatorInclusion_symplectizationToAnnihilator,
      SmoothForm.annihilatorInclusion_symplectizationToAnnihilator]
    exact cotangent_symplectizationToCotangent hf hp

omit [Nonempty M] [Nonempty N] in
include hf in
/-- **The lift of a coorientation-reversing contactomorphism in contact-form trivializations.** If
`h` pulls `α'` back to `f α`, then at a point where `f` is negative the lift of `h` to the
annihilator lines sends the covector `κ_α (t, x) = eᵗ α_x` to `κ_(-α') (t - log(-f(x)), h x)`,
in the other half of the annihilator line of `ξ'`. -/
theorem annihilatorLift_symplectizationToAnnihilator_of_neg {p : ℝ × M} (hp : f p.2 < 0) :
    letI := hD.annihilatorFiberBundle hk
    letI := hD'.annihilatorFiberBundle hk'
    h.annihilatorLift hDD' hD hD' hk hk' (α.symplectizationToAnnihilator hα p) =
      (-α').symplectizationToAnnihilator (SmoothForm.kerDistribution_neg.trans hα')
        (symplectizationLift h (-f) p) :=
  annihilatorLift_symplectizationToAnnihilator h hDD' hD hD' hk hk' hα
    (SmoothForm.kerDistribution_neg.trans hα')
    (fun x ↦ SmoothForm.mpullback_neg_apply_eq_neg_smul (hf x)) (neg_pos.2 hp)

omit [Nonempty M] [Nonempty N] in
include hf in
/-- **The lift of a coorientation-preserving contactomorphism is the lift of the cooriented
symplectizations.** If `h` pulls `α'` back to `f α` for an everywhere positive `f`, then the lift
of `h` to the annihilator lines restricts, through the trivializations `κ_α` and `κ_α'`, to the
map `(t, x) ↦ (t - log f(x), h x)` of `TauCeti.symplectizationLift`. -/
theorem annihilatorLift_comp_symplectizationToAnnihilator (hf₀ : ∀ x, 0 < f x) :
    letI := hD.annihilatorFiberBundle hk
    letI := hD'.annihilatorFiberBundle hk'
    h.annihilatorLift hDD' hD hD' hk hk' ∘ α.symplectizationToAnnihilator hα =
      α'.symplectizationToAnnihilator hα' ∘ symplectizationLift h f :=
  funext fun p ↦
    annihilatorLift_symplectizationToAnnihilator h hDD' hD hD' hk hk' hα hα' hf (hf₀ p.2)

omit [Nonempty M] [Nonempty N] in
include hf in
/-- **The lift of a coorientation-preserving contactomorphism maps half onto half.** If `h` pulls
`α'` back to `f α` for an everywhere positive `f`, then the lift of `h` to the annihilator lines
maps the image of `κ_α`, the covectors that are positive multiples of `α`, onto the image of
`κ_α'`. -/
theorem image_annihilatorLift_range_symplectizationToAnnihilator (hf₀ : ∀ x, 0 < f x) :
    letI := hD.annihilatorFiberBundle hk
    letI := hD'.annihilatorFiberBundle hk'
    h.annihilatorLift hDD' hD hD' hk hk' '' range (α.symplectizationToAnnihilator hα) =
      range (α'.symplectizationToAnnihilator hα') := by
  let := hD.annihilatorFiberBundle hk
  let := hD'.annihilatorFiberBundle hk'
  rw [← Set.range_comp,
    annihilatorLift_comp_symplectizationToAnnihilator h hDD' hD hD' hk hk' hα hα' hf hf₀,
    Set.range_comp, (symplectizationLift_surjective (F := h) h.surjective f).range_eq, image_univ]

omit [Nonempty M] [Nonempty N] in
include hf in
/-- **The lift of a coorientation-reversing contactomorphism maps half onto the opposite half.**
If `h` pulls `α'` back to `f α` for an everywhere negative `f`, then the lift of `h` to the
annihilator lines maps the image of `κ_α`, the covectors that are positive multiples of `α`, onto
the image of `κ_(-α')`, the covectors that are negative multiples of `α'`. -/
theorem image_annihilatorLift_range_symplectizationToAnnihilator_of_neg (hf₀ : ∀ x, f x < 0) :
    letI := hD.annihilatorFiberBundle hk
    letI := hD'.annihilatorFiberBundle hk'
    h.annihilatorLift hDD' hD hD' hk hk' '' range (α.symplectizationToAnnihilator hα) =
      range ((-α').symplectizationToAnnihilator (SmoothForm.kerDistribution_neg.trans hα')) :=
  image_annihilatorLift_range_symplectizationToAnnihilator h hDD' hD hD' hk hk' hα
    (SmoothForm.kerDistribution_neg.trans hα')
    (fun x ↦ SmoothForm.mpullback_neg_apply_eq_neg_smul (hf x)) fun x ↦ neg_pos.2 (hf₀ x)

end Trivialization

/-! ### Exchange of the two halves -/

section Exchange

variable [BoundarylessManifold I M] [PreconnectedSpace M] {g : M ≃ₘ⟮I, I⟯ M}
  (hgξ : ∀ x v, v ∈ ξ x ↔ mfderiv I I g x v ∈ ξ (g x)) {α : SmoothForm I M ℝ 1}
  (hα : α.kerDistribution = ξ) {f : M → ℝ}
  (hf : ∀ x, (SmoothForm.mpullback g g.contMDiff α).val x = f x • α.val x)

include hα hf in
/-- **A coorientation-reversing contactomorphism exchanges the two components of the
symplectization.** Let `ξ = ker α` be a contact structure on a preconnected manifold and let `g`
be a contactomorphism of `ξ` pulling `α` back to `f α` with `f` everywhere negative. Then the
lift of `g` to the symplectization `ξ⁰ ∖ 0` sends every covector to the connected component not
containing it: the component of `κ_α` to that of `κ_(-α)`, and conversely. -/
theorem disjoint_connectedComponentIn_annihilatorLift (hf₀ : ∀ x, f x < 0)
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x}
    (hz : z ∈ hξ.annihilatorPunctured) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    Disjoint (connectedComponentIn (hξ.annihilatorPunctured : Set _) z)
      (connectedComponentIn (hξ.annihilatorPunctured : Set _)
        (g.annihilatorLift hgξ hξ.isContMDiffDistribution hξ.isContMDiffDistribution
          hξ.finrank_sub_one_add_one hξ.finrank_sub_one_add_one z)) := by
  let := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  have hα₀ : ∀ x, α.val x ≠ 0 :=
    (SmoothForm.isContactForm_iff_isContactDistribution_kerDistribution.2 (hα ▸ hξ)).apply_ne_zero
  have hneg := SmoothForm.kerDistribution_neg.trans hα
  have hdisj := SmoothForm.disjoint_range_symplectizationToAnnihilator_neg hα hα₀
  rcases (SmoothForm.mem_range_symplectizationToAnnihilator_or_neg_iff hα hα₀).2
    (hξ.mem_annihilatorPunctured.1 hz) with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · -- The half of `α` goes to the half of `-α`.
    rw [hξ.connectedComponentIn_annihilatorPunctured_eq_range hα p,
      annihilatorLift_symplectizationToAnnihilator_of_neg g hgξ _ _ _ _ hα hα hf (hf₀ p.2),
      hξ.connectedComponentIn_annihilatorPunctured_eq_range hneg]
    exact hdisj
  · -- The half of `-α` goes to the half of `α`, since `g^* α = (-f) (-α)` with `-f > 0`.
    have hf' (x : M) : (SmoothForm.mpullback g g.contMDiff α).val x = -f x • (-α).val x := by
      rw [hf x, NegMemClass.coe_neg, Pi.neg_apply, neg_smul_neg]
    rw [hξ.connectedComponentIn_annihilatorPunctured_eq_range hneg p,
      annihilatorLift_symplectizationToAnnihilator g hgξ _ _ _ _ hneg hα hf' (neg_pos.2 (hf₀ p.2)),
      hξ.connectedComponentIn_annihilatorPunctured_eq_range hα]
    exact hdisj.symm

end Exchange

end Diffeomorph

/-! ### The standard contact space -/

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The diffeomorphism `(q, p, z) ↦ (q, c p, c z)` pulls the standard contact form back to `c`
times itself, pointwise. -/
private theorem mpullback_innerProductContactForm_apply_of_coe_eq {c : ℝ}
    {e : (V × V × ℝ) ≃ₘ[ℝ] (V × V × ℝ)} (he : ⇑e = fun x ↦ (x.1, c • x.2)) (x : V × V × ℝ) :
    (SmoothForm.mpullback e e.contMDiff (innerProductContactForm V)).val x =
      c • (innerProductContactForm V).val x := by
  rw [mpullback_innerProductContactForm_of_coe_eq he, SmoothForm.smul_toRoughForm, Pi.smul_apply]

/-- **The scalings of the standard contact space and the symplectization.** Let `e` be the
diffeomorphism `(q, p, z) ↦ (q, c p, c z)` of `V × V × ℝ`, which pulls the standard contact form
`α = dz - ⟪p, dq⟫` back to `c α`. A map `(t, x) ↦ (φ(t, x), e x)` covering `e` pulls the
symplectization form `eᵗ α` back to itself exactly when `c > 0` and `φ(t, x) = t - log c`. In
particular, for `c < 0`, such as for `(q, p, z) ↦ (q, -p, -z)`, no map covering `e` preserves
`eᵗ α`. -/
theorem mpullback_symplectization_innerProductContactForm_eq_iff_of_coe_eq {c : ℝ}
    {e : (V × V × ℝ) ≃ₘ[ℝ] (V × V × ℝ)} (he : ⇑e = fun x ↦ (x.1, c • x.2))
    {φ : ℝ × (V × V × ℝ) → ℝ} (hφ : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, V × V × ℝ)) 𝓘(ℝ) ∞ φ) :
    SmoothForm.mpullback (fun p ↦ (φ p, e p.2)) (hφ.prodMk (e.contMDiff.comp contMDiff_snd))
        (innerProductContactForm V).symplectization =
      (innerProductContactForm V).symplectization ↔
        0 < c ∧ φ = fun p ↦ p.1 - Real.log c := by
  have hpull := mpullback_innerProductContactForm_apply_of_coe_eq he
  constructor
  · intro h
    obtain ⟨hc, hφe⟩ := SmoothForm.eq_symplectizationLift_of_mpullback_symplectization_eq
      e.contMDiff hpull (isContactForm_innerProductContactForm V).apply_ne_zero hφ h
    exact ⟨hc 0, funext fun p ↦ by simpa using congrArg Prod.fst (congrFun hφe p)⟩
  · rintro ⟨hc, rfl⟩
    -- The map `(t, x) ↦ (t - log c, e x)` is the lift `symplectizationLift e (fun _ ↦ c)`.
    convert SmoothForm.mpullback_symplectizationLift_symplectization e.contMDiff contMDiff_const
      (fun _ ↦ hc) hpull <;> simp

/-- **The scalings with negative factor exchange the components of the symplectization.** For
`c < 0`, the diffeomorphism `(q, p, z) ↦ (q, c p, c z)` of `V × V × ℝ`, such as
`(q, p, z) ↦ (q, -p, -z)`, is a contactomorphism of the standard contact structure `ker α`,
`α = dz - ⟪p, dq⟫`, reversing its coorientation. Its lift to the symplectization `ξ⁰ ∖ 0` of
`ξ = ker α` preserves the tautological one-form
(`Diffeomorph.mpullback_annihilatorLift_annihilatorLiouvilleForm`) and sends every covector to the
connected component not containing it. -/
theorem disjoint_connectedComponentIn_annihilatorLift_innerProductContactForm_of_coe_eq
    [FiniteDimensional ℝ V] {c : ℝ} (hc : c < 0) {e : (V × V × ℝ) ≃ₘ[ℝ] (V × V × ℝ)}
    (he : ⇑e = fun x ↦ (x.1, c • x.2))
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦
      annihilatorSpace 𝓘(ℝ, V × V × ℝ) (innerProductContactForm V).kerDistribution x}
    (hz : z ∈ IsContactDistribution.annihilatorPunctured
      ((isContactForm_innerProductContactForm V).isContactDistribution_kerDistribution (n := ∞))) :
    let hξ : IsContactDistribution 𝓘(ℝ, V × V × ℝ) ∞ (innerProductContactForm V).kerDistribution :=
      (isContactForm_innerProductContactForm V).isContactDistribution_kerDistribution
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    Disjoint (connectedComponentIn (hξ.annihilatorPunctured : Set _) z)
      (connectedComponentIn (hξ.annihilatorPunctured : Set _)
        (e.annihilatorLift (fun x v ↦ (Diffeomorph.isContactomorphism_iff.1
            (isContactomorphism_innerProductContactForm_of_coe_eq hc.ne he) x v).symm)
          hξ.isContMDiffDistribution hξ.isContMDiffDistribution
          hξ.finrank_sub_one_add_one hξ.finrank_sub_one_add_one z)) :=
  Diffeomorph.disjoint_connectedComponentIn_annihilatorLift _ _ rfl
    (mpullback_innerProductContactForm_apply_of_coe_eq he) (fun _ ↦ hc) hz

end TauCeti
