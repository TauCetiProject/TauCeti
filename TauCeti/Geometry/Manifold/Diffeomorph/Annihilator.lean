/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Cotangent
public import TauCeti.Geometry.Manifold.Distribution.Diffeomorph
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Annihilator
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Lifting diffeomorphisms to annihilator bundles

Let `h : M → N` be a smooth diffeomorphism whose differential carries a distribution `D` on `M`
onto a distribution `D'` on `N`: a tangent vector `v` at `x` lies in `D x` exactly when `dh_x v`
lies in `D' (h x)`. Then the cotangent lift of `h`, which sends a covector `p` at `x` to
`p ∘ (dh_x)⁻¹` at `h x`, carries covectors annihilating `D` to covectors annihilating `D'`. This
file restricts the cotangent lift to the annihilators:

* `Diffeomorph.annihilatorMap h P hDD'` is the map `D⁰ → D'⁰`, `(x, p) ↦ (h x, p ∘ (dh_x)⁻¹)`,
  between the total spaces of the annihilators (`TauCeti.CotangentBundle.annihilatorSpace`). Under
  the inclusions of the annihilators into the cotangent bundles it is the cotangent lift
  `Diffeomorph.cotangent` (`Diffeomorph.annihilatorInclusion_annihilatorMap`). It respects the
  pairing of covectors with tangent vectors, preserves the zero section and its complement, and
  is functorial: the lifts of the identity, of a composite and of the inverse are the identity, the
  composite and the inverse.
* For smooth distributions of the same corank `r` on finite-dimensional manifolds, whose
  annihilators are smooth vector bundles of rank `r`
  (`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`), the map is a smooth diffeomorphism
  `Diffeomorph.annihilatorLift` of the total spaces. Smoothness comes from the smooth embedding of
  the target annihilator bundle into the cotangent bundle
  (`TauCeti.IsContMDiffDistribution.isSmoothEmbedding_annihilatorInclusion`): composed with that
  embedding the map is the smooth map `T*h ∘ j`.

For a contact structure `ξ`, the annihilator line `ξ⁰` without its zero section is the
symplectization of `ξ`, and a contactomorphism is a diffeomorphism carrying `ξ` onto `ξ'`. The
lift constructed here is its lift to the symplectizations, which needs no coorientation.

## Main definitions

* `Diffeomorph.annihilatorMap`: the map of annihilators induced by a diffeomorphism.
* `Diffeomorph.annihilatorLift`: the same map as a smooth diffeomorphism of annihilator bundles.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 and Appendix B (the annihilator line of a contact structure and the lift of
  contactomorphisms to the symplectization).
-/

public section

noncomputable section

open Bundle Function Manifold Module Set
open scoped Manifold ContDiff

open TauCeti TauCeti.CotangentBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {X : Type*} [TopologicalSpace X] [ChartedSpace H'' X]
  {D : Π x : M, Submodule 𝕜 (TangentSpace I x)} {D' : Π y : N, Submodule 𝕜 (TangentSpace J y)}
  {D'' : Π z : X, Submodule 𝕜 (TangentSpace K z)}

namespace Diffeomorph

/-! ### The map of annihilators -/

section Map

variable (P : Type*)

/-- If the differential of `h` carries `D` onto `D'`, then composing with the inverse differential
carries a covector annihilating `D` at `x` to a covector annihilating `D'` at `h x`. -/
theorem comp_mfderiv_symm_mem_annihilatorSpace (h : M ≃ₘ⟮I, J⟯ N)
    (hDD' : ∀ x v, v ∈ D x ↔ mfderiv I J h x v ∈ D' (h x)) {x : M}
    {p : TangentSpace I x →L[𝕜] 𝕜} (hp : p ∈ annihilatorSpace I D x) :
    p ∘L mfderiv J I h.symm (h x) ∈ annihilatorSpace J D' (h x) := by
  rw [mem_annihilatorSpace_iff] at hp ⊢
  intro w hw
  refine hp _ ((hDD' x _).2 ?_)
  -- Rewrite `w` as `dh (dh⁻¹ w)` in the hypothesis rather than in the goal, whose subterms are
  -- typed through the base point `h⁻¹ (h x)`.
  rw [← h.mfderiv_apply_mfderiv_symm_apply (by simp) x w] at hw
  exact hw

/-- The **lift of a diffeomorphism to annihilators.** If the differential of `h` carries `D` onto
`D'`, the covector `p` annihilating `D` at `x` goes to the covector `p ∘ (dh_x)⁻¹` annihilating `D'`
at `h x`, the inverse differential being the differential of `h.symm` at `h x`. This is the
restriction of the cotangent lift of `h`
(`Diffeomorph.annihilatorInclusion_annihilatorMap`). The model-fibre parameter `P` of
`Bundle.TotalSpace` plays no role. -/
def annihilatorMap (h : M ≃ₘ⟮I, J⟯ N) (hDD' : ∀ x v, v ∈ D x ↔ mfderiv I J h x v ∈ D' (h x))
    (z : TotalSpace P fun x ↦ annihilatorSpace I D x) :
    TotalSpace P fun y ↦ annihilatorSpace J D' y :=
  TotalSpace.mk' P (h z.proj)
    ⟨(z.snd : TangentSpace I z.proj →L[𝕜] 𝕜) ∘L mfderiv J I h.symm (h z.proj),
      h.comp_mfderiv_symm_mem_annihilatorSpace hDD' z.snd.property⟩

variable (h : M ≃ₘ⟮I, J⟯ N) (hDD' : ∀ x v, v ∈ D x ↔ mfderiv I J h x v ∈ D' (h x))

/-- The lift of `h` to annihilators covers `h`. -/
@[simp]
theorem proj_annihilatorMap (z : TotalSpace P fun x ↦ annihilatorSpace I D x) :
    (h.annihilatorMap P hDD' z).proj = h z.proj :=
  (rfl)

/-- The lifted covector evaluates a tangent vector `w` at `h x` as the original covector evaluates
`(dh_x)⁻¹ w`. -/
theorem annihilatorMap_snd_apply (z : TotalSpace P fun x ↦ annihilatorSpace I D x)
    (w : TangentSpace J (h z.proj)) :
    ((h.annihilatorMap P hDD' z).snd : TangentSpace J (h.annihilatorMap P hDD' z).proj →L[𝕜] 𝕜) w =
      (z.snd : TangentSpace I z.proj →L[𝕜] 𝕜) (mfderiv J I h.symm (h z.proj) w) :=
  (rfl)

/-- **The lift to annihilators preserves the pairing of covectors with tangent vectors:** the
lifted covector evaluated on `dh_x v` is the original covector evaluated on `v`. -/
@[simp]
theorem annihilatorMap_snd_apply_mfderiv (z : TotalSpace P fun x ↦ annihilatorSpace I D x)
    (v : TangentSpace I z.proj) :
    ((h.annihilatorMap P hDD' z).snd : TangentSpace J (h.annihilatorMap P hDD' z).proj →L[𝕜] 𝕜)
        (mfderiv I J h z.proj v) = (z.snd : TangentSpace I z.proj →L[𝕜] 𝕜) v :=
  (h.annihilatorMap_snd_apply P hDD' z _).trans
    (congrArg _ (h.mfderiv_symm_apply_mfderiv_apply (by simp) z.proj v))

/-- Under the inclusions of the annihilators into the cotangent bundles, the lift of `h` to
annihilators is the cotangent lift of `h`. -/
theorem annihilatorInclusion_annihilatorMap [IsManifold I 2 M] [IsManifold J 2 N]
    (z : TotalSpace P fun x ↦ annihilatorSpace I D x) :
    annihilatorInclusion J D' P (h.annihilatorMap P hDD' z) =
      h.cotangent (annihilatorInclusion I D P z) := by
  rw [annihilatorInclusion_apply, annihilatorInclusion_apply, cotangent_apply]
  rfl

/-- The lifted covector is zero exactly when the original covector is zero. -/
@[simp]
theorem annihilatorMap_snd_eq_zero_iff {z : TotalSpace P fun x ↦ annihilatorSpace I D x} :
    (h.annihilatorMap P hDD' z).snd = 0 ↔ z.snd = 0 := by
  refine ⟨fun hz ↦ Subtype.ext (ContinuousLinearMap.ext fun v ↦ ?_), fun hz ↦ ?_⟩
  · rw [← h.annihilatorMap_snd_apply_mfderiv P hDD' z v, hz]
    rfl
  · refine Subtype.ext (ContinuousLinearMap.ext fun w ↦ ?_)
    rw [h.annihilatorMap_snd_apply P hDD' z w, hz]
    rfl

/-- The lift of `h` to annihilators sends the zero covector at `x` to the zero covector at
`h x`. -/
@[simp]
theorem annihilatorMap_zeroSection (x : M) :
    h.annihilatorMap P hDD' (zeroSection P (fun x ↦ annihilatorSpace I D x) x) =
      zeroSection P (fun y ↦ annihilatorSpace J D' y) (h x) :=
  totalSpace_annihilatorSpace_ext rfl fun _ ↦ rfl

/-- Lifting `h` and then `h⁻¹` to annihilators returns the original covector. -/
@[simp]
theorem symm_annihilatorMap_annihilatorMap (z : TotalSpace P fun x ↦ annihilatorSpace I D x) :
    h.symm.annihilatorMap P (h.mem_iff_mfderiv_symm_apply_mem (by simp) hDD')
      (h.annihilatorMap P hDD' z) = z := by
  refine totalSpace_annihilatorSpace_ext (h.symm_apply_apply z.proj) fun v ↦ ?_
  -- Both lifts in turn give `z` applied to `dh⁻¹ (d(h⁻¹)⁻¹ v)`, and `d(h⁻¹)⁻¹ = dh`.
  exact ((h.symm.annihilatorMap_snd_apply P _ _ v).trans
    (h.annihilatorMap_snd_apply P hDD' z _)).trans
      (congrArg _ (h.symm.mfderiv_apply_mfderiv_symm_apply (by simp) (h z.proj) v))

/-- Lifting `h⁻¹` and then `h` to annihilators returns the original covector. -/
@[simp]
theorem annihilatorMap_symm_annihilatorMap (w : TotalSpace P fun y ↦ annihilatorSpace J D' y) :
    h.annihilatorMap P hDD'
      (h.symm.annihilatorMap P (h.mem_iff_mfderiv_symm_apply_mem (by simp) hDD') w) = w :=
  -- `h.symm.symm` is `h` up to structure eta, so this is the previous law for `h.symm`.
  h.symm.symm_annihilatorMap_annihilatorMap P (h.mem_iff_mfderiv_symm_apply_mem (by simp) hDD') w

/-- The lift of `h` to annihilators is bijective. -/
theorem bijective_annihilatorMap : Bijective (h.annihilatorMap P hDD') :=
  ⟨LeftInverse.injective (h.symm_annihilatorMap_annihilatorMap P hDD'),
    RightInverse.surjective (h.annihilatorMap_symm_annihilatorMap P hDD')⟩

/-- The lift of the identity diffeomorphism to annihilators is the identity. -/
@[simp]
theorem annihilatorMap_refl
    (hDD : ∀ x v, v ∈ D x ↔ mfderiv I I (Diffeomorph.refl I M ∞) x v ∈ D x)
    (z : TotalSpace P fun x ↦ annihilatorSpace I D x) :
    (Diffeomorph.refl I M ∞).annihilatorMap P hDD z = z := by
  refine totalSpace_annihilatorSpace_ext rfl fun v ↦ ?_
  -- The inverse of the identity diffeomorphism is the identity map, with identity differential.
  exact ((Diffeomorph.refl I M ∞).annihilatorMap_snd_apply P hDD z v).trans
    (congrArg _ (DFunLike.congr_fun mfderiv_id v))

/-- The lift of a composite of diffeomorphisms to annihilators is the composite of their lifts. -/
theorem annihilatorMap_trans
    (g : N ≃ₘ⟮J, K⟯ X) (hD'D'' : ∀ y w, w ∈ D' y ↔ mfderiv J K g y w ∈ D'' (g y))
    (z : TotalSpace P fun x ↦ annihilatorSpace I D x) :
    (h.trans g).annihilatorMap P (h.mem_iff_mfderiv_trans_apply_mem g (by simp) hDD' hD'D'') z =
      g.annihilatorMap P hD'D'' (h.annihilatorMap P hDD' z) := by
  refine totalSpace_annihilatorSpace_ext rfl fun v ↦ ?_
  -- The differential of `(g ∘ h)⁻¹ = h⁻¹ ∘ g⁻¹` at `g (h x)` is the composite of differentials.
  have hcomp := mfderiv_comp_apply (g (h z.proj))
    (h.symm.mdifferentiable (by simp) (g.symm (g (h z.proj))))
    (g.symm.mdifferentiable (by simp) (g (h z.proj))) v
  rw [g.symm_apply_apply] at hcomp
  exact (((h.trans g).annihilatorMap_snd_apply P _ z v).trans (congrArg _ hcomp)).trans
    ((h.annihilatorMap_snd_apply P hDD' z _).symm.trans
      (g.annihilatorMap_snd_apply P hD'D'' _ v).symm)

end Map

/-! ### The lift as a diffeomorphism of annihilator bundles -/

section Lift

variable [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  [IsManifold I ∞ M] [IsManifold J ∞ N] {k k' r : ℕ}

/-- `C^(∞ + 1)` charts, needed by the annihilator bundle construction of
`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle` at smoothness `∞`. -/
local instance instIsManifoldAnnihilatorLiftSource : IsManifold I ((∞ : WithTop ℕ∞) + 1) M :=
  IsManifold.of_le (n := ∞) (by simp)

/-- `C^(∞ + 1)` charts on the target, as for the source. -/
local instance instIsManifoldAnnihilatorLiftTarget : IsManifold J ((∞ : WithTop ℕ∞) + 1) N :=
  IsManifold.of_le (n := ∞) (by simp)

/-- **The lift to annihilators is smooth.** For smooth distributions `D` and `D'` of corank `r`,
whose annihilators are smooth vector bundles of rank `r`, the lift of a diffeomorphism carrying `D`
onto `D'` is a smooth map of the total spaces. -/
theorem contMDiff_annihilatorMap (h : M ≃ₘ⟮I, J⟯ N)
    (hDD' : ∀ x v, v ∈ D x ↔ mfderiv I J h x v ∈ D' (h x))
    (hD : IsContMDiffDistribution I ∞ k D) (hD' : IsContMDiffDistribution J ∞ k' D')
    (hk : k + r = finrank 𝕜 E) (hk' : k' + r = finrank 𝕜 F) :
    letI := hD.annihilatorFiberBundle hk
    letI := hD'.annihilatorFiberBundle hk'
    ContMDiff (I.prod 𝓘(𝕜, Fin r → 𝕜)) (J.prod 𝓘(𝕜, Fin r → 𝕜)) ∞
      (h.annihilatorMap (Fin r → 𝕜) hDD') :=
  letI := hD.annihilatorFiberBundle hk
  letI := hD'.annihilatorFiberBundle hk'
  (hD'.isSmoothEmbedding_annihilatorInclusion hk').contMDiff_iff_comp.2 <| by
    rw [show annihilatorInclusion J D' (Fin r → 𝕜) ∘ h.annihilatorMap (Fin r → 𝕜) hDD' =
      h.cotangent ∘ annihilatorInclusion I D (Fin r → 𝕜) from
        funext (h.annihilatorInclusion_annihilatorMap _ hDD')]
    exact h.cotangent.contMDiff.comp (hD.contMDiff_annihilatorInclusion hk)

/-- The **lift of a diffeomorphism to annihilator bundles**, as a smooth diffeomorphism. For smooth
distributions `D` and `D'` of corank `r` and a diffeomorphism `h` whose differential carries `D`
onto `D'`, the map `(x, p) ↦ (h x, p ∘ (dh_x)⁻¹)` is a smooth diffeomorphism from the annihilator
bundle of `D` to that of `D'`, both with the manifold structure of
`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`. Its inverse is the lift of `h⁻¹`. -/
def annihilatorLift (h : M ≃ₘ⟮I, J⟯ N) (hDD' : ∀ x v, v ∈ D x ↔ mfderiv I J h x v ∈ D' (h x))
    (hD : IsContMDiffDistribution I ∞ k D) (hD' : IsContMDiffDistribution J ∞ k' D')
    (hk : k + r = finrank 𝕜 E) (hk' : k' + r = finrank 𝕜 F) :
    letI := hD.annihilatorFiberBundle hk
    letI := hD'.annihilatorFiberBundle hk'
    (TotalSpace (Fin r → 𝕜) fun x ↦ annihilatorSpace I D x) ≃ₘ⟮I.prod 𝓘(𝕜, Fin r → 𝕜),
      J.prod 𝓘(𝕜, Fin r → 𝕜)⟯ TotalSpace (Fin r → 𝕜) fun y ↦ annihilatorSpace J D' y :=
  letI := hD.annihilatorFiberBundle hk
  letI := hD'.annihilatorFiberBundle hk'
  { toFun := h.annihilatorMap (Fin r → 𝕜) hDD'
    invFun := h.symm.annihilatorMap (Fin r → 𝕜) (h.mem_iff_mfderiv_symm_apply_mem (by simp) hDD')
    left_inv := h.symm_annihilatorMap_annihilatorMap (Fin r → 𝕜) hDD'
    right_inv := h.annihilatorMap_symm_annihilatorMap (Fin r → 𝕜) hDD'
    contMDiff_toFun := h.contMDiff_annihilatorMap hDD' hD hD' hk hk'
    contMDiff_invFun :=
      h.symm.contMDiff_annihilatorMap (h.mem_iff_mfderiv_symm_apply_mem (by simp) hDD') hD' hD
        hk' hk }

variable (h : M ≃ₘ⟮I, J⟯ N) (hDD' : ∀ x v, v ∈ D x ↔ mfderiv I J h x v ∈ D' (h x))
  (hD : IsContMDiffDistribution I ∞ k D) (hD' : IsContMDiffDistribution J ∞ k' D')
  (hk : k + r = finrank 𝕜 E) (hk' : k' + r = finrank 𝕜 F)

/-- The diffeomorphism `Diffeomorph.annihilatorLift` is the map `Diffeomorph.annihilatorMap`. -/
@[simp]
theorem coe_annihilatorLift :
    letI := hD.annihilatorFiberBundle hk
    letI := hD'.annihilatorFiberBundle hk'
    ⇑(h.annihilatorLift hDD' hD hD' hk hk') = h.annihilatorMap (Fin r → 𝕜) hDD' :=
  (rfl)

/-- The inverse of the lift of `h` to annihilator bundles is the lift of `h⁻¹`. -/
@[simp]
theorem annihilatorLift_symm :
    letI := hD.annihilatorFiberBundle hk
    letI := hD'.annihilatorFiberBundle hk'
    (h.annihilatorLift hDD' hD hD' hk hk').symm =
      h.symm.annihilatorLift (h.mem_iff_mfderiv_symm_apply_mem (by simp) hDD') hD' hD hk' hk :=
  letI := hD.annihilatorFiberBundle hk
  letI := hD'.annihilatorFiberBundle hk'
  Diffeomorph.ext fun _ ↦ rfl

end Lift

end Diffeomorph
