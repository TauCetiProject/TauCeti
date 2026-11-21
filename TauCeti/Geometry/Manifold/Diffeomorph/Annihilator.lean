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
# Annihilator lifts of diffeomorphisms

Let `h : M → N` be a smooth diffeomorphism carrying a distribution `D` on `M` onto a distribution
`D'` on `N`: a tangent vector `v` at `x` lies in `D x` exactly when `dh_x v` lies in `D' (h x)`.
Its cotangent lift `T*h : (x, p) ↦ (h x, p ∘ (dh_x)⁻¹)` (`Diffeomorph.cotangent`) then carries the
annihilator `D⁰_x` of `D` onto the annihilator `D'⁰_(h x)` of `D'`
(`Diffeomorph.cotangent_snd_mem_annihilatorSpace_iff`). For smooth distributions the annihilators
form smooth vector subbundles of the cotangent bundles
(`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`), and the restriction of `T*h` is a
smooth diffeomorphism between them, the **annihilator lift** of `h`
(`Diffeomorph.annihilatorDiffeomorph`). It is characterized by restricting the cotangent lift
(`Diffeomorph.annihilatorInclusion_annihilatorDiffeomorph`): it covers `h`, preserves the pairing
of covectors with tangent vectors, and is linear on fibres
(`Diffeomorph.annihilatorDiffeomorph_mk_smul`). Annihilator lifts preserve identity maps, inverses
and composition.

Smoothness of the restriction is inherited from the cotangent lift because the annihilator bundle
of `D'` is smoothly embedded in `T*N`
(`TauCeti.IsContMDiffDistribution.isSmoothEmbedding_annihilatorInclusion`).

For a contact structure `ξ` the annihilator `ξ⁰` is the dual of the contact line, and the
complement of its zero section is the symplectization of `ξ`. A contactomorphism lifts to the
symplectization through this construction, whether or not it preserves a coorientation.

## Main definitions

* `Diffeomorph.annihilatorDiffeomorph`: the smooth diffeomorphism `D⁰ ≃ D'⁰` induced by a
  diffeomorphism carrying `D` onto `D'`.

## Main results

* `Diffeomorph.cotangent_snd_mem_annihilatorSpace_iff`: the cotangent lift of `h` carries
  annihilating covectors of `D` exactly to annihilating covectors of `D'`.
* `Diffeomorph.annihilatorInclusion_annihilatorDiffeomorph`: the annihilator lift is the
  restriction of the cotangent lift.
* `Diffeomorph.annihilatorDiffeomorph_symm`, `Diffeomorph.annihilatorDiffeomorph_refl`,
  `Diffeomorph.annihilatorDiffeomorph_trans`: functoriality.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 and Appendix B (lifts of contactomorphisms to the symplectization).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer, 1989,
  Appendix 4.
-/

public section

noncomputable section

open Bundle Module
open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {D : Π x : M, Submodule 𝕜 (TangentSpace I x)}
  {D' : Π y : N, Submodule 𝕜 (TangentSpace J y)}
  {D'' : Π w : P, Submodule 𝕜 (TangentSpace K w)}

namespace Diffeomorph

open TauCeti TauCeti.CotangentBundle

/-! ### Annihilating covectors under cotangent lifts -/

section Pointwise

variable [IsManifold I 2 M] [IsManifold J 2 N]

/-- **Cotangent lifts preserve annihilators.** If `h` carries `D` onto `D'`, then its cotangent
lift sends a covector into the annihilator of `D'` exactly when the covector lies in the
annihilator of `D`. -/
theorem cotangent_snd_mem_annihilatorSpace_iff (h : M ≃ₘ⟮I, J⟯ N)
    (hh : ∀ x (v : TangentSpace I x), mfderiv I J h x v ∈ D' (h x) ↔ v ∈ D x)
    {z : CotangentBundle I M} :
    (h.cotangent z).snd ∈ annihilatorSpace J D' (h z.proj) ↔
      z.snd ∈ annihilatorSpace I D z.proj := by
  refine ⟨fun hz ↦ mem_annihilatorSpace_iff.2 fun v hv ↦ ?_,
    fun hz ↦ mem_annihilatorSpace_iff.2 fun w hw ↦ ?_⟩
  · exact (cotangent_snd_apply_mfderiv h z v).symm.trans
      (mem_annihilatorSpace_iff.1 hz _ ((hh _ v).2 hv))
  · refine (cotangent_snd_apply h z w).trans (mem_annihilatorSpace_iff.1 hz _ ?_)
    rwa [← mfderiv_symm_mem_iff h hh, h.symm_apply_apply] at hw

variable (R : Type*)

/-- The underlying map of the annihilator lift: the restriction of the cotangent lift of `h` to the
annihilating covectors of `D`. The model-fibre parameter `R` of `Bundle.TotalSpace` plays no
role. -/
private def annihilatorMap (h : M ≃ₘ⟮I, J⟯ N)
    (hh : ∀ x (v : TangentSpace I x), mfderiv I J h x v ∈ D' (h x) ↔ v ∈ D x)
    (z : TotalSpace R fun x ↦ annihilatorSpace I D x) :
    TotalSpace R fun y ↦ annihilatorSpace J D' y :=
  ⟨h z.proj, ⟨(h.cotangent (TotalSpace.mk' (E →L[𝕜] 𝕜) z.proj z.snd)).snd,
    (cotangent_snd_mem_annihilatorSpace_iff h hh
      (z := TotalSpace.mk' (E →L[𝕜] 𝕜) z.proj z.snd)).2 z.snd.property⟩⟩

private theorem annihilatorInclusion_annihilatorMap (h : M ≃ₘ⟮I, J⟯ N)
    (hh : ∀ x (v : TangentSpace I x), mfderiv I J h x v ∈ D' (h x) ↔ v ∈ D x)
    (z : TotalSpace R fun x ↦ annihilatorSpace I D x) :
    annihilatorInclusion J D' R (annihilatorMap R h hh z) =
      h.cotangent (annihilatorInclusion I D R z) := by
  rw [annihilatorInclusion_apply, annihilatorInclusion_apply]
  exact CotangentBundle.ext (proj_cotangent h (TotalSpace.mk' (E →L[𝕜] 𝕜) z.proj z.snd)).symm
    fun _ ↦ rfl

end Pointwise

/-! ### The annihilator lift -/

variable [IsRCLikeNormedField 𝕜] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  [FiniteDimensional 𝕜 G] [IsManifold I ∞ M] [IsManifold J ∞ N] [IsManifold K ∞ P] {k k' k'' r : ℕ}

/-- `C^(∞ + 1)` charts, needed by the annihilator bundle construction at smoothness `∞`. -/
local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)

/-- `C^(∞ + 1)` charts, needed by the annihilator bundle construction at smoothness `∞`. -/
local instance : IsManifold J ((∞ : WithTop ℕ∞) + 1) N := IsManifold.of_le (n := ∞) (by simp)

/-- `C^(∞ + 1)` charts, needed by the annihilator bundle construction at smoothness `∞`. -/
local instance : IsManifold K ((∞ : WithTop ℕ∞) + 1) P := IsManifold.of_le (n := ∞) (by simp)

/-- The **annihilator lift** of a smooth diffeomorphism `h : M → N` carrying a smooth distribution
`D` onto a smooth distribution `D'`: the smooth diffeomorphism between the annihilator bundles
`D⁰ ⊆ T*M` and `D'⁰ ⊆ T*N` sending an annihilating covector `p` at `x` to `p ∘ (dh_x)⁻¹` at
`h x`. It is the restriction of the cotangent lift of `h`
(`Diffeomorph.annihilatorInclusion_annihilatorDiffeomorph`), and its inverse is the annihilator
lift of `h.symm` (`Diffeomorph.annihilatorDiffeomorph_symm`). -/
def annihilatorDiffeomorph (h : M ≃ₘ⟮I, J⟯ N) (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + r = finrank 𝕜 E) (hD' : IsContMDiffDistribution J ∞ k' D')
    (hk' : k' + r = finrank 𝕜 F)
    (hh : ∀ x (v : TangentSpace I x), mfderiv I J h x v ∈ D' (h x) ↔ v ∈ D x) :
    letI := hD.annihilatorFiberBundle hk
    letI := hD'.annihilatorFiberBundle hk'
    (TotalSpace (Fin r → 𝕜) fun x ↦ annihilatorSpace I D x) ≃ₘ⟮I.prod 𝓘(𝕜, Fin r → 𝕜),
      J.prod 𝓘(𝕜, Fin r → 𝕜)⟯ TotalSpace (Fin r → 𝕜) fun y ↦ annihilatorSpace J D' y :=
  letI := hD.annihilatorFiberBundle hk
  letI := hD'.annihilatorFiberBundle hk'
  { toFun := annihilatorMap _ h hh
    invFun := annihilatorMap _ h.symm (mfderiv_symm_mem_iff h hh)
    left_inv z := annihilatorInclusion_injective I D _ <| by
      rw [annihilatorInclusion_annihilatorMap, annihilatorInclusion_annihilatorMap,
        ← cotangent_symm, symm_apply_apply]
    right_inv z := annihilatorInclusion_injective J D' _ <| by
      rw [annihilatorInclusion_annihilatorMap, annihilatorInclusion_annihilatorMap,
        ← cotangent_symm, apply_symm_apply]
    contMDiff_toFun := (hD'.isSmoothEmbedding_annihilatorInclusion hk').contMDiff_iff_comp.2 <|
      (h.cotangent.contMDiff.comp (hD.contMDiff_annihilatorInclusion hk)).congr
        fun z ↦ annihilatorInclusion_annihilatorMap _ h hh z
    contMDiff_invFun := (hD.isSmoothEmbedding_annihilatorInclusion hk).contMDiff_iff_comp.2 <|
      (h.symm.cotangent.contMDiff.comp (hD'.contMDiff_annihilatorInclusion hk')).congr
        fun z ↦ annihilatorInclusion_annihilatorMap _ h.symm (mfderiv_symm_mem_iff h hh) z }

section Lift

variable (h : M ≃ₘ⟮I, J⟯ N) (hD : IsContMDiffDistribution I ∞ k D)
  (hk : k + r = finrank 𝕜 E) (hD' : IsContMDiffDistribution J ∞ k' D')
  (hk' : k' + r = finrank 𝕜 F)
  (hh : ∀ x (v : TangentSpace I x), mfderiv I J h x v ∈ D' (h x) ↔ v ∈ D x)

/-- **The annihilator lift restricts the cotangent lift**: followed by the inclusion of `D'⁰` into
`T*N`, the annihilator lift of `h` is the cotangent lift of `h` on the inclusion of `D⁰` into
`T*M`. -/
@[simp]
theorem annihilatorInclusion_annihilatorDiffeomorph
    (z : TotalSpace (Fin r → 𝕜) fun x ↦ annihilatorSpace I D x) :
    annihilatorInclusion J D' (Fin r → 𝕜) (h.annihilatorDiffeomorph hD hk hD' hk' hh z) =
      h.cotangent (annihilatorInclusion I D (Fin r → 𝕜) z) :=
  annihilatorInclusion_annihilatorMap _ h hh z

/-- The annihilator lift of `h` covers `h`. -/
@[simp]
theorem proj_annihilatorDiffeomorph (z : TotalSpace (Fin r → 𝕜) fun x ↦ annihilatorSpace I D x) :
    (h.annihilatorDiffeomorph hD hk hD' hk' hh z).proj = h z.proj :=
  (rfl)

/-- The lifted covector evaluates a tangent vector `w` at `h x` as the original covector evaluates
`(dh_x)⁻¹ w`. -/
theorem annihilatorDiffeomorph_snd_apply
    (z : TotalSpace (Fin r → 𝕜) fun x ↦ annihilatorSpace I D x) (w : TangentSpace J (h z.proj)) :
    ((h.annihilatorDiffeomorph hD hk hD' hk' hh z).snd :
        TangentSpace J (h.annihilatorDiffeomorph hD hk hD' hk' hh z).proj →L[𝕜] 𝕜) w =
      (z.snd : TangentSpace I z.proj →L[𝕜] 𝕜) (mfderiv J I h.symm (h z.proj) w) :=
  cotangent_snd_apply h (TotalSpace.mk' (E →L[𝕜] 𝕜) z.proj z.snd) w

/-- **The annihilator lift preserves the pairing of covectors with tangent vectors:** the lifted
covector evaluated on `dh_x v` is the original covector evaluated on `v`. -/
@[simp]
theorem annihilatorDiffeomorph_snd_apply_mfderiv
    (z : TotalSpace (Fin r → 𝕜) fun x ↦ annihilatorSpace I D x) (v : TangentSpace I z.proj) :
    ((h.annihilatorDiffeomorph hD hk hD' hk' hh z).snd :
        TangentSpace J (h.annihilatorDiffeomorph hD hk hD' hk' hh z).proj →L[𝕜] 𝕜)
        (mfderiv I J h z.proj v) =
      (z.snd : TangentSpace I z.proj →L[𝕜] 𝕜) v :=
  cotangent_snd_apply_mfderiv h (TotalSpace.mk' (E →L[𝕜] 𝕜) z.proj z.snd) v

/-- **Annihilator lifts are linear on fibres:** rescaling a covector before lifting it rescales the
lifted covector by the same scalar. -/
theorem annihilatorDiffeomorph_mk_smul
    (z : TotalSpace (Fin r → 𝕜) fun x ↦ annihilatorSpace I D x) (c : 𝕜) :
    h.annihilatorDiffeomorph hD hk hD' hk' hh (TotalSpace.mk' (Fin r → 𝕜) z.proj (c • z.snd)) =
      TotalSpace.mk' (Fin r → 𝕜) (h.annihilatorDiffeomorph hD hk hD' hk' hh z).proj
        (c • (h.annihilatorDiffeomorph hD hk hD' hk' hh z).snd) :=
  annihilatorInclusion_injective J D' _ <| by
    rw [annihilatorInclusion_annihilatorDiffeomorph, annihilatorInclusion_mk',
      annihilatorInclusion_mk', Submodule.coe_smul, Submodule.coe_smul]
    exact (cotangent_mk_smul h (TotalSpace.mk' (E →L[𝕜] 𝕜) z.proj z.snd) c).trans
      (CotangentBundle.ext (proj_cotangent h _) fun _ ↦ rfl)

/-- The annihilator lift sends a covector to zero exactly when the covector is zero. -/
@[simp]
theorem annihilatorDiffeomorph_snd_eq_zero_iff
    {z : TotalSpace (Fin r → 𝕜) fun x ↦ annihilatorSpace I D x} :
    (h.annihilatorDiffeomorph hD hk hD' hk' hh z).snd = 0 ↔ z.snd = 0 := by
  rw [← Submodule.coe_eq_zero, ← Submodule.coe_eq_zero (x := z.snd)]
  exact cotangent_snd_eq_zero_iff h (z := TotalSpace.mk' (E →L[𝕜] 𝕜) z.proj z.snd)

/-- The annihilator lift of `h` sends the zero covector at `x` to the zero covector at `h x`. -/
@[simp]
theorem annihilatorDiffeomorph_zeroSection (x : M) :
    h.annihilatorDiffeomorph hD hk hD' hk' hh
        (zeroSection (Fin r → 𝕜) (fun x ↦ annihilatorSpace I D x) x) =
      zeroSection (Fin r → 𝕜) (fun y ↦ annihilatorSpace J D' y) (h x) :=
  annihilatorInclusion_injective J D' _ <| by
    rw [annihilatorInclusion_annihilatorDiffeomorph, annihilatorInclusion_zeroSection,
      annihilatorInclusion_zeroSection, cotangent_zeroSection]

/-- The inverse of an annihilator lift is the annihilator lift of the inverse diffeomorphism. -/
@[simp]
theorem annihilatorDiffeomorph_symm :
    letI := hD.annihilatorFiberBundle hk
    letI := hD'.annihilatorFiberBundle hk'
    (h.annihilatorDiffeomorph hD hk hD' hk' hh).symm =
      h.symm.annihilatorDiffeomorph hD' hk' hD hk (mfderiv_symm_mem_iff h hh) :=
  letI := hD.annihilatorFiberBundle hk
  letI := hD'.annihilatorFiberBundle hk'
  Diffeomorph.ext fun _ ↦ rfl

end Lift

/-- The annihilator lift of the identity diffeomorphism is the identity diffeomorphism of the
annihilator bundle. -/
@[simp]
theorem annihilatorDiffeomorph_refl (hD : IsContMDiffDistribution I ∞ k D)
    (hk : k + r = finrank 𝕜 E) :
    letI := hD.annihilatorFiberBundle hk
    (Diffeomorph.refl I M ∞).annihilatorDiffeomorph hD hk hD hk
        (fun _ _ ↦ by rw [coe_refl, mfderiv_id]; rfl) =
      Diffeomorph.refl (I.prod 𝓘(𝕜, Fin r → 𝕜)) _ ∞ :=
  letI := hD.annihilatorFiberBundle hk
  Diffeomorph.ext fun z ↦ annihilatorInclusion_injective I D _ <| by
    rw [annihilatorInclusion_annihilatorDiffeomorph, cotangent_refl]
    rfl

/-- **Annihilator lifts commute with composition** of smooth diffeomorphisms. -/
-- Not `@[simp]`: the intermediate distribution `D'`, its rank and smoothness, and `hh`, `hg`
-- occur only on the right-hand side, so `simp` could not instantiate them.
theorem annihilatorDiffeomorph_trans (h : M ≃ₘ⟮I, J⟯ N) (g : N ≃ₘ⟮J, K⟯ P)
    (hD : IsContMDiffDistribution I ∞ k D) (hk : k + r = finrank 𝕜 E)
    (hD' : IsContMDiffDistribution J ∞ k' D') (hk' : k' + r = finrank 𝕜 F)
    (hD'' : IsContMDiffDistribution K ∞ k'' D'') (hk'' : k'' + r = finrank 𝕜 G)
    (hh : ∀ x (v : TangentSpace I x), mfderiv I J h x v ∈ D' (h x) ↔ v ∈ D x)
    (hg : ∀ y (w : TangentSpace J y), mfderiv J K g y w ∈ D'' (g y) ↔ w ∈ D' y) :
    letI := hD.annihilatorFiberBundle hk
    letI := hD'.annihilatorFiberBundle hk'
    letI := hD''.annihilatorFiberBundle hk''
    (h.trans g).annihilatorDiffeomorph hD hk hD'' hk'' (mfderiv_trans_mem_iff h g hh hg) =
      (h.annihilatorDiffeomorph hD hk hD' hk' hh).trans
        (g.annihilatorDiffeomorph hD' hk' hD'' hk'' hg) :=
  letI := hD.annihilatorFiberBundle hk
  letI := hD'.annihilatorFiberBundle hk'
  letI := hD''.annihilatorFiberBundle hk''
  Diffeomorph.ext fun z ↦ annihilatorInclusion_injective K D'' _ <| by
    rw [annihilatorInclusion_annihilatorDiffeomorph, cotangent_trans, coe_trans, coe_trans,
      Function.comp_apply, Function.comp_apply, annihilatorInclusion_annihilatorDiffeomorph,
      annihilatorInclusion_annihilatorDiffeomorph]

end Diffeomorph
