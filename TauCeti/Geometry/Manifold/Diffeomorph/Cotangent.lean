/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent

/-!
# Cotangent lifts of diffeomorphisms

A diffeomorphism `h : M → N` lifts to a diffeomorphism of cotangent bundles,

`T*M → T*N, (x, p) ↦ (h x, p ∘ (dh_x)⁻¹)`,

where the inverse of the differential `dh_x` is the differential of `h⁻¹` at `h x`
(`Diffeomorph.cotangent`). It is characterized by covering `h`
(`Diffeomorph.proj_cotangent`) and by preserving the pairing of covectors with tangent vectors:
the lifted covector, evaluated on `dh_x v`, is `p v` (`Diffeomorph.cotangent_snd_apply_mfderiv`).
Smoothness of the lift is the smoothness of pulling covectors back along a map,
`TauCeti.CotangentBundle.contMDiff_mk_comp_mfderiv`.

The construction is functorial: cotangent lifts preserve identity maps, inverses and composition
(`Diffeomorph.cotangent_refl`, `Diffeomorph.cotangent_symm`, `Diffeomorph.cotangent_trans`).
It is the cotangent counterpart of the tangent lift `Diffeomorph.tangent`. The cotangent lift of
a diffeomorphism preserves the Liouville form and the canonical symplectic form of the cotangent
bundle; see `TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift`.

By functoriality, a group `G` acting on `M` by smooth maps (`ContMDiffConstSMul I ∞ G M`) acts on
`T*M` by the cotangent lifts of these maps,

`g • (x, p) = (g • x, p ∘ (dg_x)⁻¹)`

(`TauCeti.CotangentBundle.instMulAction`), again by smooth maps
(`TauCeti.CotangentBundle.instContMDiffConstSMul`). This **cotangent-lifted action** covers the
action on `M` (`TauCeti.CotangentBundle.proj_smul`), preserves the pairing of covectors with
tangent vectors (`TauCeti.CotangentBundle.smul_snd_apply_mfderiv`) and the zero section, and the
cotangent lift of each `x ↦ g • x` is the action of `g` on `T*M`
(`Diffeomorph.cotangent_constSmul`). Cotangent lifts are equivariant for these actions: the
cotangent lift of a diffeomorphism intertwines the lifted actions exactly when the diffeomorphism
intertwines the actions on the base (`Diffeomorph.cotangent_smul`,
`Diffeomorph.forall_cotangent_smul_iff`).

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 2 and 22.
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Section 12.1 (cotangent lifts of group actions).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 11.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

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

namespace Diffeomorph

open TauCeti

/-- The underlying map of the cotangent lift: a covector `p` at `x` goes to the covector
`p ∘ (dh_x)⁻¹` at `h x`, the inverse differential being the differential of `h.symm` at `h x`. -/
private def cotangentMap (h : M ≃ₘ⟮I, J⟯ N) (z : CotangentBundle I M) : CotangentBundle J N :=
  TotalSpace.mk' (F →L[𝕜] 𝕜) (h z.proj) (z.2 ∘L mfderiv J I h.symm (h z.proj))

/-- The covector `cotangentMap h z` evaluates a tangent vector `w` at `h x` as `z` evaluates
`dh⁻¹ w`. -/
private theorem cotangentMap_snd_apply (h : M ≃ₘ⟮I, J⟯ N) (z : CotangentBundle I M)
    (w : TangentSpace J (h z.proj)) :
    (h.cotangentMap z).2 w = z.2 (mfderiv J I h.symm (h z.proj) w) :=
  (rfl)

/-- Applying the cotangent lift of `h` and then that of `h.symm` returns the original covector. -/
private theorem cotangentMap_symm_cotangentMap (h : M ≃ₘ⟮I, J⟯ N) (z : CotangentBundle I M) :
    h.symm.cotangentMap (h.cotangentMap z) = z := by
  refine CotangentBundle.ext (h.symm_apply_apply z.proj) fun v ↦ ?_
  -- Evaluating both lifts in turn gives `z` applied to `dh⁻¹ (d(h⁻¹)⁻¹ v)`, and `d(h⁻¹)⁻¹ = dh`.
  have hv := h.symm.mfderiv_apply_mfderiv_symm_apply (by simp) (h z.proj) v
  exact ((cotangentMap_snd_apply _ _ v).trans (cotangentMap_snd_apply h z _)).trans
    (congrArg z.2 hv)

variable [IsManifold I 2 M] [IsManifold J 2 N] [IsManifold K 2 P]

/-- The underlying map of the cotangent lift of `h` is smooth. -/
private theorem contMDiff_cotangentMap (h : M ≃ₘ⟮I, J⟯ N) :
    ContMDiff (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (J.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) ∞ h.cotangentMap :=
  CotangentBundle.contMDiff_mk_comp_mfderiv (Ψ := fun z : CotangentBundle I M ↦ z)
    (fun z ↦ (h.symm_apply_apply z.proj).symm) contMDiff_id
    (h.contMDiff.comp (contMDiff_proj _)) h.symm.contMDiff (by simp)

/-- The **cotangent lift** of a smooth diffeomorphism `h : M → N`: the smooth diffeomorphism
`T*M → T*N` sending a covector `p` at `x` to the covector `p ∘ (dh_x)⁻¹` at `h x`. Its inverse is
the cotangent lift of `h.symm`. -/
protected def cotangent (h : M ≃ₘ⟮I, J⟯ N) :
    CotangentBundle I M ≃ₘ⟮I.prod 𝓘(𝕜, E →L[𝕜] 𝕜), J.prod 𝓘(𝕜, F →L[𝕜] 𝕜)⟯
      CotangentBundle J N where
  toFun := h.cotangentMap
  invFun := h.symm.cotangentMap
  left_inv := h.cotangentMap_symm_cotangentMap
  -- `h.symm.symm` is `h` up to structure eta, so this is the left inverse law for `h.symm`.
  right_inv := h.symm.cotangentMap_symm_cotangentMap
  contMDiff_toFun := h.contMDiff_cotangentMap
  contMDiff_invFun := h.symm.contMDiff_cotangentMap

/-- The cotangent lift sends a covector `p` at `x` to `p ∘ (dh_x)⁻¹` at `h x`, where
`(dh_x)⁻¹` is the differential of `h.symm` at `h x`. -/
theorem cotangent_apply (h : M ≃ₘ⟮I, J⟯ N) (z : CotangentBundle I M) :
    h.cotangent z =
      TotalSpace.mk' (F →L[𝕜] 𝕜) (h z.proj) (z.2 ∘L mfderiv J I h.symm (h z.proj)) :=
  (rfl)

/-- The cotangent lift of `h` covers `h`. -/
@[simp]
theorem proj_cotangent (h : M ≃ₘ⟮I, J⟯ N) (z : CotangentBundle I M) :
    (h.cotangent z).proj = h z.proj :=
  (rfl)

/-- The lifted covector evaluates a tangent vector `w` at `h x` as the original covector
evaluates `(dh_x)⁻¹ w`. -/
theorem cotangent_snd_apply (h : M ≃ₘ⟮I, J⟯ N) (z : CotangentBundle I M)
    (w : TangentSpace J (h z.proj)) :
    (h.cotangent z).2 w = z.2 (mfderiv J I h.symm (h z.proj) w) :=
  (rfl)

/-- **The cotangent lift preserves the pairing of covectors with tangent vectors:** the lifted
covector evaluated on `dh_x v` is the original covector evaluated on `v`. -/
@[simp]
theorem cotangent_snd_apply_mfderiv (h : M ≃ₘ⟮I, J⟯ N) (z : CotangentBundle I M)
    (v : TangentSpace I z.proj) :
    (h.cotangent z).2 (mfderiv I J h z.proj v) = z.2 v :=
  (cotangent_snd_apply h z _).trans
    (congrArg z.2 (h.mfderiv_symm_apply_mfderiv_apply (by simp) z.proj v))

/-- The inverse of a cotangent lift is the cotangent lift of the inverse diffeomorphism. -/
@[simp]
theorem cotangent_symm (h : M ≃ₘ⟮I, J⟯ N) :
    h.cotangent.symm = h.symm.cotangent :=
  Diffeomorph.ext fun _ ↦ rfl

/-- The cotangent lift of the identity diffeomorphism is the identity diffeomorphism of the
cotangent bundle. -/
@[simp]
theorem cotangent_refl :
    (Diffeomorph.refl I M ∞).cotangent =
      Diffeomorph.refl (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (CotangentBundle I M) ∞ := by
  refine Diffeomorph.ext fun z ↦ CotangentBundle.ext rfl fun v ↦ ?_
  -- The inverse of the identity diffeomorphism is the identity map, with identity differential.
  exact (cotangent_snd_apply _ z v).trans (congrArg z.2 (DFunLike.congr_fun mfderiv_id v))

/-- Cotangent lift commutes with composition of smooth diffeomorphisms. -/
@[simp]
theorem cotangent_trans (h : M ≃ₘ⟮I, J⟯ N) (g : N ≃ₘ⟮J, K⟯ P) :
    (h.trans g).cotangent = h.cotangent.trans g.cotangent := by
  refine Diffeomorph.ext fun z ↦ CotangentBundle.ext rfl fun v ↦ ?_
  -- The differential of `(g ∘ h)⁻¹ = h⁻¹ ∘ g⁻¹` at `g (h x)` is the composite of differentials.
  have hcomp := mfderiv_comp_apply (g (h z.proj))
    (h.symm.mdifferentiable (by simp) (g.symm (g (h z.proj))))
    (g.symm.mdifferentiable (by simp) (g (h z.proj))) v
  rw [g.symm_apply_apply] at hcomp
  exact ((cotangent_snd_apply _ z v).trans (congrArg z.2 hcomp)).trans
    ((cotangent_snd_apply h z _).symm.trans (cotangent_snd_apply g _ v).symm)

end Diffeomorph

namespace TauCeti.CotangentBundle

variable {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I ∞ G M] [IsManifold I 2 M]

/-- The **cotangent lift of a smooth group action**: an element `g` acts on `T*M` by the cotangent
lift of the diffeomorphism `x ↦ g • x`, sending a covector `p` at `x` to the covector
`p ∘ (dg_x)⁻¹` at `g • x` (`TauCeti.CotangentBundle.smul_eq_mk`). -/
instance instSMul : SMul G (CotangentBundle I M) where
  smul g := (Diffeomorph.constSmul I ∞ g).cotangent

/-- The cotangent-lifted action of `g` is the cotangent lift of the diffeomorphism `x ↦ g • x`. -/
theorem smul_def (g : G) (z : CotangentBundle I M) :
    g • z = (Diffeomorph.constSmul I ∞ g).cotangent z :=
  (rfl)

/-- The cotangent-lifted action sends a covector `p` at `x` to the covector `p ∘ (dg_x)⁻¹` at
`g • x`, where `(dg_x)⁻¹` is the differential of `x ↦ g⁻¹ • x` at `g • x`. -/
theorem smul_eq_mk (g : G) (z : CotangentBundle I M) :
    g • z = TotalSpace.mk' (E →L[𝕜] 𝕜) (g • z.proj)
      (z.2 ∘L mfderiv I I (fun x : M ↦ g⁻¹ • x) (g • z.proj)) := by
  rw [smul_def, Diffeomorph.cotangent_apply, Diffeomorph.coe_constSmul_symm,
    Diffeomorph.coe_constSmul]

/-- The cotangent-lifted action covers the action on the base. -/
@[simp]
theorem proj_smul (g : G) (z : CotangentBundle I M) : (g • z).proj = g • z.proj := by
  rw [smul_eq_mk]

/-- The covector `g • p` evaluates a tangent vector `w` at `g • x` as `p` evaluates
`(dg_x)⁻¹ w`, the differential of `x ↦ g⁻¹ • x` at `g • x` applied to `w`. -/
theorem smul_snd_apply (g : G) (z : CotangentBundle I M) (w : TangentSpace I (g • z.proj)) :
    (g • z).2 w = z.2 (mfderiv I I (fun x : M ↦ g⁻¹ • x) (g • z.proj) w) := by
  rw [smul_eq_mk]
  -- The second component of `TotalSpace.mk'` is the displayed composite.
  rfl

/-- **The cotangent-lifted action preserves the pairing of covectors with tangent vectors:** the
covector `g • p` evaluated on `dg_x v` is `p v`. -/
@[simp]
theorem smul_snd_apply_mfderiv (g : G) (z : CotangentBundle I M) (v : TangentSpace I z.proj) :
    (g • z).2 (mfderiv I I (fun x : M ↦ g • x) z.proj v) = z.2 v := by
  rw [← Diffeomorph.coe_constSmul g (I := I) (n := ∞), smul_def]
  exact (Diffeomorph.constSmul I ∞ g).cotangent_snd_apply_mfderiv z v

/-- The cotangent-lifted action preserves the zero section. -/
@[simp]
theorem smul_zeroSection (g : G) (x : M) :
    g • zeroSection (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) x =
      zeroSection (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) (g • x) :=
  CotangentBundle.ext (proj_smul g _) fun v ↦ (smul_snd_apply g _ v).trans <| by
    rw [zeroSection_snd, zeroSection_snd]
    exact (zero_apply _).trans (zero_apply _).symm

/-- The cotangent lift of a smooth group action is a group action. -/
instance instMulAction : MulAction G (CotangentBundle I M) where
  one_smul z := by
    rw [smul_def, Diffeomorph.constSmul_one, Diffeomorph.cotangent_refl, Diffeomorph.coe_refl,
      id_eq]
  mul_smul g h z := by
    rw [smul_def, Diffeomorph.constSmul_mul, Diffeomorph.cotangent_trans, Diffeomorph.coe_trans,
      Function.comp_apply, ← smul_def, ← smul_def]

/-- The cotangent lift of a smooth group action is again an action by smooth maps. -/
instance instContMDiffConstSMul :
    ContMDiffConstSMul (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) ∞ G (CotangentBundle I M) where
  contMDiff_const_smul g := (Diffeomorph.constSmul I ∞ g).cotangent.contMDiff.congr (smul_def g)

end TauCeti.CotangentBundle

namespace Diffeomorph

open TauCeti TauCeti.CotangentBundle

variable {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I ∞ G M] [IsManifold I 2 M]

/-- The cotangent lift of the diffeomorphism `x ↦ g • x` is the diffeomorphism `z ↦ g • z` of the
cotangent-lifted action. -/
@[simp]
theorem cotangent_constSmul (g : G) :
    (constSmul I ∞ g : M ≃ₘ⟮I, I⟯ M).cotangent = constSmul (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) ∞ g :=
  Diffeomorph.ext fun z ↦ (smul_def g z).symm.trans (constSmul_apply g z).symm

variable [MulAction G N] [ContMDiffConstSMul J ∞ G N] [IsManifold J 2 N]

/-- **Cotangent lifts of equivariant diffeomorphisms are equivariant.** If `h : M → N` commutes
with the action of `g`, its cotangent lift commutes with the cotangent-lifted action of `g`. -/
theorem cotangent_smul (h : M ≃ₘ⟮I, J⟯ N) (g : G) (hh : ∀ x : M, h (g • x) = g • h x)
    (z : CotangentBundle I M) : h.cotangent (g • z) = g • h.cotangent z := by
  have hcomm : (constSmul I ∞ g).trans h = h.trans (constSmul J ∞ g) :=
    Diffeomorph.ext fun x ↦ by simp only [coe_trans, Function.comp_apply, constSmul_apply, hh]
  have := congrArg (fun e : M ≃ₘ⟮I, J⟯ N ↦ e.cotangent z) hcomm
  simpa only [cotangent_trans, coe_trans, Function.comp_apply, cotangent_constSmul,
    constSmul_apply] using this

/-- **Equivariance of cotangent lifts.** The cotangent lift of a diffeomorphism `h : M → N`
commutes with the cotangent-lifted action of `g` exactly when `h` commutes with the action of `g`
on the base. -/
theorem forall_cotangent_smul_iff (h : M ≃ₘ⟮I, J⟯ N) (g : G) :
    (∀ z : CotangentBundle I M, h.cotangent (g • z) = g • h.cotangent z) ↔
      ∀ x : M, h (g • x) = g • h x := by
  refine ⟨fun hh x ↦ ?_, cotangent_smul h g⟩
  -- Project the equivariance of the lift at the zero covector over `x` to the base.
  simpa only [proj_cotangent, proj_smul, zeroSection_proj] using
    congrArg TotalSpace.proj (hh (zeroSection (E →L[𝕜] 𝕜) _ x))

end Diffeomorph
