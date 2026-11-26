/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Coorientation
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.LinearAlgebra.Orientation.Basic

/-!
# Pulling coorientations back along local diffeomorphisms

Let `f : M → N` be a smooth local diffeomorphism, for instance a diffeomorphism or the inclusion
of an open subset, and let `D'` be a hyperplane field on `N`. Its pullback `D = f^* D'`, with
`D x = (df_x)⁻¹ (D' (f x))`, is a hyperplane field on `M`, and the coorientation data of `D'`
pull back to those of `D`. This is the naturality of coorientations under diffeomorphisms
preserving the hyperplane fields and under restriction to open subsets.

* **Annihilator lines.** Composing with `df_x` identifies the annihilator line `D'⁰_(f x)` with
  `D⁰_x` (`IsLocalDiffeomorphAt.annihilatorPullback`): a covector vanishing on `D' (f x)` pulls back
  to one vanishing on `D x`, and as `df_x` is invertible every covector vanishing on `D x` arises
  this way.
* **Coorientations.** Transporting the fibre orientations along these identifications pulls a
  family `o'` of orientations of the lines `D'⁰` back to a family
  `IsLocalDiffeomorph.pullbackCoorientation hf hD o'` of orientations of the lines `D⁰`. The
  pullback of a coorientation is a coorientation (`TauCeti.IsCoorientation.pullback`): pulling a
  continuous positive annihilating covector field back along `f` gives a continuous one
  (`TauCeti.CotangentBundle.continuousAt_mk_comp_mfderiv`).
* **Defining forms.** If a one-form `β` vanishes nowhere and has kernel `D'`, then its pullback
  `f^* β` vanishes nowhere and has kernel `D`
  (`TauCeti.SmoothForm.mpullback_val_ne_zero_and_ker_eq`), and the coorientation of `f^* β` is
  the pullback of the coorientation of `β` (`TauCeti.SmoothForm.coorientation_mpullback`).
* **Functoriality.** Pulling back commutes with passing to the opposite fibre orientations
  (`IsLocalDiffeomorph.pullbackCoorientation_neg`), is the identity along the identity map
  (`IsLocalDiffeomorph.pullbackCoorientation_id`), and pulling back along a composite `g ∘ f` is
  pulling back along `g` and then along `f` (`IsLocalDiffeomorph.pullbackCoorientation_comp`).

For a diffeomorphism `e` these apply to `e.isLocalDiffeomorph`. For an open subset `U ⊆ M` they
apply to the inclusion, a local diffeomorphism by `TauCeti.isLocalDiffeomorph_subtype_val`; its
differentials are identities, so the pulled-back field is the restriction of `D` to `U`.

## Main definitions

* `IsLocalDiffeomorphAt.annihilatorPullback`: the identification `D'⁰_(f x) ≃ D⁰_x`,
  `p ↦ p ∘ df_x`, for `f` a local diffeomorphism at `x`.
* `IsLocalDiffeomorph.pullbackCoorientation`: the pullback of fibre orientations of the
  annihilator lines.

## Main results

* `TauCeti.IsCoorientation.pullback`: the pullback of a coorientation is a coorientation.
* `TauCeti.SmoothForm.coorientation_mpullback`: the coorientation of a pulled-back defining form
  is the pulled-back coorientation.
* `IsLocalDiffeomorph.pullbackCoorientation_id`, `IsLocalDiffeomorph.pullbackCoorientation_comp`:
  functoriality.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008, Section 1.1
  (coorientations of hyperplane fields).
-/

public section

noncomputable section

open Bundle Set Module TauCeti TauCeti.CotangentBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {D : Π x : M, Submodule ℝ (TangentSpace I x)} {D' : Π y : N, Submodule ℝ (TangentSpace J y)}
  {f : M → N}

namespace IsLocalDiffeomorphAt

/-- **Pulling annihilating covectors back along a local diffeomorphism.** If `f` is a local
diffeomorphism at `x` and `D x` is the preimage of `D' (f x)` under its differential, composing
with `df_x` identifies the annihilator of `D'` at `f x` with the annihilator of `D` at `x`. -/
def annihilatorPullback {n : WithTop ℕ∞} {x : M} (hf : IsLocalDiffeomorphAt I J n f x)
    (hn : n ≠ 0) (hD : (D' (f x)).comap (mfderiv I J f x).toLinearMap = D x) :
    annihilatorSpace J D' (f x) ≃ₗ[ℝ] annihilatorSpace I D x where
  toFun p := ⟨(p : TangentSpace J (f x) →L[ℝ] ℝ) ∘L mfderiv I J f x, by
    rw [mem_annihilatorSpace_iff, ← hD]
    exact fun v hv ↦ mem_annihilatorSpace_iff.1 p.property _ hv⟩
  invFun q := ⟨(q : TangentSpace I x →L[ℝ] ℝ) ∘L
      (hf.mfderivToContinuousLinearEquiv hn).symm.toContinuousLinearMap, by
    rw [mem_annihilatorSpace_iff]
    refine fun w hw ↦ mem_annihilatorSpace_iff.1 q.property _ ?_
    rw [← hD, Submodule.mem_comap]
    convert hw using 1
    exact hf.mfderiv_mfderivToContinuousLinearEquiv_symm_apply hn w⟩
  map_add' p q := Subtype.ext (ContinuousLinearMap.add_comp _ _ _)
  map_smul' c p := Subtype.ext (ContinuousLinearMap.smul_comp _ _ _)
  left_inv p := Subtype.ext <| ContinuousLinearMap.ext fun w ↦ by simp
  right_inv q := Subtype.ext <| ContinuousLinearMap.ext fun v ↦ by simp

/-- The pulled-back covector is the original covector composed with the differential. -/
@[simp]
theorem coe_annihilatorPullback_apply {n : WithTop ℕ∞} {x : M}
    (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0)
    (hD : (D' (f x)).comap (mfderiv I J f x).toLinearMap = D x)
    (p : annihilatorSpace J D' (f x)) :
    (hf.annihilatorPullback hn hD p : TangentSpace I x →L[ℝ] ℝ) =
      (p : TangentSpace J (f x) →L[ℝ] ℝ) ∘L mfderiv I J f x :=
  (rfl)

end IsLocalDiffeomorphAt

namespace IsLocalDiffeomorph

/-- The **pullback of fibre orientations** of the annihilator lines of `D'` along a local
diffeomorphism `f` with `D = f^* D'`: at `x`, the orientation of `D⁰_x` obtained by transporting
`o' (f x)` along `IsLocalDiffeomorphAt.annihilatorPullback`. A covector `p ∘ df_x` is positive for
it exactly when `p` is positive for `o' (f x)`. -/
def pullbackCoorientation (hf : IsLocalDiffeomorph I J ∞ f)
    (hD : ∀ x, (D' (f x)).comap (mfderiv I J f x).toLinearMap = D x)
    (o' : Π y : N, Orientation ℝ (annihilatorSpace J D' y) (Fin 1)) (x : M) :
    Orientation ℝ (annihilatorSpace I D x) (Fin 1) :=
  Orientation.map (Fin 1) ((hf x).annihilatorPullback (by simp) (hD x)) (o' (f x))

/-- Unfolding `IsLocalDiffeomorph.pullbackCoorientation`. -/
theorem pullbackCoorientation_apply (hf : IsLocalDiffeomorph I J ∞ f)
    (hD : ∀ x, (D' (f x)).comap (mfderiv I J f x).toLinearMap = D x)
    (o' : Π y : N, Orientation ℝ (annihilatorSpace J D' y) (Fin 1)) (x : M) :
    hf.pullbackCoorientation hD o' x =
      Orientation.map (Fin 1) ((hf x).annihilatorPullback (by simp) (hD x)) (o' (f x)) :=
  (rfl)

/-- The pullback of the opposite fibre orientations is the opposite of the pullback. -/
@[simp]
theorem pullbackCoorientation_neg (hf : IsLocalDiffeomorph I J ∞ f)
    (hD : ∀ x, (D' (f x)).comap (mfderiv I J f x).toLinearMap = D x)
    (o' : Π y : N, Orientation ℝ (annihilatorSpace J D' y) (Fin 1)) :
    hf.pullbackCoorientation hD (-o') = -hf.pullbackCoorientation hD o' :=
  funext fun x ↦ Orientation.map_neg _ (o' (f x))

/-- **Pulling back along the identity.** Pulling fibre orientations back along the identity map
does not change them. -/
@[simp]
theorem pullbackCoorientation_id (hf : IsLocalDiffeomorph I I ∞ (id : M → M))
    (hD : ∀ x, (D (id x)).comap (mfderiv I I id x).toLinearMap = D x)
    (o : Π x : M, Orientation ℝ (annihilatorSpace I D x) (Fin 1)) :
    hf.pullbackCoorientation hD o = o := by
  funext x
  have he : (hf x).annihilatorPullback (by simp) (hD x) =
      LinearEquiv.refl ℝ (annihilatorSpace I D x) :=
    LinearEquiv.ext fun p ↦ Subtype.ext <| by
      rw [IsLocalDiffeomorphAt.coe_annihilatorPullback_apply, mfderiv_id,
        ContinuousLinearMap.comp_id]
      exact congrArg Subtype.val (LinearEquiv.refl_apply (R := ℝ) p).symm
  simp [pullbackCoorientation_apply, he]

/-- **Pulling back along a composite.** Pulling fibre orientations back along `g ∘ f` is pulling
them back along `g` and then along `f`. -/
theorem pullbackCoorientation_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ G H''}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
    {D'' : Π z : P, Submodule ℝ (TangentSpace K z)} {g : N → P}
    (hf : IsLocalDiffeomorph I J ∞ f) (hg : IsLocalDiffeomorph J K ∞ g)
    (hgf : IsLocalDiffeomorph I K ∞ (g ∘ f))
    (hD : ∀ x, (D' (f x)).comap (mfderiv I J f x).toLinearMap = D x)
    (hD' : ∀ y, (D'' (g y)).comap (mfderiv J K g y).toLinearMap = D' y)
    (hD'' : ∀ x, (D'' ((g ∘ f) x)).comap (mfderiv I K (g ∘ f) x).toLinearMap = D x)
    (o'' : Π z : P, Orientation ℝ (annihilatorSpace K D'' z) (Fin 1)) :
    hgf.pullbackCoorientation hD'' o'' =
      hf.pullbackCoorientation hD (hg.pullbackCoorientation hD' o'') := by
  funext x
  have he : (hgf x).annihilatorPullback (by simp) (hD'' x) =
      ((hg (f x)).annihilatorPullback (by simp) (hD' (f x))).trans
        ((hf x).annihilatorPullback (by simp) (hD x)) :=
    LinearEquiv.ext fun p ↦ Subtype.ext <| by
      simp only [LinearEquiv.trans_apply, IsLocalDiffeomorphAt.coe_annihilatorPullback_apply,
        ContinuousLinearMap.comp_assoc,
        mfderiv_comp x ((hg (f x)).mdifferentiableAt (by simp))
          ((hf x).mdifferentiableAt (by simp))]
  rw [pullbackCoorientation_apply, he, Orientation.map_trans, pullbackCoorientation_apply,
    pullbackCoorientation_apply]
  simp only [Function.comp_apply]

end IsLocalDiffeomorph

namespace TauCeti

variable [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- **The pullback of a coorientation is a coorientation.** If `o'` is a coorientation of a
hyperplane field `D'` on `N` and `f` is a local diffeomorphism with `D = f^* D'`, then the
pulled-back fibre orientations form a coorientation of `D`. -/
theorem IsCoorientation.pullback {o' : Π y : N, Orientation ℝ (annihilatorSpace J D' y) (Fin 1)}
    (ho : IsCoorientation J D' o') (hf : IsLocalDiffeomorph I J ∞ f)
    (hD : ∀ x, (D' (f x)).comap (mfderiv I J f x).toLinearMap = D x) :
    IsCoorientation I D (hf.pullbackCoorientation hD o') := by
  rw [isCoorientation_iff] at ho ⊢
  intro x
  obtain ⟨U', hU', σ', hσ', hpos⟩ := ho (f x)
  obtain ⟨V, hVU, hVo, hxV⟩ := mem_nhds_iff.1 hU'
  refine ⟨f ⁻¹' V, (hVo.preimage hf.contMDiff.continuous).mem_nhds hxV,
    fun y ↦ (hf y).annihilatorPullback (by simp) (hD y) (σ' (f y)),
    fun y hy ↦ ContinuousAt.continuousWithinAt ?_, fun y hy ↦ ?_⟩
  · -- The pulled-back covector field is the pullback along `f` of a continuous covector field.
    have hσy : ContinuousAt (fun z ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun z : N ↦ TangentSpace J z →L[ℝ] ℝ) z (σ' z : TangentSpace J z →L[ℝ] ℝ)) (f y) :=
      hσ'.continuousAt (Filter.mem_of_superset (hVo.mem_nhds hy) hVU)
    exact continuousAt_mk_comp_mfderiv
      (Ψ := fun z ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun z : N ↦ TangentSpace J z →L[ℝ] ℝ)
        (f z) (σ' (f z) : TangentSpace J (f z) →L[ℝ] ℝ)) (g := id) (fun _ ↦ rfl)
      (hσy.comp hf.contMDiff.continuous.continuousAt) continuousAt_id
      ((hf.contMDiff y).of_le (by simp))
  · obtain ⟨β, hβ, hβo⟩ := hpos (f y) (hVU hy)
    refine ⟨β.map ((hf y).annihilatorPullback (by simp) (hD y)), by rw [Basis.map_apply, hβ], ?_⟩
    rw [Basis.orientation_map, hβo, IsLocalDiffeomorph.pullbackCoorientation_apply]

namespace SmoothForm

variable {β : SmoothForm J N ℝ 1}

/-- **Pulling back a defining form.** If `β` vanishes nowhere and has kernel `D'`, its pullback
along a local diffeomorphism `f` vanishes nowhere and has kernel `D = f^* D'`. -/
theorem mpullback_val_ne_zero_and_ker_eq (hf : IsLocalDiffeomorph I J ∞ f)
    (hD : ∀ x, (D' (f x)).comap (mfderiv I J f x).toLinearMap = D x)
    (hβ : ∀ y, β.val y ≠ 0 ∧ RoughForm.ker β.val y = D' y) (x : M) :
    (mpullback f hf.contMDiff β).val x ≠ 0 ∧
      RoughForm.ker (mpullback f hf.contMDiff β).val x = D x := by
  have hpull : degreeOneEquiv (mpullback f hf.contMDiff β) x =
      ((hf x).annihilatorPullback (by simp) (hD x)
        ⟨degreeOneEquiv β (f x), degreeOneEquiv_mem_annihilatorSpace (hβ (f x)).2⟩ :
          TangentSpace I x →L[ℝ] ℝ) :=
    degreeOneEquiv_mpullback hf.contMDiff β x
  refine ⟨fun h ↦ degreeOneEquiv_ne_zero (hβ (f x)).1 ?_, ?_⟩
  · -- A covector pulling back to zero along the bijective differential is zero.
    have h0 : degreeOneEquiv (mpullback f hf.contMDiff β) x = 0 := by
      rw [← degreeOneEquiv_coe_eq_zero_iff, LinearMap.ext_iff] at h
      exact ContinuousLinearMap.ext h
    rw [hpull] at h0
    exact congrArg Subtype.val (((hf x).annihilatorPullback (by simp) (hD x)).map_eq_zero_iff.1
      (Subtype.ext h0))
  · rw [← hD, ← (hβ (f x)).2, RoughForm.ker_eq_ker_eval, RoughForm.ker_eq_ker_eval, eval_val,
      eval_val, degreeOneEquiv_mpullback hf.contMDiff β x, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.ker_comp]

/-- **The coorientation of a pulled-back defining form.** If `β` vanishes nowhere and has kernel
`D'`, the coorientation of its pullback along a local diffeomorphism `f` is the pullback of the
coorientation of `β`. -/
theorem coorientation_mpullback (hf : IsLocalDiffeomorph I J ∞ f)
    (hD : ∀ x, (D' (f x)).comap (mfderiv I J f x).toLinearMap = D x)
    (hβ : ∀ y, β.val y ≠ 0 ∧ RoughForm.ker β.val y = D' y) :
    (mpullback f hf.contMDiff β).coorientation (mpullback_val_ne_zero_and_ker_eq hf hD hβ) =
      hf.pullbackCoorientation hD (β.coorientation hβ) := by
  funext x
  -- The one-vector basis `(β_(f x))` of `D'⁰_(f x)` has the coorientation of `β`.
  let b := FiniteDimensional.basisSingleton (Fin 1)
    (finrank_annihilatorSpace_eq_one (hβ (f x)).1 (hβ (f x)).2)
    ⟨degreeOneEquiv β (f x), degreeOneEquiv_mem_annihilatorSpace (hβ (f x)).2⟩
    fun h ↦ degreeOneEquiv_ne_zero (hβ (f x)).1 (congrArg Subtype.val h)
  have hb : b.orientation = β.coorientation hβ (f x) :=
    (orientation_eq_coorientation_iff hβ b).2 (by
      rw [FiniteDimensional.basisSingleton_apply])
  -- Its image `(β_(f x) ∘ df_x)` is a basis of `D⁰_x` with the coorientation of `f^* β`.
  rw [IsLocalDiffeomorph.pullbackCoorientation_apply, ← hb, ← Basis.orientation_map, eq_comm,
    orientation_eq_coorientation_iff, Basis.map_apply, FiniteDimensional.basisSingleton_apply,
    IsLocalDiffeomorphAt.coe_annihilatorPullback_apply, degreeOneEquiv_mpullback hf.contMDiff β x]

end SmoothForm

end TauCeti
