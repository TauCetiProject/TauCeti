/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ContMDiff
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Data.ENat.Monoid
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Pulling back almost complex structures along diffeomorphisms

A `Cʳ` diffeomorphism `h : M → N` pulls a `Cⁿ` almost complex structure `J` on `N` back to a
`Cⁿ` structure whenever `n + 1 ≤ r`. Both regularity orders range over `ℕ∞`; continuous
structures and the smooth endpoint are included. This sufficient condition accounts for the
coordinate derivative in the formula; no optimality counterexample is asserted here.

The pulled-back almost complex structure is

`(h^* J)_x = (dh_x)⁻¹ ∘ J_(h x) ∘ dh_x`

on `M` (`TauCeti.ContMDiffAlmostComplexStructure.pullback h J hnr`). The native smooth
pullback is its infinite-order specialization. It is characterized by making every
differential of `h` complex linear, `dh_x ((h^* J)_x v) = J_(h x) (dh_x v)`
(`TauCeti.SmoothAlmostComplexStructure.mfderiv_pullback_apply`). Pulling back is contravariantly
functorial. At the smooth endpoint, it carries structures tamed by, invariant under, or
compatible with a two-form `σ` on `N` to structures with the same relation to `h^* σ`.

For a symplectomorphism `φ` of `(M, σ)` this gives the structure `φ^* J` that a time-dependent
family of almost complex structures on a mapping torus has to reach after one turn of the seam
`(t + 1, x) ∼ (t, φ x)`.

## Main definitions

* `TauCeti.ContMDiffAlmostComplexStructure.pullback h J hnr`: finite-order pullback.
* `TauCeti.SmoothAlmostComplexStructure.pullback h J`: its smooth specialization.

## Main results

* `TauCeti.ContMDiffAlmostComplexStructure.mfderiv_pullback_apply`: `dh ∘ h^* J = J ∘ dh`.
* `TauCeti.ContMDiffAlmostComplexStructure.eq_pullback_iff`: uniqueness of the structure making
  the differential complex linear.
* `TauCeti.ContMDiffAlmostComplexStructure.pullback_refl`,
  `TauCeti.ContMDiffAlmostComplexStructure.pullback_trans`: contravariant functoriality.
* `TauCeti.ContMDiffAlmostComplexStructure.contMDiff_pullback_family`: fixed-coordinate
  pullback preserves joint `Cⁿ` parameter and base-point regularity.
* `TauCeti.ContMDiffAlmostComplexStructure.ofLE_pullback`,
  `TauCeti.ContMDiffAlmostComplexStructure.pullback_neg`: regularity downgrade and negation.
* The corresponding `TauCeti.SmoothAlmostComplexStructure` theorems are the infinite-order
  specializations of these results.
* `TauCeti.SmoothTwoForm.Tames.pullback`, `TauCeti.SmoothTwoForm.Invariant.pullback`,
  `TauCeti.SmoothTwoForm.Compatible.pullback`: tameness, invariance and compatibility pass to
  the pullbacks of the form and of the structure.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.2 (the action `J ↦ φ^* J` of symplectomorphisms on compatible almost complex
  structures).
-/

public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M E' H' N E'' H'' P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold I'' ∞ P]

namespace ContMDiffAlmostComplexStructure

variable {n m r : ℕ∞}

private def pullbackEndomorphism (h : M ≃ₘ^r⟮I, I'⟯ N)
    (J : ContMDiffAlmostComplexStructure I' n N) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (mfderiv I I' h x).inverse ∘L J.toEndomorphism (h x) ∘L mfderiv I I' h x

private theorem contMDiff_pullbackEndomorphism_family
    (h : M ≃ₘ^r⟮I, I'⟯ N) (hnr : n + 1 ≤ r)
    {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [TopologicalSpace HQ]
    {IQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    {J : Q → ContMDiffAlmostComplexStructure I' n N}
    (hJ : ContMDiff (IQ.prod I') (I'.prod 𝓘(ℝ, E' →L[ℝ] E')) n
      (fun q : Q × N ↦ TotalSpace.mk' (E' →L[ℝ] E')
        (E := fun y : N ↦ TangentSpace I' y →L[ℝ] TangentSpace I' y) q.2
        ((J q.1).toEndomorphism q.2))) :
    ContMDiff (IQ.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q : Q × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        (pullbackEndomorphism h (J q.1) q.2)) := by
  rw [TauCeti.contMDiff_hom_bundle_prod_iff]
  have hJ' := (TauCeti.contMDiff_hom_bundle_prod_iff _).1 hJ
  have ht := h.contMDiff.contMDiff_tangentMap (m := (n : ℕ∞ω)) (by exact_mod_cast hnr)
  have hti := h.symm.contMDiff.contMDiff_tangentMap (m := (n : ℕ∞ω))
    (by exact_mod_cast hnr)
  refine (hti.comp (hJ'.comp (contMDiff_fst.prodMk
    (ht.comp contMDiff_snd)))).congr fun p ↦ ?_
  exact (h.tangentMap_symm_mk (ENat.coe_ne_zero_of_add_one_le hnr) p.2.proj _).symm

/-- The pullback `h^* J`, with `(h^* J)_x = (dh_x)⁻¹ ∘ J_(h x) ∘ dh_x`, of a `Cⁿ`
structure along a `Cʳ` diffeomorphism with `n + 1 ≤ r`. -/
def pullback (h : M ≃ₘ^r⟮I, I'⟯ N) (J : ContMDiffAlmostComplexStructure I' n N)
    (hnr : n + 1 ≤ r) : ContMDiffAlmostComplexStructure I n M where
  toEndomorphism := ⟨pullbackEndomorphism h J,
    (contMDiff_pullbackEndomorphism_family h hnr (IQ := I) (J := fun _ : M ↦ J)
      (J.toEndomorphism.contMDiff.comp contMDiff_snd)).comp
        (contMDiff_id.prodMk contMDiff_id)⟩
  square_neg x := by
    ext v
    have hinv := h.isInvertible_mfderiv (x := x) (ENat.coe_ne_zero_of_add_one_le hnr)
    simp [pullbackEndomorphism, hinv.self_apply_inverse, hinv.inverse_apply_self]

variable (h : M ≃ₘ^r⟮I, I'⟯ N) (J : ContMDiffAlmostComplexStructure I' n N)
  (hnr : n + 1 ≤ r)

/-- The pullback at `x` is `(dh_x)⁻¹ ∘ J_(h x) ∘ dh_x`. -/
theorem pullback_apply (x : M) (v : TangentSpace I x) :
    pullback h J hnr x v =
      (mfderiv I I' h x).inverse (J (h x) (mfderiv I I' h x v)) := (rfl)

/-- The finite-order pullback endomorphism is conjugation by the actual differential. -/
theorem pullback_toEndomorphism (x : M) :
    (pullback h J hnr).toEndomorphism x =
      (h.mfderivToContinuousLinearEquiv
        (ENat.coe_ne_zero_of_add_one_le hnr) x).symm.conjContinuousAlgEquiv
          (J.toEndomorphism (h x)) := by
  have he : (h.mfderivToContinuousLinearEquiv (ENat.coe_ne_zero_of_add_one_le hnr) x :
      TangentSpace I x →L[ℝ] TangentSpace I' (h x)) = mfderiv I I' h x :=
    Diffeomorph.mfderivToContinuousLinearEquiv_coe h _
  ext v
  simp only [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
    ContinuousLinearEquiv.symm_symm]
  refine (pullback_apply h J hnr x v).trans ?_
  rw [← he, ContinuousLinearMap.inverse_equiv, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_coe]

/-- The differential of the coordinate change intertwines the pulled-back structure. -/
@[simp]
theorem mfderiv_pullback_apply (x : M) (v : TangentSpace I x) :
    mfderiv I I' h x (pullback h J hnr x v) = J (h x) (mfderiv I I' h x v) :=
  (h.isInvertible_mfderiv (ENat.coe_ne_zero_of_add_one_le hnr)).self_apply_inverse _

/-- The pullback is characterized by the intertwining identity at every tangent vector. -/
theorem eq_pullback_iff {K : ContMDiffAlmostComplexStructure I n M} :
    K = pullback h J hnr ↔ ∀ (x : M) (v : TangentSpace I x),
      mfderiv I I' h x (K x v) = J (h x) (mfderiv I I' h x v) := by
  refine ⟨fun hK x v ↦ hK ▸ mfderiv_pullback_apply h J hnr x v, fun hK ↦ ?_⟩
  ext x v
  have hinv := h.isInvertible_mfderiv (x := x) (ENat.coe_ne_zero_of_add_one_le hnr)
  rw [pullback_apply, ← hK, hinv.inverse_apply_self]

/-- Fixed-coordinate pullback preserves the joint `Cⁿ` regularity of a parameter family. -/
theorem contMDiff_pullback_family {EQ HQ Q : Type*} [NormedAddCommGroup EQ]
    [NormedSpace ℝ EQ] [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ EQ HQ}
    [TopologicalSpace Q] [ChartedSpace HQ Q]
    {J : Q → ContMDiffAlmostComplexStructure I' n N}
    (hJ : ContMDiff (IQ.prod I') (I'.prod 𝓘(ℝ, E' →L[ℝ] E')) n
      (fun q : Q × N ↦ TotalSpace.mk' (E' →L[ℝ] E')
        (E := fun y : N ↦ TangentSpace I' y →L[ℝ] TangentSpace I' y) q.2
        ((J q.1).toEndomorphism q.2))) :
    ContMDiff (IQ.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q : Q × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        ((pullback h (J q.1) hnr).toEndomorphism q.2)) :=
  contMDiff_pullbackEndomorphism_family h hnr hJ

/-- Pullback preserves identity maps at every structure order, including zero. -/
@[simp]
theorem pullback_refl (K : ContMDiffAlmostComplexStructure I n M) (hnr : n + 1 ≤ r) :
    pullback (Diffeomorph.refl I M r) K hnr = K := by
  refine ((eq_pullback_iff _ K hnr).2 fun x v ↦ ?_).symm
  simp only [Diffeomorph.coe_refl, mfderiv_id]
  -- The tangent-space base is `id x`; reducing it also exposes the identity CLM applications.
  rfl

/-- Pullback is contravariantly functorial at finite regularity. -/
theorem pullback_trans (g : N ≃ₘ^r⟮I', I''⟯ P)
    (L : ContMDiffAlmostComplexStructure I'' n P) :
    pullback (h.trans g) L hnr = pullback h (pullback g L hnr) hnr := by
  refine ((eq_pullback_iff _ L hnr).2 fun x v ↦ ?_).symm
  have hchain (w : TangentSpace I x) :
      mfderiv I I'' (h.trans g) x w = mfderiv I' I'' g (h x) (mfderiv I I' h x w) :=
    mfderiv_comp_apply x (g.mdifferentiable (ENat.coe_ne_zero_of_add_one_le hnr) (h x))
      (h.mdifferentiable (ENat.coe_ne_zero_of_add_one_le hnr) x) w
  rw [hchain, hchain, mfderiv_pullback_apply, mfderiv_pullback_apply]
  -- The remaining fibre base `(h.trans g) x` reduces to `g (h x)` through the bundled coercion.
  rfl

/-- Forgetting structure regularity commutes with pullback. -/
@[simp]
theorem ofLE_pullback (hmn : m ≤ n) :
    (pullback h J hnr).ofLE hmn =
      pullback h (J.ofLE hmn) (by
        calc
          m + 1 ≤ n + 1 := add_le_add hmn le_rfl
          _ ≤ r := hnr) := by
  ext x v
  rw [ofLE_apply, pullback_apply, pullback_apply, ofLE_apply]

/-- Negating a structure commutes with finite-order pullback. -/
@[simp]
theorem pullback_neg : pullback h (-J) hnr = -(pullback h J hnr) := by
  ext x v
  simp [pullback_apply]

end ContMDiffAlmostComplexStructure

namespace SmoothAlmostComplexStructure

/-- Smooth pullback is the infinite-order specialization of finite-regularity pullback. -/
def pullback (h : M ≃ₘ⟮I, I'⟯ N) (J : SmoothAlmostComplexStructure I' N) :
    SmoothAlmostComplexStructure I M :=
  (ContMDiffAlmostComplexStructure.pullback h (J.toContMDiff ⊤) (by simp)).toSmooth

variable (h : M ≃ₘ⟮I, I'⟯ N) (J : SmoothAlmostComplexStructure I' N)

/-- The pullback at `x` is `(dh_x)⁻¹ ∘ J_(h x) ∘ dh_x`. -/
theorem pullback_apply (x : M) (v : TangentSpace I x) :
    pullback h J x v = (mfderiv I I' h x).inverse (J (h x) (mfderiv I I' h x v)) := by
  rw [pullback, ContMDiffAlmostComplexStructure.toSmooth_apply,
    ContMDiffAlmostComplexStructure.pullback_apply, toContMDiff_apply]

/-- The endomorphism of `T_x M` underlying `h^* J` is the conjugate of `J_(h x)` by the
linear equivalence `dh_x`. -/
theorem pullback_toEndomorphism (x : M) :
    (pullback h J).toEndomorphism x =
      (h.mfderivToContinuousLinearEquiv (by simp) x).symm.conjContinuousAlgEquiv
        (J.toEndomorphism (h x)) := by
  simpa only [pullback, ContMDiffAlmostComplexStructure.toSmooth_toEndomorphism,
    toContMDiff_toEndomorphism_apply] using
      ContMDiffAlmostComplexStructure.pullback_toEndomorphism h (J.toContMDiff ⊤) (by simp) x

/-- The differentials of `h` are complex linear from `h^* J` to `J`. -/
@[simp]
theorem mfderiv_pullback_apply (x : M) (v : TangentSpace I x) :
    mfderiv I I' h x (pullback h J x v) = J (h x) (mfderiv I I' h x v) := by
  simpa only [pullback, ContMDiffAlmostComplexStructure.toSmooth_apply, toContMDiff_apply]
    using ContMDiffAlmostComplexStructure.mfderiv_pullback_apply h (J.toContMDiff ⊤)
      (by simp) x v

/-- Pulling back a family of smooth almost complex structures on `N`, depending smoothly on a
parameter in a manifold `Q`, along a diffeomorphism `h : M → N` gives a family of almost complex
structures on `M` depending smoothly on the parameter: `(q, x) ↦ (h^* J_q)_x` is a smooth section
of the tangent endomorphism bundle along the projection `Q × M → M`. -/
theorem contMDiff_pullback_family {EQ HQ Q : Type*} [NormedAddCommGroup EQ] [NormedSpace ℝ EQ]
    [TopologicalSpace HQ] {IQ : ModelWithCorners ℝ EQ HQ} [TopologicalSpace Q] [ChartedSpace HQ Q]
    {J : Q → SmoothAlmostComplexStructure I' N}
    (hJ : ContMDiff (IQ.prod I') (I'.prod 𝓘(ℝ, E' →L[ℝ] E')) ∞
      (fun q : Q × N ↦ TotalSpace.mk' (E' →L[ℝ] E')
        (E := fun y : N ↦ TangentSpace I' y →L[ℝ] TangentSpace I' y) q.2
        ((J q.1).toEndomorphism q.2))) :
    ContMDiff (IQ.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun q : Q × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        ((pullback h (J q.1)).toEndomorphism q.2)) := by
  simpa only [pullback, ContMDiffAlmostComplexStructure.toSmooth_toEndomorphism] using
    ContMDiffAlmostComplexStructure.contMDiff_pullback_family h (by simp) (IQ := IQ)
      (J := fun q => (J q).toContMDiff ⊤) (by
        simpa only [toContMDiff_toEndomorphism_apply] using hJ)

/-- Smooth-to-finite regularity conversion commutes with pullback. -/
@[simp]
theorem toContMDiff_pullback (n : ℕ∞) :
    (pullback h J).toContMDiff n =
      ContMDiffAlmostComplexStructure.pullback h (J.toContMDiff n) (by simp) := by
  ext x v
  rw [toContMDiff_apply, pullback_apply, ContMDiffAlmostComplexStructure.pullback_apply,
    toContMDiff_apply]

/-- The pullback `h^* J` is the only almost complex structure on `M` for which every
differential of `h` is complex linear into `J`. -/
theorem eq_pullback_iff {K : SmoothAlmostComplexStructure I M} :
    K = pullback h J ↔
      ∀ (x : M) (v : TangentSpace I x),
        mfderiv I I' h x (K x v) = J (h x) (mfderiv I I' h x v) := by
  have hinj := (ContMDiffAlmostComplexStructure.smoothEquiv (I := I) (M := M)).symm.injective
  rw [← hinj.eq_iff]
  simpa only [ContMDiffAlmostComplexStructure.smoothEquiv_symm_apply,
    toContMDiff_pullback, toContMDiff_apply] using
      ContMDiffAlmostComplexStructure.eq_pullback_iff h (J.toContMDiff ⊤) (by simp)
        (K := K.toContMDiff ⊤)

/-- Pulling back along the identity does nothing. -/
@[simp]
theorem pullback_refl (K : SmoothAlmostComplexStructure I M) :
    pullback (Diffeomorph.refl I M ∞) K = K := by
  simpa only [pullback, toContMDiff_toSmooth] using
    congrArg ContMDiffAlmostComplexStructure.toSmooth
      (ContMDiffAlmostComplexStructure.pullback_refl (K.toContMDiff ⊤) (by simp))

/-- Pulling back is contravariantly functorial: `(g ∘ h)^* J = h^* (g^* J)`. -/
theorem pullback_trans (g : N ≃ₘ⟮I', I''⟯ P) (J : SmoothAlmostComplexStructure I'' P) :
    pullback (h.trans g) J = pullback h (pullback g J) := by
  apply (ContMDiffAlmostComplexStructure.smoothEquiv (I := I) (M := M)).symm.injective
  simpa only [ContMDiffAlmostComplexStructure.smoothEquiv_symm_apply,
    toContMDiff_pullback] using
    ContMDiffAlmostComplexStructure.pullback_trans h (by simp) g
      (J.toContMDiff ⊤)

end SmoothAlmostComplexStructure

namespace ContMDiffAlmostComplexStructure

/-- Infinite-order pullback agrees with the native smooth pullback under smooth conversion. -/
@[simp]
theorem toSmooth_pullback (h : M ≃ₘ⟮I, I'⟯ N)
    (J : ContMDiffAlmostComplexStructure I' ⊤ N) :
    (pullback h J (by simp)).toSmooth = SmoothAlmostComplexStructure.pullback h J.toSmooth := by
  ext x v
  rw [toSmooth_apply, pullback_apply, SmoothAlmostComplexStructure.pullback_apply,
    toSmooth_apply]

end ContMDiffAlmostComplexStructure

namespace SmoothTwoForm

variable {σ : SmoothTwoForm I' N} {J : SmoothAlmostComplexStructure I' N}

/-- If `σ` tames `J`, then `h^* σ` tames `h^* J`. -/
theorem Tames.pullback (hJ : σ.Tames J) (h : M ≃ₘ⟮I, I'⟯ N) :
    SmoothTwoForm.Tames (SmoothForm.mpullback h h.contMDiff σ) (J.pullback h) := by
  rw [tames_iff]
  intro x v hv
  rw [SmoothForm.eval₂_mpullback, SmoothAlmostComplexStructure.mfderiv_pullback_apply]
  refine tames_iff.1 hJ (h x) _ fun h0 ↦ hv ?_
  rw [← (h.isInvertible_mfderiv (n := ∞) (x := x) (by simp)).inverse_apply_self v, h0, map_zero]

/-- If `σ` is invariant under `J`, then `h^* σ` is invariant under `h^* J`. -/
theorem Invariant.pullback (hJ : σ.Invariant J) (h : M ≃ₘ⟮I, I'⟯ N) :
    SmoothTwoForm.Invariant (SmoothForm.mpullback h h.contMDiff σ) (J.pullback h) := by
  rw [invariant_iff]
  intro x v w
  simp only [SmoothForm.eval₂_mpullback, SmoothAlmostComplexStructure.mfderiv_pullback_apply]
  exact invariant_iff.1 hJ (h x) _ _

/-- If `σ` is compatible with `J`, then `h^* σ` is compatible with `h^* J`. -/
theorem Compatible.pullback (hJ : σ.Compatible J) (h : M ≃ₘ⟮I, I'⟯ N) :
    SmoothTwoForm.Compatible (SmoothForm.mpullback h h.contMDiff σ) (J.pullback h) :=
  ⟨hJ.invariant.pullback h, hJ.tames.pullback h⟩

end SmoothTwoForm

end TauCeti
