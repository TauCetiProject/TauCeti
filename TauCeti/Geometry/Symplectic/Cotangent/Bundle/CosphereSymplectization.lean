/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import TauCeti.Geometry.Contact.Symplectization.Basic
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ContactType

/-!
# The punctured cotangent bundle is the symplectization of the unit cosphere bundle

Let `M` be a smooth Riemannian manifold without boundary, with cotangent bundle `T*M`, Liouville
form `λ = p dq` and canonical symplectic form `ω = -dλ`. The unit cosphere bundle
`S*M = {‖p‖ = 1}` carries the two contact forms `α_b = -λ|S*M` and `α_g = λ|S*M = -α_b`
(`TauCeti.CotangentBundle.isContactForm_mpullback_neg_liouvilleForm_cosphereBundle`). This file
identifies the **punctured cotangent bundle** `T*M \ 0` of nonzero covectors
(`TauCeti.CotangentBundle.punctured`) with the symplectization `ℝ × S*M` of `S*M`, with real
coordinate `t`, through the radial diffeomorphism

`Φ : ℝ × S*M → T*M \ 0`, `Φ(t, z) = eᵗ z`

(`TauCeti.CotangentBundle.cosphereSymplectization`). Its inverse sends a nonzero covector `q` to
`(log ‖q‖, q / ‖q‖)`, so `r = eᵗ` is the norm of covectors.

Since `Φ` multiplies a unit covector by `eᵗ` without moving its base point, it pulls `λ` back to
`eᵗ λ|S*M`, the symplectization form `eᵗ α_g` of `TauCeti.SmoothForm.symplectization`
(`TauCeti.CotangentBundle.mpullback_cosphereSymplectization_liouvilleForm`), and `-λ` back to
`θ = eᵗ α_b`. Taking exterior derivatives, `Φ` pulls the canonical form `ω = -dλ` back to `dθ`:

`Φ^* ω = d(eᵗ α_b)`

(`TauCeti.CotangentBundle.mpullback_cosphereSymplectization_symplecticForm`). So `Φ` is a
symplectomorphism from the symplectization of the contact manifold `(S*M, α_b)` onto
`(T*M \ 0, ω)`. For the opposite contact form `α_g` the same map pulls `ω` back to
`-d(eᵗ α_g)`, so it is anti-symplectic for the symplectization form `d(eᵗ α_g)`
(`TauCeti.CotangentBundle.mpullback_cosphereSymplectization_neg_symplecticForm`). In the
coordinate `r = eᵗ` these read `Φ^* ω = d(r α_b) = -d(r α_g)`.

The curve `t ↦ eᵗ z` is the integral curve through `z` of the radial field `Z = p ∂_p`
(`TauCeti.isMIntegralCurve_vectorBundleEulerField`), the Liouville field of the primitive `-λ` of
`ω` (`TauCeti.CotangentBundle.symplecticForm_interior_vectorBundleEulerField`). So `Φ` is the
Liouville flow map of `S*M`, and `Φ^* (-λ) = eᵗ α_b` is the cotangent case of the identity for
Liouville flows of `TauCeti.mpullback_globalFlow_comp_eq_symplectization`. Here it is proved
directly: the Liouville form is linear on fibres, so it pulls back along `(t, y) ↦ eᵗ ι(y)` to
`eᵗ ι^* λ` for every smooth family `ι` of covectors, with no flow or completeness argument.

## Main definitions

* `TauCeti.CotangentBundle.punctured`: the open set `T*M \ 0` of nonzero covectors.
* `TauCeti.CotangentBundle.cosphereSymplectization`: the radial diffeomorphism
  `ℝ × S*M ≃ T*M \ 0`, `(t, z) ↦ eᵗ z`.

## Main results

* `TauCeti.CotangentBundle.coe_cosphereSymplectization_apply`,
  `TauCeti.CotangentBundle.cosphereSymplectization_symm_apply`: the formulas for `Φ` and its
  inverse.
* `TauCeti.CotangentBundle.mpullback_cosphereSymplectization_liouvilleForm`,
  `TauCeti.CotangentBundle.mpullback_cosphereSymplectization_neg_liouvilleForm`: `Φ` pulls `λ`
  and `-λ` back to `eᵗ α_g` and `eᵗ α_b`.
* `TauCeti.CotangentBundle.mpullback_cosphereSymplectization_symplecticForm`: `Φ` pulls `ω` back
  to `d(eᵗ α_b)`.
* `TauCeti.CotangentBundle.mpullback_cosphereSymplectization_neg_symplecticForm`: `Φ` pulls
  `-ω` back to `d(eᵗ α_g)`.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (the symplectization of a contact manifold and the unit cotangent bundle).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 1.2 (the space of contact elements and the cotangent bundle minus its zero
  section).
-/

public section

noncomputable section

open Bundle Module TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Radial rescaling of a family of covectors -/

section ExpSMul

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {ι : N → CotangentBundle I M}

/-- The map `(t, y) ↦ eᵗ ι(y)` rescaling a family `ι` of covectors. -/
private def expSMul (ι : N → CotangentBundle I M) (p : ℝ × N) : CotangentBundle I M :=
  ⟨(ι p.2).proj, Real.exp p.1 • (ι p.2).2⟩

omit [IsManifold J ∞ N] in
private theorem contMDiff_expSMul (hι : ContMDiff J (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ ι) :
    ContMDiff (𝓘(ℝ).prod J) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (expSMul ι) :=
  (Real.contDiff_exp.contMDiff.comp contMDiff_fst).smul_totalSpace (hι.comp contMDiff_snd)

/-- The map `(t, y) ↦ eᵗ ι(y)` pulls the Liouville form back to the symplectization form of
`ι^* λ`. -/
private theorem mpullback_expSMul_liouvilleForm
    (hι : ContMDiff J (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ ι) :
    SmoothForm.mpullback (expSMul ι) (contMDiff_expSMul hι) (liouvilleForm I M) =
      (SmoothForm.mpullback ι hι (liouvilleForm I M)).symplectization := by
  apply Subtype.ext
  funext p
  -- `expSMul ι p` is `eᵗ` times the covector `ι p.2`, over the same base point.
  rw [mpullback_liouvilleForm_apply_of_eq_smul (contMDiff_expSMul hι) (hι.comp contMDiff_snd)
    (fun p : ℝ × N ↦ Real.exp p.1) (fun _ ↦ rfl) p, SmoothForm.coe_symplectization,
    SmoothForm.mpullback_mpullback]

/-- The map `(t, y) ↦ eᵗ ι(y)` pulls `-λ` back to the symplectization form of `ι^* (-λ)`. -/
private theorem mpullback_expSMul_neg_liouvilleForm
    (hι : ContMDiff J (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ ι) :
    SmoothForm.mpullback (expSMul ι) (contMDiff_expSMul hι) (-liouvilleForm I M) =
      (SmoothForm.mpullback ι hι (-liouvilleForm I M)).symplectization := by
  rw [map_neg, map_neg, mpullback_expSMul_liouvilleForm, SmoothForm.symplectization_neg]

/-- The map `(t, y) ↦ eᵗ ι(y)` pulls `ω = -dλ` back to the exterior derivative of the
symplectization form of `ι^* (-λ)`. -/
private theorem mpullback_expSMul_symplecticForm
    (hι : ContMDiff J (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ ι) :
    SmoothForm.mpullback (expSMul ι) (contMDiff_expSMul hι) (symplecticForm I M) =
      mextDerivₗ (𝓘(ℝ).prod J) 1
        (SmoothForm.mpullback ι hι (-liouvilleForm I M)).symplectization := by
  rw [symplecticForm_eq_neg_mextDerivₗ, ← map_neg, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_expSMul_neg_liouvilleForm]

/-- The map `(t, y) ↦ eᵗ ι(y)` pulls `-ω = dλ` back to the exterior derivative of the
symplectization form of `ι^* λ`. -/
private theorem mpullback_expSMul_neg_symplecticForm
    (hι : ContMDiff J (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ ι) :
    SmoothForm.mpullback (expSMul ι) (contMDiff_expSMul hι) (-symplecticForm I M) =
      mextDerivₗ (𝓘(ℝ).prod J) 1
        (SmoothForm.mpullback ι hι (liouvilleForm I M)).symplectization := by
  rw [symplecticForm_eq_neg_mextDerivₗ, neg_neg, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_expSMul_liouvilleForm]

end ExpSMul

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ### The punctured cotangent bundle -/

variable (I M) in
/-- The **punctured cotangent bundle** `T*M \ 0`, the open set of covectors other than zero. -/
def punctured : Opens (CotangentBundle I M) where
  carrier := {z | z.2 ≠ 0}
  is_open' := by
    have : {z : CotangentBundle I M | z.2 ≠ 0} = {z | ‖z.2‖ ≠ 0} := by
      ext z
      exact (norm_ne_zero_iff (a := z.2)).symm
    rw [this]
    exact isOpen_ne_fun continuous_norm_snd continuous_const

omit [I.Boundaryless] in
@[simp]
theorem mem_punctured {z : CotangentBundle I M} : z ∈ punctured I M ↔ z.2 ≠ 0 :=
  Iff.rfl

/-! ### The radial map and its inverse -/

/-- The radial map `(t, z) ↦ eᵗ z` from the symplectization of the unit cosphere bundle to the
cotangent bundle. -/
private abbrev radial : ℝ × cosphereBundle I M → CotangentBundle I M :=
  expSMul Subtype.val

private theorem contMDiff_radial :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (radial (I := I) (M := M)) :=
  contMDiff_expSMul isSmoothEmbedding_coe_cosphereBundle.contMDiff

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The norm of `eᵗ z` is `eᵗ` for a unit covector `z`. -/
private theorem norm_snd_radial (p : ℝ × cosphereBundle I M) :
    ‖(radial p).2‖ = Real.exp p.1 := by
  -- This is `norm_smul`; instance search does not find `NormSMulClass` for covectors of the
  -- Riemannian fibre norm, so it is supplied from the `NormedSpace` instance.
  rw [radial, expSMul, ((NormedSpace.toNormSMulClass (𝕜 := ℝ)
      (E := TangentSpace I p.2.1.proj →L[ℝ] ℝ)).norm_smul (Real.exp p.1) p.2.1.2),
    mem_cosphereBundle.1 p.2.2, mul_one, Real.norm_of_nonneg (Real.exp_pos p.1).le]

omit [I.Boundaryless] in
private theorem radial_mem_punctured (p : ℝ × cosphereBundle I M) :
    radial p ∈ punctured I M :=
  (norm_ne_zero_iff (a := (radial p).2)).1
    (by rw [norm_snd_radial]; exact (Real.exp_pos p.1).ne')

/-- The inverse of the radial map: a nonzero covector `q` goes to `(log ‖q‖, q / ‖q‖)`. -/
private def unradial (q : punctured I M) : ℝ × cosphereBundle I M :=
  (Real.log ‖q.1.2‖, ⟨⟨q.1.proj, NormedSpace.normalize q.1.2⟩,
    NormedSpace.norm_normalize (V := TangentSpace I q.1.proj →L[ℝ] ℝ) (mem_punctured.1 q.2)⟩)

omit [I.Boundaryless] in
private theorem unradial_radial (p : ℝ × cosphereBundle I M) :
    unradial ⟨radial p, radial_mem_punctured p⟩ = p := by
  obtain ⟨t, z⟩ := p
  ext1
  · simp only [unradial, norm_snd_radial, Real.log_exp]
  · apply Subtype.ext
    have h : NormedSpace.normalize (V := TangentSpace I z.1.proj →L[ℝ] ℝ) (Real.exp t • z.1.2) =
        z.1.2 := by
      rw [NormedSpace.normalize_smul_of_pos (Real.exp_pos t),
        NormedSpace.normalize_eq_self_of_norm_eq_one (mem_cosphereBundle.1 z.2)]
    exact congrArg (TotalSpace.mk' (E →L[ℝ] ℝ) z.1.proj) h

omit [I.Boundaryless] in
private theorem radial_unradial (q : punctured I M) : radial (unradial q) = q.1 := by
  have hq : 0 < ‖q.1.2‖ := (norm_pos_iff (a := q.1.2)).2 (mem_punctured.1 q.2)
  simp only [radial, expSMul, unradial, Real.exp_log hq]
  exact congrArg (TotalSpace.mk' (E →L[ℝ] ℝ) q.1.proj)
    (NormedSpace.norm_smul_normalize (V := TangentSpace I q.1.proj →L[ℝ] ℝ) q.1.2)

private theorem contMDiff_unradial :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (𝓘(ℝ).prod 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ)) ∞
      (unradial (I := I) (M := M)) := by
  have : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have hval : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (Subtype.val : punctured I M → CotangentBundle I M) :=
    contMDiff_subtype_val
  -- The norm of covectors is smooth and positive on the punctured bundle.
  have hnorm : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) ∞
      (fun q : punctured I M ↦ ‖q.1.2‖) := fun q ↦
    (contMDiffAt_norm_snd (n := ∞) (mem_punctured.1 q.2)).comp q (hval q)
  have hne (q : punctured I M) : ‖q.1.2‖ ≠ 0 :=
    (norm_ne_zero_iff (a := q.1.2)).2 (mem_punctured.1 q.2)
  have hlog : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) ∞
      (fun q : punctured I M ↦ Real.log ‖q.1.2‖) :=
    hnorm.log hne
  have hinv : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) ∞
      (fun q : punctured I M ↦ ‖q.1.2‖⁻¹) := fun q ↦ (hnorm q).inv₀ (hne q)
  -- The normalized covector, read in the cotangent bundle.
  have hnormalize := hinv.smul_totalSpace hval
  have hsphere : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) ∞
      (fun q : punctured I M ↦ (unradial q).2) :=
    (ContMDiff.iff_comp_isImmersion isSmoothEmbedding_coe_cosphereBundle.isImmersion).2
      ⟨hnormalize.continuous.subtype_mk _, hnormalize⟩
  exact hlog.prodMk hsphere

/-! ### The radial diffeomorphism -/

variable (I M) in
/-- **The punctured cotangent bundle is the symplectization of the unit cosphere bundle.** The
radial diffeomorphism `ℝ × S*M ≃ T*M \ 0` sends `(t, z)` to the covector `eᵗ z`; its inverse
sends a nonzero covector `q` to `(log ‖q‖, q / ‖q‖)`. -/
def cosphereSymplectization :
    (ℝ × cosphereBundle I M) ≃ₘ⟮𝓘(ℝ).prod 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ),
      I.prod 𝓘(ℝ, E →L[ℝ] ℝ)⟯ punctured I M where
  toFun p := ⟨radial p, radial_mem_punctured p⟩
  invFun := unradial
  left_inv := unradial_radial
  right_inv q := Subtype.ext (radial_unradial q)
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff (punctured I M) _).1 contMDiff_radial
  contMDiff_invFun := contMDiff_unradial

/-- The radial diffeomorphism multiplies a unit covector `z` by `eᵗ`. -/
@[simp]
theorem coe_cosphereSymplectization_apply (p : ℝ × cosphereBundle I M) :
    (cosphereSymplectization I M p : CotangentBundle I M) =
      TotalSpace.mk' (E →L[ℝ] ℝ) p.2.1.proj (Real.exp p.1 • p.2.1.2) :=
  (rfl)

/-- The inverse of the radial diffeomorphism sends a nonzero covector `q` to
`(log ‖q‖, q / ‖q‖)`. -/
@[simp]
theorem cosphereSymplectization_symm_apply (q : punctured I M) :
    (cosphereSymplectization I M).symm q =
      (Real.log ‖q.1.2‖, ⟨TotalSpace.mk' (E →L[ℝ] ℝ) q.1.proj (‖q.1.2‖⁻¹ • q.1.2),
        NormedSpace.norm_normalize (V := TangentSpace I q.1.proj →L[ℝ] ℝ)
          (mem_punctured.1 q.2)⟩) :=
  (rfl)

/-- The norm of the covector `eᵗ z` is `eᵗ`: the radial coordinate `r = eᵗ` of the
symplectization is the norm of covectors. -/
@[simp]
theorem norm_snd_cosphereSymplectization (p : ℝ × cosphereBundle I M) :
    ‖(cosphereSymplectization I M p).1.2‖ = Real.exp p.1 :=
  norm_snd_radial p

/-! ### Pullbacks of the Liouville and symplectic forms -/

/-- Pulling a form on `T*M` back to `ℝ × S*M` through the punctured bundle is pulling it back
along the radial map. -/
private theorem mpullback_cosphereSymplectization_mpullback_subtypeVal {k : ℕ}
    (φ : SmoothForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I M) ℝ k) :
    SmoothForm.mpullback (cosphereSymplectization I M) (cosphereSymplectization I M).contMDiff
        (SmoothForm.mpullback (Subtype.val : punctured I M → CotangentBundle I M)
          contMDiff_subtype_val φ) =
      SmoothForm.mpullback radial contMDiff_radial φ := by
  -- The composite of the inclusion with the radial diffeomorphism is the radial map.
  rw [SmoothForm.mpullback_mpullback]
  rfl

/-- **The radial diffeomorphism pulls the Liouville form back to the symplectization form of
`α_g = λ|S*M`**: `Φ^* λ = eᵗ α_g`. -/
theorem mpullback_cosphereSymplectization_liouvilleForm :
    SmoothForm.mpullback (cosphereSymplectization I M) (cosphereSymplectization I M).contMDiff
        (SmoothForm.mpullback (Subtype.val : punctured I M → CotangentBundle I M)
          contMDiff_subtype_val (liouvilleForm I M)) =
      (SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
        isSmoothEmbedding_coe_cosphereBundle.contMDiff (liouvilleForm I M)).symplectization := by
  rw [mpullback_cosphereSymplectization_mpullback_subtypeVal, mpullback_expSMul_liouvilleForm]

/-- **The radial diffeomorphism pulls the primitive `-λ` back to the symplectization form of the
contact form `α_b = -λ|S*M`**: `Φ^* (-λ) = eᵗ α_b`. -/
theorem mpullback_cosphereSymplectization_neg_liouvilleForm :
    SmoothForm.mpullback (cosphereSymplectization I M) (cosphereSymplectization I M).contMDiff
        (SmoothForm.mpullback (Subtype.val : punctured I M → CotangentBundle I M)
          contMDiff_subtype_val (-liouvilleForm I M)) =
      (SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
        isSmoothEmbedding_coe_cosphereBundle.contMDiff
        (-liouvilleForm I M)).symplectization := by
  rw [mpullback_cosphereSymplectization_mpullback_subtypeVal,
    mpullback_expSMul_neg_liouvilleForm]

/-- **The punctured cotangent bundle is symplectomorphic to the symplectization of
`(S*M, α_b)`.** The radial diffeomorphism pulls the canonical symplectic form `ω = -dλ` back to
`d(eᵗ α_b)`, the exterior derivative of the symplectization form of `α_b = -λ|S*M`. -/
theorem mpullback_cosphereSymplectization_symplecticForm :
    SmoothForm.mpullback (cosphereSymplectization I M) (cosphereSymplectization I M).contMDiff
        (SmoothForm.mpullback (Subtype.val : punctured I M → CotangentBundle I M)
          contMDiff_subtype_val (symplecticForm I M)) =
      mextDerivₗ (𝓘(ℝ).prod 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ)) 1
        (SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
          isSmoothEmbedding_coe_cosphereBundle.contMDiff
          (-liouvilleForm I M)).symplectization := by
  rw [mpullback_cosphereSymplectization_mpullback_subtypeVal,
    mpullback_expSMul_symplecticForm]

/-- **The radial diffeomorphism is anti-symplectic for the symplectization of `(S*M, α_g)`.** It
pulls minus the canonical symplectic form, `-ω = dλ`, back to `d(eᵗ α_g)`, the exterior derivative
of the symplectization form of `α_g = λ|S*M`. -/
theorem mpullback_cosphereSymplectization_neg_symplecticForm :
    SmoothForm.mpullback (cosphereSymplectization I M) (cosphereSymplectization I M).contMDiff
        (SmoothForm.mpullback (Subtype.val : punctured I M → CotangentBundle I M)
          contMDiff_subtype_val (-symplecticForm I M)) =
      mextDerivₗ (𝓘(ℝ).prod 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ)) 1
        (SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
          isSmoothEmbedding_coe_cosphereBundle.contMDiff
          (liouvilleForm I M)).symplectization := by
  rw [mpullback_cosphereSymplectization_mpullback_subtypeVal,
    mpullback_expSMul_neg_symplecticForm]

end CotangentBundle

end TauCeti
