/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Symplectization.Cotangent
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ContactType
public import TauCeti.Topology.VectorBundle.ZeroSection

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

(`TauCeti.CotangentBundle.cosphereSymplectizationDiffeomorph`). Its inverse sends a nonzero
covector `q` to `(log ‖q‖, q / ‖q‖)`, so `r = eᵗ` is the norm of covectors. The punctured bundle
does not depend on the metric; only `Φ` does.

Since `Φ` multiplies a unit covector by `eᵗ` without moving its base point, it pulls `λ` back to
`eᵗ λ|S*M`, the symplectization form `eᵗ α_g` of `TauCeti.SmoothForm.symplectization`
(`TauCeti.CotangentBundle.mpullback_cosphereSymplectizationDiffeomorph_liouvilleForm`), and `-λ`
back to `θ = eᵗ α_b`. Taking exterior derivatives, `Φ` pulls the canonical form `ω = -dλ` back
to `dθ`:

`Φ^* ω = d(eᵗ α_b)`

(`TauCeti.CotangentBundle.mpullback_cosphereSymplectizationDiffeomorph_symplecticForm`). So `Φ` is
a symplectomorphism from the symplectization of the contact manifold `(S*M, α_b)` onto
`(T*M \ 0, ω)`. For the opposite contact form `α_g` the same map pulls `ω` back to
`-d(eᵗ α_g)`, so it is anti-symplectic for the symplectization form `d(eᵗ α_g)`
(`TauCeti.CotangentBundle.mpullback_cosphereSymplectizationDiffeomorph_neg_symplecticForm`). In
the coordinate `r = eᵗ` these read `Φ^* ω = d(r α_b) = -d(r α_g)`.

The curve `t ↦ eᵗ z` is the integral curve through `z` of the radial field `Z = p ∂_p`
(`TauCeti.isMIntegralCurve_vectorBundleEulerField`), the Liouville field of the primitive `-λ` of
`ω` (`TauCeti.CotangentBundle.symplecticForm_interior_vectorBundleEulerField`). So `Φ` is the
Liouville flow map of `S*M`, and `Φ^* (-λ) = eᵗ α_b` is the cotangent case of the identity for
Liouville flows of `TauCeti.mpullback_globalFlow_comp_eq_symplectization`. Here it is proved
directly: the Liouville form is linear on fibres, so it pulls back along `(t, y) ↦ eᵗ ι(y)` to
`eᵗ ι^* λ` for every smooth family `ι` of covectors, with no flow or completeness argument
(`TauCeti.CotangentBundle.mpullback_expSMul_liouvilleForm`).

## Main definitions

* `TauCeti.CotangentBundle.punctured`: the open set `T*M \ 0` of nonzero covectors.
* `TauCeti.CotangentBundle.cosphereSymplectizationDiffeomorph`: the radial diffeomorphism
  `ℝ × S*M ≃ T*M \ 0`, `(t, z) ↦ eᵗ z`.

## Main results

* `TauCeti.CotangentBundle.coe_cosphereSymplectizationDiffeomorph_apply`,
  `TauCeti.CotangentBundle.cosphereSymplectizationDiffeomorph_symm_apply`: the formulas for `Φ`
  and its inverse.
* `TauCeti.CotangentBundle.mpullback_cosphereSymplectizationDiffeomorph_liouvilleForm`,
  `TauCeti.CotangentBundle.mpullback_cosphereSymplectizationDiffeomorph_neg_liouvilleForm`: `Φ`
  pulls `λ` and `-λ` back to `eᵗ α_g` and `eᵗ α_b`.
* `TauCeti.CotangentBundle.mpullback_cosphereSymplectizationDiffeomorph_symplecticForm`: `Φ` pulls
  `ω` back to `d(eᵗ α_b)`.
* `TauCeti.CotangentBundle.mpullback_cosphereSymplectizationDiffeomorph_neg_symplecticForm`: `Φ`
  pulls `-ω` back to `d(eᵗ α_g)`.

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

/-! ### The punctured cotangent bundle -/

section Punctured

omit [IsManifold I ∞ M]

variable [IsManifold I 1 M]

variable (I M) in
/-- The **punctured cotangent bundle** `T*M \ 0`, the open set of covectors other than zero
(`TauCeti.zeroSectionCompl`). It does not depend on a metric. -/
def punctured : Opens (CotangentBundle I M) :=
  ⟨zeroSectionCompl (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ),
    isOpen_zeroSectionCompl _ _⟩

@[simp]
theorem mem_punctured {z : CotangentBundle I M} : z ∈ punctured I M ↔ z.snd ≠ 0 :=
  mem_zeroSectionCompl

end Punctured

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

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
    ‖(radial p).snd‖ = Real.exp p.1 := by
  rw [radial, expSMul_apply, norm_smul_snd (Real.exp p.1) p.2.val,
    mem_cosphereBundle.1 p.2.property, mul_one, Real.norm_of_nonneg (Real.exp_pos p.1).le]

omit [FiniteDimensional ℝ E] [I.Boundaryless]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
private theorem radial_mem_punctured (p : ℝ × cosphereBundle I M) :
    radial p ∈ punctured I M :=
  mem_punctured.2 <| (norm_ne_zero_iff (a := (radial p).snd)).1
    (by rw [norm_snd_radial]; exact (Real.exp_pos p.1).ne')

/-- The inverse of the radial map: a nonzero covector `q` goes to `(log ‖q‖, q / ‖q‖)`. -/
private def unradial (q : punctured I M) : ℝ × cosphereBundle I M :=
  (Real.log ‖q.val.snd‖,
    ⟨normalize q.val, normalize_mem_cosphereBundle (mem_punctured.1 q.property)⟩)

omit [FiniteDimensional ℝ E] [I.Boundaryless]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
private theorem unradial_radial (p : ℝ × cosphereBundle I M) :
    unradial ⟨radial p, radial_mem_punctured p⟩ = p := by
  obtain ⟨t, z⟩ := p
  ext1
  · simp only [unradial, norm_snd_radial, Real.log_exp]
  · apply Subtype.ext
    simp only [unradial, radial, expSMul_apply]
    exact (normalize_mk_smul_of_pos z.val (Real.exp_pos t)).trans
      (normalize_eq_self_of_norm_eq_one z.property)

omit [FiniteDimensional ℝ E] [I.Boundaryless]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
private theorem radial_unradial (q : punctured I M) : radial (unradial q) = q.val := by
  have hq : 0 < ‖q.val.snd‖ := (norm_pos_iff (a := q.val.snd)).2 (mem_punctured.1 q.property)
  -- The radial map rescales the normalized covector `‖q‖⁻¹ • q` by `e^(log ‖q‖) = ‖q‖`.
  rw [radial, expSMul_apply]
  refine CotangentBundle.ext (proj_normalize q.val) fun v ↦ ?_
  simp only [unradial, snd_normalize, Real.exp_log hq]
  exact congrArg (· v)
    (NormedSpace.norm_smul_normalize (V := TangentSpace I q.val.proj →L[ℝ] ℝ) q.val.snd)

private theorem contMDiff_unradial :
    ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (𝓘(ℝ).prod 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ)) ∞
      (unradial (I := I) (M := M)) := by
  have : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have hval : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (Subtype.val : punctured I M → CotangentBundle I M) :=
    contMDiff_subtypeVal
  -- The logarithm of the norm of covectors is smooth on the punctured bundle.
  have hlog : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) ∞
      (fun q : punctured I M ↦ Real.log ‖q.val.snd‖) :=
    ContMDiff.log
      (fun q ↦ (contMDiffAt_norm_snd (n := ∞) (mem_punctured.1 q.property)).comp q (hval q))
      fun q ↦ (norm_ne_zero_iff (a := q.val.snd)).2 (mem_punctured.1 q.property)
  exact hlog.prodMk (contMDiff_normalize_cosphereBundle hval fun q ↦ mem_punctured.1 q.property)

/-! ### The radial diffeomorphism -/

variable (I M) in
/-- **The punctured cotangent bundle is the symplectization of the unit cosphere bundle.** The
radial diffeomorphism `ℝ × S*M ≃ T*M \ 0` sends `(t, z)` to the covector `eᵗ z`; its inverse
sends a nonzero covector `q` to `(log ‖q‖, q / ‖q‖)`. -/
def cosphereSymplectizationDiffeomorph :
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
theorem coe_cosphereSymplectizationDiffeomorph_apply (p : ℝ × cosphereBundle I M) :
    (cosphereSymplectizationDiffeomorph I M p : CotangentBundle I M) =
      TotalSpace.mk' (E →L[ℝ] ℝ) p.2.val.proj (Real.exp p.1 • p.2.val.snd) :=
  expSMul_apply Subtype.val p

/-- The inverse of the radial diffeomorphism sends a nonzero covector `q` to
`(log ‖q‖, q / ‖q‖)`. -/
@[simp]
theorem cosphereSymplectizationDiffeomorph_symm_apply (q : punctured I M) :
    (cosphereSymplectizationDiffeomorph I M).symm q =
      (Real.log ‖q.val.snd‖,
        ⟨normalize q.val, normalize_mem_cosphereBundle (mem_punctured.1 q.property)⟩) :=
  (rfl)

/-- The norm of the covector `eᵗ z` is `eᵗ`: the radial coordinate `r = eᵗ` of the
symplectization is the norm of covectors. -/
@[simp]
theorem norm_snd_cosphereSymplectizationDiffeomorph (p : ℝ × cosphereBundle I M) :
    ‖(cosphereSymplectizationDiffeomorph I M p).val.snd‖ = Real.exp p.1 :=
  norm_snd_radial p

/-! ### Pullbacks of the Liouville and symplectic forms -/

/-- Pulling a form on `T*M` back to `ℝ × S*M` through the punctured bundle is pulling it back
along the radial map. -/
private theorem mpullback_cosphereSymplectizationDiffeomorph_mpullback_subtypeVal {k : ℕ}
    (φ : SmoothForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I M) ℝ k) :
    SmoothForm.mpullback (cosphereSymplectizationDiffeomorph I M)
        (cosphereSymplectizationDiffeomorph I M).contMDiff
        (SmoothForm.mpullback (Subtype.val : punctured I M → CotangentBundle I M)
          contMDiff_subtypeVal φ) =
      SmoothForm.mpullback radial contMDiff_radial φ := by
  -- The composite of the inclusion with the radial diffeomorphism is the radial map.
  have hcomp : Subtype.val ∘ ⇑(cosphereSymplectizationDiffeomorph I M) = radial :=
    funext fun p ↦ (coe_cosphereSymplectizationDiffeomorph_apply p).trans
      (expSMul_apply Subtype.val p).symm
  simp only [SmoothForm.mpullback_mpullback, hcomp]

/-- **The radial diffeomorphism pulls the Liouville form back to the symplectization form of
`α_g = λ|S*M`**: `Φ^* λ = eᵗ α_g`. -/
theorem mpullback_cosphereSymplectizationDiffeomorph_liouvilleForm :
    SmoothForm.mpullback (cosphereSymplectizationDiffeomorph I M)
        (cosphereSymplectizationDiffeomorph I M).contMDiff
        (SmoothForm.mpullback (Subtype.val : punctured I M → CotangentBundle I M)
          contMDiff_subtypeVal (liouvilleForm I M)) =
      (SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
        isSmoothEmbedding_coe_cosphereBundle.contMDiff (liouvilleForm I M)).symplectization := by
  rw [mpullback_cosphereSymplectizationDiffeomorph_mpullback_subtypeVal,
    mpullback_expSMul_liouvilleForm]

/-- **The radial diffeomorphism pulls the primitive `-λ` back to the symplectization form of the
contact form `α_b = -λ|S*M`**: `Φ^* (-λ) = eᵗ α_b`. -/
theorem mpullback_cosphereSymplectizationDiffeomorph_neg_liouvilleForm :
    SmoothForm.mpullback (cosphereSymplectizationDiffeomorph I M)
        (cosphereSymplectizationDiffeomorph I M).contMDiff
        (SmoothForm.mpullback (Subtype.val : punctured I M → CotangentBundle I M)
          contMDiff_subtypeVal (-liouvilleForm I M)) =
      (SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
        isSmoothEmbedding_coe_cosphereBundle.contMDiff
        (-liouvilleForm I M)).symplectization := by
  rw [mpullback_cosphereSymplectizationDiffeomorph_mpullback_subtypeVal,
    mpullback_expSMul_neg_liouvilleForm]

/-- **The punctured cotangent bundle is symplectomorphic to the symplectization of
`(S*M, α_b)`.** The radial diffeomorphism pulls the canonical symplectic form `ω = -dλ` back to
`d(eᵗ α_b)`, the exterior derivative of the symplectization form of `α_b = -λ|S*M`. -/
theorem mpullback_cosphereSymplectizationDiffeomorph_symplecticForm :
    SmoothForm.mpullback (cosphereSymplectizationDiffeomorph I M)
        (cosphereSymplectizationDiffeomorph I M).contMDiff
        (SmoothForm.mpullback (Subtype.val : punctured I M → CotangentBundle I M)
          contMDiff_subtypeVal (symplecticForm I M)) =
      mextDerivₗ (𝓘(ℝ).prod 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ)) 1
        (SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
          isSmoothEmbedding_coe_cosphereBundle.contMDiff
          (-liouvilleForm I M)).symplectization := by
  rw [mpullback_cosphereSymplectizationDiffeomorph_mpullback_subtypeVal,
    mpullback_expSMul_symplecticForm]

/-- **The radial diffeomorphism is anti-symplectic for the symplectization of `(S*M, α_g)`.** It
pulls minus the canonical symplectic form, `-ω = dλ`, back to `d(eᵗ α_g)`, the exterior derivative
of the symplectization form of `α_g = λ|S*M`. -/
theorem mpullback_cosphereSymplectizationDiffeomorph_neg_symplecticForm :
    SmoothForm.mpullback (cosphereSymplectizationDiffeomorph I M)
        (cosphereSymplectizationDiffeomorph I M).contMDiff
        (SmoothForm.mpullback (Subtype.val : punctured I M → CotangentBundle I M)
          contMDiff_subtypeVal (-symplecticForm I M)) =
      mextDerivₗ (𝓘(ℝ).prod 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ)) 1
        (SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
          isSmoothEmbedding_coe_cosphereBundle.contMDiff
          (liouvilleForm I M)).symplectization := by
  rw [mpullback_cosphereSymplectizationDiffeomorph_mpullback_subtypeVal,
    mpullback_expSMul_neg_symplecticForm]

end CotangentBundle

end TauCeti
