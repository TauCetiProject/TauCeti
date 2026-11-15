/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ContactType
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift

/-!
# Radial identification of unit cosphere bundles

Let `h : M → N` be a smooth diffeomorphism between Riemannian manifolds without boundary. Its
cotangent lift `T*h` sends a nonzero covector to a nonzero covector, but in general does not
preserve the norms of covectors. Rescaling each lifted covector to norm one gives the **radial
identification** of the unit cosphere bundles

`ρ_h : S*M → S*N`, `ρ_h(z) = T*h(z) / ‖T*h(z)‖`

(`Diffeomorph.cosphereRadial h`). It is a smooth diffeomorphism, with inverse `ρ_(h⁻¹)`
(`Diffeomorph.cosphereRadial_symm`), and it is functorial in `h`
(`Diffeomorph.cosphereRadial_trans`), because `T*h` is linear on fibres and normalization only
depends on the ray of a covector. The case of two metrics `g₀` and `g₁` on one manifold `M` is
`h = TauCeti.WithMetric.diffeomorphWithMetric g₀ g₁ ∞`, the identity of `M` between the copies
of `M` carrying the two metrics: then `ρ_h(p) = p / ‖p‖_(g₁)` on covectors of `g₀`-norm one.

The cosphere bundles carry the two contact forms `α_g = λ|S*` and `α_b = -λ|S*` of opposite
coorientations
(`TauCeti.CotangentBundle.isContactForm_mpullback_liouvilleForm_cosphereBundle`). Since `T*h`
preserves the Liouville form `λ` and dividing a covector by `r` divides `λ` by `r`, the radial
identification pulls each of them back to a positive multiple of the corresponding form:

`ρ_h^* α_g = ‖T*h(z)‖⁻¹ • α_g`, `ρ_h^* α_b = ‖T*h(z)‖⁻¹ • α_b`

(`Diffeomorph.mpullback_cosphereRadial_liouvilleForm_apply`,
`Diffeomorph.mpullback_cosphereRadial_neg_liouvilleForm_apply`). Consequently `ρ_h` carries the
contact hyperplanes of `S*M` onto those of `S*N`
(`Diffeomorph.kerDistribution_mpullback_cosphereRadial_liouvilleForm`) and preserves both
coorientations: a tangent vector is on the positive side of `α_g` exactly when its image is
(`Diffeomorph.pos_mpullback_cosphereRadial_liouvilleForm_iff`), and likewise for `α_b`.

## Main definitions

* `Diffeomorph.cosphereRadial h`: the radial identification `S*M ≃ S*N` of a diffeomorphism.

## Main results

* `Diffeomorph.coe_cosphereRadial_apply`, `Diffeomorph.cosphereRadial_symm`,
  `Diffeomorph.cosphereRadial_refl`, `Diffeomorph.cosphereRadial_trans`: the formula, the inverse
  and functoriality.
* `Diffeomorph.mpullback_cosphereRadial_liouvilleForm_apply` and
  `Diffeomorph.mpullback_cosphereRadial_neg_liouvilleForm_apply`: the pullbacks of `α_g` and `α_b`.
* `Diffeomorph.kerDistribution_mpullback_cosphereRadial_liouvilleForm`: preservation of the
  contact hyperplanes.
* `Diffeomorph.pos_mpullback_cosphereRadial_liouvilleForm_iff` and
  `Diffeomorph.pos_mpullback_cosphereRadial_neg_liouvilleForm_iff`: preservation of the
  coorientations.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 1.2 (the space of cooriented contact elements, which does not depend on a
  metric).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (the unit cotangent bundle as a hypersurface of contact type).
-/

public section

noncomputable section

open Bundle Module TauCeti TauCeti.CotangentBundle
open scoped Manifold ContDiff

namespace Diffeomorph

section Normalize

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- The covector of norm one on the ray of a covector `q` (`NormedSpace.normalize` on fibres). -/
private def normalize (q : CotangentBundle J N) : CotangentBundle J N :=
  TotalSpace.mk' (F →L[ℝ] ℝ) q.proj (NormedSpace.normalize q.2)

/-- The normalization of a covector other than zero has norm one. -/
private theorem norm_snd_normalize {q : CotangentBundle J N} (hq : q.2 ≠ 0) :
    ‖(normalize q).2‖ = 1 :=
  NormedSpace.norm_normalize (V := TangentSpace J q.proj →L[ℝ] ℝ) hq

/-- Normalization only depends on the ray of a covector. -/
private theorem normalize_mk_smul (q : CotangentBundle J N) {c : ℝ} (hc : 0 < c) :
    normalize (TotalSpace.mk' (F →L[ℝ] ℝ) q.proj (c • q.2)) = normalize q := by
  simp only [normalize, NormedSpace.normalize_smul_of_pos hc]

/-- A covector of norm one is its own normalization. -/
private theorem normalize_of_norm_eq_one {q : CotangentBundle J N} (hq : ‖q.2‖ = 1) :
    normalize q = q := by
  rw [normalize, NormedSpace.normalize_eq_self_of_norm_eq_one hq]

end Normalize

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

section Map

variable [IsManifold I 2 M] [IsManifold J 2 N]

/-- Normalizing before a cotangent lift does not change the normalized lift, since the lift is
linear on fibres. -/
private theorem normalize_cotangent_normalize (h : M ≃ₘ⟮I, J⟯ N) {q : CotangentBundle I M}
    (hq : q.2 ≠ 0) : normalize (h.cotangent (normalize q)) = normalize (h.cotangent q) := by
  rw [normalize.eq_1 q, NormedSpace.normalize, cotangent_mk_smul,
    normalize_mk_smul (h.cotangent q) (c := ‖q.2‖⁻¹) (inv_pos.2 ((norm_pos_iff (a := q.2)).2 hq))]

/-- The cotangent lift of a covector of norm one, normalized to norm one. -/
private def cosphereRadialMap (h : M ≃ₘ⟮I, J⟯ N) (z : cosphereBundle I M) : cosphereBundle J N :=
  ⟨normalize (h.cotangent z.1), norm_snd_normalize
    ((h.cotangent_snd_eq_zero_iff).not.2 (snd_ne_zero_of_mem_cosphereBundle z.2))⟩

private theorem coe_cosphereRadialMap (h : M ≃ₘ⟮I, J⟯ N) (z : cosphereBundle I M) :
    (cosphereRadialMap h z : CotangentBundle J N) = normalize (h.cotangent z.1) :=
  (rfl)

private theorem cosphereRadialMap_symm_cosphereRadialMap (h : M ≃ₘ⟮I, J⟯ N)
    (z : cosphereBundle I M) : cosphereRadialMap h.symm (cosphereRadialMap h z) = z := by
  have hz : (h.cotangent z.1).2 ≠ 0 :=
    (h.cotangent_snd_eq_zero_iff).not.2 (snd_ne_zero_of_mem_cosphereBundle z.2)
  apply Subtype.ext
  -- Lifting back the normalized covector gives a positive multiple of `z`, by fibre linearity.
  rw [coe_cosphereRadialMap, coe_cosphereRadialMap, normalize_cotangent_normalize _ hz,
    ← cotangent_symm, symm_apply_apply, normalize_of_norm_eq_one z.2]

/-- The scale `‖T*h(z)‖⁻¹` of the radial identification is positive. -/
private theorem inv_norm_cotangent_snd_pos (h : M ≃ₘ⟮I, J⟯ N) (z : cosphereBundle I M) :
    0 < ‖(h.cotangent z.1).2‖⁻¹ :=
  inv_pos.2 ((norm_pos_iff (a := (h.cotangent z.1).2)).2
    ((h.cotangent_snd_eq_zero_iff).not.2 (snd_ne_zero_of_mem_cosphereBundle z.2)))

end Map

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ F] [J.Boundaryless] [IsManifold J ∞ N]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

private theorem contMDiff_cosphereRadialMap (h : M ≃ₘ⟮I, J⟯ N) :
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ)
      𝓘(ℝ, Fin (finrank ℝ (F × (F →L[ℝ] ℝ)) - 1) → ℝ) ∞ (cosphereRadialMap h) := by
  have : IsManifold J (∞ + 1) N := IsManifold.of_le (n := ∞) (by simp)
  have hψ : ContMDiff 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      fun z : cosphereBundle I M ↦ h.cotangent z.1 :=
    h.cotangent.contMDiff.comp isSmoothEmbedding_coe_cosphereBundle.contMDiff
  have hc : ContMDiff 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) 𝓘(ℝ) ∞
      fun z : cosphereBundle I M ↦ ‖(h.cotangent z.1).2‖⁻¹ := fun z ↦ by
    have hz : (h.cotangent z.1).2 ≠ 0 :=
      (h.cotangent_snd_eq_zero_iff).not.2 (snd_ne_zero_of_mem_cosphereBundle z.2)
    have hn : ContMDiffAt 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) 𝓘(ℝ) ∞
        (fun z : cosphereBundle I M ↦ ‖(h.cotangent z.1).2‖) z :=
      ContMDiffAt.comp (g := fun q : CotangentBundle J N ↦ ‖q.2‖) z
        (contMDiffAt_norm_snd (n := ∞) hz) (hψ z)
    exact hn.inv₀ ((norm_ne_zero_iff (a := (h.cotangent z.1).2)).2 hz)
  have hval := hc.smul_totalSpace hψ
  exact (ContMDiff.iff_comp_isImmersion isSmoothEmbedding_coe_cosphereBundle.isImmersion).2
    ⟨hval.continuous.subtype_mk _, hval⟩

/-- The **radial identification** of the unit cosphere bundles of Riemannian manifolds along a
smooth diffeomorphism `h : M → N`: it sends a unit covector `z` to `T*h(z) / ‖T*h(z)‖`, the unit
covector on the ray of its cotangent lift. -/
def cosphereRadial (h : M ≃ₘ⟮I, J⟯ N) :
    cosphereBundle I M ≃ₘ⟮𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ (F × (F →L[ℝ] ℝ)) - 1) → ℝ)⟯ cosphereBundle J N where
  toFun := cosphereRadialMap h
  invFun := cosphereRadialMap h.symm
  left_inv := cosphereRadialMap_symm_cosphereRadialMap h
  -- `h.symm.symm` is `h` up to structure eta, so this is the left inverse law for `h.symm`.
  right_inv := cosphereRadialMap_symm_cosphereRadialMap h.symm
  contMDiff_toFun := contMDiff_cosphereRadialMap h
  contMDiff_invFun := contMDiff_cosphereRadialMap h.symm

private theorem coe_cosphereRadial_eq_normalize (h : M ≃ₘ⟮I, J⟯ N) (z : cosphereBundle I M) :
    (h.cosphereRadial z : CotangentBundle J N) = normalize (h.cotangent z.1) :=
  (rfl)

/-- The radial identification divides the cotangent lift of a unit covector by its norm. -/
theorem coe_cosphereRadial_apply (h : M ≃ₘ⟮I, J⟯ N) (z : cosphereBundle I M) :
    (h.cosphereRadial z : CotangentBundle J N) =
      TotalSpace.mk' (F →L[ℝ] ℝ) (h z.1.proj) (‖(h.cotangent z.1).2‖⁻¹ • (h.cotangent z.1).2) :=
  CotangentBundle.ext (proj_cotangent h z.1) fun _ ↦ rfl

/-- The radial identification covers the diffeomorphism of the bases. -/
@[simp]
theorem proj_cosphereRadial (h : M ≃ₘ⟮I, J⟯ N) (z : cosphereBundle I M) :
    (h.cosphereRadial z).1.proj = h z.1.proj :=
  proj_cotangent h z.1

/-- The inverse of the radial identification along `h` is the radial identification along the
inverse of `h`. -/
@[simp]
theorem cosphereRadial_symm (h : M ≃ₘ⟮I, J⟯ N) :
    h.cosphereRadial.symm = h.symm.cosphereRadial :=
  Diffeomorph.ext fun _ ↦ rfl

/-- The radial identification along the identity is the identity. -/
@[simp]
theorem cosphereRadial_refl :
    (Diffeomorph.refl I M ∞).cosphereRadial =
      Diffeomorph.refl 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) (cosphereBundle I M) ∞ :=
  Diffeomorph.ext fun z ↦ Subtype.ext <| by
    simpa [coe_cosphereRadial_eq_normalize] using normalize_of_norm_eq_one z.2

/-- Radial identification is functorial: along a composite it is the composite of the radial
identifications. -/
@[simp]
theorem cosphereRadial_trans {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ G H''}
    [K.Boundaryless] {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]
    [RiemannianBundle (fun y : P ↦ TangentSpace K y)]
    [IsContMDiffRiemannianBundle K ∞ G (fun y : P ↦ TangentSpace K y)]
    (h : M ≃ₘ⟮I, J⟯ N) (g : N ≃ₘ⟮J, K⟯ P) :
    (h.trans g).cosphereRadial = h.cosphereRadial.trans g.cosphereRadial :=
  Diffeomorph.ext fun z ↦ Subtype.ext <| by
    simp only [Diffeomorph.coe_trans, Function.comp_apply, coe_cosphereRadial_eq_normalize]
    rw [normalize_cotangent_normalize _
      ((h.cotangent_snd_eq_zero_iff).not.2 (snd_ne_zero_of_mem_cosphereBundle z.2))]
    simp

section CotangentCoe

omit [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [FiniteDimensional ℝ F] [J.Boundaryless]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

/-- The cotangent lift restricted to the unit cosphere bundle, as a smooth map. -/
private theorem contMDiff_cotangent_coe (h : M ≃ₘ⟮I, J⟯ N) :
    ContMDiff 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      fun y : cosphereBundle I M ↦ h.cotangent y.1 :=
  h.cotangent.contMDiff.comp isSmoothEmbedding_coe_cosphereBundle.contMDiff

/-- The Liouville form of `T*N` pulled back to `S*M` along the cotangent lift is the Liouville
form of `T*M` restricted to `S*M`. -/
private theorem mpullback_cotangent_coe_liouvilleForm (h : M ≃ₘ⟮I, J⟯ N) :
    SmoothForm.mpullback _ (contMDiff_cotangent_coe h) (liouvilleForm J N) =
      SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
        isSmoothEmbedding_coe_cosphereBundle.contMDiff (liouvilleForm I M) := by
  have hcomp := LinearMap.congr_fun (SmoothForm.mpullback_comp Subtype.val h.cotangent
    isSmoothEmbedding_coe_cosphereBundle.contMDiff h.cotangent.contMDiff) (liouvilleForm J N)
  rw [LinearMap.comp_apply, mpullback_cotangent_liouvilleForm] at hcomp
  exact hcomp

end CotangentCoe

/-- The Liouville form of `T*N` pulled back to `S*M` along the radial identification, read in
`T*N`, is the pullback along the cotangent lift rescaled by `‖T*h(z)‖⁻¹`. -/
private theorem mpullback_coe_comp_cosphereRadial_liouvilleForm_apply (h : M ≃ₘ⟮I, J⟯ N)
    (z : cosphereBundle I M) :
    (SmoothForm.mpullback (Subtype.val ∘ h.cosphereRadial)
        ((isSmoothEmbedding_coe_cosphereBundle (I := J) (M := N)).contMDiff.comp
          h.cosphereRadial.contMDiff) (liouvilleForm J N)).1 z =
      ‖(h.cotangent z.1).2‖⁻¹ •
        (SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
          isSmoothEmbedding_coe_cosphereBundle.contMDiff (liouvilleForm I M)).1 z := by
  rw [← mpullback_cotangent_coe_liouvilleForm h]
  exact mpullback_liouvilleForm_apply_of_eq_smul _ (contMDiff_cotangent_coe h)
    (fun y ↦ ‖(h.cotangent y.1).2‖⁻¹) (coe_cosphereRadial_eq_normalize h) z

/-- **The radial identification rescales the contact form `λ|S*`.** It pulls the restriction of
the Liouville form of `T*N` to `S*N` back to the restriction of the Liouville form of `T*M` to
`S*M`, multiplied by the positive function `‖T*h(z)‖⁻¹`. -/
theorem mpullback_cosphereRadial_liouvilleForm_apply (h : M ≃ₘ⟮I, J⟯ N)
    (z : cosphereBundle I M) :
    (SmoothForm.mpullback h.cosphereRadial h.cosphereRadial.contMDiff
        (SmoothForm.mpullback (Subtype.val : cosphereBundle J N → CotangentBundle J N)
          isSmoothEmbedding_coe_cosphereBundle.contMDiff (liouvilleForm J N))).1 z =
      ‖(h.cotangent z.1).2‖⁻¹ •
        (SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
          isSmoothEmbedding_coe_cosphereBundle.contMDiff (liouvilleForm I M)).1 z := by
  rw [← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
  exact mpullback_coe_comp_cosphereRadial_liouvilleForm_apply h z

/-- **The radial identification rescales the contact form `-λ|S*`** by the same positive
function `‖T*h(z)‖⁻¹`. -/
theorem mpullback_cosphereRadial_neg_liouvilleForm_apply (h : M ≃ₘ⟮I, J⟯ N)
    (z : cosphereBundle I M) :
    (SmoothForm.mpullback h.cosphereRadial h.cosphereRadial.contMDiff
        (SmoothForm.mpullback (Subtype.val : cosphereBundle J N → CotangentBundle J N)
          isSmoothEmbedding_coe_cosphereBundle.contMDiff (-liouvilleForm J N))).1 z =
      ‖(h.cotangent z.1).2‖⁻¹ •
        (SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
          isSmoothEmbedding_coe_cosphereBundle.contMDiff (-liouvilleForm I M)).1 z := by
  simp only [map_neg]
  exact (congrArg Neg.neg (mpullback_cosphereRadial_liouvilleForm_apply h z)).trans
    (smul_neg _ _).symm

/-- **The radial identification preserves the contact hyperplanes.** The pullback of `λ|S*N`
along `ρ_h` has the same kernel as `λ|S*M`, so the differential of `ρ_h` carries the contact
hyperplanes of `S*M` onto those of `S*N` (`TauCeti.SmoothForm.kerDistribution_mpullback`). The
hyperplanes of `-λ|S*` are the same. -/
theorem kerDistribution_mpullback_cosphereRadial_liouvilleForm (h : M ≃ₘ⟮I, J⟯ N) :
    (SmoothForm.mpullback h.cosphereRadial h.cosphereRadial.contMDiff
        (SmoothForm.mpullback (Subtype.val : cosphereBundle J N → CotangentBundle J N)
          isSmoothEmbedding_coe_cosphereBundle.contMDiff (liouvilleForm J N))).kerDistribution =
      (SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
        isSmoothEmbedding_coe_cosphereBundle.contMDiff (liouvilleForm I M)).kerDistribution :=
  SmoothForm.kerDistribution_of_eq_smul (fun z ↦ (inv_norm_cotangent_snd_pos h z).ne')
    (mpullback_cosphereRadial_liouvilleForm_apply h)

/-- **The radial identification preserves the coorientation of `λ|S*`.** A tangent vector `v` of
`S*M` is on the positive side of the contact hyperplane of `λ|S*M` exactly when it is on the
positive side for the pullback of `λ|S*N` along `ρ_h`, that is, exactly when its image under the
differential of `ρ_h` is on the positive side of the contact hyperplane of `λ|S*N`. -/
theorem pos_mpullback_cosphereRadial_liouvilleForm_iff (h : M ≃ₘ⟮I, J⟯ N)
    (z : cosphereBundle I M)
    (v : TangentSpace 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) z) :
    0 < (SmoothForm.mpullback h.cosphereRadial h.cosphereRadial.contMDiff
        (SmoothForm.mpullback (Subtype.val : cosphereBundle J N → CotangentBundle J N)
          isSmoothEmbedding_coe_cosphereBundle.contMDiff (liouvilleForm J N))).1 z ![v] ↔
      0 < (SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
        isSmoothEmbedding_coe_cosphereBundle.contMDiff (liouvilleForm I M)).1 z ![v] := by
  rw [mpullback_cosphereRadial_liouvilleForm_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, mul_pos_iff_of_pos_left (inv_norm_cotangent_snd_pos h z)]

/-- **The radial identification preserves the coorientation of `-λ|S*`.** -/
theorem pos_mpullback_cosphereRadial_neg_liouvilleForm_iff (h : M ≃ₘ⟮I, J⟯ N)
    (z : cosphereBundle I M)
    (v : TangentSpace 𝓘(ℝ, Fin (finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) z) :
    0 < (SmoothForm.mpullback h.cosphereRadial h.cosphereRadial.contMDiff
        (SmoothForm.mpullback (Subtype.val : cosphereBundle J N → CotangentBundle J N)
          isSmoothEmbedding_coe_cosphereBundle.contMDiff (-liouvilleForm J N))).1 z ![v] ↔
      0 < (SmoothForm.mpullback (Subtype.val : cosphereBundle I M → CotangentBundle I M)
        isSmoothEmbedding_coe_cosphereBundle.contMDiff (-liouvilleForm I M)).1 z ![v] := by
  rw [mpullback_cosphereRadial_neg_liouvilleForm_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, mul_pos_iff_of_pos_left (inv_norm_cotangent_snd_pos h z)]

end Diffeomorph
