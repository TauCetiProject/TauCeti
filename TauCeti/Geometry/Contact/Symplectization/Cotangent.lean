/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Symplectization.Basic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift
public import TauCeti.Geometry.Symplectic.Lagrangian.SymplecticTangent
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Symplectic.Manifold.Rescale

/-!
# The symplectization of a contact form inside the cotangent bundle

Let `α` be a one-form on a manifold `M`. The map

`ι_α : ℝ × M → T*M`, `(t, x) ↦ eᵗ α_x`

(`TauCeti.SmoothForm.symplectizationToCotangent α`) puts the symplectization `ℝ × M` of `α` into
the cotangent bundle, over the identity of `M`. It pulls the Liouville form `λ` of `T*M` back to
the symplectization form `θ = eᵗ α`
(`TauCeti.SmoothForm.mpullback_symplectizationToCotangent_liouvilleForm`), so `θ` is the
tautological form `θ_(t, x)(v) = eᵗ α_x (dπ v)` of the covectors in its image. Hence it pulls the
canonical symplectic form `ω = -dλ` back to `-dθ`, and this is nondegenerate exactly when `α` is
a contact form (`TauCeti.SmoothForm.isNondegenerate_mpullback_symplectizationToCotangent_iff`). In
particular, for a contact form `α` the tangent images of `ι_α` are symplectic subspaces of `T*M`
(`TauCeti.SmoothForm.IsContactForm.hasSymplecticTangentImages_symplectizationToCotangent`). The map
`ι_α` is an immersion wherever `α` does not vanish
(`TauCeti.SmoothForm.injective_mfderiv_symplectizationToCotangent`).

The image of `ι_α` is the half `{c α_x | c > 0}` of the annihilator line `(ker α)⁰ ⊂ T*M`. The
other half is the image of `ι_(-α)`, the symplectization of the oppositely cooriented form; over
each point where `α` does not vanish, the two images together are exactly the nonzero covectors
vanishing on `ker α` (`TauCeti.SmoothForm.mem_range_symplectizationToCotangent_or_neg_iff`). For a
nowhere vanishing `α`, the map `ι_α` is injective and the two images are disjoint. Since
both maps are injective, two copies of `ℝ × M` parametrize the punctured annihilator line of the
contact structure `ker α` bijectively: this is the trivialization by `α` of its punctured dual
contact line.

Contactomorphisms act on this picture through their cotangent lifts. Let `F : M ≃ M'` be a
diffeomorphism with `F^* α' = f α`. Where `f > 0`, the cotangent lift of `F` restricts to the lift
`(t, x) ↦ (t - log f(x), F(x))` of `TauCeti.symplectizationLift`
(`Diffeomorph.cotangent_symplectizationToCotangent`); where `f < 0`, it sends the positive half to
the negative half, by the lift for `-α'` and `-f`
(`Diffeomorph.cotangent_symplectizationToCotangent_of_neg`). Since cotangent lifts preserve `λ`,
these lifts preserve `θ`, including for coorientation-reversing contactomorphisms
(`TauCeti.SmoothForm.mpullback_symplectizationLift_neg_symplectization`). For a nowhere vanishing
`α`, they are the only lifts of `F` of the form `(t, x) ↦ (φ(t, x), F(x))` preserving `θ`
(`TauCeti.SmoothForm.eq_symplectizationLift_of_mpullback_symplectization_eq`).

## Main definitions

* `TauCeti.SmoothForm.symplectizationToCotangent α`: the map `(t, x) ↦ eᵗ α_x` into `T*M`.

## Main results

* `TauCeti.SmoothForm.mpullback_symplectizationToCotangent_liouvilleForm`: `ι_α^* λ = eᵗ α`.
* `TauCeti.SmoothForm.mpullback_symplectizationToCotangent_symplecticForm`: `ι_α^* ω = -d(eᵗ α)`.
* `TauCeti.SmoothForm.isNondegenerate_mpullback_symplectizationToCotangent_iff`: `ι_α^* ω` is
  nondegenerate exactly when `α` is a contact form.
* `TauCeti.SmoothForm.mem_range_symplectizationToCotangent_or_neg_iff`: the images of `ι_α` and
  `ι_(-α)` cover the punctured annihilator line of `ker α`.
* `Diffeomorph.cotangent_symplectizationToCotangent`,
  `Diffeomorph.cotangent_symplectizationToCotangent_of_neg`: cotangent lifts of contactomorphisms
  restrict to the lifts of the symplectizations, on either half.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 and Appendix B (the symplectization as the annihilator of the contact structure in
  the cotangent bundle).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer, 1989,
  Appendix 4 (contact structures, and the symplectification of a contact manifold).
-/

public section

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The map `(t, x) ↦ eᵗ α_x` from the symplectization `ℝ × M` of a one-form `α` to the cotangent
bundle `T*M`. It lies over the projection to `M`, and pulls the Liouville form of `T*M` back to the
symplectization form `eᵗ α`
(`TauCeti.SmoothForm.mpullback_symplectizationToCotangent_liouvilleForm`). -/
def symplectizationToCotangent (α : SmoothForm I M ℝ 1) (p : ℝ × M) : CotangentBundle I M :=
  TotalSpace.mk' (E →L[ℝ] ℝ) p.2 (Real.exp p.1 • degreeOneEquiv α p.2)

/-- The covector `eᵗ α_x` lies over `x`. -/
@[simp]
theorem proj_symplectizationToCotangent (α : SmoothForm I M ℝ 1) (p : ℝ × M) :
    (α.symplectizationToCotangent p).proj = p.2 :=
  (rfl)

/-- The covector `eᵗ α_x` evaluates a tangent vector `v` to `eᵗ α_x(v)`. -/
@[simp]
theorem symplectizationToCotangent_snd_apply (α : SmoothForm I M ℝ 1) (p : ℝ × M)
    (v : TangentSpace I p.2) :
    (α.symplectizationToCotangent p).2 v = Real.exp p.1 * α.1 p.2 ![v] := by
  rw [symplectizationToCotangent, smul_apply, degreeOneEquiv_apply_apply_vec,
    smul_eq_mul]

/-- The map `(t, x) ↦ eᵗ α_x` is smooth. -/
theorem contMDiff_symplectizationToCotangent (α : SmoothForm I M ℝ 1) :
    ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ α.symplectizationToCotangent :=
  ContMDiff.smul_totalSpace (Real.contDiff_exp.contMDiff.comp contMDiff_fst)
    ((degreeOneEquiv α).contMDiff.comp contMDiff_snd)

/-- **The symplectization form is tautological.** The map `(t, x) ↦ eᵗ α_x` pulls the Liouville
form of `T*M` back to the symplectization form `eᵗ α` of `α`. -/
@[simp]
theorem mpullback_symplectizationToCotangent_liouvilleForm (α : SmoothForm I M ℝ 1) :
    mpullback α.symplectizationToCotangent α.contMDiff_symplectizationToCotangent
        (CotangentBundle.liouvilleForm I M) =
      α.symplectization := by
  apply Subtype.ext
  funext p
  ext v
  rw [coe_mpullback, CotangentBundle.mpullback_liouvilleForm_apply_of_proj_comp_eq
      (g := Prod.snd) (fun _ ↦ rfl)
      ((α.contMDiff_symplectizationToCotangent p).mdifferentiableAt (by simp)),
    symplectizationToCotangent_snd_apply, coe_symplectization,
    ContinuousAlternatingMap.smul_apply, mpullback_snd_apply, smul_eq_mul]
  congr 2
  ext i
  fin_cases i
  simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one,
    Manifold.tangentSpaceProdEquiv_apply]
  exact mfderiv_snd_apply p (v 0)

/-- The map `(t, x) ↦ eᵗ α_x` pulls the canonical symplectic form `ω = -dλ` of `T*M` back to
`-d(eᵗ α)`. -/
theorem mpullback_symplectizationToCotangent_symplecticForm (α : SmoothForm I M ℝ 1) :
    mpullback α.symplectizationToCotangent α.contMDiff_symplectizationToCotangent
        (CotangentBundle.symplecticForm I M) =
      -mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization := by
  rw [CotangentBundle.symplecticForm_eq_neg_mextDerivₗ, map_neg, ← mextDerivₗ_mpullback,
    mpullback_symplectizationToCotangent_liouvilleForm]

/-- The map `(t, x) ↦ eᵗ α_x` pulls the canonical symplectic form of `T*M` back to a nondegenerate
form exactly when `α` is a contact form. -/
theorem isNondegenerate_mpullback_symplectizationToCotangent_iff {α : SmoothForm I M ℝ 1} :
    SmoothTwoForm.IsNondegenerate
        (mpullback α.symplectizationToCotangent α.contMDiff_symplectizationToCotangent
          (CotangentBundle.symplecticForm I M)) ↔
      α.IsContactForm := by
  rw [mpullback_symplectizationToCotangent_symplecticForm,
    ← isNondegenerate_mextDerivₗ_symplectization_iff]
  exact ⟨fun h ↦ by simpa using h.neg, fun h ↦ h.neg⟩

/-- The map `(t, x) ↦ eᵗ α_x` pulls the canonical symplectic form of `T*M` back to a symplectic
form exactly when `α` is a contact form. -/
theorem isSymplectic_mpullback_symplectizationToCotangent_iff {α : SmoothForm I M ℝ 1} :
    SmoothTwoForm.IsSymplectic
        (mpullback α.symplectizationToCotangent α.contMDiff_symplectizationToCotangent
          (CotangentBundle.symplecticForm I M)) ↔
      α.IsContactForm := by
  rw [mpullback_symplectizationToCotangent_symplecticForm, SmoothTwoForm.isSymplectic_neg_iff,
    isSymplectic_mextDerivₗ_symplectization_iff]

/-- At a point `(t, x)` where the one-form `α` does not vanish, the map `(t, x) ↦ eᵗ α_x` has
injective derivative. So it is an immersion when `α` vanishes nowhere, for instance when `α` is a
contact form. -/
theorem injective_mfderiv_symplectizationToCotangent {α : SmoothForm I M ℝ 1} {p : ℝ × M}
    (hα : α.1 p.2 ≠ 0) :
    Function.Injective
      (mfderiv (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) α.symplectizationToCotangent p) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu ↦ ?_
  -- Since the map lies over the projection to `M`, the component of `u` along `M` vanishes.
  have hw : (Manifold.tangentSpaceProdEquiv p u).2 = 0 := by
    have h := mfderiv_comp_apply p
      ((Bundle.contMDiff_proj (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) _).mdifferentiableAt
        one_ne_zero)
      ((α.contMDiff_symplectizationToCotangent p).mdifferentiableAt (by simp)) u
    rw [hu, map_zero] at h
    rw [Manifold.tangentSpaceProdEquiv_apply]
    exact (mfderiv_snd_apply p u).symm.trans h
  -- Pairing `u` with a vector `(0, v)` under the pullback `-d(eᵗ α)` of `ω` shows that the
  -- component of `u` along `ℝ` vanishes too.
  obtain ⟨v, hv⟩ := RoughForm.exists_apply_ne_zero hα
  set w : TangentSpace (𝓘(ℝ).prod I) p := (Manifold.tangentSpaceProdEquiv p).symm (0, v)
  have h := eval₂_mpullback _ α.contMDiff_symplectizationToCotangent
    (CotangentBundle.symplecticForm I M) p u w
  have hω : (CotangentBundle.symplecticForm I M).eval₂ (α.symplectizationToCotangent p) 0
      (mfderiv (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) α.symplectizationToCotangent p w) = 0 := by
    simpa using (CotangentBundle.symplecticForm I M).eval₂_smul_left _ 0 0
      (mfderiv (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) α.symplectizationToCotangent p w)
  have hdα : (mextDerivₗ I 1 α).eval₂ p.2 0 v = 0 := by
    simpa using (mextDerivₗ I 1 α).eval₂_smul_left p.2 0 0 v
  rw [hu, hω, mpullback_symplectizationToCotangent_symplecticForm, SmoothBundleForm.eval₂_neg,
    eval₂_mextDerivₗ_symplectization, hw, ContinuousLinearEquiv.apply_symm_apply, hdα] at h
  simp only [Manifold.tangentSpaceProdEquiv_apply, map_zero, zero_mul, sub_zero, add_zero,
    neg_eq_zero, mul_eq_zero, Real.exp_ne_zero, EmbeddingLike.map_eq_zero_iff, false_or] at h
  rw [Manifold.tangentSpaceProdEquiv_apply] at hw
  exact Prod.ext (h.resolve_right hv) hw

/-- For a contact form `α`, the tangent images of the map `(t, x) ↦ eᵗ α_x` are symplectic
subspaces of the tangent spaces of `T*M`. -/
theorem IsContactForm.hasSymplecticTangentImages_symplectizationToCotangent
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) :
    CotangentBundle.isSymplectic_symplecticForm.isNondegenerate.HasSymplecticTangentImages
      (𝓘(ℝ).prod I) α.symplectizationToCotangent :=
  ((CotangentBundle.isSymplectic_symplecticForm.isNondegenerate.isNondegenerate_mpullback_iff
    α.contMDiff_symplectizationToCotangent).1
      (isNondegenerate_mpullback_symplectizationToCotangent_iff.2 hα)).1

/-! ### The two halves of the annihilator line -/

/-- For a nowhere vanishing one-form `α`, the map `(t, x) ↦ eᵗ α_x` is injective. -/
theorem symplectizationToCotangent_injective {α : SmoothForm I M ℝ 1} (hα : ∀ x, α.1 x ≠ 0) :
    Function.Injective α.symplectizationToCotangent := by
  rintro ⟨t, x⟩ ⟨s, y⟩ h
  obtain rfl : x = y := congrArg TotalSpace.proj h
  obtain ⟨v, hv⟩ := RoughForm.exists_apply_ne_zero (hα x)
  have hv' := congrArg (fun z : CotangentBundle I M ↦ z.2 v) h
  simp only [symplectizationToCotangent_snd_apply] at hv'
  rw [mul_left_inj' hv, Real.exp_eq_exp] at hv'
  rw [hv']

/-- A covector lies in the image of `(t, x) ↦ eᵗ α_x` exactly when it is a positive multiple of the
value of `α` at its base point. -/
theorem mem_range_symplectizationToCotangent_iff {α : SmoothForm I M ℝ 1}
    {z : CotangentBundle I M} :
    z ∈ Set.range α.symplectizationToCotangent ↔
      ∃ c : ℝ, 0 < c ∧ ∀ v, z.2 v = c * α.1 z.proj ![v] := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨Real.exp p.1, Real.exp_pos _, symplectizationToCotangent_snd_apply α p⟩
  · rintro ⟨c, hc, hz⟩
    refine ⟨(Real.log c, z.proj), CotangentBundle.ext rfl fun v ↦ ?_⟩
    exact (symplectizationToCotangent_snd_apply α _ v).trans
      (by rw [Real.exp_log hc]; exact (hz v).symm)

/-- A covector lies in the image of `(t, x) ↦ eᵗ α_x` or in that of `(t, x) ↦ eᵗ (-α)_x` exactly
when it is a nonzero multiple of the value of `α` at its base point. -/
private theorem mem_range_or_neg_iff_exists_ne_zero {α : SmoothForm I M ℝ 1}
    {z : CotangentBundle I M} :
    z ∈ Set.range α.symplectizationToCotangent ∨ z ∈ Set.range (-α).symplectizationToCotangent ↔
      ∃ c : ℝ, c ≠ 0 ∧ ∀ v, z.2 v = c * α.1 z.proj ![v] := by
  simp only [mem_range_symplectizationToCotangent_iff]
  constructor
  · rintro (⟨c, hc, hz⟩ | ⟨c, hc, hz⟩)
    · exact ⟨c, hc.ne', hz⟩
    · exact ⟨-c, neg_ne_zero.2 hc.ne', fun v ↦ by simp [hz]⟩
  · rintro ⟨c, hc, hz⟩
    rcases hc.lt_or_gt with hc | hc
    · exact Or.inr ⟨-c, neg_pos.2 hc, fun v ↦ by simp [hz]⟩
    · exact Or.inl ⟨c, hc, hz⟩

/-- For a nowhere vanishing one-form `α`, the images of `(t, x) ↦ eᵗ α_x` and of
`(t, x) ↦ eᵗ (-α)_x` are disjoint. -/
theorem disjoint_range_symplectizationToCotangent_neg {α : SmoothForm I M ℝ 1}
    (hα : ∀ x, α.1 x ≠ 0) :
    Disjoint (Set.range α.symplectizationToCotangent)
      (Set.range (-α).symplectizationToCotangent) := by
  refine Set.disjoint_left.2 fun z hz hz' ↦ ?_
  obtain ⟨c, hc, hzc⟩ := mem_range_symplectizationToCotangent_iff.1 hz
  obtain ⟨d, hd, hzd⟩ := mem_range_symplectizationToCotangent_iff.1 hz'
  obtain ⟨v, hv⟩ := RoughForm.exists_apply_ne_zero (hα z.proj)
  have h : (c + d) * α.1 z.proj ![v] = 0 := by
    have h := (hzc v).symm.trans (hzd v)
    simp only [NegMemClass.coe_neg, Pi.neg_apply, ContinuousAlternatingMap.coe_neg] at h
    linear_combination h
  exact (mul_ne_zero (add_pos hc hd).ne' hv) h

/-- **The punctured annihilator line.** At a point where a one-form `α` does not vanish, the
images of `(t, x) ↦ eᵗ α_x` and of `(t, x) ↦ eᵗ (-α)_x` together consist exactly of the nonzero
covectors vanishing on `ker α`. -/
theorem mem_range_symplectizationToCotangent_or_neg_iff {α : SmoothForm I M ℝ 1}
    {z : CotangentBundle I M} (hα : α.1 z.proj ≠ 0) :
    z ∈ Set.range α.symplectizationToCotangent ∨ z ∈ Set.range (-α).symplectizationToCotangent ↔
      z.2 ≠ 0 ∧ ∀ v, α.1 z.proj ![v] = 0 → z.2 v = 0 := by
  rw [mem_range_or_neg_iff_exists_ne_zero]
  constructor
  · rintro ⟨c, hc, hz⟩
    obtain ⟨v₀, hv₀⟩ := RoughForm.exists_apply_ne_zero hα
    refine ⟨fun h0 ↦ ?_, fun v hv ↦ by rw [hz, hv, mul_zero]⟩
    have := hz v₀
    rw [h0, zero_apply] at this
    exact mul_ne_zero hc hv₀ this.symm
  · rintro ⟨hz0, hz⟩
    -- A functional vanishing on `ker α` is a multiple of `α`.
    have hspan : (z.2 : TangentSpace I z.proj →ₗ[ℝ] ℝ) ∈
        Submodule.span ℝ (Set.range fun _ : Unit ↦ RoughForm.eval α.1 z.proj) :=
      mem_span_of_iInf_ker_le_ker fun v hv ↦ hz v (by simpa using hv)
    rw [Set.range_const, Submodule.mem_span_singleton] at hspan
    obtain ⟨c, hc⟩ := hspan
    have hzc (v : TangentSpace I z.proj) : z.2 v = c * α.1 z.proj ![v] := by
      simpa using (LinearMap.congr_fun hc v).symm
    refine ⟨c, fun h0 ↦ hz0 (ContinuousLinearMap.ext fun v ↦ ?_), hzc⟩
    rw [hzc, h0, zero_mul, zero_apply]

end SmoothForm

end TauCeti

/-! ### Cotangent lifts of contactomorphisms -/

namespace Diffeomorph

open TauCeti

variable {E H M E' H' M' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {F : M ≃ₘ⟮I, I'⟯ M'} {f : M → ℝ} {α : SmoothForm I M ℝ 1} {α' : SmoothForm I' M' ℝ 1}

/-- If a diffeomorphism `F` pulls `α'` back to `f α`, then `f(x)` times the image of the covector
`eᵗ α_x` under the cotangent lift of `F` is `eᵗ α'_(F x)`. -/
private theorem cotangent_symplectizationToCotangent_snd_apply
    (hα : ∀ x, (SmoothForm.mpullback F F.contMDiff α').1 x = f x • α.1 x) (p : ℝ × M)
    (w : TangentSpace I' (F p.2)) :
    f p.2 * (F.cotangent (α.symplectizationToCotangent p)).2 w =
      Real.exp p.1 * α'.1 (F p.2) ![w] := by
  set u := mfderiv I' I F.symm (F p.2) w
  have hvec : (fun i ↦ mfderiv I I' F p.2 (![u] i)) = ![w] := by
    ext i
    fin_cases i
    exact F.mfderiv_apply_mfderiv_symm_apply (by simp) p.2 w
  have h : α'.1 (F p.2) ![w] = f p.2 * α.1 p.2 ![u] := by
    rw [← hvec]
    have h' := congrArg (fun A ↦ A ![u]) (hα p.2)
    simp only [SmoothForm.mpullback_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h'
    exact h'
  rw [h]
  refine (congrArg (f p.2 * ·) ((cotangent_snd_apply F _ w).trans
    (SmoothForm.symplectizationToCotangent_snd_apply α p u))).trans ?_
  ring

/-- **Cotangent lifts of contactomorphisms, positive case.** If a diffeomorphism `F` pulls `α'` back
to `f α` and `f` is positive at the base point `x` of `p = (t, x)`, the cotangent lift of `F` sends
`eᵗ α_x` to `e^(t - log f(x)) α'_(F x)`: on the image of `(t, x) ↦ eᵗ α_x` it is the lift
`(t, x) ↦ (t - log f(x), F(x))` of the symplectizations. -/
theorem cotangent_symplectizationToCotangent
    (hα : ∀ x, (SmoothForm.mpullback F F.contMDiff α').1 x = f x • α.1 x) {p : ℝ × M}
    (hp : 0 < f p.2) :
    F.cotangent (α.symplectizationToCotangent p) =
      α'.symplectizationToCotangent (symplectizationLift F f p) := by
  refine CotangentBundle.ext (by simp) fun w ↦ ?_
  have h := cotangent_symplectizationToCotangent_snd_apply hα p w
  refine Eq.trans ?_ (SmoothForm.symplectizationToCotangent_snd_apply α' _ w).symm
  rw [symplectizationLift_apply, Real.exp_sub, Real.exp_log hp, div_mul_eq_mul_div,
    eq_div_iff hp.ne', mul_comm]
  exact h

/-- **Cotangent lifts of contactomorphisms, negative case.** If a diffeomorphism `F` pulls `α'`
back to `f α` and `f` is negative at the base point `x` of `p = (t, x)`, the cotangent lift of `F`
sends `eᵗ α_x` to `e^(t - log(-f(x))) (-α')_(F x)`: it carries the image of `(t, x) ↦ eᵗ α_x` to
the image of `(t, x) ↦ eᵗ (-α')_x` by the lift `(t, x) ↦ (t - log(-f(x)), F(x))`. -/
theorem cotangent_symplectizationToCotangent_of_neg
    (hα : ∀ x, (SmoothForm.mpullback F F.contMDiff α').1 x = f x • α.1 x) {p : ℝ × M}
    (hp : f p.2 < 0) :
    F.cotangent (α.symplectizationToCotangent p) =
      (-α').symplectizationToCotangent (symplectizationLift F (-f) p) :=
  cotangent_symplectizationToCotangent
    (fun x ↦ SmoothForm.mpullback_neg_apply_eq_neg_smul (hα x))
    (neg_pos.2 hp)

end Diffeomorph
