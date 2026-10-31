/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Contactization

Let `θ` be a one-form on a manifold `M`, so that `ω = -dθ` is an exact two-form. On `M × ℝ`, with
real coordinate `z`, the **contactization form** of `θ` is the one-form

`α = dz - pr₁^* θ`

(`TauCeti.SmoothForm.contactizationForm`). At a tangent vector `(v, c)` of `M × ℝ` it takes the
value `c - θ(v)`. Its exterior derivative is the pullback of `ω` along the first projection,
`dα = pr₁^* ω` (`TauCeti.SmoothForm.mextDerivₗ_contactizationForm`).

The form `α` is a contact form exactly when `dθ` is nondegenerate
(`TauCeti.SmoothForm.isContactForm_contactizationForm_iff`). Indeed `α(∂_z) = 1`, so `α` vanishes
nowhere, and its kernel at `(x, z)` is the graph `{(v, θ(v))}` of `θ_x`, on which `dα` pairs
`(v, θ(v))` with `(w, θ(w))` to `ω(v, w)`. So `dα` is nondegenerate on the kernel exactly when `ω`
is nondegenerate at `x`. In particular the contactization of an exact symplectic manifold
`(M, -dθ)` is a contact manifold.

Changing the primitive by an exact form only moves the coordinate `z`. If `θ' = θ + dg` for a
smooth function `g`, the diffeomorphism `(x, z) ↦ (x, z + g x)` of `M × ℝ`
(`TauCeti.SmoothForm.contactizationShift`) pulls the contactization form of `θ'` back to that of
`θ` (`TauCeti.SmoothForm.mpullback_contactizationShift_contactizationForm`), so it is a strict
contactomorphism between the two contactizations.

For the cotangent bundle `T*Q` with its Liouville form `λ`, the contactization form `dz - λ` on
`T*Q × ℝ` is the standard contact form of the manifold of one-jets `J¹Q = T*Q × ℝ`
(`TauCeti.CotangentBundle.isContactForm_contactizationForm_liouvilleForm`).

## Main declarations

* `TauCeti.SmoothForm.contactizationForm`: the one-form `dz - pr₁^* θ` on `M × ℝ`.
* `TauCeti.SmoothForm.contactizationForm_apply`: its value `c - θ(v)` on a tangent vector `(v, c)`.
* `TauCeti.SmoothForm.mem_kerDistribution_contactizationForm_iff`: its kernel is the graph of `θ`.
* `TauCeti.SmoothForm.mextDerivₗ_contactizationForm`: `d(dz - pr₁^* θ) = pr₁^* (-dθ)`.
* `TauCeti.SmoothForm.isContactForm_contactizationForm_iff`: the contactization form is a contact
  form exactly when `dθ` is nondegenerate.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isContactForm_contactizationForm`: the contactization of
  an exact symplectic manifold `(M, -dθ)` is a contact manifold.
* `TauCeti.SmoothForm.contactizationShift`,
  `TauCeti.SmoothForm.mpullback_contactizationShift_contactizationForm`: changing the primitive by
  an exact form shifts the coordinate `z`.
* `TauCeti.CotangentBundle.isContactForm_contactizationForm_liouvilleForm`: the standard contact
  form `dz - λ` of the one-jet manifold `T*Q × ℝ`.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (contact structures, contactization and the one-jet bundle).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Appendix 4 (the contact structure of the manifold of one-jets).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The real coordinate `z` of `M × ℝ`, as a smooth `0`-form. -/
private def realCoord : SmoothForm (I.prod 𝓘(ℝ)) (M × ℝ) ℝ 0 :=
  ⟨RoughForm.ofFunction (I.prod 𝓘(ℝ)) Prod.snd,
    (isSmoothForm_ofFunction_iff.mpr contMDiff_snd).mem_smoothBundleForms⟩

/-- The **contactization form** `dz - pr₁^* θ` of a one-form `θ` on `M`: a one-form on `M × ℝ`,
where `z` is the real coordinate. It is a contact form exactly when `dθ` is nondegenerate
(`TauCeti.SmoothForm.isContactForm_contactizationForm_iff`), and its exterior derivative is
`pr₁^* (-dθ)`. -/
def contactizationForm (θ : SmoothForm I M ℝ 1) : SmoothForm (I.prod 𝓘(ℝ)) (M × ℝ) ℝ 1 :=
  mextDerivₗ (I.prod 𝓘(ℝ)) 0 realCoord - mpullback Prod.fst contMDiff_fst θ

/-- The contactization form is `dz - pr₁^* θ`, as a rough form. -/
theorem coe_contactizationForm (θ : SmoothForm I M ℝ 1) :
    (contactizationForm θ).1 =
      mextDeriv (RoughForm.ofFunction (I.prod 𝓘(ℝ)) Prod.snd) -
        TauCeti.mpullback (I.prod 𝓘(ℝ)) I Prod.fst θ.1 := by
  rw [contactizationForm, AddSubgroupClass.coe_sub, mextDerivₗ_apply, coe_mpullback]
  -- The underlying rough form of `realCoord` is the `0`-form of `Prod.snd`, by definition.
  rfl

/-- The contactization form `dz - pr₁^* θ` evaluates the tangent vector `(v, c)` of `M × ℝ` to
`c - θ(v)`. -/
theorem contactizationForm_apply (θ : SmoothForm I M ℝ 1) (p : M × ℝ) (v : TangentSpace I p.1)
    (c : ℝ) :
    (contactizationForm θ).1 p ![(Manifold.tangentSpaceProdEquiv p).symm (v, c)] =
      c - θ.1 p.1 ![v] := by
  rw [coe_contactizationForm, Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
    mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    TauCeti.mpullback_apply, mvfderiv_apply_eq_mfderiv_apply, mfderiv_fst, mfderiv_snd]
  rw [Manifold.tangentSpaceProdEquiv_symm_apply]
  -- The projections `ContinuousLinearMap.snd` and `ContinuousLinearMap.fst` read the components of
  -- the pair `(v, c)`; the components are typed as tangent spaces, so the projection lemmas do not
  -- apply syntactically and the components are read off by `rfl`.
  refine congrArg₂ (· - ·) (rfl) (congrArg (θ.1 p.1) (funext fun i ↦ ?_))
  fin_cases i
  rfl

/-- The kernel of the contactization form `dz - pr₁^* θ` at `(x, z)` is the graph of `θ_x`: it
consists of the tangent vectors `(v, θ(v))`. -/
theorem mem_kerDistribution_contactizationForm_iff {θ : SmoothForm I M ℝ 1} {p : M × ℝ}
    {v : TangentSpace I p.1} {c : ℝ} :
    (Manifold.tangentSpaceProdEquiv p).symm (v, c) ∈ (contactizationForm θ).kerDistribution p ↔
      c = θ.1 p.1 ![v] := by
  rw [mem_kerDistribution, contactizationForm_apply, sub_eq_zero]

/-- The contactization form `dz - pr₁^* θ` takes the value `1` on the vector field `∂_z`. -/
theorem contactizationForm_apply_zero_one (θ : SmoothForm I M ℝ 1) (p : M × ℝ) :
    (contactizationForm θ).1 p ![(Manifold.tangentSpaceProdEquiv p).symm (0, (1 : ℝ))] = 1 := by
  rw [contactizationForm_apply, ContinuousAlternatingMap.map_coord_zero _ 0 rfl, sub_zero]

/-- **The exterior derivative of the contactization form** `dz - pr₁^* θ` is `pr₁^* (-dθ)`. -/
theorem mextDerivₗ_contactizationForm (θ : SmoothForm I M ℝ 1) :
    mextDerivₗ (I.prod 𝓘(ℝ)) 1 (contactizationForm θ) =
      mpullback Prod.fst contMDiff_fst (-mextDerivₗ I 1 θ) := by
  rw [contactizationForm, map_sub, ← LinearMap.comp_apply, mextDerivₗ_comp_mextDerivₗ,
    LinearMap.zero_apply, zero_sub, mextDerivₗ_mpullback, map_neg]

/-- The exterior derivative of the contactization form `dz - pr₁^* θ` pairs the tangent vectors
`(v, c)` and `(w, d)` of `M × ℝ` to `-dθ(v, w)`. -/
theorem mextDeriv_contactizationForm_apply (θ : SmoothForm I M ℝ 1) (p : M × ℝ)
    (v w : TangentSpace I p.1) (c d : ℝ) :
    mextDeriv (contactizationForm θ).1 p
        ![(Manifold.tangentSpaceProdEquiv p).symm (v, c),
          (Manifold.tangentSpaceProdEquiv p).symm (w, d)] =
      -mextDeriv θ.1 p.1 ![v, w] := by
  have h := congrArg (fun φ : SmoothForm (I.prod 𝓘(ℝ)) (M × ℝ) ℝ 2 ↦
    SmoothBundleForm.eval₂ φ p ((Manifold.tangentSpaceProdEquiv p).symm (v, c))
      ((Manifold.tangentSpaceProdEquiv p).symm (w, d))) (mextDerivₗ_contactizationForm θ)
  rw [eval₂_mpullback_fst, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply] at h
  simpa only [SmoothBundleForm.eval₂_apply, mextDerivₗ_apply, NegMemClass.coe_neg, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply] using h

/-- **Contactization.** The contactization form `dz - pr₁^* θ` on `M × ℝ` is a contact form
exactly when `dθ` is nondegenerate, that is when `-dθ` is a nondegenerate two-form on `M`. -/
theorem isContactForm_contactizationForm_iff {θ : SmoothForm I M ℝ 1} :
    (contactizationForm θ).IsContactForm ↔ SmoothTwoForm.IsNondegenerate (mextDerivₗ I 1 θ) := by
  -- Every tangent vector of `M × ℝ` is a pair `(v, c)`.
  have hpair (p : M × ℝ) (u : TangentSpace (I.prod 𝓘(ℝ)) p) :
      ∃ q : TangentSpace I p.1 × ℝ, (Manifold.tangentSpaceProdEquiv p).symm q = u :=
    ⟨_, (Manifold.tangentSpaceProdEquiv p).symm_apply_apply u⟩
  -- The kernel vectors at `p` are the pairs `(w, θ(w))`.
  have hker (p : M × ℝ) (w : TangentSpace I p.1) :
      (contactizationForm θ).1 p ![(Manifold.tangentSpaceProdEquiv p).symm (w, θ.1 p.1 ![w])] =
        0 :=
    (contactizationForm_apply θ p w _).trans (sub_self _)
  rw [isContactForm_iff, SmoothTwoForm.isNondegenerate_iff_separatingLeft]
  constructor
  · -- A vector `v` which is `dθ`-orthogonal to everything gives the kernel vector `(v, θ(v))`,
    -- which is `dα`-orthogonal to the kernel, hence zero.
    intro h x v hv
    have h0 := (h (x, 0)).2 _ (hker (x, 0) v) fun w _ ↦ by
      obtain ⟨⟨w, d⟩, rfl⟩ := hpair (x, 0) w
      refine (mextDeriv_contactizationForm_apply θ (x, 0) v w _ d).trans ?_
      rw [neg_eq_zero]
      simpa only [SmoothBundleForm.eval₂_apply, mextDerivₗ_apply] using hv w
    simpa using congrArg (fun u ↦ (Manifold.tangentSpaceProdEquiv (x, 0) u).1) h0
  · intro h p
    refine ⟨⟨_, (contactizationForm_apply_zero_one θ p).trans_ne one_ne_zero⟩,
      fun u hu hu' ↦ ?_⟩
    -- Write `u = (v, c)`; the kernel condition says `c = θ(v)`.
    obtain ⟨⟨v, c⟩, rfl⟩ := hpair p u
    have hc : c = θ.1 p.1 ![v] := sub_eq_zero.mp ((contactizationForm_apply θ p v c).symm.trans hu)
    -- Testing against the kernel vectors `(w, θ(w))` shows that `v` is `dθ`-orthogonal to all.
    have hv : v = 0 := h p.1 v fun w ↦ by
      have := (mextDeriv_contactizationForm_apply θ p v w c _).symm.trans (hu' _ (hker p w))
      rw [neg_eq_zero] at this
      simpa only [SmoothBundleForm.eval₂_apply, mextDerivₗ_apply] using this
    have hc0 : c = 0 := by
      rw [hc, hv]
      exact ContinuousAlternatingMap.map_coord_zero _ 0 rfl
    rw [hv, hc0]
    exact (Manifold.tangentSpaceProdEquiv p).symm.map_zero

/-- **The contactization of an exact symplectic manifold is a contact manifold.** If `σ = -dθ` is
nondegenerate, the contactization form `dz - pr₁^* θ` on `M × ℝ` is a contact form. -/
theorem _root_.TauCeti.SmoothTwoForm.IsNondegenerate.isContactForm_contactizationForm
    {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate) {θ : SmoothForm I M ℝ 1}
    (hθ : σ = -mextDerivₗ I 1 θ) : (contactizationForm θ).IsContactForm := by
  rw [isContactForm_contactizationForm_iff, ← neg_neg (mextDerivₗ I 1 θ), ← hθ]
  exact hσ.neg

/-! ### Changing the primitive by an exact form -/

variable (I) in
/-- The shift `(x, z) ↦ (x, z + g x)` of `M × ℝ` along a smooth function `g`, as a
diffeomorphism. It pulls the contactization form of `θ + dg` back to that of `θ`
(`TauCeti.SmoothForm.mpullback_contactizationShift_contactizationForm`). -/
def contactizationShift {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ), I.prod 𝓘(ℝ)⟯ (M × ℝ) where
  toFun p := (p.1, p.2 + g p.1)
  invFun p := (p.1, p.2 - g p.1)
  left_inv p := by simp
  right_inv p := by simp
  contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_snd.add (hg.comp contMDiff_fst))
  contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_snd.sub (hg.comp contMDiff_fst))

omit [IsManifold I ∞ M] in
@[simp]
theorem contactizationShift_apply {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g) (p : M × ℝ) :
    contactizationShift I hg p = (p.1, p.2 + g p.1) :=
  (rfl)

omit [IsManifold I ∞ M] in
@[simp]
theorem contactizationShift_symm_apply {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g) (p : M × ℝ) :
    (contactizationShift I hg).symm p = (p.1, p.2 - g p.1) :=
  (rfl)

/-- **Changing the primitive by an exact form shifts the coordinate `z`.** If `θ' = θ + dg` for a
smooth function `g`, then the shift `(x, z) ↦ (x, z + g x)` pulls the contactization form of `θ'`
back to that of `θ`. -/
theorem mpullback_contactizationShift_contactizationForm {θ θ' : SmoothForm I M ℝ 1} {g : M → ℝ}
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) (hθ' : θ'.1 = θ.1 + mextDeriv (RoughForm.ofFunction I g)) :
    mpullback (contactizationShift I hg) (contactizationShift I hg).contMDiff
        (contactizationForm θ') = contactizationForm θ := by
  -- The `0`-form `g`, whose differential is `θ' - θ`.
  let g₀ : SmoothForm I M ℝ 0 :=
    ⟨RoughForm.ofFunction I g, (isSmoothForm_ofFunction_iff.mpr hg).mem_smoothBundleForms⟩
  have hθ'₀ : θ' = θ + mextDerivₗ I 0 g₀ :=
    Subtype.ext (by rw [AddMemClass.coe_add, mextDerivₗ_apply]; exact hθ')
  -- The shift pulls the coordinate `z` back to `z + g`.
  have hz : mpullback (contactizationShift I hg) (contactizationShift I hg).contMDiff realCoord =
      realCoord + mpullback Prod.fst contMDiff_fst g₀ := by
    refine Subtype.ext (funext fun p ↦ ContinuousAlternatingMap.ext fun v ↦ ?_)
    simp only [realCoord, g₀, coe_mpullback, TauCeti.mpullback_apply, AddMemClass.coe_add,
      Pi.add_apply, ContinuousAlternatingMap.add_apply, RoughForm.ofFunction_apply,
      contactizationShift_apply]
  -- The shift commutes with the first projection.
  have hfst (φ : SmoothForm I M ℝ 1) :
      mpullback (contactizationShift I hg) (contactizationShift I hg).contMDiff
        (mpullback Prod.fst contMDiff_fst φ) = mpullback Prod.fst contMDiff_fst φ := by
    rw [← LinearMap.comp_apply, ← mpullback_comp]
    -- `Prod.fst ∘ contactizationShift I hg` is `Prod.fst` by definition of the shift.
    rfl
  rw [contactizationForm, contactizationForm, map_sub, ← mextDerivₗ_mpullback, hz, map_add,
    mextDerivₗ_mpullback, hfst, hθ'₀, map_add]
  abel

end SmoothForm

namespace CotangentBundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The one-jet manifold is a contact manifold.** On `J¹M = T*M × ℝ`, the contactization
`dz - λ` of the Liouville form `λ` of the cotangent bundle is a contact form. -/
theorem isContactForm_contactizationForm_liouvilleForm :
    (SmoothForm.contactizationForm (liouvilleForm I M)).IsContactForm :=
  (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.isContactForm_contactizationForm
    (symplecticForm_eq_neg_mextDerivₗ (I := I) (M := M))

end CotangentBundle

end TauCeti
