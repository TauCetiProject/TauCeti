/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Contactization of an exact symplectic manifold

Let `θ` be a one-form on a manifold `W` whose two-form `ω = -dθ` is nondegenerate, so that
`(W, ω = -dθ)` is an exact symplectic manifold. Its **contactization** is the product `W × ℝ`,
with real coordinate `z`, carrying the one-form

`α = dz - θ` (`TauCeti.SmoothForm.contactization θ`),

where `θ` is pulled back along the projection to `W`. Then `dα = ω`, pulled back along the same
projection (`TauCeti.SmoothForm.mextDerivₗ_contactization`), and `α` is a contact form exactly when
`ω` is nondegenerate (`TauCeti.SmoothForm.isContactForm_contactization_iff`). The proof is linear
algebra on each tangent space `T_w W × ℝ`: the kernel of `α` is the graph `{(v, θ v)}` of `θ`
(`TauCeti.SmoothForm.mem_kerDistribution_contactization`), which the projection identifies with
`T_w W`, and on it `dα` is `ω`.

For the cotangent bundle `W = T*Q` with its Liouville form `λ_Q`, this is the standard contact
form `dz - λ_Q` of the space of one-jets `J¹Q = T*Q × ℝ`
(`TauCeti.CotangentBundle.isContactForm_contactization_liouvilleForm`).

The construction depends on the primitive `θ`, not only on `ω`. Changing `θ` by an exact form
`dg` changes the coordinate `z`: the diffeomorphism `(w, z) ↦ (w, z - g w)` of `W × ℝ`
(`TauCeti.contactizationShift`) pulls the contactization form of `θ` back to the contactization
form of `θ + dg` (`TauCeti.mpullback_contactizationShift_contactization`). So the two contact forms
are identified by a strict contactomorphism.

## Main definitions

* `TauCeti.SmoothForm.contactization θ`: the one-form `dz - θ` on `W × ℝ`.
* `TauCeti.contactizationShift`: the diffeomorphism `(w, z) ↦ (w, z - g w)`.

## Main results

* `TauCeti.SmoothForm.mextDerivₗ_contactization`: `d(dz - θ) = -dθ`.
* `TauCeti.SmoothForm.isContactForm_contactization_iff`: `dz - θ` is a contact form exactly when
  `-dθ` is nondegenerate.
* `TauCeti.mpullback_contactizationShift_contactization`: change of primitive.
* `TauCeti.CotangentBundle.isContactForm_contactization_liouvilleForm`: the one-jet space of a
  manifold is a contact manifold.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Chapter 2 (contact manifolds, including the space of one-jets).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (contact structures).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothForm

variable {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W] [IsManifold I ∞ W]

/-- The **contactization form** `dz - θ` on `W × ℝ` of a one-form `θ` on `W`, where `z` is the
real coordinate and `θ` is pulled back along the projection to `W`. When `-dθ` is nondegenerate it
is a contact form (`TauCeti.SmoothForm.isContactForm_contactization_iff`). -/
def contactization (θ : SmoothForm I W ℝ 1) : SmoothForm (I.prod 𝓘(ℝ)) (W × ℝ) ℝ 1 :=
  mpullback Prod.snd contMDiff_snd realLineCoordForm - mpullback Prod.fst contMDiff_fst θ

/-- The contactization form sends a tangent vector `(v, c)` at `(w, z)` to `c - θ_w(v)`. -/
@[simp]
theorem contactization_apply (θ : SmoothForm I W ℝ 1) (p : W × ℝ)
    (v : TangentSpace (I.prod 𝓘(ℝ)) p) :
    θ.contactization.1 p ![v] =
      NormedSpace.fromTangentSpace p.2 (Manifold.tangentSpaceProdEquiv p v).2 -
        θ.1 p.1 ![(Manifold.tangentSpaceProdEquiv p v).1] := by
  simp only [contactization, Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
    mpullback_apply, mfderiv_fst, mfderiv_snd, realLineCoordForm_apply,
    Matrix.vec_single_eq_const, Manifold.tangentSpaceProdEquiv_apply,
    NormedSpace.fromTangentSpace_apply]
  -- Both sides read off the components of `v`.
  rfl

variable (I) in
/-- The exterior derivative of the contactization form `dz - θ` is `-dθ`, pulled back along the
projection `W × ℝ → W`. -/
theorem mextDerivₗ_contactization (θ : SmoothForm I W ℝ 1) :
    mextDerivₗ (I.prod 𝓘(ℝ)) 1 θ.contactization =
      mpullback Prod.fst contMDiff_fst (-mextDerivₗ I 1 θ) := by
  have hdz : mextDerivₗ 𝓘(ℝ) 1 realLineCoordForm = 0 :=
    (isClosed_iff_mextDerivₗ_eq_zero _).1 isClosed_realLineCoordForm
  rw [contactization, map_sub, mextDerivₗ_mpullback, mextDerivₗ_mpullback, hdz, map_zero,
    zero_sub, map_neg]

/-- The exterior derivative of the contactization form evaluates on two tangent vectors of
`W × ℝ` as `-dθ` on their components in `W`. -/
theorem eval₂_mextDerivₗ_contactization (θ : SmoothForm I W ℝ 1) (p : W × ℝ)
    (v w : TangentSpace (I.prod 𝓘(ℝ)) p) :
    (mextDerivₗ (I.prod 𝓘(ℝ)) 1 θ.contactization).eval₂ p v w =
      (-mextDerivₗ I 1 θ).eval₂ p.1 (Manifold.tangentSpaceProdEquiv p v).1
        (Manifold.tangentSpaceProdEquiv p w).1 := by
  rw [mextDerivₗ_contactization, eval₂_mpullback_fst]

/-- The exterior derivative of the contactization form, evaluated as a rough form on two tangent
vectors, is `-dθ` on their components in `W`. -/
theorem mextDeriv_contactization_apply (θ : SmoothForm I W ℝ 1) (p : W × ℝ)
    (v w : TangentSpace (I.prod 𝓘(ℝ)) p) :
    mextDeriv θ.contactization.1 p ![v, w] =
      (-mextDerivₗ I 1 θ).eval₂ p.1 (Manifold.tangentSpaceProdEquiv p v).1
        (Manifold.tangentSpaceProdEquiv p w).1 := by
  rw [← eval₂_mextDerivₗ_contactization, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply]

/-- The kernel of the contactization form `dz - θ` at `(w, z)` is the graph of `θ_w`: a tangent
vector `(v, c)` lies in it exactly when `c = θ_w(v)`. -/
theorem mem_kerDistribution_contactization {θ : SmoothForm I W ℝ 1} {p : W × ℝ}
    {v : TangentSpace (I.prod 𝓘(ℝ)) p} :
    v ∈ θ.contactization.kerDistribution p ↔
      NormedSpace.fromTangentSpace p.2 (Manifold.tangentSpaceProdEquiv p v).2 =
        θ.1 p.1 ![(Manifold.tangentSpaceProdEquiv p v).1] := by
  rw [mem_kerDistribution, contactization_apply, sub_eq_zero]

/-- The tangent vector `(v, θ_w(v))` at `(w, z)` lies in the kernel of the contactization form. -/
private theorem contactization_apply_graph (θ : SmoothForm I W ℝ 1) (p : W × ℝ)
    (v : TangentSpace I p.1) :
    θ.contactization.1 p ![(Manifold.tangentSpaceProdEquiv p).symm
      (v, (NormedSpace.fromTangentSpace p.2).symm (θ.1 p.1 ![v]))] = 0 :=
  mem_kerDistribution.1 <| mem_kerDistribution_contactization.2 <| by
    simp only [ContinuousLinearEquiv.apply_symm_apply]

/-- **Contactization.** For a one-form `θ` on `W`, the one-form `dz - θ` on `W × ℝ` is a contact
form exactly when `-dθ` is nondegenerate, that is when `(W, -dθ)` is an exact symplectic
manifold. -/
theorem isContactForm_contactization_iff {θ : SmoothForm I W ℝ 1} :
    θ.contactization.IsContactForm ↔ SmoothTwoForm.IsNondegenerate (-mextDerivₗ I 1 θ) := by
  rw [isContactForm_iff, SmoothTwoForm.isNondegenerate_iff_separatingLeft]
  constructor
  · -- A vector `a` in the kernel of `-dθ` at `w` lifts to the vector `(a, θ a)` at `(w, 0)`, which
    -- is in the kernel of `dz - θ` and `d(dz - θ)`-orthogonal to that kernel.
    intro h w a ha
    set e := Manifold.tangentSpaceProdEquiv (I := I) (J := 𝓘(ℝ)) (w, (0 : ℝ))
    have hv := (h (w, 0)).2 (e.symm (a, (NormedSpace.fromTangentSpace 0).symm (θ.1 w ![a])))
      (contactization_apply_graph θ (w, 0) a) fun u _ ↦ by
        rw [mextDeriv_contactization_apply, ContinuousLinearEquiv.apply_symm_apply]
        exact ha _
    simpa using congrArg (fun u ↦ (e u).1) hv
  · intro h p
    refine ⟨⟨(Manifold.tangentSpaceProdEquiv p).symm (0, (NormedSpace.fromTangentSpace p.2).symm 1),
      ?_⟩, fun v hv hvw ↦ ?_⟩
    · simp only [contactization_apply, ContinuousLinearEquiv.apply_symm_apply]
      rw [(θ.1 p.1).map_coord_zero 0 rfl, sub_zero]
      exact one_ne_zero
    rw [contactization_apply, sub_eq_zero] at hv
    set e := Manifold.tangentSpaceProdEquiv (I := I) (J := 𝓘(ℝ)) p
    -- The `W`-component of `v` is in the kernel of `-dθ`, by testing against the lifts
    -- `(b, θ b)` of all tangent vectors `b` of `W`.
    have h₁ : (e v).1 = 0 := h p.1 _ fun b ↦ by
      have := hvw (e.symm (b, (NormedSpace.fromTangentSpace p.2).symm (θ.1 p.1 ![b])))
        (contactization_apply_graph θ p b)
      rwa [mextDeriv_contactization_apply, ContinuousLinearEquiv.apply_symm_apply] at this
    -- Its real component is then `θ` of the zero vector.
    have h₂ : (e v).2 = 0 := by
      rw [h₁, (θ.1 p.1).map_coord_zero 0 rfl] at hv
      exact (NormedSpace.fromTangentSpace p.2).map_eq_zero_iff.1 hv
    exact e.injective (by rw [map_zero]; exact Prod.ext h₁ h₂)

end SmoothForm

/-! ### Change of primitive -/

section Shift

variable {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W] [IsManifold I ∞ W]
  {g : W → ℝ}

variable (I) in
/-- The diffeomorphism `(w, z) ↦ (w, z - g w)` of `W × ℝ`, for a smooth function `g` on `W`. It
pulls the contactization form of a one-form `θ` back to the contactization form of `θ + dg`
(`TauCeti.mpullback_contactizationShift_contactization`). -/
def contactizationShift (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    (W × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ), I.prod 𝓘(ℝ)⟯ (W × ℝ) where
  toFun p := (p.1, p.2 - g p.1)
  invFun p := (p.1, p.2 + g p.1)
  left_inv p := by simp
  right_inv p := by simp
  contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_snd.sub (hg.comp contMDiff_fst))
  contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_snd.add (hg.comp contMDiff_fst))

omit [IsManifold I ∞ W] in
@[simp]
theorem contactizationShift_apply (hg : ContMDiff I 𝓘(ℝ) ∞ g) (p : W × ℝ) :
    contactizationShift I hg p = (p.1, p.2 - g p.1) :=
  (rfl)

omit [IsManifold I ∞ W] in
@[simp]
theorem contactizationShift_symm_apply (hg : ContMDiff I 𝓘(ℝ) ∞ g) (p : W × ℝ) :
    (contactizationShift I hg).symm p = (p.1, p.2 + g p.1) :=
  (rfl)

/-- **Change of primitive.** If `θ' = θ + dg` for a smooth function `g` on `W`, then the
diffeomorphism `(w, z) ↦ (w, z - g w)` of `W × ℝ` pulls the contactization form `dz - θ` back to
`dz - θ'`. When `-dθ` is nondegenerate, so that both forms are contact forms, it is therefore a
strict contactomorphism between the two contactizations. -/
theorem mpullback_contactizationShift_contactization (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    {θ θ' : SmoothForm I W ℝ 1} (hθ' : θ'.1 = θ.1 + mextDeriv (RoughForm.ofFunction I g)) :
    SmoothForm.mpullback (contactizationShift I hg) (contactizationShift I hg).contMDiff
      θ.contactization = θ'.contactization := by
  have hΦ := (contactizationShift I hg).contMDiff.mdifferentiable (by simp)
  have hgf : MDifferentiable (I.prod 𝓘(ℝ)) 𝓘(ℝ) (g ∘ Prod.fst : W × ℝ → ℝ) :=
    (hg.comp contMDiff_fst).mdifferentiable (by simp)
  have hsub : MDifferentiable (I.prod 𝓘(ℝ)) 𝓘(ℝ) (Prod.snd - g ∘ Prod.fst : W × ℝ → ℝ) :=
    (contMDiff_snd.sub (hg.comp contMDiff_fst)).mdifferentiable (by simp)
  -- The shift changes the coordinate `z` by `-g`, so it pulls `dz` back to `d(z - g)`.
  have hdz : mpullback (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (contactizationShift I hg)
      (mpullback (I.prod 𝓘(ℝ)) 𝓘(ℝ) Prod.snd SmoothForm.realLineCoordForm.1) =
        mextDeriv (RoughForm.ofFunction (I.prod 𝓘(ℝ)) (Prod.snd - g ∘ Prod.fst : W × ℝ → ℝ)) := by
    rw [← mpullback_comp hΦ mdifferentiable_snd]
    exact SmoothForm.mpullback_realLineCoordForm _
  -- The shift fixes the first coordinate, so it fixes forms pulled back from `W`.
  have hθ : mpullback (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (contactizationShift I hg)
      (mpullback (I.prod 𝓘(ℝ)) I Prod.fst θ.1) =
        mpullback (I.prod 𝓘(ℝ)) I Prod.fst θ.1 := by
    rw [← mpullback_comp hΦ mdifferentiable_fst]
    rfl
  -- `dz = d(z - g) + d(g ∘ pr₁)` on `W × ℝ`.
  have hsplit : mextDeriv (RoughForm.ofFunction (I.prod 𝓘(ℝ)) (Prod.snd : W × ℝ → ℝ)) =
      mextDeriv (RoughForm.ofFunction (I.prod 𝓘(ℝ)) (Prod.snd - g ∘ Prod.fst : W × ℝ → ℝ)) +
        mextDeriv (RoughForm.ofFunction (I.prod 𝓘(ℝ)) (g ∘ Prod.fst : W × ℝ → ℝ)) := by
    rw [← mextDeriv_ofFunction_add hsub hgf, sub_add_cancel]
  -- Pulling `dg` back to `W × ℝ` gives `d(g ∘ pr₁)`.
  have hdg : mpullback (I.prod 𝓘(ℝ)) I Prod.fst (mextDeriv (RoughForm.ofFunction I g)) =
      mextDeriv (RoughForm.ofFunction (I.prod 𝓘(ℝ)) (g ∘ Prod.fst : W × ℝ → ℝ)) :=
    mpullback_mextDeriv_ofFunction mdifferentiable_fst (hg.mdifferentiable (by simp))
  apply Subtype.ext
  simp only [SmoothForm.contactization, map_sub, Submodule.coe_sub, SmoothForm.coe_mpullback]
  rw [hdz, hθ, hθ', mpullback_add, hdg, SmoothForm.mpullback_realLineCoordForm, hsplit]
  abel

end Shift

namespace CotangentBundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The one-jet space is a contact manifold.** On `J¹M = T*M × ℝ`, the one-form `dz - λ`, for
the Liouville form `λ` of the cotangent bundle, is a contact form. -/
theorem isContactForm_contactization_liouvilleForm :
    (liouvilleForm I M).contactization.IsContactForm :=
  SmoothForm.isContactForm_contactization_iff.2 <| by
    rw [← symplecticForm_eq_neg_mextDerivₗ]
    exact isSymplectic_symplecticForm.isNondegenerate

end CotangentBundle

end TauCeti
