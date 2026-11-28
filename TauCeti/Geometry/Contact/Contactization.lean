/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Contact.Isotropic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Symplectic.Lagrangian.Exact
import TauCeti.Geometry.Contact.Pullback
import TauCeti.Geometry.Contact.Volume
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic

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

When `W` has dimension `2 n`, the contact volume of `α` is the product volume:
`α ∧ (dα)ⁿ = dz ∧ ωⁿ` (`TauCeti.SmoothForm.wedge_contactization_wedgePow_mextDerivₗ`). Indeed
`α ∧ (dα)ⁿ = dz ∧ ωⁿ - θ ∧ ωⁿ`, and `θ ∧ ωⁿ` is pulled back from a form of degree `2 n + 1` on
`W`, which vanishes. So `dz ∧ ωⁿ` vanishes nowhere when `ω` is nondegenerate
(`TauCeti.SmoothForm.wedge_mpullback_realLineCoordForm_wedgePow_apply_ne_zero`).

For the cotangent bundle `W = T*Q` with its Liouville form `λ_Q`, this is the standard contact
form `dz - λ_Q` of the space of one-jets `J¹Q = T*Q × ℝ`
(`TauCeti.CotangentBundle.isContactForm_contactization_liouvilleForm`).

The construction depends on the primitive `θ`, not only on `ω`. Changing `θ` by an exact form
`dg` changes the coordinate `z`: the diffeomorphism `(w, z) ↦ (w, z - g w)` of `W × ℝ`
(`TauCeti.contactizationShift`) pulls the contactization form of `θ` back to the contactization
form of `θ + dg` (`TauCeti.mpullback_contactizationShift_contactization`). So the two contact forms
are identified by a strict contactomorphism.

For smooth maps `ι : L → W` and `h : L → ℝ`, the map `x ↦ (ι x, h x)` pulls `dz - θ` back to
`dh - ι^* θ` (`TauCeti.SmoothForm.mpullback_prodMk_contactization`). Hence it is horizontal for
the distribution `ker (dz - θ)` exactly when `ι^* θ = dh`
(`TauCeti.SmoothForm.isHorizontalMap_contactization_iff`). This is the **Legendrian lift**: when
`ω = -dθ` is nondegenerate, so that `ker (dz - θ)` is a contact structure, an exact Lagrangian
map `ι` for `ω` with primitive `h` lifts to the isotropic map `(ι, h)`, which is a
Legendrian immersion when `ι` is an immersion and a Legendrian embedding when `ι` is an embedding
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsExactLagrangianMap.isLegendrianImmersion_contactization`,
`TauCeti.SmoothTwoForm.IsNondegenerate.IsExactLagrangianMap.isLegendrianEmbedding_contactization`).
Conversely, for maps of half the dimension with injective differentials, `ι` is exact Lagrangian
with primitive `h` as soon as its lift is horizontal
(`TauCeti.SmoothTwoForm.IsNondegenerate.isExactLagrangianMap_iff_isHorizontalMap_contactization`),
the projection `ι` of any horizontal immersed lift `(ι, h)` is an immersion
(`TauCeti.SmoothForm.isImmersion_of_isHorizontalMap_contactization`), and the projection of any
Legendrian immersion `(ι, h)` into the contactization is an exact Lagrangian immersion with
primitive `h` (`TauCeti.IsLegendrianImmersion.isExactLagrangianMap_contactization`): the
Legendrian immersions into `W × ℝ` are exactly the lifts of the exact Lagrangian immersions of `W`.

## Main definitions

* `TauCeti.SmoothForm.contactization θ`: the one-form `dz - θ` on `W × ℝ`.
* `TauCeti.contactizationShift`: the diffeomorphism `(w, z) ↦ (w, z - g w)`.

## Main results

* `TauCeti.SmoothForm.mextDerivₗ_contactization`: `d(dz - θ) = -dθ`.
* `TauCeti.SmoothForm.mpullback_prodMk_contactization`: `(ι, h)^* (dz - θ) = dh - ι^* θ`.
* `TauCeti.SmoothForm.mpullback_prodMap_id_contactization`: `(f × id)^* (dz - θ) = dz - f^* θ`.
* `TauCeti.SmoothForm.isContactForm_contactization_iff`: `dz - θ` is a contact form exactly when
  `-dθ` is nondegenerate.
* `TauCeti.SmoothForm.wedge_contactization_wedgePow_mextDerivₗ`: the contact volume formula
  `α ∧ (dα)ⁿ = dz ∧ ωⁿ` for `α = dz - θ` and `ω = -dθ`.
* `TauCeti.mpullback_contactizationShift_contactization`: change of primitive.
* `TauCeti.mpullback_comp_contactizationShift_eq_contactization`,
  `PartialDiffeomorph.exists_prod_contactizationShift`: pullback and chart
  composition for `contactizationShift`.
* `TauCeti.SmoothForm.isHorizontalMap_contactization_iff`: `(ι, h)` is horizontal exactly when
  `ι^* θ = dh`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.IsExactLagrangianMap.isLegendrianImmersion_contactization`:
  the Legendrian lift of an exact Lagrangian immersion.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isExactLagrangianMap_iff_isHorizontalMap_contactization`:
  a half-dimensional map is exact Lagrangian exactly when its lift is horizontal.
* `TauCeti.SmoothForm.isImmersion_of_isHorizontalMap_contactization` and
  `TauCeti.IsLegendrianImmersion.isExactLagrangianMap_contactization`: the projection of a
  horizontal immersed lift is an immersion, and that of a Legendrian immersion into the
  contactization is an exact Lagrangian map.
* `TauCeti.CotangentBundle.isContactForm_contactization_liouvilleForm`: the one-jet space of a
  manifold is a contact manifold.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Chapter 2 (contact manifolds, including the space of one-jets).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (contact structures).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Appendix 4
  (Legendrian lifts of exact Lagrangian submanifolds).
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

/-- The contactization form is `dz - θ`, with `dz` and `θ` pulled back along the two
projections of `W × ℝ`. -/
theorem contactization_def (θ : SmoothForm I W ℝ 1) :
    θ.contactization =
      mpullback Prod.snd contMDiff_snd realLineCoordForm - mpullback Prod.fst contMDiff_fst θ :=
  (rfl)

/-- The contactization form sends a tangent vector `(v, c)` at `(w, z)` to `c - θ_w(v)`. -/
@[simp]
theorem contactization_apply (θ : SmoothForm I W ℝ 1) (p : W × ℝ)
    (v : TangentSpace (I.prod 𝓘(ℝ)) p) :
    θ.contactization.val p ![v] =
      NormedSpace.fromTangentSpace p.2 (Manifold.tangentSpaceProdEquiv p v).2 -
        θ.val p.1 ![(Manifold.tangentSpaceProdEquiv p v).1] := by
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
    mextDeriv θ.contactization.val p ![v, w] =
      (-mextDerivₗ I 1 θ).eval₂ p.1 (Manifold.tangentSpaceProdEquiv p v).1
        (Manifold.tangentSpaceProdEquiv p w).1 := by
  rw [← eval₂_mextDerivₗ_contactization, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply]

/-- The kernel of the contactization form `dz - θ` at `(w, z)` is the graph of `θ_w`: a tangent
vector `(v, c)` lies in it exactly when `c = θ_w(v)`. -/
theorem mem_kerDistribution_contactization {θ : SmoothForm I W ℝ 1} {p : W × ℝ}
    {v : TangentSpace (I.prod 𝓘(ℝ)) p} :
    v ∈ θ.contactization.kerDistribution p ↔
      NormedSpace.fromTangentSpace p.2 (Manifold.tangentSpaceProdEquiv p v).2 =
        θ.val p.1 ![(Manifold.tangentSpaceProdEquiv p v).1] := by
  rw [mem_kerDistribution, contactization_apply, sub_eq_zero]

/-- For smooth maps `ι : L → W` and `h : L → ℝ`, the map `x ↦ (ι x, h x)` pulls the contactization
form `dz - θ` back to `dh - ι^* θ`. -/
theorem mpullback_prodMk_contactization {E' H' L : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace L]
    [ChartedSpace H' L] [IsManifold J ∞ L] (θ : SmoothForm I W ℝ 1) {ι : L → W} {h : L → ℝ}
    (hι : ContMDiff J I ∞ ι) (hh : ContMDiff J 𝓘(ℝ) ∞ h) :
    (mpullback (fun x ↦ (ι x, h x)) (hι.prodMk hh) θ.contactization).val =
      mextDeriv (RoughForm.ofFunction J h) - (mpullback ι hι θ).val := by
  -- The two projections of `x ↦ (ι x, h x)` are `ι` and `h`.
  have hfst : Prod.fst ∘ (fun x ↦ (ι x, h x)) = ι := rfl
  have hsnd : Prod.snd ∘ (fun x ↦ (ι x, h x)) = h := rfl
  rw [contactization, map_sub, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← mpullback_comp, ← mpullback_comp, Submodule.coe_sub, coe_mpullback]
  simp only [hfst, hsnd, SmoothForm.mpullback_realLineCoordForm]

/-- For a smooth map `f : L → W`, the product map `Prod.map f id : L × ℝ → W × ℝ` pulls the
contactization form `dz - θ` back to the contactization form `dz - f^* θ`. -/
@[simp]
theorem mpullback_prodMap_id_contactization {E' H' L : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace L]
    [ChartedSpace H' L] [IsManifold J ∞ L] (θ : SmoothForm I W ℝ 1) {f : L → W}
    (hf : ContMDiff J I ∞ f) :
    mpullback (Prod.map f id) (hf.prodMap contMDiff_id) θ.contactization =
      (mpullback f hf θ).contactization := by
  have hfst : Prod.fst ∘ Prod.map f (id : ℝ → ℝ) = f ∘ Prod.fst := rfl
  have hsnd : Prod.snd ∘ Prod.map f (id : ℝ → ℝ) = Prod.snd := rfl
  rw [contactization, contactization, map_sub, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← mpullback_comp, ← mpullback_comp, ← LinearMap.comp_apply, ← mpullback_comp]
  simp only [hfst, hsnd]

/-- The tangent vector `(v, θ_w(v))` at `(w, z)` lies in the kernel of the contactization form. -/
private theorem contactization_apply_graph (θ : SmoothForm I W ℝ 1) (p : W × ℝ)
    (v : TangentSpace I p.1) :
    θ.contactization.val p ![(Manifold.tangentSpaceProdEquiv p).symm
      (v, (NormedSpace.fromTangentSpace p.2).symm (θ.val p.1 ![v]))] = 0 :=
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
    have hv := (h (w, 0)).2 (e.symm (a, (NormedSpace.fromTangentSpace 0).symm (θ.val w ![a])))
      (contactization_apply_graph θ (w, 0) a) fun u _ ↦ by
        rw [mextDeriv_contactization_apply, ContinuousLinearEquiv.apply_symm_apply]
        exact ha _
    simpa using congrArg (fun u ↦ (e u).1) hv
  · intro h p
    refine ⟨⟨(Manifold.tangentSpaceProdEquiv p).symm (0, (NormedSpace.fromTangentSpace p.2).symm 1),
      ?_⟩, fun v hv hvw ↦ ?_⟩
    · simp only [contactization_apply, ContinuousLinearEquiv.apply_symm_apply]
      rw [(θ.val p.1).map_coord_zero 0 rfl, sub_zero]
      exact one_ne_zero
    rw [contactization_apply, sub_eq_zero] at hv
    set e := Manifold.tangentSpaceProdEquiv (I := I) (J := 𝓘(ℝ)) p
    -- The `W`-component of `v` is in the kernel of `-dθ`, by testing against the lifts
    -- `(b, θ b)` of all tangent vectors `b` of `W`.
    have h₁ : (e v).1 = 0 := h p.1 _ fun b ↦ by
      have := hvw (e.symm (b, (NormedSpace.fromTangentSpace p.2).symm (θ.val p.1 ![b])))
        (contactization_apply_graph θ p b)
      rwa [mextDeriv_contactization_apply, ContinuousLinearEquiv.apply_symm_apply] at this
    -- Its real component is then `θ` of the zero vector.
    have h₂ : (e v).2 = 0 := by
      rw [h₁, (θ.val p.1).map_coord_zero 0 rfl] at hv
      exact (NormedSpace.fromTangentSpace p.2).map_eq_zero_iff.1 hv
    exact e.injective (by rw [map_zero]; exact Prod.ext h₁ h₂)

/-! ### The contact volume -/

variable [FiniteDimensional ℝ E] {n : ℕ}

variable (I) in
/-- **The contact volume of a contactization.** If the model space of `W` has dimension at most
`2 n`, the contactization form `α = dz - θ` on `W × ℝ` satisfies `α ∧ (dα)ⁿ = dz ∧ ωⁿ` with
`ω = -dθ`, where `dz` and `ωⁿ` are pulled back along the two projections. -/
theorem wedge_contactization_wedgePow_mextDerivₗ (hn : Module.finrank ℝ E ≤ 2 * n)
    (θ : SmoothForm I W ℝ 1) :
    wedge θ.contactization ((mextDerivₗ (I.prod 𝓘(ℝ)) 1 θ.contactization).wedgePow n) =
      wedge (mpullback Prod.snd contMDiff_snd realLineCoordForm)
        (mpullback Prod.fst contMDiff_fst ((-mextDerivₗ I 1 θ).wedgePow n)) := by
  -- `α ∧ (dα)ⁿ = dz ∧ ωⁿ - θ ∧ ωⁿ`, and `θ ∧ ωⁿ` has degree `2 n + 1` on `W`, so it vanishes.
  rw [mextDerivₗ_contactization, ← mpullback_wedgePow, contactization, map_sub,
    LinearMap.sub_apply, ← mpullback_wedge,
    eq_zero_of_finrank_lt (by omega) (wedge θ ((-mextDerivₗ I 1 θ).wedgePow n)), map_zero,
    sub_zero]

/-- **The contactization volume vanishes nowhere.** If `W` has dimension `2 n` and `ω = -dθ` is
nondegenerate, the volume form `dz ∧ ωⁿ` on `W × ℝ`, which is the contact volume `α ∧ (dα)ⁿ` of
the contactization form `α = dz - θ`, vanishes nowhere. -/
theorem wedge_mpullback_realLineCoordForm_wedgePow_apply_ne_zero (hn : Module.finrank ℝ E = 2 * n)
    {θ : SmoothForm I W ℝ 1} (hθ : SmoothTwoForm.IsNondegenerate (-mextDerivₗ I 1 θ))
    (p : W × ℝ) :
    (wedge (mpullback Prod.snd contMDiff_snd realLineCoordForm)
      (mpullback Prod.fst contMDiff_fst ((-mextDerivₗ I 1 θ).wedgePow n))).val p ≠ 0 := by
  have hn' : Module.finrank ℝ (E × ℝ) = 2 * n + 1 := by
    rw [Module.finrank_prod, Module.finrank_self, hn]
  rw [← wedge_contactization_wedgePow_mextDerivₗ I hn.le]
  exact (isContactForm_iff_wedge_wedgePow_apply_ne_zero hn' _).1
    (isContactForm_contactization_iff.2 hθ) p

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
    {θ θ' : SmoothForm I W ℝ 1} (hθ' : θ'.val = θ.val + mextDeriv (RoughForm.ofFunction I g)) :
    SmoothForm.mpullback (contactizationShift I hg) (contactizationShift I hg).contMDiff
      θ.contactization = θ'.contactization := by
  have hΦ := (contactizationShift I hg).contMDiff.mdifferentiable (by simp)
  have hgf : MDifferentiable (I.prod 𝓘(ℝ)) 𝓘(ℝ) (g ∘ Prod.fst : W × ℝ → ℝ) :=
    (hg.comp contMDiff_fst).mdifferentiable (by simp)
  have hsub : MDifferentiable (I.prod 𝓘(ℝ)) 𝓘(ℝ) (Prod.snd - g ∘ Prod.fst : W × ℝ → ℝ) :=
    (contMDiff_snd.sub (hg.comp contMDiff_fst)).mdifferentiable (by simp)
  -- The shift changes the coordinate `z` by `-g`, so it pulls `dz` back to `d(z - g)`.
  have hdz : mpullback (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (contactizationShift I hg)
      (mpullback (I.prod 𝓘(ℝ)) 𝓘(ℝ) Prod.snd SmoothForm.realLineCoordForm.val) =
        mextDeriv (RoughForm.ofFunction (I.prod 𝓘(ℝ)) (Prod.snd - g ∘ Prod.fst : W × ℝ → ℝ)) := by
    rw [← mpullback_comp hΦ mdifferentiable_snd]
    exact SmoothForm.mpullback_realLineCoordForm _
  -- The shift fixes the first coordinate, so it fixes forms pulled back from `W`.
  have hθ : mpullback (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (contactizationShift I hg)
      (mpullback (I.prod 𝓘(ℝ)) I Prod.fst θ.val) =
        mpullback (I.prod 𝓘(ℝ)) I Prod.fst θ.val := by
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

/-- Pulling back a one-form along the four-step composition
`assoc ∘ Prod.map inc id ∘ contactizationShift g ∘ Prod.map e id` reduces to the contactization of
`e^* β` whenever `assoc^* α = θ.contactization` and `β = inc^* θ + dg`. -/
theorem mpullback_comp_contactizationShift_eq_contactization
    {E₁ H₁ M₁ E₂ H₂ M₂ E₃ H₃ M₃ E₄ H₄ M₄ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [TopologicalSpace H₃]
    {I₃ : ModelWithCorners ℝ E₃ H₃} [TopologicalSpace M₃] [ChartedSpace H₃ M₃] [IsManifold I₃ ∞ M₃]
    [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [TopologicalSpace H₄]
    {I₄ : ModelWithCorners ℝ E₄ H₄} [TopologicalSpace M₄] [ChartedSpace H₄ M₄] [IsManifold I₄ ∞ M₄]
    {e : M₁ → M₂} (he : ContMDiff I₁ I₂ ∞ e)
    {g : M₂ → ℝ} (hg : ContMDiff I₂ 𝓘(ℝ) ∞ g)
    {inc : M₂ → M₃} (hinc : ContMDiff I₂ I₃ ∞ inc)
    {assoc : M₃ × ℝ → M₄} (hassoc : ContMDiff (I₃.prod 𝓘(ℝ)) I₄ ∞ assoc)
    {α : SmoothForm I₄ M₄ ℝ 1} {θ : SmoothForm I₃ M₃ ℝ 1} {β : SmoothForm I₂ M₂ ℝ 1}
    (hassoc_pull : SmoothForm.mpullback assoc hassoc α = θ.contactization)
    (hshift_eq : β.val =
      (SmoothForm.mpullback inc hinc θ).val + mextDeriv (RoughForm.ofFunction I₂ g)) :
    SmoothForm.mpullback
      (assoc ∘ Prod.map inc id ∘ contactizationShift I₂ hg ∘ Prod.map e id)
      (hassoc.comp ((hinc.prodMap contMDiff_id).comp
        ((contactizationShift I₂ hg).contMDiff.comp (he.prodMap contMDiff_id)))) α =
      (SmoothForm.mpullback e he β).contactization := by
  rw [SmoothForm.mpullback_comp _ _
      ((hinc.prodMap contMDiff_id).comp
        ((contactizationShift I₂ hg).contMDiff.comp (he.prodMap contMDiff_id))) hassoc,
    LinearMap.comp_apply, hassoc_pull,
    SmoothForm.mpullback_comp _ _
      ((contactizationShift I₂ hg).contMDiff.comp (he.prodMap contMDiff_id))
      (hinc.prodMap contMDiff_id),
    LinearMap.comp_apply, SmoothForm.mpullback_prodMap_id_contactization θ hinc,
    SmoothForm.mpullback_comp _ _ (he.prodMap contMDiff_id) (contactizationShift I₂ hg).contMDiff,
    LinearMap.comp_apply, mpullback_contactizationShift_contactization hg hshift_eq,
    SmoothForm.mpullback_prodMap_id_contactization β he]

/-- Compose a partial diffeomorphism `ψ : M → M'` with `contactizationShift` for a smooth
function `g : B → ℝ` on a nonempty open subset `B : Opens M'` to obtain a partial
diffeomorphism `Ω : M × ℝ → M' × ℝ` together with the restricted map `e_B : W_ψ → B`. -/
theorem _root_.PartialDiffeomorph.exists_prod_contactizationShift {E H M E' H' M' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
    (ψ : PartialDiffeomorph I I' M M' ∞) {B : TopologicalSpace.Opens M'} (hB : Nonempty B)
    {g : B → ℝ} (hg : ContMDiff I' 𝓘(ℝ) ∞ g) :
    ∃ (W_ψ : TopologicalSpace.Opens M) (e_B : W_ψ → B)
      (Ω : PartialDiffeomorph (I.prod 𝓘(ℝ)) (I'.prod 𝓘(ℝ)) (M × ℝ) (M' × ℝ) ∞),
      ContMDiff I I' ∞ e_B ∧
      (∀ x : W_ψ, x.val ∈ ψ.source) ∧
      (∀ x : W_ψ, (e_B x : M') = ψ x.val) ∧
      (∀ q : M × ℝ, q ∈ Ω.source ↔ q.1 ∈ (W_ψ : Set M)) ∧
      (∀ q : M × ℝ, q ∈ Ω.source ↔ q.1 ∈ ψ.source ∧ ψ q.1 ∈ (B : Set M')) ∧
      (∀ (q : M × ℝ) (hqB : ψ q.1 ∈ (B : Set M')), Ω q = (ψ q.1, q.2 - g ⟨ψ q.1, hqB⟩)) ∧
      ⇑Ω ∘ (Prod.map (Subtype.val : W_ψ → M) (id : ℝ → ℝ)) =
        Prod.map Subtype.val id ∘ contactizationShift I' hg ∘ Prod.map e_B id := by
  let sv_B := PartialDiffeomorph.subtypeVal I' ∞ B hB
  let ψ_B := ψ.trans sv_B.symm
  let id_ℝ := (Diffeomorph.refl 𝓘(ℝ) ℝ ∞).toPartialDiffeomorph
  let shift := (contactizationShift I' hg).toPartialDiffeomorph
  let inc_B := sv_B.prod id_ℝ
  let Ω := (ψ_B.prod id_ℝ).trans (shift.trans inc_B)
  have hψB_src : ψ_B.source = ψ.source ∩ ψ ⁻¹' (B : Set M') := by
    rw [PartialDiffeomorph.trans_source, PartialDiffeomorph.symm_toPartialEquiv,
      PartialEquiv.symm_source, PartialDiffeomorph.subtypeVal_target]
  have hψB_coe (x : M) : ψ_B x = sv_B.symm (ψ x) := by
    rw [PartialDiffeomorph.coe_trans, Function.comp_apply]
  have hψB_val (x : M) (hx : ψ x ∈ (B : Set M')) : (ψ_B x : M') = ψ x := by
    rw [hψB_coe, PartialDiffeomorph.symm_toPartialEquiv,
      PartialDiffeomorph.subtypeVal_symm_apply B hB hx]
  have hsrc (q : M × ℝ) : q ∈ Ω.source ↔ q.1 ∈ ψ_B.source := by
    simp only [Ω, inc_B, id_ℝ, shift, sv_B, PartialDiffeomorph.trans_source,
      PartialDiffeomorph.prod_source, PartialDiffeomorph.subtypeVal_source,
      Diffeomorph.toPartialDiffeomorph_toPartialEquiv, Equiv.toPartialEquiv_source,
      Set.univ_prod_univ, Set.preimage_univ, Set.inter_univ, Set.mem_prod, Set.mem_univ, and_true]
  have hΩ_coe (q : M × ℝ) :
      Ω q = ((contactizationShift I' hg (ψ_B q.1, q.2)).1.val,
        (contactizationShift I' hg (ψ_B q.1, q.2)).2) := by
    simp only [Ω, inc_B, id_ℝ, shift, sv_B, PartialDiffeomorph.coe_trans,
      Function.comp_apply, PartialDiffeomorph.prod_apply, Diffeomorph.coe_toPartialDiffeomorph,
      Diffeomorph.coe_refl, id_eq, PartialDiffeomorph.coe_subtypeVal]
  let W_ψ : TopologicalSpace.Opens M := ⟨ψ_B.source, ψ_B.open_source⟩
  let e_B : W_ψ → B := fun x ↦ ψ_B x.val
  have he_B : ContMDiff I I' ∞ e_B :=
    ψ_B.contMDiffOn.comp_contMDiff contMDiff_subtypeVal fun x ↦ x.property
  have hx_mem (x : W_ψ) : x.val ∈ ψ.source ∩ ψ ⁻¹' (B : Set M') := by
    have hx_src : x.val ∈ ψ_B.source := by
      simpa only [W_ψ, TopologicalSpace.Opens.mem_mk] using x.property
    exact hψB_src ▸ hx_src
  refine ⟨W_ψ, e_B, Ω, he_B, fun x ↦ (hx_mem x).1, fun x ↦ hψB_val x.val (hx_mem x).2,
    hsrc, fun q ↦ by rw [hsrc, hψB_src, Set.mem_inter_iff, Set.mem_preimage],
    fun q hqB ↦ ?_, funext fun ⟨x, t⟩ ↦ ?_⟩
  · rw [hΩ_coe, contactizationShift_apply, hψB_val q.1 hqB]
    congr 2
    rw [hψB_coe, PartialDiffeomorph.symm_toPartialEquiv,
      PartialDiffeomorph.subtypeVal_symm_apply B hB hqB]
  · simp only [Function.comp_apply, Prod.map, id_eq, e_B, hΩ_coe]

/-! ### Lifts to the contactization -/

section Lifts

open Module

variable {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace W] [ChartedSpace H W] [IsManifold I ∞ W]
  {E' H' L : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace L] [ChartedSpace H' L] [IsManifold J ∞ L]
  {ι : L → W} {h : L → ℝ}

namespace SmoothForm

/-- **Legendrian lifts.** The map `x ↦ (ι x, h x)` is horizontal for the kernel of the
contactization form `dz - θ` exactly when `ι` pulls `θ` back to `dh`. -/
theorem isHorizontalMap_contactization_iff (θ : SmoothForm I W ℝ 1) (hι : ContMDiff J I ∞ ι)
    (hh : ContMDiff J 𝓘(ℝ) ∞ h) :
    IsHorizontalMap J θ.contactization.kerDistribution (fun x ↦ (ι x, h x)) ↔
      (mpullback ι hι θ).val = mextDeriv (RoughForm.ofFunction J h) := by
  rw [isHorizontalMap_kerDistribution_iff_mpullback_eq_zero _ (hι.prodMk hh), ← Subtype.coe_inj,
    mpullback_prodMk_contactization θ hι hh, ZeroMemClass.coe_zero, sub_eq_zero, eq_comm]

/-- **Projections of horizontal immersed lifts are immersions.** If the lift `x ↦ (ι x, h x)` is an
immersion which is horizontal for the contact structure `ker (dz - θ)`, then `ι` is an immersion:
a tangent vector killed by `dι` is killed by `dh = θ ∘ dι` as well. -/
theorem isImmersion_of_isHorizontalMap_contactization [FiniteDimensional ℝ E] [I.Boundaryless]
    [J.Boundaryless] (θ : SmoothForm I W ℝ 1)
    (himm : Manifold.IsImmersion J (I.prod 𝓘(ℝ)) ∞ (fun x ↦ (ι x, h x)))
    (hhor : IsHorizontalMap J θ.contactization.kerDistribution (fun x ↦ (ι x, h x))) :
    Manifold.IsImmersion J I ∞ ι := by
  have hι : ContMDiff J I ∞ ι := contMDiff_fst.comp himm.contMDiff
  have hh : ContMDiff J 𝓘(ℝ) ∞ h := contMDiff_snd.comp himm.contMDiff
  have hpull := (isHorizontalMap_contactization_iff θ hι hh).1 hhor
  rw [coe_mpullback] at hpull
  have hdh (x : L) (u : TangentSpace J x) :
      mfderiv J 𝓘(ℝ) h x u = θ.val (ι x) ![mfderiv J I ι x u] := by
    have := congr($hpull x ![u])
    rw [_root_.TauCeti.mpullback_apply, mextDeriv_ofFunction_apply] at this
    rw [← this]
    congr 1
    ext j
    fin_cases j
    rfl
  refine hι.isImmersion_of_injective_mfderiv (by simp) fun x v w hvw ↦
    himm.mfderiv_injective (by simp) x ?_
  rw [mfderiv_prodMk (hι.mdifferentiable (by simp) x) (hh.mdifferentiable (by simp) x)]
  exact Prod.ext hvw ((hdh x v).trans (by rw [hvw]; exact (hdh x w).symm))

end SmoothForm

namespace SmoothTwoForm.IsNondegenerate

variable {σ : SmoothTwoForm I W} {hσ : σ.IsNondegenerate} {θ : SmoothForm I W ℝ 1}

/-- The Legendrian lift `(ι, h)` of an exact Lagrangian map `ι` with primitive `h` is horizontal
for the kernel of the contactization form `dz - θ`. -/
theorem IsExactLagrangianMap.isHorizontalMap_contactization (hL : hσ.IsExactLagrangianMap J θ ι h)
    (hι : ContMDiff J I ∞ ι) :
    IsHorizontalMap J θ.contactization.kerDistribution (fun x ↦ (ι x, h x)) := by
  rw [SmoothForm.isHorizontalMap_contactization_iff θ hι hL.contMDiff_primitive,
    SmoothForm.coe_mpullback]
  exact hL.mpullback_eq

/-- **Projections of horizontal lifts are exact Lagrangian.** Let `σ = -dθ`. A smooth map
`ι : L → W` with injective differentials from a manifold of half the dimension is an exact
Lagrangian map with smooth primitive `h` exactly when its lift `x ↦ (ι x, h x)` is horizontal for
the kernel of the contactization form `dz - θ`. -/
theorem isExactLagrangianMap_iff_isHorizontalMap_contactization [FiniteDimensional ℝ E]
    (hθ : σ = -mextDerivₗ I 1 θ) (hι : ContMDiff J I ∞ ι) (hh : ContMDiff J 𝓘(ℝ) ∞ h)
    (hinj : ∀ x, Function.Injective (mfderiv J I ι x)) (hdim : 2 * finrank ℝ E' = finrank ℝ E) :
    hσ.IsExactLagrangianMap J θ ι h ↔
      IsHorizontalMap J θ.contactization.kerDistribution (fun x ↦ (ι x, h x)) := by
  rw [isExactLagrangianMap_iff_of_finrank hθ hι hinj hdim,
    SmoothForm.isHorizontalMap_contactization_iff θ hι hh, SmoothForm.coe_mpullback,
    and_iff_right hh]

variable [CompleteSpace E] [FiniteDimensional ℝ E] [I.Boundaryless] [J.Boundaryless]

/-- **The Legendrian lift of an exact Lagrangian immersion.** Let `σ = -dθ`. If `ι : L → W` is an
immersion from a nonempty manifold which is an exact Lagrangian map with primitive `h`, then
`x ↦ (ι x, h x)` is a Legendrian immersion for the contact structure `ker (dz - θ)`. -/
theorem IsExactLagrangianMap.isLegendrianImmersion_contactization [Nonempty L]
    (hθ : σ = -mextDerivₗ I 1 θ) (hL : hσ.IsExactLagrangianMap J θ ι h)
    (hι : Manifold.IsImmersion J I ∞ ι) :
    IsLegendrianImmersion J θ.contactization.kerDistribution (fun x ↦ (ι x, h x)) where
  isContactDistribution :=
    -- The kernel of `dz - θ` is a `C¹` contact structure, which needs a `C²` manifold structure.
    have : IsManifold (I.prod 𝓘(ℝ)) (1 + 1) (W × ℝ) := .of_le (n := ∞) (by norm_num)
    (SmoothForm.isContactForm_contactization_iff.2 (hθ ▸ hσ)).isContactDistribution_kerDistribution
  isImmersion := hι.prodMk hL.contMDiff_primitive (by simp)
  isHorizontalMap := hL.isHorizontalMap_contactization hι.contMDiff
  two_mul_finrank_add_one := by
    rw [finrank_prod, finrank_self, hL.isLagrangianMap.two_mul_finrank
      (hι.mfderiv_injective (by simp) (Classical.arbitrary L))]

/-- **The Legendrian lift of an exact Lagrangian embedding.** Let `σ = -dθ`. If `ι : L → W` is a
smooth embedding of a nonempty manifold which is an exact Lagrangian map with primitive `h`, then
`x ↦ (ι x, h x)` is a Legendrian embedding for the contact structure `ker (dz - θ)`. -/
theorem IsExactLagrangianMap.isLegendrianEmbedding_contactization [Nonempty L]
    (hθ : σ = -mextDerivₗ I 1 θ) (hL : hσ.IsExactLagrangianMap J θ ι h)
    (hι : Manifold.IsSmoothEmbedding J I ∞ ι) :
    IsLegendrianEmbedding J θ.contactization.kerDistribution (fun x ↦ (ι x, h x)) where
  toIsLegendrianImmersion := hL.isLegendrianImmersion_contactization hθ hι.isImmersion
  isEmbedding := .of_comp (hι.isImmersion.contMDiff.continuous.prodMk
    hL.contMDiff_primitive.continuous) continuous_fst hι.isEmbedding

/-- **Projections of Legendrian immersions are exact Lagrangian.** Let `σ = -dθ`. If the lift
`x ↦ (ι x, h x)` is a Legendrian immersion for the contact structure `ker (dz - θ)`, then `ι` is
an exact Lagrangian map with primitive `h`. Together with
`IsExactLagrangianMap.isLegendrianImmersion_contactization`, the Legendrian immersions into the
contactization are exactly the lifts of the exact Lagrangian immersions through their primitives. -/
theorem _root_.TauCeti.IsLegendrianImmersion.isExactLagrangianMap_contactization
    (hθ : σ = -mextDerivₗ I 1 θ)
    (hL : IsLegendrianImmersion J θ.contactization.kerDistribution (fun x ↦ (ι x, h x))) :
    hσ.IsExactLagrangianMap J θ ι h := by
  have hι := SmoothForm.isImmersion_of_isHorizontalMap_contactization θ hL.isImmersion
    hL.isHorizontalMap
  refine (isExactLagrangianMap_iff_isHorizontalMap_contactization hθ hι.contMDiff
    (contMDiff_snd.comp hL.isImmersion.contMDiff) (hι.mfderiv_injective (by simp)) ?_).2
    hL.isHorizontalMap
  have := hL.two_mul_finrank_add_one
  rw [finrank_prod, finrank_self] at this
  omega

end SmoothTwoForm.IsNondegenerate

end Lifts

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
