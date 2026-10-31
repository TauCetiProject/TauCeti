/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Descending almost complex structures along local diffeomorphisms

Let `q : M → N` be a surjective smooth local diffeomorphism, for instance the projection of a
manifold onto its quotient by a free properly discontinuous group action. A smooth almost complex
structure `J` on `M` descends to `N` when it is compatible with the identifications that `q`
makes: whenever two tangent vectors `v` at `x` and `v'` at `x'` have the same image under the
differentials of `q`, so do `J v` and `J v'`. The descended structure
`TauCeti.SmoothAlmostComplexStructure.descend` is then the unique almost complex structure `K` on
`N` making every differential of `q` complex linear, `K (dq v) = dq (J v)`. It is smooth because
`q` is a local diffeomorphism: near each point of `N`, the evaluation of `K` on a smooth vector
field is the image under `dq` of `J` applied to the pulled back vector field.

The usual source of the compatibility hypothesis is a family of deck transformations: if every
pair of points in a fibre of `q` is related by a chain of maps `g` with `q ∘ g = q` whose
differentials commute with `J`, then `J` descends
(`TauCeti.SmoothAlmostComplexStructure.mfderiv_apply_eq_of_eqvGen`).

Tameness, invariance and compatibility with a two-form `σ` on `N` can all be checked upstairs,
against the pullback `q^* σ`, because `q` is surjective and its differentials are bijective.

## Main definitions

* `TauCeti.SmoothAlmostComplexStructure.descend`: the almost complex structure on `N` induced by
  a `q`-compatible almost complex structure on `M`.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.descend_apply_mfderiv`: every differential of `q` is
  complex linear for `J` and its descent.
* `TauCeti.SmoothAlmostComplexStructure.eq_descend_iff`: the descent is the only almost complex
  structure with this property.
* `TauCeti.SmoothAlmostComplexStructure.mfderiv_apply_eq_of_deck`,
  `TauCeti.SmoothAlmostComplexStructure.mfderiv_apply_eq_of_eqvGen`: deck transformations commuting
  with `J` give the compatibility hypothesis on the equivalence relation they generate.
* `TauCeti.SmoothAlmostComplexStructure.tames_descend_iff`,
  `TauCeti.SmoothAlmostComplexStructure.invariant_descend_iff`,
  `TauCeti.SmoothAlmostComplexStructure.compatible_descend_iff`: tameness, invariance and
  compatibility of the descent with `σ` are those of `J` with `q^* σ`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.2 (almost complex structures).
-/

public noncomputable section

open Bundle Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M E' H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace N] [ChartedSpace H' N]
  {q : M → N}

section Deck

/-- Deck transformations commuting with `J` make `J` compatible with the identifications of `q`:
if `g` satisfies `q ∘ g = q`, sends `x` to `x'` and its differential at `x` commutes with `J`, then
any two tangent vectors at `x` and `x'` with the same image under the differentials of `q` are sent
by `J` to two vectors with the same image. -/
theorem mfderiv_apply_eq_of_deck (hq : IsLocalDiffeomorph I I' ∞ q)
    (J : SmoothAlmostComplexStructure I M) {g : M → M} {x x' : M} (hgx : g x = x')
    (hg : MDifferentiableAt I I g x) (hqg : q ∘ g = q)
    (hgJ : ∀ v, mfderiv I I g x (J x v) = J (g x) (mfderiv I I g x v))
    (v : TangentSpace I x) (v' : TangentSpace I x')
    (hvv' : mfderiv I I' q x v = mfderiv I I' q x' v') :
    mfderiv I I' q x (J x v) = mfderiv I I' q x' (J x' v') := by
  subst hgx
  -- The chain rule for `q ∘ g = q` identifies `dq_x` with `dq_{g x} ∘ dg_x`.
  have hchain (w : TangentSpace I x) :
      mfderiv I I' q x w = mfderiv I I' q (g x) (mfderiv I I g x w) := by
    have h := mfderiv_comp x ((hq (g x)).mdifferentiableAt (by simp)) hg
    rw [hqg] at h
    -- After rewriting, `ContinuousLinearMap.comp_apply` closes the goal definitionally; it
    -- cannot be used by `rw` because the tangent spaces at `q x` and `q (g x)` differ
    -- syntactically.
    rw [h]
    rfl
  -- Injectivity of `dq_{g x}` identifies `v'` with `dg_x v`.
  have hv' : v' = mfderiv I I g x v :=
    ((hq (g x)).isInvertible_mfderiv (by simp)).injective (by rw [← hvv', hchain])
  rw [hv', hchain, hgJ]

/-- Deck transformations commuting with `J` make `J` compatible with the identifications of `q`
along the equivalence relation they generate: if each step `R x x'` is realized by a map `g` with
`q ∘ g = q`, `g x = x'` and differential at `x` commuting with `J`, then for points related by
`Relation.EqvGen R`, tangent vectors with the same image under the differentials of `q` are sent by
`J` to vectors with the same image. When the generated relation contains the fibres of `q`, this is
the hypothesis of `TauCeti.SmoothAlmostComplexStructure.descend`. -/
theorem mfderiv_apply_eq_of_eqvGen (hq : IsLocalDiffeomorph I I' ∞ q)
    (J : SmoothAlmostComplexStructure I M) {R : M → M → Prop}
    (hR : ∀ x x', R x x' → ∃ g : M → M, g x = x' ∧ MDifferentiableAt I I g x ∧ q ∘ g = q ∧
      ∀ v, mfderiv I I g x (J x v) = J (g x) (mfderiv I I g x v))
    {x x' : M} (hxx' : Relation.EqvGen R x x') (v : TangentSpace I x) (v' : TangentSpace I x')
    (hvv' : mfderiv I I' q x v = mfderiv I I' q x' v') :
    mfderiv I I' q x (J x v) = mfderiv I I' q x' (J x' v') := by
  induction hxx' with
  | rel x x' h =>
    obtain ⟨g, hgx, hg, hqg, hgJ⟩ := hR x x' h
    exact mfderiv_apply_eq_of_deck hq J hgx hg hqg hgJ v v' hvv'
  | refl x => rw [((hq x).isInvertible_mfderiv (by simp)).injective hvv']
  | symm x x' _ ih => exact (ih v' v hvv'.symm).symm
  | trans x x' x'' _ _ ih ih' =>
    -- Pass through the tangent vector at `x'` with the same image as `v`.
    obtain ⟨w, hw⟩ := ((hq x').isInvertible_mfderiv (by simp)).surjective (mfderiv I I' q x v)
    exact (ih v w hw.symm).trans (ih' w v' (hw.trans hvv'))

end Deck

variable (hq : IsLocalDiffeomorph I I' ∞ q) (hsurj : Surjective q)
  (J : SmoothAlmostComplexStructure I M)
  (hJ : ∀ ⦃x x' : M⦄ (v : TangentSpace I x) (v' : TangentSpace I x'), q x = q x' →
    mfderiv I I' q x v = mfderiv I I' q x' v' →
      mfderiv I I' q x (J x v) = mfderiv I I' q x' (J x' v'))

/-- The endomorphism `dq_x ∘ J_x ∘ dq_x⁻¹` of the tangent space at `y`, read at the chosen preimage
`x` of `y`. Tangent spaces of `N` are all the model space, so this is an endomorphism of the tangent
space at `y` even though it is built at `q x`. -/
private def descendEndomorphism (y : N) : TangentSpace I' y →L[ℝ] TangentSpace I' y :=
  (mfderiv I I' q (surjInv hsurj y)).comp ((J.toEndomorphism (surjInv hsurj y)).comp
    (hq.mfderivToContinuousLinearEquiv (by simp) (surjInv hsurj y)).symm.toContinuousLinearMap)

private theorem descendEndomorphism_apply (y : N) (w : TangentSpace I' y) :
    descendEndomorphism hq hsurj J y w =
      mfderiv I I' q (surjInv hsurj y) (J (surjInv hsurj y)
        ((hq.mfderivToContinuousLinearEquiv (by simp) (surjInv hsurj y)).symm w)) :=
  (rfl)

include hJ in
private theorem descendEndomorphism_apply_mfderiv (x : M) (v : TangentSpace I x) :
    descendEndomorphism hq hsurj J (q x) (mfderiv I I' q x v) = mfderiv I I' q x (J x v) := by
  set x₀ := surjInv hsurj (q x)
  set D := hq.mfderivToContinuousLinearEquiv (by simp) x₀
  have hx₀ : q x₀ = q x := surjInv_eq hsurj (q x)
  have hD : mfderiv I I' q x₀ (D.symm (mfderiv I I' q x v)) = mfderiv I I' q x v := by
    rw [← IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe hq (by simp) x₀]
    exact D.apply_symm_apply _
  rw [descendEndomorphism_apply]
  exact hJ _ v hx₀ hD

include hJ in
private theorem descendEndomorphism_comp_square (y : N) :
    (descendEndomorphism hq hsurj J y).comp (descendEndomorphism hq hsurj J y) =
      -ContinuousLinearMap.id ℝ _ := by
  obtain ⟨x, rfl⟩ := hsurj y
  ext w
  obtain ⟨v, rfl⟩ := (hq.isInvertible_mfderiv (by simp) x).surjective w
  simp only [ContinuousLinearMap.comp_apply, descendEndomorphism_apply_mfderiv hq hsurj J hJ,
    apply_apply, map_neg, _root_.neg_apply, ContinuousLinearMap.id_apply]

variable [CompleteSpace E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ N] [T2Space N]

include hJ in
private theorem contMDiff_descendEndomorphism :
    ContMDiff I' (I'.prod 𝓘(ℝ, E' →L[ℝ] E')) ∞
      (fun y ↦ TotalSpace.mk' (E' →L[ℝ] E')
        (E := fun y : N ↦ TangentSpace I' y →L[ℝ] TangentSpace I' y) y
        (descendEndomorphism hq hsurj J y)) := by
  refine (Manifold.contMDiff_hom_iff _).2 fun s hs ↦ ?_
  rw [← hq.contMDiff_comp_iff hsurj le_rfl]
  -- Upstairs, the evaluation on `s` is the image under `dq` of `J` applied to `q^* s`.
  have hpull : ContMDiff I I.tangent ∞
      (fun x ↦ TotalSpace.mk' E x (VectorField.mpullback I I' q s x)) :=
    hs.mpullback_vectorField hq.contMDiff (hq.isInvertible_mfderiv (by simp)) le_rfl
  have hJs := (J.contMDiff_apply contMDiff_id hpull).of_le (le_refl ∞)
  have htangent := (hq.contMDiff.contMDiff_tangentMap (m := ∞) le_rfl).comp hJs
  refine htangent.congr fun x ↦ ?_
  have hs' : mfderiv I I' q x (VectorField.mpullback I I' q s x) = s (q x) := by
    rw [VectorField.mpullback_apply]
    exact ((hq.isInvertible_mfderiv (by simp) x).inverse_apply_eq.1 rfl).symm
  simp only [comp_apply, tangentMap, id_eq]
  rw [← hs', descendEndomorphism_apply_mfderiv hq hsurj J hJ]

/-- The almost complex structure on `N` induced by a smooth almost complex structure `J` on `M`
along a surjective smooth local diffeomorphism `q : M → N`, provided that `J` respects the
identifications of `q`: tangent vectors with the same image under the differentials of `q` are
sent by `J` to vectors with the same image. It is characterized by `K (dq v) = dq (J v)`
(`TauCeti.SmoothAlmostComplexStructure.descend_apply_mfderiv`,
`TauCeti.SmoothAlmostComplexStructure.eq_descend_iff`). -/
def descend : SmoothAlmostComplexStructure I' N where
  toEndomorphism := ⟨descendEndomorphism hq hsurj J, contMDiff_descendEndomorphism hq hsurj J hJ⟩
  square_neg := descendEndomorphism_comp_square hq hsurj J hJ

/-- Every differential of `q` is complex linear for `J` and its descent:
`K (dq v) = dq (J v)`. -/
@[simp]
theorem descend_apply_mfderiv (x : M) (v : TangentSpace I x) :
    descend hq hsurj J hJ (q x) (mfderiv I I' q x v) = mfderiv I I' q x (J x v) :=
  descendEndomorphism_apply_mfderiv hq hsurj J hJ x v

/-- The descent of `J` is the only almost complex structure on `N` for which every differential of
`q` is complex linear. -/
theorem eq_descend_iff (K : SmoothAlmostComplexStructure I' N) :
    K = descend hq hsurj J hJ ↔
      ∀ (x : M) (v : TangentSpace I x),
        K (q x) (mfderiv I I' q x v) = mfderiv I I' q x (J x v) := by
  refine ⟨fun h x v ↦ by rw [h, descend_apply_mfderiv], fun h ↦ ext fun y w ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨v, rfl⟩ := (hq.isInvertible_mfderiv (by simp) x).surjective w
  rw [h, descend_apply_mfderiv]

variable (σ : SmoothTwoForm I' N)

/-- The descent of `J` is tamed by a two-form `σ` exactly when `J` is tamed by `q^* σ`. -/
theorem tames_descend_iff :
    σ.Tames (descend hq hsurj J hJ) ↔
      SmoothTwoForm.Tames (SmoothForm.mpullback q hq.contMDiff σ) J := by
  simp only [SmoothTwoForm.tames_iff, SmoothForm.eval₂_mpullback,
    ← descend_apply_mfderiv hq hsurj J hJ]
  refine ⟨fun h x v hv ↦ h _ _ ?_, fun h y w hw ↦ ?_⟩
  · exact fun h0 ↦ hv ((hq.isInvertible_mfderiv (by simp) x).injective
      (h0.trans (map_zero _).symm))
  · obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨v, rfl⟩ := (hq.isInvertible_mfderiv (by simp) x).surjective w
    exact h x v fun h0 ↦ hw (by rw [h0, map_zero])

/-- The descent of `J` leaves a two-form `σ` invariant exactly when `J` leaves `q^* σ`
invariant. -/
theorem invariant_descend_iff :
    σ.Invariant (descend hq hsurj J hJ) ↔
      SmoothTwoForm.Invariant (SmoothForm.mpullback q hq.contMDiff σ) J := by
  simp only [SmoothTwoForm.invariant_iff, SmoothForm.eval₂_mpullback,
    ← descend_apply_mfderiv hq hsurj J hJ]
  refine ⟨fun h x v w ↦ h _ _ _, fun h y w w' ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨v, rfl⟩ := (hq.isInvertible_mfderiv (by simp) x).surjective w
  obtain ⟨v', rfl⟩ := (hq.isInvertible_mfderiv (by simp) x).surjective w'
  exact h x v v'

/-- The descent of `J` is compatible with a two-form `σ` exactly when `J` is compatible with
`q^* σ`. -/
theorem compatible_descend_iff :
    σ.Compatible (descend hq hsurj J hJ) ↔
      SmoothTwoForm.Compatible (SmoothForm.mpullback q hq.contMDiff σ) J :=
  ⟨fun h ↦ ⟨(invariant_descend_iff hq hsurj J hJ σ).1 h.invariant,
      (tames_descend_iff hq hsurj J hJ σ).1 h.tames⟩,
    fun h ↦ ⟨(invariant_descend_iff hq hsurj J hJ σ).2 h.invariant,
      (tames_descend_iff hq hsurj J hJ σ).2 h.tames⟩⟩

end TauCeti.SmoothAlmostComplexStructure
