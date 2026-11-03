/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactization
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Symplectic.Lagrangian.Exact
import TauCeti.Geometry.Contact.Pullback
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph

/-!
# Isotropic maps and Legendrian immersions

Let `α` be a real one-form on a manifold `M`, with kernel hyperplanes `ξ = ker α`. A map
`f : N → M` is **isotropic** for `α` when every tangent image `df_x(T_x N)` lies in `ξ_(f x)`
(`TauCeti.SmoothForm.IsIsotropicMap`). The condition only depends on the hyperplane field `ξ`, so
it is unchanged when `α` is multiplied by a nowhere vanishing function; it is invariant under
reparametrization of the source and is carried along by diffeomorphisms preserving the hyperplane
fields, that is by contactomorphisms. A smooth map is isotropic exactly when it pulls `α` back to
zero; it then pulls `dα` back to `d(f^* α) = 0` as well, so `dα` vanishes on its tangent images.

When `α` is a contact form on a manifold of dimension `2 n + 1`, the tangent image of an isotropic
immersion is an isotropic subspace of the symplectic vector space `(ξ_(f x), dα)`, so its source
has dimension at most `n` (`TauCeti.SmoothForm.IsIsotropicMap.two_mul_finrank_add_one_le`). A
**Legendrian immersion** (`TauCeti.SmoothForm.IsLegendrianImmersion`) is a smooth isotropic
immersion from a manifold of this maximal dimension `n`. Its image may have self-intersections.

The basic examples live in the contactization `(W × ℝ, dz - θ)` of an exact symplectic manifold
`(W, -dθ)`. A map `y ↦ (g y, h y)` into it is isotropic exactly when `g^* θ = dh`
(`TauCeti.SmoothForm.isIsotropicMap_contactization_iff`), and it is a Legendrian immersion exactly
when `g` is an exact Lagrangian immersion with primitive `h`
(`TauCeti.SmoothForm.isLegendrianImmersion_contactization_iff`). This is the correspondence
between exact Lagrangian immersions and their Legendrian lifts. For the cotangent bundle
`W = T*M`, whose contactization is the space of one-jets `J¹M = T*M × ℝ`, the section
`x ↦ (β_x, g x)` defined by a smooth one-form `β` and a function `g` is a Legendrian immersion
exactly when `g` is smooth and `β = dg`
(`TauCeti.CotangentBundle.isLegendrianImmersion_section_iff`), since the section of `T*M` defined
by `β` is then an exact Lagrangian graph
(`TauCeti.CotangentBundle.isExactLagrangianMap_section_iff`). In particular the one-jet
`j¹g : x ↦ (dg_x, g x)` of a smooth function is a Legendrian immersion
(`TauCeti.CotangentBundle.isLegendrianImmersion_oneJet`).

## Main declarations

* `TauCeti.SmoothForm.IsIsotropicMap`: maps tangent to the kernel of a one-form.
* `TauCeti.SmoothForm.isIsotropicMap_iff_mpullback_eq_zero`: isotropy is the vanishing of the
  pullback.
* `TauCeti.SmoothForm.isIsotropicMap_diffeomorph_comp_iff`: transport by contactomorphisms.
* `TauCeti.SmoothForm.IsIsotropicMap.eval₂_mextDerivₗ_mfderiv`: `dα` vanishes on tangent images.
* `TauCeti.SmoothForm.IsIsotropicMap.two_mul_finrank_add_one_le`: the dimension bound.
* `TauCeti.SmoothForm.IsLegendrianImmersion`: Legendrian immersions.
* `TauCeti.SmoothForm.isLegendrianImmersion_contactization_iff`: Legendrian lifts of exact
  Lagrangian immersions.
* `TauCeti.CotangentBundle.oneJet`, `TauCeti.CotangentBundle.isLegendrianImmersion_oneJet`: one-jets
  of functions are Legendrian.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Sections 1.5 and 2.5 (Legendrian submanifolds, isotropic submanifolds and the space of
  one-jets).
* V. I. Arnold, A. B. Givental, *Symplectic geometry*, in *Dynamical Systems IV*, Encyclopaedia of
  Mathematical Sciences 4, Springer, 2001, Chapter 4, Section 2 (Legendrian manifolds and
  contactization).
-/

public section

noncomputable section

open Function Manifold Module
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {α β : SmoothForm I M ℝ 1} {f : N → M}

/-! ### Isotropic maps -/

variable (J) in
/-- A map `f : N → M` is **isotropic** for a one-form `α` when every tangent image
`df_x(T_x N)` lies in the kernel hyperplane `ker α_(f x)`. When `α` is a contact form and `f` is an
immersion, `f` parametrizes an isotropic immersed submanifold. As for the symplectic predicates, the
differential is `0` where `f` is not differentiable, so the condition is only meaningful for
differentiable maps. -/
def IsIsotropicMap (α : SmoothForm I M ℝ 1) (f : N → M) : Prop :=
  ∀ x, LinearMap.range (mfderiv J I f x).toLinearMap ≤ α.kerDistribution (f x)

/-- A map is isotropic for `α` exactly when `α` vanishes on all pushed-forward tangent vectors. -/
theorem isIsotropicMap_iff :
    α.IsIsotropicMap J f ↔ ∀ x (v : TangentSpace J x), α.1 (f x) ![mfderiv J I f x v] = 0 := by
  refine forall_congr' fun x ↦ ?_
  simp only [LinearMap.range_le_iff_comap, Submodule.eq_top_iff', Submodule.mem_comap,
    ContinuousLinearMap.coe_coe, mem_kerDistribution]

/-- **Only the hyperplane field matters.** Two one-forms with the same kernel hyperplanes have the
same isotropic maps; for instance `α` and `g α` for a nowhere vanishing function `g`. -/
theorem isIsotropicMap_congr_kerDistribution (h : β.kerDistribution = α.kerDistribution) :
    β.IsIsotropicMap J f ↔ α.IsIsotropicMap J f := by
  simp only [IsIsotropicMap, h]

/-- **Isotropy is the vanishing of the pullback.** A smooth map is isotropic for `α` exactly when
it pulls `α` back to zero. -/
theorem isIsotropicMap_iff_mpullback_eq_zero [IsManifold J ∞ N] (hf : ContMDiff J I ∞ f) :
    α.IsIsotropicMap J f ↔ mpullback f hf α = 0 := by
  rw [isIsotropicMap_iff, ← degreeOneEquiv.injective.eq_iff, map_zero]
  refine ⟨fun h ↦ ?_, fun h x v ↦ ?_⟩
  · ext x v
    simpa [degreeOneEquiv_apply_apply, mpullback_apply, Matrix.vec_single_eq_const] using h x v
  · have := congrArg (fun s ↦ s x v) h
    simpa [degreeOneEquiv_apply_apply, mpullback_apply, Matrix.vec_single_eq_const] using this

/-! ### Reparametrization and transport -/

section Transport

variable {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ E'' H''} {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω}

/-- Precomposing with a diffeomorphism of the source does not change isotropy. -/
theorem isIsotropicMap_comp_diffeomorph_iff (φ : P ≃ₘ^n⟮K, J⟯ N) (hn : n ≠ 0) :
    α.IsIsotropicMap K (f ∘ φ) ↔ α.IsIsotropicMap J f := by
  simp only [IsIsotropicMap, φ.range_mfderiv_comp_diffeomorph hn, Function.comp_apply]
  refine ⟨fun h y ↦ ?_, fun h x ↦ h (φ x)⟩
  obtain ⟨x, rfl⟩ := φ.surjective y
  exact h x

variable {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [IsManifold I₂ ∞ M₂] {α₂ : SmoothForm I₂ M₂ ℝ 1}

/-- **Transport by contactomorphisms.** If a diffeomorphism `ψ : M → M₂` pulls `α₂` back to a
one-form with the same kernel hyperplanes as `α`, then `ψ ∘ f` is isotropic for `α₂` exactly when
`f` is isotropic for `α`. -/
theorem isIsotropicMap_diffeomorph_comp_iff (ψ : M ≃ₘ⟮I, I₂⟯ M₂)
    (hψ : (mpullback ψ ψ.contMDiff α₂).kerDistribution = α.kerDistribution) :
    α₂.IsIsotropicMap J (ψ ∘ f) ↔ α.IsIsotropicMap J f := by
  refine forall_congr' fun x ↦ ?_
  -- `range_mfderiv_diffeomorph_comp` pushes the tangent image forward along `dψ` packaged as a
  -- linear equivalence; as a linear map this is the differential `mfderiv I I₂ ψ`.
  have hdψ : (ψ.mfderivToContinuousLinearEquiv (by simp) (f x)).toLinearEquiv.toLinearMap =
      (mfderiv I I₂ ψ (f x)).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (ψ.mfderivToContinuousLinearEquiv_coe _)
  rw [ψ.range_mfderiv_diffeomorph_comp (by simp), Function.comp_apply, hdψ,
    Submodule.map_le_iff_le_comap, ← hψ, kerDistribution_mpullback]

end Transport

/-! ### The exterior derivative on tangent images -/

section ExtDeriv

variable [IsManifold J ∞ N]

/-- An isotropic smooth map pulls `dα` back to zero, since `f^* dα = d(f^* α) = 0`. -/
theorem IsIsotropicMap.mpullback_mextDerivₗ_eq_zero (h : α.IsIsotropicMap J f)
    (hf : ContMDiff J I ∞ f) : mpullback f hf (mextDerivₗ I 1 α) = 0 := by
  rw [← mextDerivₗ_mpullback, (isIsotropicMap_iff_mpullback_eq_zero hf).1 h, map_zero]

/-- **`dα` vanishes on the tangent images of an isotropic map.** For a smooth map tangent to
`ker α`, the two-form `dα` vanishes on every pair of pushed-forward tangent vectors. -/
theorem IsIsotropicMap.eval₂_mextDerivₗ_mfderiv (h : α.IsIsotropicMap J f)
    (hf : ContMDiff J I ∞ f) (x : N) (v w : TangentSpace J x) :
    (mextDerivₗ I 1 α).eval₂ (f x) (mfderiv J I f x v) (mfderiv J I f x w) = 0 := by
  rw [← eval₂_mpullback f hf, h.mpullback_mextDerivₗ_eq_zero hf]
  simp [SmoothBundleForm.eval₂_apply]

variable [FiniteDimensional ℝ E]

/-- **Dimension bound for isotropic maps.** For a contact form `α`, a smooth isotropic map with
injective differential at some point comes from a manifold of dimension at most `n`, where
`2 n + 1` is the dimension of `M`. -/
theorem IsIsotropicMap.two_mul_finrank_add_one_le (hα : α.IsContactForm)
    (h : α.IsIsotropicMap J f) (hf : ContMDiff J I ∞ f) {x : N}
    (hx : Injective (mfderiv J I f x)) : 2 * finrank ℝ E' + 1 ≤ finrank ℝ E := by
  have := (isContactForm_def.1 hα (f x)).two_mul_finrank_add_one_le
    (W := LinearMap.range (mfderiv J I f x)) (by rw [← kerDistribution_def]; exact h x) (by
      rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
      rw [bilinFormAt_apply]
      exact h.eval₂_mextDerivₗ_mfderiv hf x v w)
  rwa [LinearMap.finrank_range_of_inj hx, finrank_tangentSpace, finrank_tangentSpace] at this

end ExtDeriv

/-! ### Legendrian immersions -/

variable (J) in
/-- A **Legendrian immersion** for a one-form `α` on a manifold of dimension `2 n + 1` is a smooth
immersion `f : N → M` with isotropic tangent images from a manifold of dimension `n`. For a contact
form this is the maximal dimension of an isotropic immersion
(`TauCeti.SmoothForm.IsIsotropicMap.two_mul_finrank_add_one_le`). Its image may have
self-intersections. -/
structure IsLegendrianImmersion (α : SmoothForm I M ℝ 1) (f : N → M) : Prop where
  /-- A Legendrian immersion is a smooth immersion. -/
  isImmersion : IsImmersion J I ∞ f
  /-- A Legendrian immersion is tangent to the kernel of the one-form. -/
  isIsotropicMap : α.IsIsotropicMap J f
  /-- A Legendrian immersion comes from a manifold of dimension `n`, if `M` has dimension
  `2 n + 1`. -/
  two_mul_finrank_add_one : 2 * finrank ℝ E' + 1 = finrank ℝ E

/-! ### Legendrian lifts in a contactization -/

section Contactization

variable {θ : SmoothForm I M ℝ 1} {g : N → M} {h : N → ℝ}

/-- A map `y ↦ (g y, h y)` into the contactization `(M × ℝ, dz - θ)` is isotropic exactly when
`dh = θ ∘ dg` at every point, for differentiable `g` and `h`. -/
theorem isIsotropicMap_contactization_iff_forall (hg : MDifferentiable J I g)
    (hh : MDifferentiable J 𝓘(ℝ) h) :
    θ.contactization.IsIsotropicMap J (fun y ↦ (g y, h y)) ↔
      ∀ y (v : TangentSpace J y), mfderiv J 𝓘(ℝ) h y v = θ.1 (g y) ![mfderiv J I g y v] := by
  rw [isIsotropicMap_iff]
  refine forall₂_congr fun y v ↦ ?_
  rw [contactization_apply, mfderiv_prodMk (hg y) (hh y), sub_eq_zero,
    Manifold.tangentSpaceProdEquiv_apply, NormedSpace.fromTangentSpace_apply]
  -- The components of `(dg_y, dh_y) v` are `dg_y v` and `dh_y v`.
  exact Iff.rfl

/-- **Isotropic maps into a contactization.** A map `y ↦ (g y, h y)` into the contactization
`(M × ℝ, dz - θ)`, with `g` and `h` differentiable, is isotropic exactly when `g^* θ = dh`. -/
theorem isIsotropicMap_contactization_iff (hg : MDifferentiable J I g)
    (hh : MDifferentiable J 𝓘(ℝ) h) :
    θ.contactization.IsIsotropicMap J (fun y ↦ (g y, h y)) ↔
      TauCeti.mpullback J I g θ.1 = mextDeriv (RoughForm.ofFunction J h) := by
  rw [isIsotropicMap_contactization_iff_forall hg hh, funext_iff]
  refine forall_congr' fun y ↦ ?_
  -- A one-form at `y` is determined by its values on the constant vectors `![v]`.
  rw [← (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace J y) ℝ 0).symm.injective.eq_iff,
    ContinuousLinearMap.ext_iff, mextDeriv_ofFunction, Equiv.symm_apply_apply]
  simp only [ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply, TauCeti.mpullback_apply,
    Matrix.vec_single_eq_const, mvfderiv_apply_eq_mfderiv_apply]
  exact forall_congr' fun _ ↦ eq_comm

variable [IsManifold J ∞ N] [FiniteDimensional ℝ E] [I.Boundaryless] [J.Boundaryless]

/-- **Legendrian lifts of exact Lagrangian immersions.** Let `θ` be a one-form on `M` with `-dθ`
nondegenerate. A map `y ↦ (g y, h y)` into the contactization `(M × ℝ, dz - θ)` is a Legendrian
immersion exactly when `g` is a Lagrangian immersion into `(M, -dθ)` and an exact Lagrangian map
with primitive `h`, that is when `h` is a smooth primitive of `g^* θ`. -/
theorem isLegendrianImmersion_contactization_iff
    (hσ : SmoothTwoForm.IsNondegenerate (-mextDerivₗ I 1 θ)) :
    θ.contactization.IsLegendrianImmersion J (fun y ↦ (g y, h y)) ↔
      hσ.IsLagrangianImmersion J g ∧ hσ.IsExactLagrangianMap J θ g h := by
  have hdim : finrank ℝ (E × ℝ) = finrank ℝ E + 1 := by rw [finrank_prod, finrank_self]
  constructor
  · intro hL
    have hpair := hL.isImmersion.contMDiff
    have hg : ContMDiff J I ∞ g := contMDiff_fst.comp hpair
    have hh : ContMDiff J 𝓘(ℝ) ∞ h := contMDiff_snd.comp hpair
    have hg₁ := hg.mdifferentiable (by simp)
    have hh₁ := hh.mdifferentiable (by simp)
    have hiso := (isIsotropicMap_contactization_iff_forall hg₁ hh₁).1 hL.isIsotropicMap
    -- `dg` is injective: if `dg v = 0`, then also `dh v = θ (dg v) = 0`.
    have hinj (y : N) : Injective (mfderiv J I g y) := by
      refine (injective_iff_map_eq_zero _).2 fun v hv ↦ hL.isImmersion.mfderiv_injective
        (by simp) y ?_
      have h0 : (mfderiv J I g y).prod (mfderiv J 𝓘(ℝ) h y) v = 0 := by
        rw [ContinuousLinearMap.prod_apply, hiso, hv, (θ.1 (g y)).map_coord_zero 0 rfl]
        exact Prod.mk_zero_zero
      rw [mfderiv_prodMk (hg₁ y) (hh₁ y)]
      exact h0.trans (map_zero _).symm
    have hdim' : 2 * finrank ℝ E' = finrank ℝ E := by
      have := hL.two_mul_finrank_add_one
      rw [hdim] at this
      omega
    have hE := (SmoothTwoForm.IsNondegenerate.isExactLagrangianMap_iff_of_finrank (hσ := hσ) rfl
      hg hinj hdim').2 ⟨hh, (isIsotropicMap_contactization_iff hg₁ hh₁).1 hL.isIsotropicMap⟩
    exact ⟨⟨hg.isImmersion_of_injective_mfderiv (by simp) hinj, hE.isLagrangianMap.isIsotropicMap,
      hdim'⟩, hE⟩
  · rintro ⟨hg, -, hh, hpull⟩
    have hg' := hg.isImmersion.contMDiff
    refine ⟨?_, (isIsotropicMap_contactization_iff (hg'.mdifferentiable (by simp))
      (hh.mdifferentiable (by simp))).2 hpull, by rw [hdim, hg.two_mul_finrank]⟩
    -- The pair is an immersion, since its first component is.
    refine (hg'.prodMk hh).isImmersion_of_injective_mfderiv (by simp) fun y ↦ ?_
    rw [mfderiv_prodMk ((hg' y).mdifferentiableAt (by simp)) ((hh y).mdifferentiableAt (by simp))]
    exact fun v w hvw ↦ hg.isImmersion.mfderiv_injective (by simp) y (congrArg Prod.fst hvw)

end Contactization

end SmoothForm

/-! ### One-jets -/

namespace CotangentBundle

open Bundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The **one-jet** `j¹g : x ↦ (dg_x, g x)` of a real function `g` on `M`, with values in the space
of one-jets `J¹M = T*M × ℝ`. For smooth `g` it is a Legendrian immersion for the contact form
`dz - λ` (`TauCeti.CotangentBundle.isLegendrianImmersion_oneJet`). -/
def oneJet (g : M → ℝ) (x : M) : CotangentBundle I M × ℝ :=
  (TotalSpace.mk' (E →L[ℝ] ℝ) x (mvfderiv I g x), g x)

@[simp]
theorem oneJet_apply (g : M → ℝ) (x : M) :
    oneJet (I := I) g x = (TotalSpace.mk' (E →L[ℝ] ℝ) x (mvfderiv I g x), g x) :=
  (rfl)

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E] [I.Boundaryless]

/-- **Legendrian sections of the space of one-jets.** Let `β` be a smooth one-form on `M` and `g`
a real function. The section `x ↦ (β_x, g x)` of `J¹M = T*M × ℝ` is a Legendrian immersion for the
contact form `dz - λ` exactly when `g` is smooth and `β = dg`, that is when the section is the
one-jet of `g`. -/
theorem isLegendrianImmersion_section_iff (β : SmoothForm I M ℝ 1) {g : M → ℝ} :
    (liouvilleForm I M).contactization.IsLegendrianImmersion I
        (fun x ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv β x), g x)) ↔
      ContMDiff I 𝓘(ℝ) ∞ g ∧ β.1 = mextDeriv (RoughForm.ofFunction I g) := by
  have hσ : SmoothTwoForm.IsNondegenerate (-mextDerivₗ (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (liouvilleForm I M)) := by
    rw [← symplecticForm_eq_neg_mextDerivₗ]
    exact isSymplectic_symplecticForm.isNondegenerate
  refine (SmoothForm.isLegendrianImmersion_contactization_iff hσ).trans
    (Iff.trans ?_ (isExactLagrangianMap_section_iff β))
  -- The canonical symplectic form is `-dλ`, so the two exact Lagrangian predicates agree.
  simp only [symplecticForm_eq_neg_mextDerivₗ]
  refine ⟨And.right, fun hE ↦ ⟨⟨?_, hE.isLagrangianMap.isIsotropicMap, ?_⟩, hE⟩⟩
  · -- The bundle projection is a smooth left inverse of the section.
    exact (SmoothForm.degreeOneEquiv β).contMDiff.isImmersion_of_leftInverse (by simp)
      (fun p ↦ (contMDiff_proj (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) p).mdifferentiableAt
        one_ne_zero)
      fun _ ↦ rfl
  · rw [finrank_prod, ContinuousLinearMap.dual_finrank_eq, two_mul]

/-- **One-jets are Legendrian.** The one-jet `j¹g : x ↦ (dg_x, g x)` of a smooth function is a
Legendrian immersion into the space of one-jets `J¹M = T*M × ℝ` with its contact form `dz - λ`. -/
theorem isLegendrianImmersion_oneJet {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    (liouvilleForm I M).contactization.IsLegendrianImmersion I (oneJet g) := by
  let dg : SmoothForm I M ℝ 1 := mextDerivₗ I 0
    ⟨RoughForm.ofFunction I g, (isSmoothForm_ofFunction_iff.mpr hg).mem_smoothBundleForms⟩
  have hdg : dg.1 = mextDeriv (RoughForm.ofFunction I g) := mextDerivₗ_apply I 0 _
  -- The section defined by the one-form `dg` is the one-jet of `g`.
  have hj : (fun x ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv dg x), g x)) =
      oneJet g := by
    funext x
    have hx : SmoothForm.degreeOneEquiv dg x = mvfderiv I g x := by
      ext v
      rw [SmoothForm.degreeOneEquiv_apply_apply, hdg, ← Matrix.vec_single_eq_const,
        mextDeriv_ofFunction_apply, mvfderiv_apply_eq_mfderiv_apply]
    rw [oneJet_apply, hx]
  exact hj ▸ (isLegendrianImmersion_section_iff dg).2 ⟨hg, hdg⟩

end CotangentBundle

end TauCeti
