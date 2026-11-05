/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactization
public import TauCeti.Geometry.Contact.Levi
public import TauCeti.Geometry.Symplectic.Lagrangian.Exact
import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Contact.Pullback
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Isotropic and Legendrian maps into a contact manifold

Let `α` be a one-form on a manifold `M`, with kernel distribution `ξ = ker α`. A map `f : N → M`
is **isotropic** for `α` when every tangent image `df_y(T_y N)` lies in `ξ_(f y)`
(`TauCeti.SmoothForm.IsIsotropicMap`), equivalently when `f^*α = 0`
(`TauCeti.SmoothForm.isIsotropicMap_iff_mpullback_eq_zero`). The condition only depends on the
hyperplane field `ξ`: it is unchanged when `α` is multiplied by a nowhere vanishing function
(`TauCeti.SmoothForm.isIsotropicMap_iff_of_eq_smul`). As for the symplectic tangent-image
predicates, the source is an arbitrary charted space and `f` need not be injective, so the
predicate applies to embedded and immersed submanifolds alike, through any parametrization.

For a smooth isotropic map, `f^*dα = d(f^*α) = 0`, so the tangent images are also isotropic for
`dα` (`TauCeti.SmoothForm.IsIsotropicMap.mextDeriv_apply_mfderiv_eq_zero`). Since `α` identifies
the Levi form of `ξ` with `dα` on `ξ`, the Levi form of `ξ` vanishes on the tangent images of an
isotropic map wherever `α` does not vanish
(`TauCeti.SmoothForm.IsIsotropicMap.distributionLeviForm_eq_zero`). For a contact form, `dα` is
nondegenerate on `ξ`, so an isotropic immersion of `N` into a manifold of dimension `2 n + 1`
has `dim N ≤ n` (`TauCeti.SmoothForm.IsIsotropicMap.two_mul_finrank_add_one_le`).

A **Legendrian immersion** (`TauCeti.SmoothForm.IsLegendrianImmersion`) is a smooth immersion
with isotropic tangent images from a manifold of the maximal dimension `n`. Its image may have
self-intersections. A **Legendrian embedding** (`TauCeti.SmoothForm.IsLegendrianEmbedding`) is a
Legendrian immersion which is moreover a topological embedding, and parametrizes an embedded
Legendrian submanifold. Both notions only depend on `ξ`, and are transported by diffeomorphisms
pulling one contact form back to a nowhere vanishing multiple of the other.

The contactization `W × ℝ` of an exact symplectic manifold `(W, -dθ)` carries the contact form
`dz - θ` (`TauCeti.SmoothForm.contactization`). A map `y ↦ (i y, h y)` into it is isotropic exactly
when `i^*θ = dh` (`TauCeti.SmoothForm.isIsotropicMap_contactization_iff`). Hence, on manifolds
without boundary, the Legendrian immersions into the contactization are exactly the lifts
`(i, h)` of the exact Lagrangian immersions `i` of `W` with their primitives `h`
(`TauCeti.SmoothForm.isLegendrianImmersion_contactization_iff`): projecting a Legendrian immersion
to `W` gives an exact Lagrangian immersion, and conversely every exact Lagrangian immersion with a
chosen primitive lifts.

For the cotangent bundle with its Liouville form `λ`, the contactization is the space of one-jets
`J¹M = T*M × ℝ` with contact form `dz - λ`. A differentiable section `x ↦ (σ_x, g x)` of
`J¹M → M` is isotropic exactly when `σ = dg`
(`TauCeti.CotangentBundle.isIsotropicMap_contactization_section_iff`), so the Legendrian
sections are exactly the one-jets `j¹g : x ↦ (dg_x, g x)` of functions
(`TauCeti.CotangentBundle.oneJet`). These are Legendrian embeddings
(`TauCeti.CotangentBundle.isLegendrianEmbedding_oneJet`), since the projection to `M` is a
continuous left inverse.

## Main declarations

* `TauCeti.SmoothForm.IsIsotropicMap`: maps tangent to the kernel of a one-form.
* `TauCeti.SmoothForm.isIsotropicMap_iff_mpullback_eq_zero`: isotropy is `f^*α = 0`.
* `TauCeti.SmoothForm.isIsotropicMap_iff_of_eq_smul`: invariance under rescaling of `α`.
* `TauCeti.SmoothForm.isIsotropicMap_comp_diffeomorph_iff`: independence of the parametrization.
* `Diffeomorph.isIsotropicMap_comp_iff`: transport by contactomorphisms.
* `TauCeti.SmoothForm.IsIsotropicMap.distributionLeviForm_eq_zero`: the Levi form vanishes on the
  tangent images of an isotropic map.
* `TauCeti.SmoothForm.IsIsotropicMap.two_mul_finrank_add_one_le`: the dimension bound.
* `TauCeti.SmoothForm.IsLegendrianImmersion`, `TauCeti.SmoothForm.IsLegendrianEmbedding`:
  Legendrian immersions and embeddings.
* `Diffeomorph.isLegendrianImmersion_comp_iff`, `Diffeomorph.isLegendrianEmbedding_comp_iff`:
  transport by contactomorphisms.
* `TauCeti.SmoothForm.isLegendrianImmersion_contactization_iff`: Legendrian immersions into a
  contactization are the lifts of exact Lagrangian immersions.
* `TauCeti.CotangentBundle.isIsotropicMap_contactization_section_iff`: the graph criterion in
  `J¹M`.
* `TauCeti.CotangentBundle.oneJet`, `TauCeti.CotangentBundle.isLegendrianEmbedding_oneJet`: one-jets
  of functions are Legendrian embeddings into `J¹M`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109,
  Cambridge University Press, 2008, Chapter 2 (isotropic and Legendrian submanifolds, the
  dimension bound, and the space of one-jets).
* V. I. Arnold, A. B. Givental, *Symplectic geometry*, in Dynamical Systems IV, Encyclopaedia of
  Mathematical Sciences 4, Springer, 2001, Chapter 4 (contact geometry, Legendrian manifolds and
  their relation to Lagrangian manifolds).
-/

public section

noncomputable section

open Module Manifold Bundle
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothForm

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {α β : SmoothForm I M ℝ 1} {f : N → M}

/-! ### Isotropic maps -/

variable (J) in
/-- A map `f : N → M` is **isotropic** for a one-form `α` when every tangent image
`df_y(T_y N)` lies in the kernel `ξ = ker α`. For a contact form `α`, smooth immersions satisfying
this predicate parametrize the isotropic immersed submanifolds of the contact manifold `(M, ξ)`;
the condition only depends on `ξ`
(`TauCeti.SmoothForm.isIsotropicMap_iff_of_eq_smul`).

The tangent image is taken with `mfderiv`, which is `0` at points where `f` is not
differentiable, so the condition is only meaningful for differentiable maps. -/
def IsIsotropicMap (α : SmoothForm I M ℝ 1) (f : N → M) : Prop :=
  ∀ y, LinearMap.range (mfderiv J I f y).toLinearMap ≤ α.kerDistribution (f y)

/-- A map is isotropic for `α` exactly when `α` vanishes on all its tangent vectors. -/
theorem isIsotropicMap_iff :
    α.IsIsotropicMap J f ↔ ∀ y v, α.1 (f y) ![mfderiv J I f y v] = 0 := by
  refine forall_congr' fun y ↦ ⟨fun h v ↦ mem_kerDistribution.1 (h ⟨v, rfl⟩), ?_⟩
  rintro h _ ⟨v, rfl⟩
  exact mem_kerDistribution.2 (h v)

/-- The tangent vectors of an isotropic map lie in the kernel of the one-form. -/
theorem IsIsotropicMap.mfderiv_mem (h : α.IsIsotropicMap J f) (y : N) (v : TangentSpace J y) :
    mfderiv J I f y v ∈ α.kerDistribution (f y) :=
  h y ⟨v, rfl⟩

/-- **Isotropy is the vanishing of the pullback.** A map `f` is isotropic for `α` exactly when it
pulls `α` back to zero. -/
theorem isIsotropicMap_iff_mpullback_eq_zero :
    α.IsIsotropicMap J f ↔ TauCeti.mpullback J I f α.1 = 0 := by
  rw [isIsotropicMap_iff]
  refine ⟨fun h ↦ funext fun y ↦ ContinuousAlternatingMap.ext fun u ↦ ?_, fun h y v ↦ ?_⟩
  · -- A family of one tangent vector is `![u 0]`.
    have hu : (fun i ↦ mfderiv J I f y (u i)) = ![mfderiv J I f y (u 0)] := by
      ext i
      fin_cases i
      rfl
    rw [TauCeti.mpullback_apply, hu, h]
    rfl
  · have := congr($h y ![v])
    simp only [TauCeti.mpullback_apply, Matrix.vec_single_eq_const] at this ⊢
    simpa using this

/-- **Isotropy only depends on the kernel.** If `β = g α` for a nowhere vanishing function `g`,
then a map is isotropic for `β` exactly when it is isotropic for `α`. -/
theorem isIsotropicMap_iff_of_eq_smul {g : M → ℝ} (hg₀ : ∀ x, g x ≠ 0)
    (hβ : ∀ x, β.1 x = g x • α.1 x) :
    β.IsIsotropicMap J f ↔ α.IsIsotropicMap J f := by
  rw [IsIsotropicMap, IsIsotropicMap, kerDistribution_of_eq_smul hg₀ hβ]

/-! ### Reparametrization and transport -/

section Reparametrization

variable {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ E'' H''} {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  {n : ℕ∞ω}

/-- **Independence of the parametrization.** Precomposing with a diffeomorphism of the source does
not change whether a map is isotropic. -/
theorem isIsotropicMap_comp_diffeomorph_iff (φ : P ≃ₘ^n⟮K, J⟯ N) (hn : n ≠ 0) :
    α.IsIsotropicMap K (f ∘ φ) ↔ α.IsIsotropicMap J f := by
  simp only [IsIsotropicMap, φ.range_mfderiv_comp_diffeomorph hn, Function.comp_apply]
  refine ⟨fun h y ↦ ?_, fun h x ↦ h (φ x)⟩
  obtain ⟨x, rfl⟩ := φ.surjective y
  exact h x

end Reparametrization

section Transport

variable {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [IsManifold I₂ ∞ M₂] {α₂ : SmoothForm I₂ M₂ ℝ 1}

/-- **Transport by contactomorphisms.** If a diffeomorphism `ψ` pulls `α₂` back to `g α` for a
nowhere vanishing function `g`, so that it carries `ker α` to `ker α₂`, then `ψ ∘ f` is isotropic
for `α₂` exactly when `f` is isotropic for `α`. -/
theorem _root_.Diffeomorph.isIsotropicMap_comp_iff (ψ : M ≃ₘ⟮I, I₂⟯ M₂) {g : M → ℝ}
    (hg₀ : ∀ x, g x ≠ 0) (hψ : ∀ x, (SmoothForm.mpullback ψ ψ.contMDiff α₂).1 x = g x • α.1 x) :
    α₂.IsIsotropicMap J (ψ ∘ f) ↔ α.IsIsotropicMap J f := by
  refine forall_congr' fun y ↦ ?_
  -- The differential of `ψ` identifies `ker α` with `ker α₂`.
  have hker := congr_fun (kerDistribution_of_eq_smul hg₀ hψ) (f y)
  rw [kerDistribution_mpullback] at hker
  have hder : (ψ.mfderivToContinuousLinearEquiv (by simp) (f y)).toLinearEquiv.toLinearMap =
      (mfderiv I I₂ ψ (f y)).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (ψ.mfderivToContinuousLinearEquiv_coe _)
  rw [ψ.range_mfderiv_diffeomorph_comp (by simp), Function.comp_apply,
    Submodule.map_le_iff_le_comap, hder, hker]

end Transport

/-! ### The exterior derivative and the Levi form on isotropic tangent images -/

section ExtDeriv

variable [IsManifold J ∞ N]

/-- **Isotropic maps are isotropic for `dα`.** A smooth map which pulls `α` back to zero also pulls
`dα` back to zero, since `f^*(dα) = d(f^*α) = 0`. -/
theorem IsIsotropicMap.mpullback_mextDerivₗ_eq_zero (h : α.IsIsotropicMap J f)
    (hf : ContMDiff J I ∞ f) : SmoothForm.mpullback f hf (mextDerivₗ I 1 α) = 0 := by
  have h₀ : SmoothForm.mpullback f hf α = 0 := Subtype.ext <| by
    rw [coe_mpullback, ZeroMemClass.coe_zero]
    exact isIsotropicMap_iff_mpullback_eq_zero.1 h
  rw [← mextDerivₗ_mpullback, h₀, map_zero]

/-- The exterior derivative `dα` vanishes on pairs of tangent vectors of a smooth isotropic map. -/
theorem IsIsotropicMap.mextDeriv_apply_mfderiv_eq_zero (h : α.IsIsotropicMap J f)
    (hf : ContMDiff J I ∞ f) (y : N) (v w : TangentSpace J y) :
    mextDeriv α.1 (f y) ![mfderiv J I f y v, mfderiv J I f y w] = 0 := by
  have := congr($(h.mpullback_mextDerivₗ_eq_zero hf).1 y ![v, w])
  rw [SmoothForm.mpullback_apply, mextDerivₗ_apply] at this
  convert this using 2
  ext i
  fin_cases i <;> rfl

/-- **The Levi form vanishes on isotropic tangent images.** At a point where `α` does not vanish,
the Levi form of the distribution `ξ = ker α` vanishes on pairs of tangent vectors of a smooth
isotropic map. -/
theorem IsIsotropicMap.distributionLeviForm_eq_zero [FiniteDimensional ℝ E]
    (h : α.IsIsotropicMap J f) (hf : ContMDiff J I ∞ f) {y : N} (hy : α.1 (f y) ≠ 0)
    (v w : TangentSpace J y) :
    distributionLeviForm α.kerDistribution (f y) ⟨_, h.mfderiv_mem y v⟩ ⟨_, h.mfderiv_mem y w⟩ =
      0 := by
  -- The map induced by `α` on `T M ⧸ ker α` is injective and carries the Levi form to `dα`.
  have hinj : Function.Injective ((α.kerDistribution (f y)).liftQ
      (degreeOneEquiv α (f y) : TangentSpace I (f y) →ₗ[ℝ] ℝ)
      (kerDistribution_def α (f y)).le) := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (kerDistribution_def α (f y)).ge
  apply hinj
  rw [liftQ_distributionLeviForm_kerDistribution hy, map_zero]
  exact h.mextDeriv_apply_mfderiv_eq_zero hf y v w

/-- **The dimension bound for isotropic maps.** A smooth isotropic map for a contact form, with
injective differential at some point, comes from a manifold of dimension at most `n` when the
contact manifold has dimension `2 n + 1`. -/
theorem IsIsotropicMap.two_mul_finrank_add_one_le [FiniteDimensional ℝ E] (hα : α.IsContactForm)
    (h : α.IsIsotropicMap J f) (hf : ContMDiff J I ∞ f) {y : N}
    (hy : Function.Injective (mfderiv J I f y)) : 2 * finrank ℝ E' + 1 ≤ finrank ℝ E := by
  have hW := (isContactForm_def.1 hα (f y)).two_mul_finrank_add_one_le
    (W := LinearMap.range (mfderiv J I f y).toLinearMap) ((kerDistribution_def α (f y)) ▸ h y) ?_
  · rwa [LinearMap.finrank_range_of_inj hy, finrank_tangentSpace, finrank_tangentSpace] at hW
  · rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    rw [bilinFormAt_apply, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply]
    exact h.mextDeriv_apply_mfderiv_eq_zero hf y v w

end ExtDeriv

/-! ### Legendrian immersions -/

variable (J) in
/-- A **Legendrian immersion** for a one-form `α` on a finite-dimensional manifold `M` is a smooth
immersion `f : N → M` with isotropic tangent images from a manifold of dimension `n`, where `M` has
dimension `2 n + 1`. For a contact form this is the maximal dimension of an isotropic immersion
(`TauCeti.SmoothForm.IsIsotropicMap.two_mul_finrank_add_one_le`). Its image may have
self-intersections. -/
structure IsLegendrianImmersion [FiniteDimensional ℝ E] (α : SmoothForm I M ℝ 1) (f : N → M) :
    Prop where
  /-- A Legendrian immersion is a smooth immersion. -/
  isImmersion : IsImmersion J I ∞ f
  /-- A Legendrian immersion has tangent images in the kernel of the one-form. -/
  isIsotropicMap : α.IsIsotropicMap J f
  /-- A Legendrian immersion comes from a manifold of dimension `n`, for `M` of dimension
  `2 n + 1`. -/
  two_mul_finrank_add_one : 2 * finrank ℝ E' + 1 = finrank ℝ E

section Legendrian

variable [FiniteDimensional ℝ E]

/-- A Legendrian immersion is a smooth immersion with isotropic tangent images from a manifold of
dimension `n`, where `M` has dimension `2 n + 1`. -/
theorem isLegendrianImmersion_iff :
    α.IsLegendrianImmersion J f ↔ IsImmersion J I ∞ f ∧ α.IsIsotropicMap J f ∧
      2 * finrank ℝ E' + 1 = finrank ℝ E :=
  ⟨fun h ↦ ⟨h.1, h.2, h.3⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

/-- **Legendrian immersions only depend on the kernel.** If `β = g α` for a nowhere vanishing
function `g`, then a map is a Legendrian immersion for `β` exactly when it is one for `α`. -/
theorem isLegendrianImmersion_iff_of_eq_smul {g : M → ℝ} (hg₀ : ∀ x, g x ≠ 0)
    (hβ : ∀ x, β.1 x = g x • α.1 x) :
    β.IsLegendrianImmersion J f ↔ α.IsLegendrianImmersion J f := by
  rw [isLegendrianImmersion_iff, isLegendrianImmersion_iff, isIsotropicMap_iff_of_eq_smul hg₀ hβ]

variable (J) in
/-- A **Legendrian embedding** for `α` is a Legendrian immersion which is moreover a topological
embedding. It parametrizes an embedded Legendrian submanifold, without self-intersections. -/
structure IsLegendrianEmbedding (α : SmoothForm I M ℝ 1) (f : N → M) : Prop
    extends α.IsLegendrianImmersion J f where
  /-- A Legendrian embedding is a homeomorphism onto its image. -/
  isEmbedding : Topology.IsEmbedding f

/-- A Legendrian embedding is a smooth embedding in Mathlib's sense. -/
theorem IsLegendrianEmbedding.isSmoothEmbedding (h : α.IsLegendrianEmbedding J f) :
    IsSmoothEmbedding J I ∞ f :=
  ⟨h.isImmersion, h.isEmbedding⟩

/-- A Legendrian embedding is a Legendrian immersion which is a topological embedding. -/
theorem isLegendrianEmbedding_iff :
    α.IsLegendrianEmbedding J f ↔ α.IsLegendrianImmersion J f ∧ Topology.IsEmbedding f :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

variable {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H M₂] [IsManifold I ∞ M₂]
  {α₂ : SmoothForm I M₂ ℝ 1}

/-- **Transport of Legendrian immersions by contactomorphisms.** If a diffeomorphism `ψ` pulls
`α₂` back to `g α` for a nowhere vanishing function `g`, then `ψ ∘ f` is a Legendrian immersion
for `α₂` exactly when `f` is a Legendrian immersion for `α`. -/
theorem _root_.Diffeomorph.isLegendrianImmersion_comp_iff (ψ : M ≃ₘ⟮I, I⟯ M₂) {g : M → ℝ}
    (hg₀ : ∀ x, g x ≠ 0) (hψ : ∀ x, (SmoothForm.mpullback ψ ψ.contMDiff α₂).1 x = g x • α.1 x) :
    α₂.IsLegendrianImmersion J (ψ ∘ f) ↔ α.IsLegendrianImmersion J f := by
  rw [isLegendrianImmersion_iff, isLegendrianImmersion_iff, isImmersion_diffeomorph_comp_iff,
    ψ.isIsotropicMap_comp_iff hg₀ hψ]

/-- **Transport of Legendrian embeddings by contactomorphisms.** If a diffeomorphism `ψ` pulls
`α₂` back to `g α` for a nowhere vanishing function `g`, then `ψ ∘ f` is a Legendrian embedding
for `α₂` exactly when `f` is a Legendrian embedding for `α`. -/
theorem _root_.Diffeomorph.isLegendrianEmbedding_comp_iff (ψ : M ≃ₘ⟮I, I⟯ M₂) {g : M → ℝ}
    (hg₀ : ∀ x, g x ≠ 0) (hψ : ∀ x, (SmoothForm.mpullback ψ ψ.contMDiff α₂).1 x = g x • α.1 x) :
    α₂.IsLegendrianEmbedding J (ψ ∘ f) ↔ α.IsLegendrianEmbedding J f := by
  rw [isLegendrianEmbedding_iff, isLegendrianEmbedding_iff, ψ.isLegendrianImmersion_comp_iff hg₀ hψ,
    ← ψ.coe_toHomeomorph, Homeomorph.comp_isEmbedding_iff]

end Legendrian

/-! ### Isotropic maps into a contactization -/

section Contactization

variable {θ : SmoothForm I M ℝ 1} {i : N → M} {h : N → ℝ}

/-- **Isotropic maps into a contactization.** A map `y ↦ (i y, h y)` into `M × ℝ`, with `i` and `h`
differentiable, is isotropic for the contactization form `dz - θ` exactly when `i^*θ = dh`. -/
theorem isIsotropicMap_contactization_iff (hi : MDifferentiable J I i)
    (hh : MDifferentiable J 𝓘(ℝ) h) :
    θ.contactization.IsIsotropicMap J (fun y ↦ (i y, h y)) ↔
      TauCeti.mpullback J I i θ.1 = mextDeriv (RoughForm.ofFunction J h) := by
  -- The contactization form on the tangent vector `(di v, dh v)` is `dh v - θ (di v)`.
  have key (y : N) (v : TangentSpace J y) :
      θ.contactization.1 (i y, h y) ![mfderiv J (I.prod 𝓘(ℝ)) (fun y ↦ (i y, h y)) y v] =
        mextDeriv (RoughForm.ofFunction J h) y ![v] - TauCeti.mpullback J I i θ.1 y ![v] := by
    rw [contactization_apply, mfderiv_prodMk (hi y) (hh y), mextDeriv_ofFunction_apply,
      TauCeti.mpullback_apply]
    congr 1
    · rw [NormedSpace.fromTangentSpace_apply, Manifold.tangentSpaceProdEquiv_apply]
      rfl
    · congr 1
      ext j
      fin_cases j
      rw [Matrix.cons_val_fin_one, Matrix.cons_val_fin_one, Manifold.tangentSpaceProdEquiv_apply]
      rfl
  rw [isIsotropicMap_iff]
  simp only [key, sub_eq_zero]
  refine ⟨fun H ↦ funext fun y ↦ ContinuousAlternatingMap.ext fun u ↦ ?_, fun H y v ↦ by rw [H]⟩
  -- A family of one tangent vector is `![u 0]`.
  have hu : u = ![u 0] := by
    ext j
    fin_cases j
    rfl
  rw [hu, H]

variable [FiniteDimensional ℝ E] [IsManifold J ∞ N] [I.Boundaryless] [J.Boundaryless]

/-- **Legendrian immersions into a contactization are lifts of exact Lagrangian immersions.**
Let `(M, -dθ)` be an exact symplectic manifold without boundary, and let `N` be a manifold without
boundary. A map `y ↦ (i y, h y)` into the contactization `M × ℝ` is a Legendrian immersion for
`dz - θ` exactly when `i` is a Lagrangian immersion for `-dθ` and `h` is a smooth primitive of
`i^*θ`. In particular the Lagrangian projection of a Legendrian immersion is an exact Lagrangian
immersion, and every exact Lagrangian immersion lifts to a Legendrian immersion through any of
its primitives. -/
theorem isLegendrianImmersion_contactization_iff
    (hθ : SmoothTwoForm.IsNondegenerate (-mextDerivₗ I 1 θ)) :
    θ.contactization.IsLegendrianImmersion J (fun y ↦ (i y, h y)) ↔
      hθ.IsLagrangianImmersion J i ∧ ContMDiff J 𝓘(ℝ) ∞ h ∧
        TauCeti.mpullback J I i θ.1 = mextDeriv (RoughForm.ofFunction J h) := by
  have hdimW : finrank ℝ (E × ℝ) = finrank ℝ E + 1 := by
    rw [finrank_prod, finrank_self]
  constructor
  · rintro ⟨himm, hiso, hdim⟩
    have hsmooth := himm.contMDiff
    have hi : ContMDiff J I ∞ i := contMDiff_fst.comp hsmooth
    have hh : ContMDiff J 𝓘(ℝ) ∞ h := contMDiff_snd.comp hsmooth
    have hpull := (isIsotropicMap_contactization_iff (hi.mdifferentiable (by simp))
      (hh.mdifferentiable (by simp))).1 hiso
    refine ⟨⟨?_, hθ.isIsotropicMap_of_mpullback_eq_mextDeriv rfl hi (hh.of_le (by simp)) hpull,
      by omega⟩, hh, hpull⟩
    -- If `di v = 0` then `dh v = θ (di v) = 0`, so `v` is killed by the differential of `(i, h)`.
    refine isImmersion_iff_forall_isImmersionAt.2 fun y ↦
      (hi.contMDiffOn (s := Set.univ)).isImmersionAt_iff_injective_mfderiv isOpen_univ
        (Set.mem_univ y) (by simp) |>.2 fun v w hvw ↦ himm.mfderiv_injective (by simp) y ?_
    have hdh : ∀ u, mfderiv J 𝓘(ℝ) h y u = θ.1 (i y) ![mfderiv J I i y u] := fun u ↦ by
      have := congr($hpull y ![u])
      rw [TauCeti.mpullback_apply, mextDeriv_ofFunction_apply] at this
      rw [← this]
      congr 1
      ext j
      fin_cases j
      rfl
    rw [mfderiv_prodMk (hi.mdifferentiable (by simp) y) (hh.mdifferentiable (by simp) y)]
    exact Prod.ext hvw ((hdh v).trans (by rw [hvw]; exact (hdh w).symm))
  · rintro ⟨hL, hh, hpull⟩
    have hi := hL.isImmersion.contMDiff
    have hsmooth : ContMDiff J (I.prod 𝓘(ℝ)) ∞ (fun y ↦ (i y, h y)) := hi.prodMk hh
    refine ⟨?_, (isIsotropicMap_contactization_iff (hi.mdifferentiable (by simp))
      (hh.mdifferentiable (by simp))).2 hpull, by rw [hdimW, ← hL.two_mul_finrank]⟩
    -- The differential of `(i, h)` is injective because that of `i` is.
    refine isImmersion_iff_forall_isImmersionAt.2 fun y ↦
      hsmooth.contMDiffOn.isImmersionAt_iff_injective_mfderiv isOpen_univ (Set.mem_univ y)
        (by simp) |>.2 fun v w hvw ↦ hL.isImmersion.mfderiv_injective (by simp) y ?_
    rw [mfderiv_prodMk (hi.mdifferentiable (by simp) y) (hh.mdifferentiable (by simp) y)] at hvw
    exact congrArg Prod.fst hvw

end Contactization

end SmoothForm

/-! ### Legendrian one-jets -/

namespace CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- **The graph criterion in the one-jet space.** A section `x ↦ (σ_x, g x)` of
`J¹M = T*M × ℝ → M`, with `σ` and `g` differentiable, is isotropic for the contact form `dz - λ`
exactly when `σ` is the differential of `g`. -/
theorem isIsotropicMap_contactization_section_iff {σ : (x : M) → TangentSpace I x →L[ℝ] ℝ}
    (hσ : MDifferentiable I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (σ x)))
    {g : M → ℝ} (hg : MDifferentiable I 𝓘(ℝ) g) :
    (liouvilleForm I M).contactization.IsIsotropicMap I
        (fun x ↦ (TotalSpace.mk' (E →L[ℝ] ℝ) x (σ x), g x)) ↔
      σ = mvfderiv I g := by
  rw [SmoothForm.isIsotropicMap_contactization_iff hσ hg]
  refine ⟨fun H ↦ funext fun x ↦ ?_, fun H ↦ funext fun x ↦ ?_⟩
  · -- The Liouville form is tautological: the section pulls it back to `σ`.
    have := congr_fun H x
    rwa [mpullback_liouvilleForm_section (hσ x), mextDeriv_ofFunction,
      (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ (0 : Fin 1)).injective.eq_iff]
      at this
  · rw [mpullback_liouvilleForm_section (hσ x), mextDeriv_ofFunction, H]

/-- The **one-jet** `j¹g : x ↦ (dg_x, g x)` of a function `g : M → ℝ`, as a section of the one-jet
space `J¹M = T*M × ℝ`. -/
def oneJet (g : M → ℝ) (x : M) : CotangentBundle I M × ℝ :=
  (TotalSpace.mk' (E →L[ℝ] ℝ) x (mvfderiv I g x), g x)

omit [IsManifold I ∞ M] in
@[simp]
theorem oneJet_apply (g : M → ℝ) (x : M) :
    oneJet (I := I) g x = (TotalSpace.mk' (E →L[ℝ] ℝ) x (mvfderiv I g x), g x) :=
  (rfl)

/-- The one-jet of a smooth function is smooth. -/
theorem contMDiff_oneJet {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    ContMDiff I ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod 𝓘(ℝ)) ∞ (oneJet (I := I) g) :=
  (ContMDiff.contMDiff_totalSpaceMk_mvfderiv (n := ∞) hg).prodMk hg

/-- **One-jets are isotropic.** The one-jet of a smooth function is an isotropic map for the
contact form `dz - λ` of `J¹M`. -/
theorem isIsotropicMap_oneJet {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    (liouvilleForm I M).contactization.IsIsotropicMap I (oneJet (I := I) g) :=
  (isIsotropicMap_contactization_section_iff
    ((ContMDiff.contMDiff_totalSpaceMk_mvfderiv (n := ∞) hg).mdifferentiable (by simp))
    (hg.mdifferentiable (by simp))).2 rfl

/-- **One-jets are Legendrian immersions.** On a finite-dimensional manifold without boundary, the
one-jet `j¹g` of a smooth function is a Legendrian immersion into `J¹M` for the contact form
`dz - λ`. -/
theorem isLegendrianImmersion_oneJet [FiniteDimensional ℝ E] [I.Boundaryless] {g : M → ℝ}
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    (liouvilleForm I M).contactization.IsLegendrianImmersion I (oneJet (I := I) g) := by
  refine ⟨isImmersion_iff_forall_isImmersionAt.2 fun x ↦ ?_, isIsotropicMap_oneJet hg, ?_⟩
  · -- The projection `(p, z) ↦ π p` is a left inverse of the one-jet.
    exact (contMDiff_oneJet hg).contMDiffOn.isImmersionAt_of_comp_eventuallyEq_id
      (g := TotalSpace.proj ∘ Prod.fst) isOpen_univ (Set.mem_univ x) (by simp)
      (((contMDiff_proj (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)).comp contMDiff_fst)
        |>.mdifferentiableAt (n := 1) (x := oneJet g x) one_ne_zero)
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  · rw [finrank_prod, finrank_prod, ContinuousLinearMap.dual_finrank_eq, finrank_self]
    ring

/-- **One-jets are Legendrian embeddings.** On a finite-dimensional manifold without boundary, the
one-jet `j¹g` of a smooth function is a Legendrian embedding into `J¹M`: the projection
`(p, z) ↦ π p` is a continuous left inverse, so the image of `j¹g` has no self-intersections. -/
theorem isLegendrianEmbedding_oneJet [FiniteDimensional ℝ E] [I.Boundaryless] {g : M → ℝ}
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    (liouvilleForm I M).contactization.IsLegendrianEmbedding I (oneJet (I := I) g) :=
  { isLegendrianImmersion_oneJet hg with
    isEmbedding := Function.LeftInverse.isEmbedding (f := TotalSpace.proj ∘ Prod.fst)
      (fun _ ↦ rfl)
      ((FiberBundle.continuous_proj (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)).comp
        continuous_fst)
      (contMDiff_oneJet hg).continuous }

end CotangentBundle

end TauCeti
