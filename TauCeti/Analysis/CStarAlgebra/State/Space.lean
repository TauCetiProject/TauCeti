/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
public import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# The state space of a C⋆-algebra

A *state* of a possibly nonunital C⋆-algebra `A` is a positive linear functional of norm one.
This file defines the state space `TauCeti.stateSpace A` as a subset of the weak-* dual
`WeakDual ℂ A`, so that convexity, closedness and compactness refer to the weak-* topology.

* `TauCeti.mem_stateSpace_iff_exists_positiveLinearMap`: the states are exactly the positive
  linear maps `A →ₚ[ℂ] ℂ` of norm one, through the automatic continuity of positive maps.
* `TauCeti.convex_stateSpace`: the state space is convex. No unit is needed, because the norm of
  a positive functional is its limit along an approximate unit.
* `TauCeti.map_eq_zero_of_mem_openSegment_of_mem_stateSpace`: if a functional in an open
  segment between two states vanishes at a nonnegative element, so do both states.
* `TauCeti.mapsTo_pullbackFunctional_stateSpace_of_surjective` and
  `TauCeti.mapsTo_pullbackFunctional_stateSpace`: precomposition with a star homomorphism
  (`ContinuousLinearMap.pullbackFunctional`) restricts to an affine map of state spaces along
  surjective star homomorphisms and along unital star homomorphisms. Along a surjective `f`, its
  image on states consists of the states vanishing on the kernel of `f`,
  `TauCeti.mem_image_pullbackFunctional_stateSpace_iff`.
* `TauCeti.mem_stateSpace_of_pullbackFunctional_mem_stateSpace`: a positive functional of norm at
  most `1` whose restriction along a star homomorphism is a state is itself a state.

For unital `A`:

* `TauCeti.mem_stateSpace_iff_map_one`: a positive functional is a state exactly when `φ 1 = 1`,
  and `TauCeti.mem_stateSpace_iff_norm_eq_one_and_map_one`: a functional is a state exactly when
  `‖φ‖ = φ 1 = 1`, with positivity then automatic.
* `TauCeti.isCompact_stateSpace`: the state space is weak-* compact, by Banach–Alaoglu.
* `TauCeti.stateSpace_nonempty`: if `A` is nonzero it has a state, by Hahn–Banach. The state
  space of `ℂ` is the single functional `z ↦ z`, `TauCeti.stateSpace_complex`.
* `TauCeti.closure_convexHull_extremePoints_stateSpace`: the state space is the weak-* closed
  convex hull of its extreme points, the pure states, by the Krein–Milman theorem; in particular
  a nonzero unital C⋆-algebra has a pure state, `TauCeti.extremePoints_stateSpace_nonempty`.

Without a unit the state space is still closed in the norm topology of the dual,
`TauCeti.isClosed_preimage_toWeakDual_stateSpace`, but in general it is not weak-* closed: on
`c₀` the point evaluations are states that converge weak-* to `0`.

## References

Jesse Peterson, *Notes on operator algebras*, Section 4.1.
-/

public section

open Set Filter WeakDual
open scoped ComplexOrder ComplexStarModule Topology

namespace TauCeti

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] {φ : WeakDual ℂ A}

variable (A) in
/-- The **state space** of a C⋆-algebra `A`: the functionals in the weak-* dual of `A` that are
nonnegative on nonnegative elements and have norm one. The results about it take the order on `A`
to be the C⋆-algebra order, through `StarOrderedRing A`. -/
def stateSpace : Set (WeakDual ℂ A) :=
  {φ | (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ ‖toStrongDual φ‖ = 1}

/-- Membership in the state space unfolds to positivity and norm one. -/
theorem mem_stateSpace_iff :
    φ ∈ stateSpace A ↔ (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ ‖toStrongDual φ‖ = 1 :=
  Iff.rfl

/-- A state is nonnegative on nonnegative elements. -/
theorem map_nonneg_of_mem_stateSpace (hφ : φ ∈ stateSpace A) {a : A} (ha : 0 ≤ a) : 0 ≤ φ a :=
  (mem_stateSpace_iff.1 hφ).1 a ha

/-- A state has norm one. -/
theorem norm_toStrongDual_of_mem_stateSpace (hφ : φ ∈ stateSpace A) : ‖toStrongDual φ‖ = 1 :=
  (mem_stateSpace_iff.1 hφ).2

/-- An algebra with a state is nonzero. -/
theorem nontrivial_of_mem_stateSpace (hφ : φ ∈ stateSpace A) : Nontrivial A := by
  by_contra hA
  rw [not_nontrivial_iff_subsingleton] at hA
  have h0 : ‖toStrongDual φ‖ ≤ 0 :=
    (toStrongDual φ).opNorm_le_bound le_rfl fun a => by simp [Subsingleton.elim a 0]
  linarith [norm_toStrongDual_of_mem_stateSpace hφ]

/-- A state is contractive. -/
theorem norm_apply_le_of_mem_stateSpace (hφ : φ ∈ stateSpace A) (a : A) : ‖φ a‖ ≤ ‖a‖ := by
  simpa [norm_toStrongDual_of_mem_stateSpace hφ] using (toStrongDual φ).le_opNorm a

/-- In the norm topology of the continuous dual, the state space is closed. -/
theorem isClosed_preimage_toWeakDual_stateSpace :
    IsClosed (StrongDual.toWeakDual ⁻¹' stateSpace A) := by
  exact (isClosed_setOf_map_nonneg.preimage NormedSpace.Dual.toWeakDual_continuous).inter
    (isClosed_eq continuous_norm continuous_const)

/-- A positive continuous linear functional is a state exactly when its norm is one. -/
@[simp]
theorem _root_.PositiveContinuousLinearMap.toWeakDual_mem_stateSpace_iff (ω : A →P[ℂ] ℂ) :
    StrongDual.toWeakDual (ω : A →L[ℂ] ℂ) ∈ stateSpace A ↔ ‖(ω : A →L[ℂ] ℂ)‖ = 1 := by
  simp only [mem_stateSpace_iff, StrongDual.toWeakDual_apply,
    StrongDual.toStrongDual_toWeakDual, and_iff_right_iff_imp]
  exact fun _ a ha => ω.map_nonneg ha

/-- **States vanishing at a nonnegative element form a face.** If a functional in an open segment
between two states vanishes at a nonnegative element `x`, both endpoints vanish at `x`. -/
theorem map_eq_zero_of_mem_openSegment_of_mem_stateSpace {ψ₁ ψ₂ : WeakDual ℂ A}
    (hψ₁ : ψ₁ ∈ stateSpace A) (hψ₂ : ψ₂ ∈ stateSpace A) {x : A} (hx : 0 ≤ x)
    (hφ : φ ∈ openSegment ℝ ψ₁ ψ₂) (hφx : φ x = 0) : ψ₁ x = 0 ∧ ψ₂ x = 0 := by
  obtain ⟨s, t, hs, ht, -, rfl⟩ := hφ
  have hsum : (s : ℂ) * ψ₁ x + (t : ℂ) * ψ₂ x = 0 := by simpa [Complex.real_smul] using hφx
  -- Both terms are nonnegative, and their sum vanishes.
  obtain ⟨e₁, e₂⟩ := (add_eq_zero_iff_of_nonneg
    (mul_nonneg (Complex.zero_le_real.2 hs.le) (map_nonneg_of_mem_stateSpace hψ₁ hx))
    (mul_nonneg (Complex.zero_le_real.2 ht.le) (map_nonneg_of_mem_stateSpace hψ₂ hx))).1 hsum
  exact ⟨(mul_eq_zero.1 e₁).resolve_left (Complex.ofReal_ne_zero.2 hs.ne'),
    (mul_eq_zero.1 e₂).resolve_left (Complex.ofReal_ne_zero.2 ht.ne')⟩

variable [StarOrderedRing A]

/-- The states of `A` are exactly the positive linear maps `A →ₚ[ℂ] ℂ` of norm one, viewed in the
weak-* dual. -/
theorem mem_stateSpace_iff_exists_positiveLinearMap :
    φ ∈ stateSpace A ↔ ∃ ω : A →ₚ[ℂ] ℂ, ‖(PositiveContinuousLinearMap.ofClass ω : A →L[ℂ] ℂ)‖ = 1 ∧
      StrongDual.toWeakDual (PositiveContinuousLinearMap.ofClass ω : A →L[ℂ] ℂ) = φ := by
  refine ⟨fun hφ => ?_, fun ⟨ω, hω, h⟩ =>
    h ▸ (PositiveContinuousLinearMap.ofClass ω).toWeakDual_mem_stateSpace_iff.2 hω⟩
  let ω : A →ₚ[ℂ] ℂ := .mk₀ (toStrongDual φ : A →ₗ[ℂ] ℂ) fun _ => map_nonneg_of_mem_stateSpace hφ
  have hω : (PositiveContinuousLinearMap.ofClass ω : A →L[ℂ] ℂ) = toStrongDual φ := by
    -- `PositiveLinearMap.mk₀` has no evaluation lemma; it evaluates as `φ` by definition
    ext
    rfl
  exact ⟨ω, hω ▸ norm_toStrongDual_of_mem_stateSpace hφ, by rw [hω, toWeakDual_toStrongDual]⟩

/-- A state takes real values on self-adjoint elements. -/
theorem isSelfAdjoint_apply_of_mem_stateSpace (hφ : φ ∈ stateSpace A) {a : A}
    (ha : IsSelfAdjoint a) : IsSelfAdjoint (φ a) := by
  have hpos : ∀ x, 0 ≤ x → 0 ≤ toStrongDual φ x := fun x hx =>
    (map_nonneg_of_mem_stateSpace hφ hx).trans_eq (toStrongDual_apply φ x).symm
  simpa only [PositiveContinuousLinearMap.mk₀_apply, toStrongDual_apply] using
    ha.map' (PositiveContinuousLinearMap.mk₀ _ hpos)

/-- A state sees only the real part of an element: `re (φ (ℜ x)) = re (φ x)`. -/
theorem re_apply_realPart_of_mem_stateSpace (hφ : φ ∈ stateSpace A) (x : A) :
    (φ (ℜ x : A)).re = (φ x).re := by
  have him : (φ (ℑ x : A)).im = 0 :=
    RCLike.conj_eq_iff_im.1 (isSelfAdjoint_apply_of_mem_stateSpace hφ (ℑ x).property).star_eq
  conv_rhs => rw [← realPart_add_I_smul_imaginaryPart x]
  simp [him]

/-- **Convexity of the state space.** Real convex combinations of states are states. -/
theorem convex_stateSpace : Convex ℝ (stateSpace A) := by
  intro φ hφ ψ hψ s t hs ht hst
  rw [mem_stateSpace_iff] at hφ hψ ⊢
  have hpos (a : A) (ha : 0 ≤ a) : 0 ≤ (s • φ + t • ψ) a := by
    simpa using add_nonneg (smul_nonneg hs (hφ.1 a ha)) (smul_nonneg ht (hψ.1 a ha))
  refine ⟨hpos, ?_⟩
  -- the norm of a positive functional is its limit along an approximate unit
  have h := ((tendsto_approximateUnit_norm_of_map_nonneg hφ.1).const_smul s).add
    ((tendsto_approximateUnit_norm_of_map_nonneg hψ.1).const_smul t)
  simp only [hφ.2, hψ.2, Complex.ofReal_one, ← add_smul, hst, one_smul] at h
  exact_mod_cast tendsto_nhds_unique (tendsto_approximateUnit_norm_of_map_nonneg hpos)
    (h.congr fun e => by simp)

variable {B F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **Pullback of states along a surjective star homomorphism.** Composing a state of `B` with a
surjective star homomorphism `A → B` gives a state of `A`. Without surjectivity the norm of the
composite can drop, for instance to `0`. -/
theorem mapsTo_pullbackFunctional_stateSpace_of_surjective (f : F) (hf : Function.Surjective f) :
    MapsTo (PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional
      (stateSpace B) (stateSpace A) := by
  intro φ hφ
  let ω : B →P[ℂ] ℂ := .mk₀ (toStrongDual φ) fun x hx =>
    (map_nonneg_of_mem_stateSpace hφ hx).trans_eq (toStrongDual_apply φ x).symm
  have hφω : StrongDual.toWeakDual (ω : B →L[ℂ] ℂ) = φ := by
    rw [PositiveContinuousLinearMap.toContinuousLinearMap_mk₀, toWeakDual_toStrongDual]
  have hcomp : ((ω.comp (.ofClass f) : A →P[ℂ] ℂ) : A →L[ℂ] ℂ) =
      toStrongDual ((PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional φ) := by
    rw [← hφω, ContinuousLinearMap.pullbackFunctional_toWeakDual,
      StrongDual.toStrongDual_toWeakDual, PositiveContinuousLinearMap.toContinuousLinearMap_comp]
  refine mem_stateSpace_iff.2 ⟨fun a ha => ?_, ?_⟩
  · simpa using map_nonneg_of_mem_stateSpace hφ (map_nonneg f ha)
  · rw [← hcomp, PositiveContinuousLinearMap.opNorm_comp_ofClass_of_surjective ω f hf]
    exact norm_toStrongDual_of_mem_stateSpace hφ

/-- **States factoring through a surjection.** For a surjective star homomorphism `f : A → B`, the
pullbacks of states of `B` along `f` are exactly the states of `A` vanishing on the kernel of `f`.
-/
theorem mem_image_pullbackFunctional_stateSpace_iff (f : F) (hf : Function.Surjective f)
    {ψ : WeakDual ℂ A} :
    ψ ∈ (PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional '' stateSpace B ↔
      ψ ∈ stateSpace A ∧ ∀ k, f k = 0 → ψ k = 0 := by
  refine ⟨?_, fun ⟨hψ, hker⟩ => ?_⟩
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨mapsTo_pullbackFunctional_stateSpace_of_surjective f hf hφ, fun k hk => by simp [hk]⟩
  -- `ψ` vanishes on the kernel of `f`, so it factors linearly through `f`
  let g : B →ₗ[ℂ] ℂ := (f : A →ₗ[ℂ] B).liftOfSurjective hf
    ⟨toStrongDual ψ, fun k hk => by simpa using hker k hk⟩
  have hg (a : A) : g (f a) = ψ a := by
    simpa using LinearMap.equivOfSurjective_apply (f := (f : A →ₗ[ℂ] B)) hf
      (g := (toStrongDual ψ : A →ₗ[ℂ] ℂ)) (fun k hk => by simpa using hker k hk) (m := a)
  have hgpos (b : B) (hb : 0 ≤ b) : 0 ≤ g b := by
    obtain ⟨c, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hb
    obtain ⟨a, rfl⟩ := hf c
    rw [← map_star, ← map_mul, hg]
    exact map_nonneg_of_mem_stateSpace hψ (star_mul_self_nonneg a)
  let ω : B →P[ℂ] ℂ := .ofClass (PositiveLinearMap.mk₀ g hgpos)
  have hcomp : ((ω.comp (.ofClass f) : A →P[ℂ] ℂ) : A →L[ℂ] ℂ) = toStrongDual ψ := by
    -- `PositiveLinearMap.mk₀` has no evaluation lemma; `ω` evaluates as `g` by definition
    ext a
    exact hg a
  refine ⟨StrongDual.toWeakDual (ω : B →L[ℂ] ℂ), ?_, ?_⟩
  · rw [PositiveContinuousLinearMap.toWeakDual_mem_stateSpace_iff,
      ← PositiveContinuousLinearMap.opNorm_comp_ofClass_of_surjective ω f hf, hcomp]
    exact norm_toStrongDual_of_mem_stateSpace hψ
  · rw [ContinuousLinearMap.pullbackFunctional_toWeakDual,
      ← PositiveContinuousLinearMap.toContinuousLinearMap_comp, hcomp, toWeakDual_toStrongDual]

/-- The restriction of a state along a star homomorphism is nonnegative on nonnegative
elements. -/
theorem map_nonneg_pullbackFunctional_of_mem_stateSpace (f : F) {φ : WeakDual ℂ B}
    (hφ : φ ∈ stateSpace B) {a : A} (ha : 0 ≤ a) :
    0 ≤ (PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional φ a := by
  simpa using map_nonneg_of_mem_stateSpace hφ (map_nonneg f ha)

/-- Restriction along a star homomorphism does not increase the norm of a functional. -/
theorem norm_toStrongDual_pullbackFunctional_le (f : F) (φ : WeakDual ℂ B) :
    ‖toStrongDual ((PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional φ)‖ ≤
      ‖toStrongDual φ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  calc ‖toStrongDual ((PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional φ) x‖
      = ‖toStrongDual φ (f x)‖ := by simp
    _ ≤ ‖toStrongDual φ‖ * ‖f x‖ := (toStrongDual φ).le_opNorm _
    _ ≤ ‖toStrongDual φ‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le f x) (norm_nonneg _)

/-- The restriction of a state along a star homomorphism has norm at most `1`. -/
theorem norm_toStrongDual_pullbackFunctional_le_one (f : F) {φ : WeakDual ℂ B}
    (hφ : φ ∈ stateSpace B) :
    ‖toStrongDual ((PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional φ)‖ ≤
      1 :=
  (norm_toStrongDual_pullbackFunctional_le f φ).trans (norm_toStrongDual_of_mem_stateSpace hφ).le

/-- The restriction of a state along a star homomorphism is a state exactly when it has norm
`1`. -/
theorem pullbackFunctional_mem_stateSpace_iff (f : F) {φ : WeakDual ℂ B}
    (hφ : φ ∈ stateSpace B) :
    (PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional φ ∈ stateSpace A ↔
      ‖toStrongDual ((PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional φ)‖ =
        1 :=
  mem_stateSpace_iff.trans
    (and_iff_right fun _ ha => map_nonneg_pullbackFunctional_of_mem_stateSpace f hφ ha)

/-- A functional `χ` of `B` that is nonnegative on nonnegative elements and has norm at most `1`
is a state if its restriction along a star homomorphism `f : A → B` is a state. -/
theorem mem_stateSpace_of_pullbackFunctional_mem_stateSpace (f : F) {χ : WeakDual ℂ B}
    (hpos : ∀ b, 0 ≤ b → 0 ≤ χ b) (hnorm : ‖toStrongDual χ‖ ≤ 1)
    (h : (PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional χ ∈
      stateSpace A) : χ ∈ stateSpace B := by
  refine mem_stateSpace_iff.2 ⟨hpos, le_antisymm hnorm ?_⟩
  rw [← norm_toStrongDual_of_mem_stateSpace h]
  exact norm_toStrongDual_pullbackFunctional_le f χ

/-- If the restriction of a state of `C` along a composite `A → B → C` of star homomorphisms is a
state of `A`, then its restriction to `B` is a state of `B`. -/
theorem pullbackFunctional_mem_stateSpace_of_pullbackFunctional_pullbackFunctional_mem_stateSpace
    {C G : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    [FunLike G B C] [NonUnitalAlgHomClass G ℂ B C] [StarHomClass G B C] (f : F) (g : G)
    {ψ : WeakDual ℂ C} (hψ : ψ ∈ stateSpace C)
    (h : (PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional
      ((PositiveContinuousLinearMap.ofClass g : B →L[ℂ] C).pullbackFunctional ψ) ∈
      stateSpace A) :
    (PositiveContinuousLinearMap.ofClass g : B →L[ℂ] C).pullbackFunctional ψ ∈ stateSpace B :=
  mem_stateSpace_of_pullbackFunctional_mem_stateSpace f
    (fun _ hb => map_nonneg_pullbackFunctional_of_mem_stateSpace g hψ hb)
    (norm_toStrongDual_pullbackFunctional_le_one g hψ) h

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {φ : WeakDual ℂ A}

/-- On a unital C⋆-algebra, a functional that is nonnegative on nonnegative elements is a state
exactly when it takes the value `1` at `1`. -/
theorem mem_stateSpace_iff_map_one :
    φ ∈ stateSpace A ↔ (∀ a, 0 ≤ a → 0 ≤ φ a) ∧ φ 1 = 1 := by
  refine and_congr_right fun hpos => ?_
  rw [← norm_toStrongDual_eq_map_one_of_map_nonneg hpos]
  exact_mod_cast Iff.rfl

/-- A state of a unital C⋆-algebra takes the value `1` at `1`. -/
theorem map_one_of_mem_stateSpace (hφ : φ ∈ stateSpace A) : φ 1 = 1 :=
  (mem_stateSpace_iff_map_one.1 hφ).2

/-- A state of a unital C⋆-algebra takes the value `c` at `c • 1`, so it extends the unique state
`c • 1 ↦ c` of the subalgebra `ℂ·1`. -/
theorem map_algebraMap_of_mem_stateSpace (hφ : φ ∈ stateSpace A) (c : ℂ) :
    φ (algebraMap ℂ A c) = c := by
  simp [Algebra.algebraMap_eq_smul_one, map_one_of_mem_stateSpace hφ]

/-- On a unital C⋆-algebra, a functional is a state exactly when `‖φ‖ = φ 1 = 1`. Positivity is
then automatic: it follows from `φ 1 = ‖φ‖ = 1`. -/
theorem mem_stateSpace_iff_norm_eq_one_and_map_one :
    φ ∈ stateSpace A ↔ ‖toStrongDual φ‖ = 1 ∧ φ 1 = 1 := by
  refine ⟨fun hφ => ⟨norm_toStrongDual_of_mem_stateSpace hφ, map_one_of_mem_stateSpace hφ⟩,
    fun ⟨hnorm, h1⟩ => ?_⟩
  have hmono : Monotone (toStrongDual φ) := by
    rw [ContinuousLinearMap.monotone_iff_opNorm_eq_map_one, hnorm, toStrongDual_apply, h1,
      Complex.ofReal_one]
  exact mem_stateSpace_iff.2
    ⟨fun a ha => by simpa using (monotone_iff_map_nonneg _).mp hmono a ha, hnorm⟩

/-- For unital `A`, the state space is weak-* closed. -/
theorem isClosed_stateSpace : IsClosed (stateSpace A) := by
  have h : stateSpace A = {φ : WeakDual ℂ A | ∀ a, 0 ≤ a → 0 ≤ φ a} ∩ {φ | φ 1 = 1} :=
    Set.ext fun _ => mem_stateSpace_iff_map_one
  rw [h]
  exact isClosed_setOf_map_nonneg.inter (isClosed_eq (eval_continuous 1) continuous_const)

/-- **Weak-* compactness of the state space.** For unital `A`, the state space is weak-* compact,
by the Banach–Alaoglu theorem. -/
theorem isCompact_stateSpace : IsCompact (stateSpace A) := by
  refine (WeakDual.isCompact_closedBall 0 1).of_isClosed_subset isClosed_stateSpace
    fun φ hφ => ?_
  simp [norm_toStrongDual_of_mem_stateSpace hφ]

/-- **Existence of states.** A nonzero unital C⋆-algebra has a state. -/
theorem stateSpace_nonempty [Nontrivial A] : (stateSpace A).Nonempty := by
  -- by Hahn–Banach there is a functional of norm one attaining the norm `‖1‖ = 1` at `1`
  obtain ⟨g, hg, hg1⟩ := exists_dual_vector ℂ (1 : A) (by simp)
  refine ⟨StrongDual.toWeakDual g, mem_stateSpace_iff_norm_eq_one_and_map_one.2 ⟨hg, ?_⟩⟩
  simpa using hg1

/-- **Krein–Milman for states.** For unital `A`, the state space is the weak-* closed convex hull
of its extreme points, the pure states. -/
theorem closure_convexHull_extremePoints_stateSpace :
    closure (convexHull ℝ (extremePoints ℝ (stateSpace A))) = stateSpace A :=
  closure_convexHull_extremePoints isCompact_stateSpace convex_stateSpace

/-- **Existence of pure states.** A nonzero unital C⋆-algebra has an extreme state. -/
theorem extremePoints_stateSpace_nonempty [Nontrivial A] :
    (extremePoints ℝ (stateSpace A)).Nonempty :=
  isCompact_stateSpace.extremePoints_nonempty stateSpace_nonempty

/-- The only state of `ℂ` is the identity functional. -/
theorem stateSpace_complex :
    stateSpace ℂ = {StrongDual.toWeakDual (ContinuousLinearMap.id ℂ ℂ)} := by
  ext φ
  rw [mem_stateSpace_iff_map_one, mem_singleton_iff]
  refine ⟨fun ⟨_, h1⟩ => DFunLike.ext _ _ fun z => ?_, ?_⟩
  · simpa [h1] using (toStrongDual φ).map_smul z 1
  · rintro rfl
    exact ⟨fun a ha => by simpa using ha, by simp⟩

variable {B F : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **Pullback of states along a unital star homomorphism.** Composing a state of `B` with a
unital star homomorphism `A → B` gives a state of `A`. -/
theorem mapsTo_pullbackFunctional_stateSpace (f : F) :
    MapsTo (PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional
      (stateSpace B) (stateSpace A) := by
  intro φ hφ
  refine mem_stateSpace_iff_map_one.2 ⟨fun a ha => ?_, ?_⟩
  · simpa using map_nonneg_of_mem_stateSpace hφ (map_nonneg f ha)
  · simpa using map_one_of_mem_stateSpace hφ

end Unital

end TauCeti
