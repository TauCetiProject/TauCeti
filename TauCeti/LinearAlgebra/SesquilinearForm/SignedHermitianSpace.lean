/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Signed hermitian spaces and their adjoints

Let `K` be a commutative ring with an involution `star`, and let `ε = ±1`. An `ε`-hermitian
form on a `K`-module `V` is a pairing `h : V × V → K`, conjugate-linear in its first argument
and linear in its second, with `h y x = ε • star (h x y)`. For `ε = 1` these are the hermitian
forms, for `ε = -1` the skew-hermitian ones; when the involution is trivial they are the
symmetric and the skew-symmetric bilinear forms. A *signed hermitian space* is a module with
a nondegenerate `ε`-hermitian form. These are the spaces whose isometry groups are the unitary,
symplectic and orthogonal groups over local fields, as in Kurinczuk–Skodlerack–Stevens.

Over a field `K` with involution and for finite-dimensional `V`, the map `v ↦ h v ·` is a
conjugate-linear isomorphism of `V` onto its dual. Hence every endomorphism `T` of `V` has a
unique *signed hermitian adjoint* `T*`, characterized by `h (T x) y = h x (T* y)`, and
`T ↦ T*` is a conjugate-linear involution that reverses composition.

## Main definitions

* `TauCeti.SignedHermitianSpace K V ε`: a nondegenerate `ε`-hermitian form on `V`, for a sign
  `ε : ℤˣ`.
* `TauCeti.SignedHermitianSpace.line a`: the rank-one space `K` with form `star x * a * y`, for
  a non-zero-divisor `a` with `star a = ε • a`.
* `TauCeti.SignedHermitianSpace.toDual`: over a field, for finite-dimensional `V`, the
  conjugate-linear isomorphism `V ≃ Dual K V` induced by the form.
* `TauCeti.SignedHermitianSpace.adjoint`: the signed hermitian adjoint, as a conjugate-linear
  equivalence of `Module.End K V` with itself.

## Main results

* `TauCeti.SignedHermitianSpace.eq_adjoint_iff`: `S` is the adjoint of `T` if and only if
  `h (T x) y = h x (S y)` for all `x`, `y`.
* `TauCeti.SignedHermitianSpace.adjoint_id`, `TauCeti.SignedHermitianSpace.adjoint_comp` and
  `TauCeti.SignedHermitianSpace.adjoint_adjoint`: the adjoint fixes the identity, reverses
  composition and is an involution.

Finite dimension is essential for the adjoint: on the direct sum of countably many rational
lines with the dot pairing, the endomorphism sending every basis vector to the first one has no
adjoint, as the adjoint would send the first basis vector to the vector with every coordinate one.

## References

* R. Kurinczuk, D. Skodlerack and S. Stevens, *Endo-parameters for p-adic classical groups*,
  Invent. Math. 223 (2021), §3.3.
-/

public section

open Module

namespace TauCeti

/-- A **signed hermitian space** with sign `ε = ±1` over a commutative ring `K` with involution:
a `K`-module `V` with a nondegenerate pairing `form`, conjugate-linear in its first argument and
linear in its second, satisfying `form y x = ε • star (form x y)`. For `ε = 1` the form is
hermitian, for `ε = -1` skew-hermitian. -/
@[ext]
structure SignedHermitianSpace (K V : Type*) [CommRing K] [StarRing K] [AddCommGroup V]
    [Module K V] (ε : ℤˣ) where
  /-- The pairing, conjugate-linear in its first argument and linear in its second. -/
  form : V →ₗ⋆[K] V →ₗ[K] K
  /-- Exchanging the arguments conjugates the value and multiplies it by the sign `ε`. -/
  form_swap (x y : V) : form y x = ε • star (form x y)
  /-- The pairing is nondegenerate: it separates points in each argument. -/
  nondegenerate : form.Nondegenerate

namespace SignedHermitianSpace

section CommRing

variable {K V : Type*} [CommRing K] [StarRing K] [AddCommGroup V] [Module K V] {ε : ℤˣ}
  (h : SignedHermitianSpace K V ε)

/-- Conjugating the value of the form exchanges its arguments, up to the sign `ε`. -/
@[simp]
theorem star_form (x y : V) : star (h.form x y) = ε • h.form y x := by
  rw [h.form_swap x y, smul_smul, Int.units_mul_self, one_smul]

/-- The form of a signed hermitian space is reflexive: `form x y = 0` iff `form y x = 0`. -/
theorem isRefl_form : h.form.IsRefl := fun x y hxy => by
  rw [h.form_swap, hxy, star_zero, smul_zero]

/-- The form of a hermitian space, the sign `ε = 1`, is symmetric in Mathlib's sesquilinear
sense: `star (form x y) = form y x`. -/
theorem isSymm_form (h : SignedHermitianSpace K V 1) : h.form.IsSymm :=
  ⟨fun x y => by rw [h.form_swap x y, one_smul, starRingEnd_apply]⟩

/-- The rank-one signed hermitian space `⟨a⟩`: the ring `K` with the form
`form x y = star x * a * y`, for a non-zero-divisor `a` with `star a = ε • a`. Over a field this
is the line `⟨a⟩` for any nonzero `a`. -/
def line (a : K) (ha : star a = ε • a) (ha₀ : a ∈ nonZeroDivisors K) :
    SignedHermitianSpace K K ε where
  form := LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => star x * a * y)
    (fun _ _ _ => by simp [add_mul])
    (fun _ _ _ => by simp only [smul_eq_mul, star_mul', starRingEnd_apply]; ring)
    (fun _ _ _ => by simp [mul_add])
    (fun _ _ _ => by simp only [smul_eq_mul, RingHom.id_apply]; ring)
  form_swap x y := by
    have hε : ((ε : ℤ) : K) ^ 2 = 1 := by
      rw [← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq, Units.val_one, Int.cast_one]
    simp only [LinearMap.mk₂'ₛₗ_apply, star_mul', star_star, ha, Units.smul_def, zsmul_eq_mul]
    linear_combination (-(star y * a * x)) * hε
  nondegenerate := by
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · have := hx 1
      rw [LinearMap.mk₂'ₛₗ_apply, mul_one, mul_right_mem_nonZeroDivisors_eq_zero_iff ha₀,
        star_eq_zero] at this
      exact this
    · have := hy 1
      rw [LinearMap.mk₂'ₛₗ_apply, star_one, one_mul,
        mul_left_mem_nonZeroDivisors_eq_zero_iff ha₀] at this
      exact this

@[simp]
theorem line_form_apply (a : K) (ha : star a = ε • a) (ha₀ : a ∈ nonZeroDivisors K) (x y : K) :
    (line a ha ha₀).form x y = star x * a * y :=
  (rfl)

end CommRing

section Field

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {ε : ℤˣ}
  (h : SignedHermitianSpace K V ε)

variable [FiniteDimensional K V]

/-- Over a field and in finite dimension, `v ↦ form v ·` is bijective onto the dual. -/
theorem bijective_form : Function.Bijective h.form := by
  have hinj : Function.Injective h.form :=
    LinearMap.ker_eq_bot.1 (LinearMap.separatingLeft_iff_ker_eq_bot.1 h.nondegenerate.1)
  refine ⟨hinj, LinearMap.range_eq_top.1 (Submodule.eq_top_of_finrank_eq ?_)⟩
  refine le_antisymm (Submodule.finrank_le _) ?_
  rw [Subspace.dual_finrank_eq]
  refine finrank_le_finrank_of_rank_le_rank ?_ (rank_lt_aleph0 _ _)
  simpa using lift_rank_le_of_surjective_injective (starRingEnd K)
    h.form.rangeRestrict.toAddMonoidHom (starRingEnd K).surjective
    ((LinearMap.injective_rangeRestrict_iff _).2 hinj)
    (fun r m => h.form.rangeRestrict.map_smulₛₗ r m)

/-- Over a field and in finite dimension, the form of a signed hermitian space induces a
conjugate-linear isomorphism `v ↦ form v ·` of `V` onto its dual. -/
noncomputable def toDual : V ≃ₗ⋆[K] Dual K V :=
  LinearEquiv.ofBijective h.form h.bijective_form

@[simp]
theorem toDual_apply (v w : V) : h.toDual v w = h.form v w :=
  (rfl)

@[simp]
theorem form_toDual_symm_apply (f : Dual K V) (w : V) : h.form (h.toDual.symm f) w = f w := by
  rw [← toDual_apply, LinearEquiv.apply_symm_apply]

/-- The adjoint before it is bundled: `toDual⁻¹ ∘ Tᵀ ∘ toDual`. -/
private noncomputable def adjointAux (T : Module.End K V) : Module.End K V :=
  h.toDual.symm.toLinearMap ∘ₛₗ T.dualMap ∘ₛₗ h.toDual.toLinearMap

private theorem form_adjointAux_left (T : Module.End K V) (x y : V) :
    h.form (h.adjointAux T x) y = h.form x (T y) := by
  simp [adjointAux]

private theorem form_adjointAux_right (T : Module.End K V) (x y : V) :
    h.form x (h.adjointAux T y) = h.form (T x) y := by
  rw [h.form_swap, form_adjointAux_left, ← h.form_swap]

private theorem eq_adjointAux_iff {S T : Module.End K V} :
    S = h.adjointAux T ↔ ∀ x y, h.form (T x) y = h.form x (S y) := by
  refine ⟨fun hS x y => by rw [hS, form_adjointAux_right], fun hS => ?_⟩
  ext y
  refine LinearMap.ker_eq_bot.1
    (LinearMap.separatingRight_iff_flip_ker_eq_bot.1 h.nondegenerate.2) (LinearMap.ext fun x => ?_)
  rw [LinearMap.flip_apply, LinearMap.flip_apply, ← hS, form_adjointAux_right]

private theorem adjointAux_adjointAux (T : Module.End K V) :
    h.adjointAux (h.adjointAux T) = T :=
  ((h.eq_adjointAux_iff).2 fun x y => by rw [form_adjointAux_left]).symm

/-- The **signed hermitian adjoint** `T ↦ T*` of a finite-dimensional signed hermitian space
over a field, characterized by `form (T x) y = form x (T* y)` (`eq_adjoint_iff`). It is a
conjugate-linear involution of `Module.End K V`. -/
noncomputable def adjoint : Module.End K V ≃ₗ⋆[K] Module.End K V where
  toFun := h.adjointAux
  invFun := h.adjointAux
  map_add' S T := ((h.eq_adjointAux_iff).2 fun x y => by
    simp [form_adjointAux_right]).symm
  map_smul' c T := ((h.eq_adjointAux_iff).2 fun x y => by
    simp [form_adjointAux_right]).symm
  left_inv := h.adjointAux_adjointAux
  right_inv := h.adjointAux_adjointAux

@[simp]
theorem adjoint_form_left (T : Module.End K V) (x y : V) :
    h.form (h.adjoint T x) y = h.form x (T y) :=
  h.form_adjointAux_left T x y

@[simp]
theorem adjoint_form_right (T : Module.End K V) (x y : V) :
    h.form x (h.adjoint T y) = h.form (T x) y :=
  h.form_adjointAux_right T x y

/-- The adjoint is characterized by `form (T x) y = form x (T* y)`; in particular it is the
unique endomorphism with this property. -/
theorem eq_adjoint_iff {S T : Module.End K V} :
    S = h.adjoint T ↔ ∀ x y, h.form (T x) y = h.form x (S y) :=
  h.eq_adjointAux_iff

@[simp]
theorem adjoint_adjoint (T : Module.End K V) : h.adjoint (h.adjoint T) = T :=
  h.adjointAux_adjointAux T

theorem adjoint_involutive : Function.Involutive h.adjoint :=
  h.adjoint_adjoint

@[simp]
theorem adjoint_symm : h.adjoint.symm = h.adjoint :=
  (rfl)

@[simp]
theorem adjoint_id : h.adjoint LinearMap.id = LinearMap.id :=
  ((h.eq_adjoint_iff).2 fun _ _ => rfl).symm

/-- The adjoint reverses composition: `(S ∘ T)* = T* ∘ S*`. -/
@[simp]
theorem adjoint_comp (S T : Module.End K V) :
    h.adjoint (S ∘ₗ T) = h.adjoint T ∘ₗ h.adjoint S :=
  ((h.eq_adjoint_iff).2 fun x y => by simp).symm

end Field

end SignedHermitianSpace

end TauCeti
