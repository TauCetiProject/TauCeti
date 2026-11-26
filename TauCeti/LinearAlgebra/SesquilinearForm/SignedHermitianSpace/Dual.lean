/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Signed hermitian spaces over a ring with involution

Let `K` be a commutative ring with an involution `star`, and let `ε = ±1`. A signed hermitian
space `TauCeti.SignedHermitianSpace K V (starRingEnd K) ε` is a module `V` with a nondegenerate
`ε`-hermitian form, conjugate-linear in its first argument and linear in its second, with
`h y x = ε • star (h x y)`. For `ε = 1` these are the hermitian forms, for `ε = -1` the
skew-hermitian ones; when the involution is trivial they are the symmetric and the
skew-symmetric bilinear forms. These are the spaces whose isometry groups are the unitary,
symplectic and orthogonal groups over local fields, as in Kurinczuk–Skodlerack–Stevens.

This file adds to the carrier and adjoint of `TauCeti/LinearAlgebra/SesquilinearForm/
SignedHermitianSpace/Basic.lean` the rank-one spaces, the induced isomorphism onto the dual, and
the adjoint as an equivalence.

## Main definitions

* `TauCeti.SignedHermitianSpace.line a`: the rank-one space `K` with form `star x * a * y`, for
  a non-zero-divisor `a` with `star a = ε • a`.
* `TauCeti.SignedHermitianSpace.toDual`: over a field, for finite-dimensional `V`, the
  conjugate-linear isomorphism `V ≃ Dual K V` induced by the form.
* `TauCeti.SignedHermitianSpace.adjointEquiv`: the adjoint `TauCeti.signedHermitianAdjoint`,
  bundled as a `σ`-semilinear involutive equivalence of `Module.End K V` with itself.

Finite dimension is essential for the adjoint: on the direct sum of countably many rational
lines with the dot pairing, the endomorphism sending every basis vector to the first one has no
adjoint, as the adjoint would send the first basis vector to the vector with every coordinate one.

## Implementation notes

`toDual` adapts Mathlib's `LinearMap.BilinForm.toDual` (in
`Mathlib/LinearAlgebra/BilinearForm/Properties.lean`) to a form that is conjugate-linear in its
first argument.

## References

* R. Kurinczuk, D. Skodlerack and S. Stevens, *Endo-parameters for p-adic classical groups*,
  Invent. Math. 223 (2021), §3.3.
-/

public section

open Module

namespace TauCeti

namespace SignedHermitianSpace

section CommRing

variable {K V : Type*} [CommRing K] [StarRing K] [AddCommGroup V] [Module K V] {ε : ℤˣ}
  (h : SignedHermitianSpace K V (starRingEnd K) ε)

/-- Conjugating the value of the form exchanges its arguments, up to the sign `ε`. -/
@[simp]
theorem star_form (x y : V) : star (h.form x y) = ε • h.form y x := by
  rw [h.form_swap x y, smul_smul, Int.units_mul_self, one_smul, starRingEnd_apply]

/-- The rank-one signed hermitian space `⟨a⟩`: the ring `K` with the form
`form x y = star x * a * y`, for a non-zero-divisor `a` with `star a = ε • a`. Over a field this
is the line `⟨a⟩` for any nonzero `a`. -/
def line (a : K) (ha : star a = ε • a) (ha₀ : a ∈ nonZeroDivisors K) :
    SignedHermitianSpace K K (starRingEnd K) ε where
  form := LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => star x * a * y)
    (fun _ _ _ => by simp [add_mul])
    (fun _ _ _ => by simp only [smul_eq_mul, star_mul', starRingEnd_apply]; ring)
    (fun _ _ _ => by simp [mul_add])
    (fun _ _ _ => by simp only [smul_eq_mul, RingHom.id_apply]; ring)
  form_swap x y := by
    have hε : ((ε : ℤ) : K) ^ 2 = 1 := by rw [← Int.cast_pow, Int.isUnit_sq ε.isUnit, Int.cast_one]
    simp only [LinearMap.mk₂'ₛₗ_apply, starRingEnd_apply, star_mul', star_star, ha,
      Units.smul_def, zsmul_eq_mul]
    linear_combination (-(star y * a * x)) * hε
  separatingLeft x hx := by
    have := hx 1
    rw [LinearMap.mk₂'ₛₗ_apply, mul_one, mul_right_mem_nonZeroDivisors_eq_zero_iff ha₀,
      star_eq_zero] at this
    exact this

@[simp]
theorem line_form_apply (a : K) (ha : star a = ε • a) (ha₀ : a ∈ nonZeroDivisors K) (x y : K) :
    (line a ha ha₀).form x y = star x * a * y :=
  (rfl)

end CommRing

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* K} [RingHomSurjective σ]
  {ε : ℤˣ} (h : SignedHermitianSpace K V σ ε) [FiniteDimensional K V]

/-- Over a field and in finite dimension, `v ↦ form v ·` is bijective onto the dual, for any
surjective `σ`. -/
theorem form_bijective : Function.Bijective h.form := by
  have hinj : Function.Injective h.form :=
    LinearMap.ker_eq_bot.1 (LinearMap.separatingLeft_iff_ker_eq_bot.1 h.separatingLeft)
  refine ⟨hinj, LinearMap.range_eq_top.1 (Submodule.eq_top_of_finrank_eq ?_)⟩
  refine le_antisymm (Submodule.finrank_le _) ?_
  rw [Subspace.dual_finrank_eq]
  refine finrank_le_finrank_of_rank_le_rank ?_ (rank_lt_aleph0 _ _)
  simpa using lift_rank_le_of_surjective_injective σ
    h.form.rangeRestrict.toAddMonoidHom (RingHomSurjective.is_surjective (σ := σ))
    ((LinearMap.injective_rangeRestrict_iff _).2 hinj)
    (fun r m => h.form.rangeRestrict.map_smulₛₗ r m)

end Field

section StarField

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {ε : ℤˣ}
  (h : SignedHermitianSpace K V (starRingEnd K) ε) [FiniteDimensional K V]

/-- Over a field and in finite dimension, the form of a signed hermitian space induces a
conjugate-linear isomorphism `v ↦ form v ·` of `V` onto its dual. -/
noncomputable def toDual : V ≃ₗ⋆[K] Dual K V :=
  LinearEquiv.ofBijective h.form h.form_bijective

@[simp]
theorem toDual_apply (v w : V) : h.toDual v w = h.form v w := by
  rw [toDual, LinearEquiv.ofBijective_apply]

@[simp]
theorem form_toDual_symm_apply (f : Dual K V) (w : V) : h.form (h.toDual.symm f) w = f w := by
  rw [← toDual_apply, LinearEquiv.apply_symm_apply]

end StarField

section AdjointEquiv

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* K}
  [RingHomInvPair σ σ] {ε : ℤˣ} (h : SignedHermitianSpace K V σ ε) [FiniteDimensional K V]

/-- The adjoint `TauCeti.signedHermitianAdjoint` of a finite-dimensional signed hermitian space
over a field with an involution `σ`, bundled as a `σ`-semilinear equivalence of `Module.End K V`
with itself; it is its own inverse (`adjointEquiv_symm`). -/
noncomputable def adjointEquiv : Module.End K V ≃ₛₗ[σ] Module.End K V where
  __ := signedHermitianAdjoint h
  invFun := signedHermitianAdjoint h
  left_inv := signedHermitianAdjoint_involutive h
  right_inv := signedHermitianAdjoint_involutive h

@[simp]
theorem adjointEquiv_apply (T : Module.End K V) :
    h.adjointEquiv T = signedHermitianAdjoint h T :=
  (rfl)

@[simp]
theorem adjointEquiv_symm : h.adjointEquiv.symm = h.adjointEquiv :=
  (rfl)

end AdjointEquiv

end SignedHermitianSpace

end TauCeti
