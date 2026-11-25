/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.BilinearForm.Isometry
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Isometric endomorphisms of a bilinear form

This file defines the predicate that an endomorphism preserves a bilinear form and provides its
elementary API, including the bridge to Mathlib's bundled isometric maps. It also records that
scaling two forms by the same regular scalar preserves whether they are isometric
(`LinearMap.BilinForm.equivalent_smul_iff`), and gives the underlying-equivalence and evaluation
lemmas `LinearMap.BilinForm.IsometryEquiv.toLinearEquiv_refl`,
`LinearMap.BilinForm.IsometryEquiv.toLinearEquiv_symm`,
`LinearMap.BilinForm.IsometryEquiv.coe_symm_toLinearEquiv`,
`LinearMap.BilinForm.IsometryEquiv.toLinearEquiv_trans`,
`LinearMap.BilinForm.IsometryEquiv.refl_apply`,
`LinearMap.BilinForm.IsometryEquiv.trans_apply`,
`LinearMap.BilinForm.IsometryEquiv.symm_apply_apply` and
`LinearMap.BilinForm.IsometryEquiv.apply_symm_apply` for Mathlib's isometric equivalences, which
map the kernel of one form onto the kernel of the other
(`LinearMap.BilinForm.IsometryEquiv.map_ker`).
Isometric bilinear forms have isometric associated quadratic maps
(`LinearMap.BilinForm.Equivalent.toQuadraticMap`); for symmetric forms the converse holds when `2`
is a non-zero-divisor (`LinearMap.BilinForm.IsSymm.equivalent_iff_toQuadraticMap_equivalent`).
The isometry group and the determinant, base-change, and orthogonal-complement API are developed
in `TauCeti.LinearAlgebra.BilinearForm.Isometry`.
-/

public section

namespace TauCeti

open LinearMap (BilinForm)

namespace BilinForm

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- An endomorphism `f` of `M` is an *isometry* of the bilinear form `B` when it preserves `B`,
that is, when `B (f x) (f y) = B x y` for all `x` and `y`.

Isometric endomorphisms form a monoid, not a group: for the zero form on `ℤ ^ 2` every endomorphism
is one. For a finite free `ℤ`-module `V` and a left-separating integral form `Q` an isometric
endomorphism is automatically invertible (`TauCeti.BilinForm.IsIsometry.toIsometryGroup`), and the
resulting automorphisms are the arithmetic group `Aut(V, Q)`; see
`LinearMap.isometryGroup`. -/
def IsIsometry (B : BilinForm R M) (f : M →ₗ[R] M) : Prop :=
  ∀ x y, B (f x) (f y) = B x y

variable {B : BilinForm R M} {f g : M →ₗ[R] M}

/-- An endomorphism is an isometry of `B` exactly when it preserves `B` pointwise. -/
theorem isIsometry_iff : IsIsometry B f ↔ ∀ x y, B (f x) (f y) = B x y := (Iff.rfl)

/-- An endomorphism is an isometry of `B` exactly when precomposing `B` with it on both sides
returns `B`. -/
theorem isIsometry_iff_comp : IsIsometry B f ↔ B.comp f f = B := by
  simp [LinearMap.BilinForm.ext_iff, isIsometry_iff]

/-- The underlying map of one of Mathlib's isometric maps `B →bᵢ B` is an isometry. -/
theorem isIsometry_toLinearMap (φ : B →bᵢ B) : IsIsometry B φ.toLinearMap := φ.map_app

namespace IsIsometry

/-- An isometry takes the same value under `B` after applying the endomorphism to both inputs. -/
@[grind =]
protected theorem apply (hf : IsIsometry B f) (x y : M) : B (f x) (f y) = B x y :=
  isIsometry_iff.mp hf x y

/-- An isometry, bundled as one of Mathlib's isometric maps `B →bᵢ B`. -/
def toIsometry (hf : IsIsometry B f) : B →bᵢ B := ⟨f, hf⟩

@[simp]
theorem toIsometry_apply (hf : IsIsometry B f) (x : M) : hf.toIsometry x = f x := (rfl)

@[simp]
theorem toIsometry_toLinearMap (hf : IsIsometry B f) : hf.toIsometry.toLinearMap = f := (rfl)

protected theorem id : IsIsometry B LinearMap.id := fun _ _ => rfl

protected theorem comp (hf : IsIsometry B f) (hg : IsIsometry B g) : IsIsometry B (f ∘ₗ g) :=
  fun x y => (hf (g x) (g y)).trans (hg x y)

end IsIsometry

end CommSemiring

section AddCommGroup

variable {R M : Type*} [CommSemiring R] [AddCommGroup M] [Module R M]
  {B : BilinForm R M} {f : M →ₗ[R] M}

/-- **Unipotent isometries of anisotropic forms are trivial.** If `f` preserves a bilinear form
`B` with `B v v ≠ 0` for every `v ≠ 0`, such as a positive definite real form, and `f - 1` is
nilpotent, then `f = 1`. A nontrivial transvection such as the shear `(q, p) ↦ (q + p, p)`
therefore preserves no inner product. -/
theorem IsIsometry.eq_one_of_isNilpotent_sub_one (hf : IsIsometry B f)
    (hB : B.toQuadraticMap.Anisotropic) (hN : IsNilpotent (f - 1)) : f = 1 := by
  -- A vector `w = f u - u` fixed by `f` vanishes: `B w w = B (f u) w + B (-u) w`, and
  -- `B (f u) w = B (f u) (f w) = B u w`.
  have key (u : M) (hfw : f (f u - u) = f u - u) : f u - u = 0 := by
    refine hB _ ?_
    have hw := hf.apply u (f u - u)
    rw [hfw] at hw
    rw [LinearMap.BilinMap.toQuadraticMap_apply]
    calc B (f u - u) (f u - u) = B (f u + -u) (f u - u) := by rw [sub_eq_add_neg]
      _ = B (u + -u) (f u - u) := by rw [LinearMap.map_add₂, hw, ← LinearMap.map_add₂]
      _ = 0 := by rw [add_neg_cancel, LinearMap.map_zero₂]
  -- Hence `(f - 1) ^ (n + 1) v = 0` forces `(f - 1) v = 0`, by induction on `n`: the induction
  -- hypothesis applied to `(f - 1) v` says that `f v - v` is fixed by `f`.
  have descend (n : ℕ) (v : M) (hv : ((f - 1) ^ (n + 1)) v = 0) : (f - 1) v = 0 := by
    induction n generalizing v with
    | zero => rwa [pow_one] at hv
    | succ n ih =>
      have hfw := ih _ (by rwa [pow_succ, mul_apply_eq_comp] at hv)
      simp only [LinearMap.sub_apply, one_apply_eq_self] at hfw ⊢
      exact key v (sub_eq_zero.mp hfw)
  obtain ⟨n, hn⟩ := hN
  rw [← sub_eq_zero]
  exact LinearMap.ext fun v ↦ descend n v (by rw [pow_succ, hn, zero_mul, LinearMap.zero_apply])

end AddCommGroup

end BilinForm

end TauCeti

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {R M M' : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M']
  [Module R M'] {C : BilinForm R M} {C' : BilinForm R M'} {a : R}

/-- Scaling two bilinear forms by the same regular scalar `a` neither creates nor destroys an
isometry between them. In particular the constituents `a • C` and `a • C'` of two Jordan splittings
are isometric exactly when their unimodular rescalings `C` and `C'` are. -/
@[simp] theorem equivalent_smul_iff (ha : IsRegular a) :
    (a • C).Equivalent (a • C') ↔ C.Equivalent C' :=
  ⟨fun ⟨e⟩ ↦ ⟨⟨e.toLinearEquiv, fun x y ↦ ha.left (by simpa using e.map_app y x)⟩⟩,
    fun ⟨e⟩ ↦ ⟨⟨e.toLinearEquiv, fun x y ↦ by simp⟩⟩⟩

namespace IsometryEquiv

variable {R M₁ M₂ M₃ : Type*} [CommSemiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
  [AddCommMonoid M₃] [Module R M₁] [Module R M₂] [Module R M₃] {B₁ : BilinForm R M₁}
  {B₂ : BilinForm R M₂} {B₃ : BilinForm R M₃}

/-- The underlying linear equivalence of the identity isometric equivalence is the identity linear
equivalence. -/
@[simp]
theorem toLinearEquiv_refl (B : BilinForm R M₁) :
    (IsometryEquiv.refl B).toLinearEquiv = LinearEquiv.refl R M₁ :=
  (rfl)

/-- The underlying linear equivalence of the inverse isometric equivalence is the inverse of the
underlying linear equivalence. -/
@[simp]
theorem toLinearEquiv_symm (f : B₁.IsometryEquiv B₂) :
    f.symm.toLinearEquiv = f.toLinearEquiv.symm :=
  (rfl)

/-- Coercing the inverse of the underlying linear equivalence agrees with coercing the inverse
isometric equivalence. -/
@[simp]
theorem coe_symm_toLinearEquiv (f : B₁.IsometryEquiv B₂) :
    ⇑f.toLinearEquiv.symm = f.symm :=
  (rfl)

/-- The underlying linear equivalence of a composite of isometric equivalences is the composite of
their underlying linear equivalences. -/
@[simp]
theorem toLinearEquiv_trans (f : B₁.IsometryEquiv B₂) (g : B₂.IsometryEquiv B₃) :
    (f.trans g).toLinearEquiv = f.toLinearEquiv.trans g.toLinearEquiv :=
  (rfl)

/-- The identity isometric equivalence fixes every vector. -/
@[simp]
theorem refl_apply (B : BilinForm R M₁) (x : M₁) : IsometryEquiv.refl B x = x :=
  (rfl)

/-- A composite of isometric equivalences applies the first and then the second. -/
@[simp]
theorem trans_apply (f : B₁.IsometryEquiv B₂) (g : B₂.IsometryEquiv B₃) (x : M₁) :
    f.trans g x = g (f x) :=
  (rfl)

/-- The inverse of an isometric equivalence undoes it. -/
@[simp]
theorem symm_apply_apply (f : B₁.IsometryEquiv B₂) (x : M₁) : f.symm (f x) = x :=
  f.toLinearEquiv.symm_apply_apply x

/-- An isometric equivalence undoes its inverse. -/
@[simp]
theorem apply_symm_apply (f : B₁.IsometryEquiv B₂) (x : M₂) : f (f.symm x) = x :=
  f.toLinearEquiv.apply_symm_apply x

/-- An isometric equivalence maps the kernel of one bilinear form onto the kernel of the other. -/
theorem map_ker (f : B₁.IsometryEquiv B₂) :
    (LinearMap.ker B₁).map (f : M₁ ≃ₗ[R] M₂).toLinearMap = LinearMap.ker B₂ := by
  ext y
  obtain ⟨x, rfl⟩ := (f : M₁ ≃ₗ[R] M₂).surjective y
  simp only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, LinearMap.mem_ker,
    LinearMap.ext_iff, LinearMap.zero_apply]
  -- Every vector of `M₂` is `f z`, and `B₂ (f x) (f z) = B₁ x z`.
  rw [← (f : M₁ ≃ₗ[R] M₂).toEquiv.forall_congr_right]
  simp

end IsometryEquiv

/-- Isometric bilinear forms have isometric associated quadratic maps `x ↦ B x x`. -/
theorem Equivalent.toQuadraticMap {R M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁]
    [AddCommMonoid M₂] [Module R M₁] [Module R M₂] {B₁ : BilinForm R M₁} {B₂ : BilinForm R M₂}
    (h : B₁.Equivalent B₂) : B₁.toQuadraticMap.Equivalent B₂.toQuadraticMap :=
  h.map fun f ↦ { f.toLinearEquiv with map_app' := fun x ↦ by simp }

/-- When `2` is a non-zero-divisor, symmetric bilinear forms are equivalent exactly when their
associated quadratic maps are equivalent. The underlying modules need not be finite or free. Some
hypothesis on `2` is needed: over `ZMod 2`, the identity matrix and the all-ones matrix on
`Fin 2 → ZMod 2` define symmetric forms with the same quadratic map `x 0 + x 1`, and only the
first is nondegenerate. The scalars need only form a commutative semiring, provided `M` is an
additive group, so that every value of `B` has an additive inverse. -/
theorem IsSymm.equivalent_iff_toQuadraticMap_equivalent
    {R M N : Type*} [CommSemiring R] [AddCommGroup M] [Module R M] [AddCommMonoid N] [Module R N]
    {B : BilinForm R M} {C : BilinForm R N} (hB : B.IsSymm) (hC : C.IsSymm)
    (h2 : (2 : R) ∈ nonZeroDivisors R) :
    B.Equivalent C ↔ B.toQuadraticMap.Equivalent C.toQuadraticMap := by
  refine ⟨Equivalent.toQuadraticMap, ?_⟩
  rintro ⟨f⟩
  refine ⟨{ toLinearEquiv := f.toLinearEquiv
            map_app' := fun x y ↦ ?_ }⟩
  -- `M` is an additive group, so `B (-z) w` is an additive inverse of `B z w` in `R`.
  have hneg (z w : M) : B z w + B (-z) w = 0 := by
    rw [← LinearMap.map_add₂, add_neg_cancel, LinearMap.map_zero₂]
  -- Expanding both quadratic maps at `x + y` recovers `2 * C (f x) (f y)` and `2 * B x y`.
  have h : B x x + B y y + 2 * C (f x) (f y) = B x x + B y y + 2 * B x y := by
    have hf (z : M) : C (f z) (f z) = B z z := f.map_app z
    have h := hf (x + y)
    simp only [map_add, LinearMap.add_apply, hB.eq y x, hC.eq (f y) (f x)] at h
    rw [hf x, hf y] at h
    rw [two_mul, two_mul]
    convert h using 1 <;> abel
  -- Adding the inverses of `B x x`, `B y y` and `2 * B x y` cancels everything but
  -- `2 * (C (f x) (f y) + B (-x) y)`, which therefore vanishes; now cancel `2`.
  have hd : 2 * (C (f x) (f y) + B (-x) y) = 0 := by
    calc 2 * (C (f x) (f y) + B (-x) y)
        = 2 * (C (f x) (f y) + B (-x) y) + ((B x x + B (-x) x) + (B y y + B (-y) y)) := by
          simp only [hneg, add_zero]
      _ = (B x x + B y y + 2 * C (f x) (f y)) + (B (-x) x + B (-y) y + 2 * B (-x) y) := by ring
      _ = (B x x + B (-x) x) + (B y y + B (-y) y) + 2 * (B x y + B (-x) y) := by rw [h]; ring
      _ = 0 := by simp only [hneg, add_zero, mul_zero]
  calc C (f x) (f y) = C (f x) (f y) + (B (-x) y + B x y) := by
        rw [add_comm (B (-x) y), hneg, add_zero]
    _ = B x y := by rw [← add_assoc, (mul_left_mem_nonZeroDivisors_eq_zero_iff h2).mp hd, zero_add]

end LinearMap.BilinForm
