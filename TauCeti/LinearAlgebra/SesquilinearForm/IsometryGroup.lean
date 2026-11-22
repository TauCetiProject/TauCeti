/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Isometry and similitude groups of a sesquilinear form

For a sesquilinear form `B : M →ₛₗ[I₁] M →ₛₗ[I₂] N`, this file defines

* the *isometry group* `B.isometryGroup`, the linear automorphisms `e` of `M` with
  `B (e x) (e y) = B x y`;
* the *similitude group* `B.similitudeGroup S`, the pairs `(e, λ)` of a linear automorphism `e`
  of `M` and a unit `λ` of a monoid `S` acting on `N`, with `B (e x) (e y) = λ • B x y`.

For a nondegenerate hermitian form `h` on a module `V` over a quadratic étale algebra `E/F`, with
`S = F`, these are the groups of rational points of the unitary group `U(V)` and of the unitary
similitude group `GU(V)`. For a symmetric or alternating bilinear form they are the orthogonal
and symplectic groups and their similitude groups.

The similitude group records the multiplier `λ` as data, rather than as a property of `e`: the
two projections are the homomorphisms `LinearMap.similitudeToLinearEquiv` and
`LinearMap.similitudeMultiplier`, and an element is determined by both together
(`LinearMap.similitudeGroup_ext`). The action alone determines the multiplier once `B` is
nonzero and `S` is a cancellative ring acting on `N` without torsion
(`LinearMap.similitudeToLinearEquiv_injective`), but not for the zero form, for instance on the
zero module: then every unit is a multiplier
(`LinearMap.similitudeMultiplier_surjective_of_eq_zero`). This is why the rank-zero unitary
similitude group `GU(0)` is `Sˣ` rather than trivial.

## Main definitions

* `LinearMap.isometryGroup`: the isometry group of a sesquilinear form.
* `LinearMap.similitudeGroup`: the similitude group, with multipliers in `Sˣ`.
* `LinearMap.similitudeToLinearEquiv`, `LinearMap.similitudeMultiplier`: the action and the
  multiplier of a similitude, as group homomorphisms.
* `LinearMap.isometryToSimilitude`: an isometry is a similitude of multiplier `1`.

## Main results

* `LinearMap.range_isometryToSimilitude`: the isometries are exactly the similitudes of
  multiplier `1`.
* `LinearMap.isometryGroup_neg`, `LinearMap.similitudeGroup_neg`: the forms `B` and `-B` have the
  same isometries and the same similitudes.
* `LinearMap.similitudeToLinearEquiv_injective`: for a nonzero form, with multipliers in a
  cancellative ring acting on `N` without torsion, a similitude is determined by its action.
* `LinearMap.similitudeMultiplier_surjective_of_eq_zero`: for the zero form every unit is a
  multiplier.

For a bilinear form `B : LinearMap.BilinForm R M`, the module
`TauCeti.LinearAlgebra.BilinearForm.Isometry` develops an API for `B.isometryGroup` specific to
bilinear forms.

## References

* E. Eischen, M. Harris, J.-S. Li and C. Skinner, *p-adic L-functions for unitary groups*,
  Forum Math. Pi 8 (2020), §4.1.1.
-/

public section

namespace LinearMap

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

section AddCommMonoid

variable [AddCommMonoid N] [Module R N] {I₁ I₂ : R →+* R} (B : M →ₛₗ[I₁] M →ₛₗ[I₂] N)

/-! ### The isometry group -/

/-- The isometry group of a sesquilinear form `B`: the linear automorphisms `e` of `M` with
`B (e x) (e y) = B x y`. For a hermitian form on a module `V` over a quadratic étale algebra this
is the unitary group `U(V)`. -/
def isometryGroup : Subgroup (M ≃ₗ[R] M) where
  carrier := {e | ∀ x y, B (e x) (e y) = B x y}
  one_mem' _ _ := rfl
  mul_mem' {e f} he hf x y := (he (f x) (f y)).trans (hf x y)
  inv_mem' {e} he x y := by
    simpa using (he (e.symm x) (e.symm y)).symm

variable {B} in
@[simp]
theorem mem_isometryGroup_iff {e : M ≃ₗ[R] M} :
    e ∈ B.isometryGroup ↔ ∀ x y, B (e x) (e y) = B x y := Iff.rfl

/-- An element of the isometry group preserves the form. -/
theorem isometryGroup_map_app (e : B.isometryGroup) (x y : M) :
    B ((e : M ≃ₗ[R] M) x) ((e : M ≃ₗ[R] M) y) = B x y :=
  e.property x y

/-! ### The similitude group -/

variable (S : Type*) [Monoid S] [DistribMulAction S N]

/-- The similitude group of a sesquilinear form `B` with multipliers in `Sˣ`: the pairs `(e, λ)`
of a linear automorphism `e` of `M` and a unit `λ` of `S` with `B (e x) (e y) = λ • B x y`. The
multiplier is recorded as part of the element. For a hermitian form on a module `V` over a
quadratic étale algebra `E/F`, with `S = F`, this is the unitary similitude group `GU(V)`. -/
def similitudeGroup : Subgroup ((M ≃ₗ[R] M) × Sˣ) where
  carrier := {p | ∀ x y, B (p.1 x) (p.1 y) = p.2 • B x y}
  one_mem' _ _ := (one_smul _ _).symm
  mul_mem' {p q} hp hq x y := by
    rw [Prod.snd_mul, mul_smul, ← hq]
    exact hp (q.1 x) (q.1 y)
  inv_mem' {p} hp x y := by
    rw [Prod.fst_inv, Prod.snd_inv, eq_inv_smul_iff, ← hp]
    simp

variable {B S} in
@[simp]
theorem mem_similitudeGroup_iff {p : (M ≃ₗ[R] M) × Sˣ} :
    p ∈ B.similitudeGroup S ↔ ∀ x y, B (p.1 x) (p.1 y) = p.2 • B x y := Iff.rfl

/-- The linear automorphism underlying a similitude, as a group homomorphism. -/
def similitudeToLinearEquiv : B.similitudeGroup S →* M ≃ₗ[R] M :=
  (MonoidHom.fst _ _).comp (B.similitudeGroup S).subtype

/-- The multiplier of a similitude, as a group homomorphism. -/
def similitudeMultiplier : B.similitudeGroup S →* Sˣ :=
  (MonoidHom.snd _ _).comp (B.similitudeGroup S).subtype

@[simp]
theorem similitudeToLinearEquiv_apply (g : B.similitudeGroup S) :
    B.similitudeToLinearEquiv S g = (g : (M ≃ₗ[R] M) × Sˣ).1 := (rfl)

@[simp]
theorem similitudeMultiplier_apply (g : B.similitudeGroup S) :
    B.similitudeMultiplier S g = (g : (M ≃ₗ[R] M) × Sˣ).2 := (rfl)

/-- A similitude scales the form by its multiplier. -/
theorem similitudeGroup_map_app (g : B.similitudeGroup S) (x y : M) :
    B ((g : (M ≃ₗ[R] M) × Sˣ).1 x) ((g : (M ≃ₗ[R] M) × Sˣ).1 y) =
      (g : (M ≃ₗ[R] M) × Sˣ).2 • B x y :=
  g.property x y

/-- A similitude is determined by its action together with its multiplier. -/
theorem similitudeGroup_ext {g h : B.similitudeGroup S}
    (hact : B.similitudeToLinearEquiv S g = B.similitudeToLinearEquiv S h)
    (hmul : B.similitudeMultiplier S g = B.similitudeMultiplier S h) : g = h :=
  Subtype.ext (Prod.ext hact hmul)

/-- An isometry is a similitude of multiplier `1`. -/
def isometryToSimilitude : B.isometryGroup →* B.similitudeGroup S where
  toFun e := ⟨((e : M ≃ₗ[R] M), 1), fun x y ↦ by simpa using e.property x y⟩
  map_one' := rfl
  map_mul' _ _ := Subtype.ext (Prod.ext rfl (mul_one 1).symm)

@[simp]
theorem coe_isometryToSimilitude (e : B.isometryGroup) :
    (B.isometryToSimilitude S e : (M ≃ₗ[R] M) × Sˣ) = ((e : M ≃ₗ[R] M), 1) := (rfl)

theorem isometryToSimilitude_injective : Function.Injective (B.isometryToSimilitude S) :=
  fun _ _ h ↦ Subtype.ext (by simpa using congrArg (B.similitudeToLinearEquiv S) h)

/-- The isometries are exactly the similitudes of multiplier `1`. -/
theorem range_isometryToSimilitude :
    (B.isometryToSimilitude S).range = (B.similitudeMultiplier S).ker := by
  ext g
  simp only [MonoidHom.mem_range, MonoidHom.mem_ker, similitudeMultiplier_apply]
  refine ⟨?_, fun hg ↦ ⟨⟨(g : (M ≃ₗ[R] M) × Sˣ).1, fun x y ↦ ?_⟩, Subtype.ext ?_⟩⟩
  · rintro ⟨e, rfl⟩
    rfl
  · simpa [hg] using B.similitudeGroup_map_app S g x y
  · simp [← hg]

/-- Every pair of an automorphism and a unit is a similitude of the zero form. -/
@[simp]
theorem similitudeGroup_zero : (0 : M →ₛₗ[I₁] M →ₛₗ[I₂] N).similitudeGroup S = ⊤ :=
  eq_top_iff.2 fun _ _ _ _ ↦ by simp

/-- For the zero form every unit is a multiplier. This applies to the zero module, where the
similitude group therefore does not reduce to the trivial group. -/
theorem similitudeMultiplier_surjective_of_eq_zero (hB : B = 0) :
    Function.Surjective (B.similitudeMultiplier S) := by
  subst hB
  exact fun c ↦ ⟨⟨(1, c), by simp⟩, rfl⟩

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup N] [Module R N] {I₁ I₂ : R →+* R} (B : M →ₛₗ[I₁] M →ₛₗ[I₂] N)

/-- The forms `B` and `-B` have the same isometries. -/
@[simp]
theorem isometryGroup_neg : (-B).isometryGroup = B.isometryGroup := by
  ext e
  simp

/-- The forms `B` and `-B` have the same similitudes. -/
@[simp]
theorem similitudeGroup_neg {S : Type*} [Monoid S] [DistribMulAction S N] :
    (-B).similitudeGroup S = B.similitudeGroup S := by
  ext p
  simp [smul_neg]

/-- For a nonzero form, with multipliers in a ring acting on `N` without torsion (for instance a
field `F` acting on an `F`-vector space), a similitude is determined by its action: the multiplier
can be read off from any pair of vectors on which `B` does not vanish. -/
theorem similitudeToLinearEquiv_injective (S : Type*) [Ring S] [IsCancelMulZero S] [Module S N]
    [Module.IsTorsionFree S N]
    (hB : B ≠ 0) : Function.Injective (B.similitudeToLinearEquiv S) := by
  obtain ⟨x, y, hxy⟩ : ∃ x y, B x y ≠ 0 := by
    by_contra! h
    exact hB (ext₂ h)
  refine fun g h hgh ↦ B.similitudeGroup_ext S hgh (Units.ext (smul_left_injective S hxy ?_))
  simp only [similitudeToLinearEquiv_apply] at hgh
  calc ((B.similitudeMultiplier S g : Sˣ) : S) • B x y
      = B ((g : (M ≃ₗ[R] M) × Sˣ).1 x) ((g : (M ≃ₗ[R] M) × Sˣ).1 y) :=
        (B.similitudeGroup_map_app S g x y).symm
    _ = B ((h : (M ≃ₗ[R] M) × Sˣ).1 x) ((h : (M ≃ₗ[R] M) × Sˣ).1 y) := by rw [hgh]
    _ = ((B.similitudeMultiplier S h : Sˣ) : S) • B x y := B.similitudeGroup_map_app S h x y

end AddCommGroup

end LinearMap
