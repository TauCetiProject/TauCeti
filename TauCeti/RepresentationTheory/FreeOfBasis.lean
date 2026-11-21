/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RepresentationTheory.Equiv

/-!
# Representations with a freely permuted or monomial basis

Let `ρ` be a representation of a monoid `G` with a basis `b` whose index set is identified with
`Σ _ : ι, G`, so that every basis vector is `b ⟨i, h⟩` for a label `i` and a group element `h`. If
`ρ g` sends `b ⟨i, h⟩` to `b ⟨i, g * h⟩`, then `ρ` is the free representation on `ι`: the
generator `single i (single h 1)` of `Representation.free k G ι` corresponds to `b ⟨i, h⟩`
(`Representation.freeEquivOfBasis`).

When `G` is a group and `ρ g` only sends each `b ⟨i, h⟩` to a scalar multiple of `b ⟨i, g * h⟩`,
the group laws force those scalars to be units (`Representation.isUnit_of_apply_basis_eq_smul`).
Rescaling the basis vector at `⟨i, h⟩` to `ρ h (b ⟨i, 1⟩)` therefore produces a new basis freely
permuted by `G` without scalars, so `ρ` is still equivalent to the free representation on `ι`, with
the generator `single i (single h 1)` corresponding to `ρ h (b ⟨i, 1⟩)`
(`Representation.freeEquivOfMonomialBasis`).

## Main definitions

* `Representation.freeEquivOfBasis`: a basis freely permuted by the action identifies the
  representation with the free representation on the labels.
* `Representation.monomialRescaledBasis`: rescaling a monomial basis along group translates so
  that the group permutes the rescaled basis without scalars.
* `Representation.freeEquivOfMonomialBasis`: a basis on which a group acts monomially and freely on
  the index set identifies the representation with the free representation on the labels.

## Main results

* `Representation.isUnit_of_apply_basis_eq_smul`: a scalar by which a group element carries one
  basis vector to another, when its inverse carries the second back to a scalar multiple of the
  first, is a unit.
-/

public section

noncomputable section

open Finsupp

namespace Representation

section Basis

variable {k G V ι X : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) (b : Module.Basis X k V) (e : (Σ _ : ι, G) ≃ X)
  (hb : ∀ (g h : G) (i : ι), ρ g (b (e ⟨i, h⟩)) = b (e ⟨i, g * h⟩))

omit [Monoid G] in
/-- The basis equivalence underlying `Representation.freeEquivOfBasis` sends the generator
`single i (single h 1)` to the basis vector `b (e ⟨i, h⟩)`. -/
private lemma basisEquiv_single (i : ι) (h : G) :
    (Finsupp.basis fun _ ↦ MonoidAlgebra.basis G k).equiv b e
        (Finsupp.single i (MonoidAlgebra.single h 1)) = b (e ⟨i, h⟩) := by
  simpa only [Finsupp.coe_basis, MonoidAlgebra.basis_apply] using
    Module.Basis.equiv_apply (b := Finsupp.basis fun _ ↦ MonoidAlgebra.basis G k) (i := ⟨i, h⟩)
      b e

/-- **A representation with a freely permuted basis is free.** If the basis `b` of `ρ` is indexed,
through `e`, by `Σ _ : ι, G`, and `ρ g` sends `b (e ⟨i, h⟩)` to `b (e ⟨i, g * h⟩)`, then `ρ` is
equivalent to the free representation on `ι`, the generator `single i (single h 1)` corresponding
to `b (e ⟨i, h⟩)`. -/
def freeEquivOfBasis : (free k G ι).Equiv ρ :=
  .mk ((Finsupp.basis fun _ ↦ MonoidAlgebra.basis G k).equiv b e) fun g ↦
    (Finsupp.basis fun _ ↦ MonoidAlgebra.basis G k).ext fun x ↦ by
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Finsupp.coe_basis,
        MonoidAlgebra.basis_apply, free_single_single, basisEquiv_single, hb]

/-- The generator `single i (single h r)` of the free representation corresponds to
`r • b (e ⟨i, h⟩)`. -/
@[simp]
theorem freeEquivOfBasis_single (i : ι) (h : G) (r : k) :
    ρ.freeEquivOfBasis b e hb (Finsupp.single i (MonoidAlgebra.single h r)) = r • b (e ⟨i, h⟩) := by
  rw [freeEquivOfBasis, Equiv.mk_apply, ← basisEquiv_single b e i h, ← map_smul,
    Finsupp.smul_single, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]

/-- The basis vector `b (e ⟨i, h⟩)` corresponds to the generator `single i (single h 1)` of the
free representation. -/
@[simp]
theorem freeEquivOfBasis_symm_basis (i : ι) (h : G) :
    (ρ.freeEquivOfBasis b e hb).symm (b (e ⟨i, h⟩)) =
      Finsupp.single i (MonoidAlgebra.single h 1) := by
  rw [← one_smul k (b (e ⟨i, h⟩)), ← freeEquivOfBasis_single ρ b e hb]
  exact (ρ.freeEquivOfBasis b e hb).symm_apply_apply _

end Basis

section Monomial

/-- **Scalars of a monomial group action on a basis are units.** If `ρ g` sends `b x` to `c • b y`
and `ρ g⁻¹` sends `b y` to `d • b x`, then `c` is a unit. -/
theorem isUnit_of_apply_basis_eq_smul {k G V X : Type*} [Semiring k] [Group G]
    [AddCommMonoid V] [Module k V] (ρ : Representation k G V) (b : Module.Basis X k V)
    {g : G} {x y : X} {c d : k} (hxy : ρ g (b x) = c • b y) (hyx : ρ g⁻¹ (b y) = d • b x) :
    IsUnit c := by
  have hcd : c * d = 1 := by
    apply b.linearIndependent.smul_left_injective x
    have h := ρ.inv_self_apply g (b x)
    rw [hxy, map_smul, hyx, ← mul_smul] at h
    simpa [one_smul] using h
  have hdc : d * c = 1 := by
    apply b.linearIndependent.smul_left_injective y
    have h := ρ.self_inv_apply g (b y)
    rw [hyx, map_smul, hxy, ← mul_smul] at h
    simpa [one_smul] using h
  exact ⟨⟨c, d, hcd, hdc⟩, rfl⟩

section Rescale

variable {k G V ι X : Type*} [Semiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) (b : Module.Basis X k V) (e : (Σ _ : ι, G) ≃ X)
  (hb : ∀ (g h : G) (i : ι), ∃ c : k, ρ g (b (e ⟨i, h⟩)) = c • b (e ⟨i, g * h⟩))

include hb in
/-- The scalar relating `ρ g (b (e ⟨i, h⟩))` to `b (e ⟨i, g * h⟩)` is its coordinate at
`e ⟨i, g * h⟩`. -/
private lemma apply_basis_eq_repr_smul (g h : G) (i : ι) :
    ρ g (b (e ⟨i, h⟩)) = b.repr (ρ g (b (e ⟨i, h⟩))) (e ⟨i, g * h⟩) • b (e ⟨i, g * h⟩) := by
  obtain ⟨c, hc⟩ := hb g h i
  have hrepr : b.repr (ρ g (b (e ⟨i, h⟩))) (e ⟨i, g * h⟩) = c := by
    rw [hc, map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  rw [hrepr, hc]

/-- **Rescaling a monomial basis along group translates.** Given a basis `b` on which `G` acts
monomially along `e`, rescales `b` so that the basis vector at `e ⟨i, h⟩` is
`ρ h (b (e ⟨i, 1⟩))`. -/
def monomialRescaledBasis : Module.Basis X k V :=
  b.isUnitSMul (w := fun x ↦ b.repr (ρ (e.symm x).2 (b (e ⟨(e.symm x).1, 1⟩))) x) fun x ↦ by
    have h1 := apply_basis_eq_repr_smul ρ b e hb (e.symm x).2 1 (e.symm x).1
    have h2 := apply_basis_eq_repr_smul ρ b e hb (e.symm x).2⁻¹ (e.symm x).2 (e.symm x).1
    rw [mul_one, _root_.Equiv.apply_symm_apply] at h1
    rw [inv_mul_cancel, _root_.Equiv.apply_symm_apply] at h2
    exact ρ.isUnit_of_apply_basis_eq_smul b h1 h2

/-- The rescaled basis `Representation.monomialRescaledBasis` sends `e ⟨i, h⟩` to
`ρ h (b (e ⟨i, 1⟩))`. -/
@[simp]
theorem monomialRescaledBasis_apply (i : ι) (h : G) :
    ρ.monomialRescaledBasis b e hb (e ⟨i, h⟩) = ρ h (b (e ⟨i, 1⟩)) := by
  rw [monomialRescaledBasis, Module.Basis.isUnitSMul_apply, e.symm_apply_apply]
  have h1 := apply_basis_eq_repr_smul ρ b e hb h 1 i
  rw [mul_one] at h1
  exact h1.symm

end Rescale

variable {k G V ι X : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) (b : Module.Basis X k V) (e : (Σ _ : ι, G) ≃ X)
  (hb : ∀ (g h : G) (i : ι), ∃ c : k, ρ g (b (e ⟨i, h⟩)) = c • b (e ⟨i, g * h⟩))

/-- **A representation with a freely permuted monomial basis is free.** If the basis `b` of `ρ` is
indexed, through `e`, by `Σ _ : ι, G`, and `ρ g` sends each `b (e ⟨i, h⟩)` to a scalar multiple of
`b (e ⟨i, g * h⟩)`, then `ρ` is equivalent to the free representation on `ι`, the generator
`single i (single h 1)` corresponding to `ρ h (b (e ⟨i, 1⟩))`. -/
def freeEquivOfMonomialBasis : (free k G ι).Equiv ρ :=
  ρ.freeEquivOfBasis (monomialRescaledBasis ρ b e hb) e fun g h i ↦ by
    rw [monomialRescaledBasis_apply, monomialRescaledBasis_apply, ← mul_apply_eq_comp,
      ← map_mul]

/-- The single-supported element `single i (single h r)` of the free representation corresponds
to `r • ρ h (b (e ⟨i, 1⟩))`. -/
@[simp]
theorem freeEquivOfMonomialBasis_single (i : ι) (h : G) (r : k) :
    ρ.freeEquivOfMonomialBasis b e hb (Finsupp.single i (MonoidAlgebra.single h r)) =
      r • ρ h (b (e ⟨i, 1⟩)) := by
  rw [freeEquivOfMonomialBasis, freeEquivOfBasis_single, monomialRescaledBasis_apply]

/-- The translated representative `ρ h (b (e ⟨i, 1⟩))` corresponds to the generator
`single i (single h 1)` of the free representation. -/
@[simp]
theorem freeEquivOfMonomialBasis_symm_apply_basis (i : ι) (h : G) :
    (ρ.freeEquivOfMonomialBasis b e hb).symm (ρ h (b (e ⟨i, 1⟩))) =
      Finsupp.single i (MonoidAlgebra.single h 1) := by
  rw [← one_smul k (ρ h (b (e ⟨i, 1⟩))), ← freeEquivOfMonomialBasis_single ρ b e hb]
  exact (ρ.freeEquivOfMonomialBasis b e hb).symm_apply_apply _

/-- The basis vector `b (e ⟨i, 1⟩)` corresponds to the generator `single i (single 1 1)` of the
free representation. -/
@[simp]
theorem freeEquivOfMonomialBasis_symm_basis_one (i : ι) :
    (ρ.freeEquivOfMonomialBasis b e hb).symm (b (e ⟨i, 1⟩)) =
      Finsupp.single i (MonoidAlgebra.single 1 1) := by
  simpa only [map_one, one_apply_eq_self] using
    freeEquivOfMonomialBasis_symm_apply_basis ρ b e hb i 1

/-- The basis vector `b (e ⟨i, h⟩)` corresponds to `single i (single h c)`, where `c` is the
coordinate of `ρ h⁻¹ (b (e ⟨i, h⟩))` at `e ⟨i, 1⟩`. -/
theorem freeEquivOfMonomialBasis_symm_basis (i : ι) (h : G) :
    (ρ.freeEquivOfMonomialBasis b e hb).symm (b (e ⟨i, h⟩)) =
      Finsupp.single i (MonoidAlgebra.single h
        (b.repr (ρ h⁻¹ (b (e ⟨i, h⟩))) (e ⟨i, 1⟩))) := by
  rw [← (ρ.freeEquivOfMonomialBasis b e hb).symm_apply_apply
    (Finsupp.single i (MonoidAlgebra.single h (b.repr (ρ h⁻¹ (b (e ⟨i, h⟩))) (e ⟨i, 1⟩))))]
  congr 1
  rw [freeEquivOfMonomialBasis_single, ← map_smul]
  have hinv := apply_basis_eq_repr_smul ρ b e hb h⁻¹ h i
  rw [inv_mul_cancel] at hinv
  rw [← hinv, ρ.self_inv_apply]

end Monomial

end Representation
