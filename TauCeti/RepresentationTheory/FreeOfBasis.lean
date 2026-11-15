/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RepresentationTheory.Equiv

/-!
# Representations with a freely permuted basis

Let `ρ` be a representation of a monoid `G` with a basis `b` whose index set is identified with
`Σ _ : ι, G`, so that every basis vector is `b ⟨i, h⟩` for a label `i` and a group element `h`. If
`ρ g` sends `b ⟨i, h⟩` to `b ⟨i, g * h⟩`, then `ρ` is the free representation on `ι`: the
generator `single i (single h 1)` of `Representation.free k G ι` corresponds to `b ⟨i, h⟩`.

## Main definitions

* `Representation.freeEquivOfBasis`: a basis freely permuted by the action identifies the
  representation with the free representation on the labels.
-/

public section

noncomputable section

open Finsupp

namespace Representation

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

end Representation
