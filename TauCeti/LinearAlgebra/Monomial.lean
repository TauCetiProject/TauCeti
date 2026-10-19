/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring

/-!
# Monomial linear equivalences of coordinate spaces

A monomial equivalence rescales coordinates by units and then relabels them along an
equivalence of index types. These transformations form the monomial subgroup of the group of
linear automorphisms. Coordinate permutations form a subgroup, equal to the monomial subgroup
when the coefficient semiring has only one unit. The construction allows infinite coordinate
sets; only the dot-product statements require finite coordinates.

The application, composition, inverse and support formulas provide the coordinate description
used to compare monomial linear automorphisms with monomial matrices. In particular these
subgroups make sense over small fields where the normalizer of the rational points of a
diagonal torus need not be the monomial subgroup.

The code-specific invariants and automorphism groups are developed in
`TauCeti.InformationTheory.Coding.Equivalence`.

## References

* W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes* (2003), §1.6.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter IV, §2, no. 2.
-/

public section

open Function Matrix

namespace TauCeti

variable {ι κ μ R : Type*}

section Monomial

variable [CommSemiring R]

/-- The monomial equivalence of coordinate spaces attached to a family of units `u : ι → Rˣ`
and a relabelling `e : ι ≃ κ` of coordinates: it rescales the `i`-th coordinate by `u i` and
places the result in the coordinate `e i`. -/
def monomialEquiv (u : ι → Rˣ) (e : ι ≃ κ) : (ι → R) ≃ₗ[R] (κ → R) :=
  (LinearEquiv.piCongrRight fun i ↦ LinearEquiv.smulOfUnit (M := R) (u i)).trans
    (LinearEquiv.funCongrLeft R R e.symm)

/-- At a target coordinate, a monomial equivalence multiplies the corresponding source
coordinate by its assigned unit. -/
@[simp]
theorem monomialEquiv_apply (u : ι → Rˣ) (e : ι ≃ κ) (x : ι → R) (j : κ) :
    monomialEquiv u e x j = u (e.symm j) * x (e.symm j) :=
  (rfl)

/-- The inverse monomial equivalence reads the relabelled coordinate and multiplies it by
the inverse of the source coordinate's unit. -/
theorem monomialEquiv_symm_apply (u : ι → Rˣ) (e : ι ≃ κ) (y : κ → R) (i : ι) :
    (monomialEquiv u e).symm y i = ↑(u i)⁻¹ * y (e i) :=
  (rfl)

/-- With trivial scalars a monomial equivalence is a bare relabelling of coordinates. -/
@[simp]
theorem monomialEquiv_one (e : ι ≃ κ) :
    monomialEquiv (1 : ι → Rˣ) e = LinearEquiv.funCongrLeft R R e.symm :=
  LinearEquiv.ext fun x ↦ funext fun j ↦ by simp

/-- Composing monomial equivalences multiplies their coordinate units after relabelling
and composes their coordinate equivalences. -/
@[simp]
theorem monomialEquiv_trans (u : ι → Rˣ) (e : ι ≃ κ) (v : κ → Rˣ) (f : κ ≃ μ) :
    (monomialEquiv u e).trans (monomialEquiv v f) =
      monomialEquiv (fun i ↦ u i * v (e i)) (e.trans f) := by
  refine LinearEquiv.ext fun x ↦ funext fun m ↦ ?_
  simp only [LinearEquiv.trans_apply, monomialEquiv_apply, Equiv.symm_trans_apply,
    Equiv.apply_symm_apply, Units.val_mul]
  ring

/-- Inverting a monomial equivalence inverts and relabels its coordinate units and inverts
its coordinate equivalence. -/
@[simp]
theorem monomialEquiv_symm (u : ι → Rˣ) (e : ι ≃ κ) :
    (monomialEquiv u e).symm = monomialEquiv (fun j ↦ (u (e.symm j))⁻¹) e.symm :=
  LinearEquiv.ext fun y ↦ funext fun i ↦ by simp [monomialEquiv_symm_apply]

/-- A monomial equivalence transports support along its coordinate equivalence. -/
@[simp]
theorem support_monomialEquiv (u : ι → Rˣ) (e : ι ≃ κ) (x : ι → R) :
    support (monomialEquiv u e x) = e '' support x := by
  rw [Equiv.image_eq_preimage_symm]
  ext j
  simp [Units.mul_right_eq_zero]

/-- A monomial equivalence is coordinatewise rescaling followed by reindexing. -/
theorem monomialEquiv_apply_eq_comp (u : ι → Rˣ) (e : ι ≃ κ) (x : ι → R) :
    (monomialEquiv u e x : κ → R) = (fun i ↦ (u i : R) * x i) ∘ e.symm :=
  funext fun j ↦ by simp

section DotProduct

variable [Fintype ι] [Fintype κ]

/-- A monomial coordinate change preserves the standard dot product exactly when every
coordinate multiplier has square one. -/
theorem dotProduct_monomialEquiv_iff (u : ι → Rˣ) (e : ι ≃ κ) :
    (∀ x y : ι → R, monomialEquiv u e x ⬝ᵥ monomialEquiv u e y = x ⬝ᵥ y) ↔
      ∀ i, (u i : R) ^ 2 = 1 := by
  classical
  have hdot (x y : ι → R) :
      monomialEquiv u e x ⬝ᵥ monomialEquiv u e y =
        (fun i ↦ (u i : R) * x i) ⬝ᵥ (fun i ↦ (u i : R) * y i) := by
    rw [monomialEquiv_apply_eq_comp, monomialEquiv_apply_eq_comp,
      comp_equiv_dotProduct_comp_equiv]
  constructor
  · intro h i
    have hi := h (Pi.single i 1) (Pi.single i 1)
    rw [hdot] at hi
    simpa [dotProduct, Pi.single_apply, pow_two] using hi
  · intro h x y
    rw [hdot]
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    calc
      (u i : R) * x i * ((u i : R) * y i) = (u i : R) ^ 2 * (x i * y i) := by ring
      _ = x i * y i := by rw [h i]; simp

end DotProduct

end Monomial

section Group

/-- The group of monomial transformations of the coordinate space `ι → R`, as a subgroup of its
group of linear automorphisms. -/
def monomialGroup (R ι : Type*) [CommSemiring R] : Subgroup ((ι → R) ≃ₗ[R] (ι → R)) where
  carrier := {f | ∃ (u : ι → Rˣ) (e : Equiv.Perm ι), monomialEquiv u e = f}
  one_mem' := ⟨1, Equiv.refl ι, by
    rw [monomialEquiv_one, Equiv.refl_symm, LinearEquiv.funCongrLeft_id,
      LinearEquiv.one_eq_refl]⟩
  mul_mem' := by
    rintro f g ⟨u, e, rfl⟩ ⟨v, d, rfl⟩
    exact ⟨fun i ↦ v i * u (d i), d.trans e, by
      rw [← monomialEquiv_trans, LinearEquiv.mul_eq_trans]⟩
  inv_mem' := by
    rintro f ⟨u, e, rfl⟩
    exact ⟨fun j ↦ (u (e.symm j))⁻¹, e.symm, (monomialEquiv_symm u e).symm⟩

variable [CommSemiring R]

/-- The monomial group consists exactly of the monomial transformations of `ι → R`. -/
@[simp]
theorem mem_monomialGroup {f : (ι → R) ≃ₗ[R] (ι → R)} :
    f ∈ monomialGroup R ι ↔ ∃ (u : ι → Rˣ) (e : Equiv.Perm ι), monomialEquiv u e = f :=
  Iff.rfl

/-- A monomial equivalence induced by coordinate units and a coordinate permutation belongs
to the monomial group. -/
theorem monomialEquiv_mem_monomialGroup (u : ι → Rˣ) (e : Equiv.Perm ι) :
    monomialEquiv u e ∈ monomialGroup R ι :=
  ⟨u, e, rfl⟩

end Group

section PermutationGroup

/-- The group of coordinate permutations of `ι → R`, as a subgroup of its group of linear
automorphisms. -/
def permutationGroup (R ι : Type*) [Semiring R] : Subgroup ((ι → R) ≃ₗ[R] (ι → R)) where
  carrier := {f | ∃ e : Equiv.Perm ι, LinearEquiv.funCongrLeft R R e.symm = f}
  one_mem' := ⟨Equiv.refl ι, by
    rw [Equiv.refl_symm, LinearEquiv.funCongrLeft_id, LinearEquiv.one_eq_refl]⟩
  mul_mem' := by
    rintro f g ⟨e, rfl⟩ ⟨d, rfl⟩
    exact ⟨d.trans e, by
      rw [Equiv.symm_trans, LinearEquiv.funCongrLeft_comp, LinearEquiv.mul_eq_trans]⟩
  inv_mem' := by
    rintro f ⟨e, rfl⟩
    exact ⟨e.symm, by rw [Equiv.symm_symm, ← LinearEquiv.funCongrLeft_symm]; rfl⟩

variable [Semiring R]

/-- The permutation group consists exactly of the coordinate relabellings of `ι → R`. -/
@[simp]
theorem mem_permutationGroup {f : (ι → R) ≃ₗ[R] (ι → R)} :
    f ∈ permutationGroup R ι ↔ ∃ e : Equiv.Perm ι, LinearEquiv.funCongrLeft R R e.symm = f :=
  Iff.rfl

/-- A coordinate relabelling belongs to the permutation group. -/
theorem funCongrLeft_mem_permutationGroup (e : Equiv.Perm ι) :
    LinearEquiv.funCongrLeft R R e.symm ∈ permutationGroup R ι :=
  ⟨e, rfl⟩

end PermutationGroup

section PermutationLeMonomial

variable [CommSemiring R]

/-- A coordinate permutation is the monomial transformation with all scalars equal to one. -/
theorem permutationGroup_le_monomialGroup : permutationGroup R ι ≤ monomialGroup R ι := by
  intro f hf
  obtain ⟨e, rfl⟩ := mem_permutationGroup.1 hf
  exact mem_monomialGroup.2 ⟨1, e, monomialEquiv_one e⟩

end PermutationLeMonomial

section TrivialUnits

variable [CommSemiring R] [Subsingleton Rˣ]

/-- When one is the only unit, a monomial transformation is its underlying coordinate
permutation. -/
@[simp]
theorem monomialEquiv_eq_funCongrLeft (u : ι → Rˣ) (e : ι ≃ κ) :
    monomialEquiv u e = LinearEquiv.funCongrLeft R R e.symm := by
  rw [Subsingleton.elim u 1, monomialEquiv_one]

/-- When one is the only unit, the monomial group is the coordinate-permutation group. -/
@[simp]
theorem monomialGroup_eq_permutationGroup : monomialGroup R ι = permutationGroup R ι := by
  refine le_antisymm (fun f hf ↦ ?_) permutationGroup_le_monomialGroup
  obtain ⟨u, e, rfl⟩ := mem_monomialGroup.mp hf
  exact mem_permutationGroup.mpr ⟨e, (monomialEquiv_eq_funCongrLeft u e).symm⟩

end TrivialUnits

end TauCeti
