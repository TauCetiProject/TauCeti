/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Dual.Index

/-!
# Symplectic lattices with an action of a ring with involution

Let `O` be a ring with an involution `b ↦ star b`. A *symplectic `O`-lattice* is a left
`O`-module `L` with an alternating `ℤ`-bilinear pairing `⟨·,·⟩ : L × L → ℤ`, nondegenerate after
extending scalars to `ℚ`, for which the action of `b` is adjoint to the action of `star b`:
`⟨b • x, y⟩ = ⟨x, star b • y⟩`. These are the lattices of PEL data, where `O` is an order in a
semisimple `ℚ`-algebra with positive involution and the pairing takes values in the Tate twist
`ℤ(1) = 2π√−1 ℤ`; choosing `√−1` identifies `ℤ(1)` with `ℤ`, and nothing here depends on that
choice.

The *dual lattice* is `L^# = {x ∈ L ⊗ ℚ : ⟨x, L⟩ ⊆ ℤ}`, computed with the rational extension of
the pairing (`LinearMap.BilinForm.dualLattice`, after swapping the factors to `ℚ ⊗ L`). It
contains the image of `L` and is an `O`-submodule of `L ⊗ ℚ` because the adjoint of `b` is
`star b`. When `L` is
finite free over `ℤ`, it contains `L` with finite index `[L^# : L]`, the *dual index*, which is
the absolute value of the Gram determinant of any `ℤ`-basis. The lattice is *self-dual at `p`*
when `L` and `L^#` agree after localizing at `p`; for `L` finite free over `ℤ` and `p` prime,
this happens exactly when `p` does not divide the dual index. These primes are the good primes of
the lattice for the PEL moduli problems.

The dual lattice, dual index and self-duality only use the pairing and its rational
nondegeneracy; their general theory is in `TauCeti.LinearAlgebra.BilinearForm.Dual.Index`, and
this file specializes it to symplectic lattices.

## Main definitions

* `TauCeti.SymplecticOLattice O L`: an alternating `ℤ`-valued pairing on the `O`-module `L`,
  nondegenerate over `ℚ`, with `b` and `star b` adjoint.
* `TauCeti.SymplecticOLattice.ofIsAlt`: over `O = ℤ`, every alternating pairing that is
  nondegenerate over `ℚ` is a symplectic lattice.
* `TauCeti.SymplecticOLattice.dual`: the dual lattice `L^#`, an `O`-submodule of `L ⊗[ℤ] ℚ`.
* `TauCeti.SymplecticOLattice.dualIndex`: the index `[L^# : L]`.
* `TauCeti.SymplecticOLattice.IsSelfDualAt`: self-duality at a prime.
* `TauCeti.SymplecticOLattice.zero`: the zero lattice.

## Main results

* `TauCeti.SymplecticOLattice.baseChange_isAdjointPair`: the adjointness of `b` and `star b`
  persists over `ℚ`.
* `TauCeti.SymplecticOLattice.baseChange_smul_mem_dualLattice`: the dual lattice of the pairing
  is stable under the rational extension of the action of `O`.
* `TauCeti.SymplecticOLattice.le_dual`: the image of `L` lies in `L^#`.
* `TauCeti.SymplecticOLattice.dualIndex_eq_relIndex`: the dual index is the index of the image
  of `L` in `L^#`.
* `TauCeti.SymplecticOLattice.dualIndex_zero`: the zero lattice has dual index one.
* `TauCeti.SymplecticOLattice.dualIndex_ne_zero`: for `L` finite free over `ℤ`, `L^#` contains
  `L` with finite index.
* `TauCeti.SymplecticOLattice.isSelfDualAt_iff_not_dvd_dualIndex`: for `L` finite free over `ℤ`,
  `L` is self-dual at a prime `p` exactly when `p ∤ [L^# : L]`.

## References

* K.-W. Lan, *Arithmetic compactifications of PEL-type Shimura varieties*, §1.1.4 and §1.2.1.
* R. Kottwitz, *Points on some Shimura varieties over finite fields*, §1 and §5.
-/

public section

open Module TensorProduct

namespace TauCeti

universe u v

variable (O : Type u) (L : Type v) [Ring O] [Star O] [AddCommGroup L] [Module O L]

/-- A **symplectic `O`-lattice** structure on a left `O`-module `L`, for a ring `O` with
involution: an alternating `ℤ`-bilinear pairing on `L`, nondegenerate after extending scalars to
`ℚ`, for which the action of each `b : O` is adjoint to the action of `star b`.

The pairing takes values in `ℤ`, which stands for the Tate twist `ℤ(1)` after choosing `√−1`.
In the PEL setting `L` is finite free over `ℤ`; the results needing this assume
`Module.Free ℤ L` and `Module.Finite ℤ L`. -/
@[ext]
structure SymplecticOLattice where
  /-- The integral pairing `⟨·,·⟩` on `L`. -/
  form : LinearMap.BilinForm ℤ L
  /-- The pairing is alternating: `⟨x, x⟩ = 0`. -/
  isAlt : form.IsAlt
  /-- The action of `b` is adjoint to the action of `star b`: `⟨b • x, y⟩ = ⟨x, star b • y⟩`. -/
  adjoint (b : O) : form.IsAdjointPair form (b • · : L → L) (star b • · : L → L)
  /-- The pairing is nondegenerate after extending scalars to `ℚ`. -/
  nondegenerate : (form.baseChange ℚ).Nondegenerate

namespace SymplecticOLattice

variable {O L} (Λ : SymplecticOLattice O L)

/-- Over `O = ℤ`, acting by scalars with the trivial involution, every alternating pairing that is
nondegenerate over `ℚ` is a symplectic lattice: the adjointness of `b` and `star b = b` is
bilinearity. -/
def ofIsAlt (B : LinearMap.BilinForm ℤ L) (hB : B.IsAlt) (hnd : (B.baseChange ℚ).Nondegenerate) :
    SymplecticOLattice ℤ L where
  form := B
  isAlt := hB
  adjoint b x y := by simp
  nondegenerate := hnd

@[simp]
theorem ofIsAlt_form (B : LinearMap.BilinForm ℤ L) (hB : B.IsAlt)
    (hnd : (B.baseChange ℚ).Nondegenerate) : (ofIsAlt B hB hnd).form = B :=
  (rfl)

/-- The defining adjointness of a symplectic lattice, as a rewriting rule. -/
theorem form_smul_left_eq_form_star_smul_right (b : O) (x y : L) :
    Λ.form (b • x) y = Λ.form x (star b • y) :=
  Λ.adjoint b x y

/-- The adjointness of `b` and `star b` persists over `ℚ`: the rational extensions of their
actions are adjoint for the rational extension of the pairing. -/
theorem baseChange_isAdjointPair (b : O) :
    (Λ.form.baseChange ℚ).IsAdjointPair (Λ.form.baseChange ℚ)
      ((DistribSMul.toLinearMap ℤ L b).baseChange ℚ)
      ((DistribSMul.toLinearMap ℤ L (star b)).baseChange ℚ) := by
  intro x y
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul q x =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul r y => simp [Λ.form_smul_left_eq_form_star_smul_right]

/-- The dual lattice of the pairing is stable under the rational extension of the action of `O`:
if `⟨x, L⟩ ⊆ ℤ` then `⟨b • x, y⟩ = ⟨x, star b • y⟩ ∈ ℤ` for every `y ∈ L`. -/
theorem baseChange_smul_mem_dualLattice (b : O) {x : ℚ ⊗[ℤ] L} (hx : x ∈ Λ.form.dualLattice) :
    (DistribSMul.toLinearMap ℤ L b).baseChange ℚ x ∈ Λ.form.dualLattice := by
  refine Λ.form.mem_dualLattice_iff.2 fun y ↦ ?_
  rw [Λ.baseChange_isAdjointPair b, LinearMap.baseChange_tmul]
  exact Λ.form.mem_dualLattice_iff.1 hx _

/-- The **dual lattice** `L^# = {x ∈ L ⊗ ℚ : ⟨x, L⟩ ⊆ ℤ}` of a symplectic lattice, as an
`O`-submodule of `L ⊗[ℤ] ℚ`: the vectors whose swap into `ℚ ⊗[ℤ] L` lies in the dual lattice
`LinearMap.BilinForm.dualLattice` of the pairing. It is `O`-stable because the adjoint of `b` is
`star b` (`baseChange_smul_mem_dualLattice`). -/
def dual : Submodule O (L ⊗[ℤ] ℚ) where
  carrier := {x | TensorProduct.comm ℤ L ℚ x ∈ Λ.form.dualLattice}
  add_mem' hx hy := by simpa using add_mem hx hy
  zero_mem' := by simp
  smul_mem' b x hx := by
    -- swapping the factors carries `b • ·` to the rational extension of the action of `b`
    have hb (z : L ⊗[ℤ] ℚ) : TensorProduct.comm ℤ L ℚ (b • z) =
        (DistribSMul.toLinearMap ℤ L b).baseChange ℚ (TensorProduct.comm ℤ L ℚ z) := by
      induction z using TensorProduct.inductionOn with
      | tmul y q => simp [TensorProduct.smul_tmul']
      | add x₁ x₂ h₁ h₂ => simp only [smul_add, map_add, h₁, h₂]
    change TensorProduct.comm ℤ L ℚ (b • x) ∈ Λ.form.dualLattice
    exact hb x ▸ Λ.baseChange_smul_mem_dualLattice b hx

/-- A vector of `L ⊗ ℚ` lies in `L^#` exactly when its swap into `ℚ ⊗ L` lies in the dual lattice
of the pairing. -/
theorem mem_dual_iff {x : L ⊗[ℤ] ℚ} :
    x ∈ Λ.dual ↔ TensorProduct.comm ℤ L ℚ x ∈ Λ.form.dualLattice :=
  Iff.rfl

/-- The image of `L` in `L ⊗ ℚ` lies in the dual lattice `L^#`, since the pairing is integral. -/
theorem le_dual :
    ((TensorProduct.mk ℤ L ℚ).flip 1 : L →+ L ⊗[ℤ] ℚ).range ≤ Λ.dual.toAddSubgroup := by
  rintro _ ⟨y, rfl⟩
  simp [mem_dual_iff]

/-- The **dual index** `[L^# : L]` of a symplectic lattice: the dual index
`LinearMap.BilinForm.dualIndex` of its pairing. It is nonzero when `L` is finite free over `ℤ`
(`dualIndex_ne_zero`). -/
noncomputable abbrev dualIndex : ℕ :=
  Λ.form.dualIndex

/-- The dual index is the index of the image of `L` in the `O`-stable dual lattice `L^#`. -/
theorem dualIndex_eq_relIndex :
    Λ.dualIndex =
      ((TensorProduct.mk ℤ L ℚ).flip 1 : L →+ L ⊗[ℤ] ℚ).range.relIndex Λ.dual.toAddSubgroup := by
  let e : L ⊗[ℤ] ℚ →+ ℚ ⊗[ℤ] L := (TensorProduct.comm ℤ L ℚ).toAddEquiv.toAddMonoidHom
  have hL : ((TensorProduct.mk ℤ L ℚ).flip 1 : L →+ L ⊗[ℤ] ℚ).range =
      (TensorProduct.mk ℤ ℚ L 1 : L →+ ℚ ⊗[ℤ] L).range.comap e := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp [e]⟩
    · rintro ⟨y, hy⟩
      refine ⟨y, (TensorProduct.comm ℤ L ℚ).injective ?_⟩
      simpa [e] using hy
  have hdual : Λ.dual.toAddSubgroup = Λ.form.dualLattice.toAddSubgroup.comap e := rfl
  rw [hL, hdual, AddSubgroup.relIndex_comap,
    AddSubgroup.map_comap_eq_self_of_surjective (f := e) (TensorProduct.comm ℤ L ℚ).surjective]
  exact Λ.form.dualIndex_def

/-- If `L` is finite free over `ℤ`, the dual lattice contains the image of `L` with finite
index. -/
theorem dualIndex_ne_zero [Module.Free ℤ L] [Module.Finite ℤ L] : Λ.dualIndex ≠ 0 :=
  Λ.form.dualIndex_ne_zero Λ.nondegenerate

/-- A symplectic lattice is **self-dual at `p`** when its pairing is
(`LinearMap.BilinForm.IsSelfDualAt`): `L` and its dual lattice `L^#` agree after localizing at
`p`. -/
abbrev IsSelfDualAt (p : ℕ) : Prop :=
  Λ.form.IsSelfDualAt p

/-- A symplectic lattice that is finite free over `ℤ` is self-dual at a prime `p` exactly when `p`
does not divide its dual index `[L^# : L]`. -/
theorem isSelfDualAt_iff_not_dvd_dualIndex [Module.Free ℤ L] [Module.Finite ℤ L] {p : ℕ}
    (hp : p.Prime) : Λ.IsSelfDualAt p ↔ ¬p ∣ Λ.dualIndex :=
  Λ.form.isSelfDualAt_iff_not_dvd_dualIndex Λ.dualIndex_ne_zero hp

variable (O L) in
/-- The **zero lattice**: the zero pairing on a subsingleton `O`-module, which is vacuously
alternating, adjoint and nondegenerate. -/
def zero [Subsingleton L] : SymplecticOLattice O L where
  form := 0
  isAlt _ := rfl
  adjoint _ _ _ := rfl
  nondegenerate := ⟨fun x _ ↦ Subsingleton.elim x 0, fun x _ ↦ Subsingleton.elim x 0⟩

/-- The zero lattice has dual index one. -/
theorem dualIndex_zero [Subsingleton L] : (zero O L).dualIndex = 1 :=
  LinearMap.BilinForm.dualIndex_eq_one_of_subsingleton _

end SymplecticOLattice

end TauCeti
