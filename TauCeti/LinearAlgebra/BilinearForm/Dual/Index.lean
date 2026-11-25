/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import TauCeti.LinearAlgebra.BilinearForm.BaseChange
import TauCeti.LinearAlgebra.TensorProduct.ScalarExtension

/-!
# The dual lattice of an integral bilinear form and its index

Let `B` be a `ℤ`-valued bilinear form on an additive group `L`. Its *dual lattice* is
`L^# = {x ∈ ℚ ⊗ L : B(x, L) ⊆ ℤ}`, computed with the rational extension of `B`. It contains the
image of `L`, and the *dual index* `[L^# : L]` is the index of that image in `L^#`. When `L` is
finite free over `ℤ` and `B` is nondegenerate over `ℚ`, the dual index is finite: for a `ℤ`-basis
of `L` it is the absolute value of the Gram determinant. The form is *self-dual at `p`* when every
element of `L^#` has a multiple prime to `p` in the image of `L`; for `p` prime this says that `L`
and `L^#` agree after localizing at `p`, and when the dual index is finite it happens exactly when
`p` does not divide the dual index.

## Main definitions

* `LinearMap.BilinForm.dualLattice`: the dual lattice `L^#` inside `ℚ ⊗[ℤ] L`.
* `LinearMap.BilinForm.dualIndex`: the index `[L^# : L]`.
* `LinearMap.BilinForm.IsSelfDualAt`: self-duality at `p`.

## Main results

* `LinearMap.BilinForm.mem_dualLattice_iff`: `x ∈ L^#` exactly when `B(x, y) ∈ ℤ` for all
  `y ∈ L`.
* `LinearMap.BilinForm.le_dualLattice`: the image of `L` lies in `L^#`.
* `LinearMap.BilinForm.exists_tmul_eq_dualIndex_smul`: `[L^# : L] • L^#` lies in the image of
  `L`.
* `LinearMap.BilinForm.dualIndex_eq_natAbs_det`: if `B` is nondegenerate over `ℚ`, then
  `[L^# : L] = |det (B(b i, b j))|` for every `ℤ`-basis `b` of `L`.
* `LinearMap.BilinForm.dualIndex_ne_zero`: for `L` finite free over `ℤ` and `B` nondegenerate over
  `ℚ`, `L^#` contains `L` with finite index.
* `LinearMap.BilinForm.isSelfDualAt_iff_not_dvd_dualIndex`: if the dual index is finite, `B` is
  self-dual at a prime `p` exactly when `p ∤ [L^# : L]`.
-/

public section

open Module TensorProduct

namespace LinearMap.BilinForm

variable {L : Type*} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L)

/-- The **dual lattice** `L^# = {x ∈ ℚ ⊗ L : B(x, L) ⊆ ℤ}` of a `ℤ`-valued bilinear form, for the
rational extension of the form. -/
def dualLattice : Submodule ℤ (ℚ ⊗[ℤ] L) :=
  -- The image of `L` is the additive range of `y ↦ 1 ⊗ₜ y`, made a `ℤ`-submodule through
  -- `AddSubgroup.toIntSubmodule`, so that every `ℤ`-module structure on `ℚ ⊗[ℤ] L` here is the
  -- canonical one of an additive group. The `ℤ`-module structure of a tensor product over `ℤ`
  -- agrees with it only propositionally, and `LinearMap.range (TensorProduct.mk ℤ ℚ L 1)` uses it.
  (B.baseChange ℚ).dualSubmodule
    (AddSubgroup.toIntSubmodule (TensorProduct.mk ℤ ℚ L 1 : L →+ ℚ ⊗[ℤ] L).range)

/-- A rational vector lies in the dual lattice exactly when its pairing with every lattice vector
is an integer. -/
theorem mem_dualLattice_iff {x : ℚ ⊗[ℤ] L} :
    x ∈ B.dualLattice ↔ ∀ y : L, ∃ n : ℤ, B.baseChange ℚ x (1 ⊗ₜ y) = n := by
  rw [dualLattice, LinearMap.BilinForm.mem_dualSubmodule]
  refine ⟨fun h y ↦ ?_, fun h z hz ↦ ?_⟩
  · obtain ⟨n, hn⟩ := Submodule.mem_one.1 (h _ ⟨y, rfl⟩)
    exact ⟨n, by simpa using hn.symm⟩
  · obtain ⟨y, rfl⟩ := hz
    obtain ⟨n, hn⟩ := h y
    exact Submodule.mem_one.2 ⟨n, by simpa using hn.symm⟩

/-- The image of each lattice vector lies in the dual lattice, since the form is integral. -/
@[simp]
theorem tmul_mem_dualLattice (y : L) : (1 : ℚ) ⊗ₜ[ℤ] y ∈ B.dualLattice :=
  B.mem_dualLattice_iff.2 fun z ↦ ⟨B y z, by simp⟩

/-- The image of `L` in `ℚ ⊗ L` lies in the dual lattice `L^#`. -/
theorem le_dualLattice :
    (TensorProduct.mk ℤ ℚ L 1 : L →+ ℚ ⊗[ℤ] L).range ≤ B.dualLattice.toAddSubgroup := by
  rintro _ ⟨y, rfl⟩
  exact B.tmul_mem_dualLattice y

/-- The **dual index** `[L^# : L]` of a `ℤ`-valued bilinear form: the index of the image of `L` in
its dual lattice. It is nonzero when `L` is finite free over `ℤ` and the form is nondegenerate
over `ℚ` (`dualIndex_ne_zero`). -/
noncomputable def dualIndex : ℕ :=
  (TensorProduct.mk ℤ ℚ L 1 : L →+ ℚ ⊗[ℤ] L).range.relIndex B.dualLattice.toAddSubgroup

/-- The dual index is the relative index of the image of `L` in the dual lattice. -/
theorem dualIndex_def :
    B.dualIndex = (TensorProduct.mk ℤ ℚ L 1 : L →+ ℚ ⊗[ℤ] L).range.relIndex
      B.dualLattice.toAddSubgroup :=
  (rfl)

/-- Multiplication by the dual index carries the dual lattice into the image of `L`. -/
theorem exists_tmul_eq_dualIndex_smul {x : ℚ ⊗[ℤ] L} (hx : x ∈ B.dualLattice) :
    ∃ y : L, (1 : ℚ) ⊗ₜ[ℤ] y = B.dualIndex • x := by
  simpa [dualIndex] using AddSubgroup.nsmul_relIndex_mem
    (TensorProduct.mk ℤ ℚ L 1 : L →+ ℚ ⊗[ℤ] L).range (K := B.dualLattice.toAddSubgroup) hx

/-- **The dual index is the Gram determinant.** If `B` is nondegenerate over `ℚ`, then for every
`ℤ`-basis `b` of `L`, `[L^# : L] = |det (B(b i, b j))|`. -/
theorem dualIndex_eq_natAbs_det (hB : (B.baseChange ℚ).Nondegenerate) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι ℤ L) :
    B.dualIndex = (LinearMap.BilinForm.toMatrix b B).det.natAbs := by
  set c := (B.baseChange ℚ).dualBasis hB (b.baseChange ℚ)
  have hL := b.range_mk_one_eq_closure (K := ℚ)
  have hdual : B.dualLattice.toAddSubgroup = AddSubgroup.closure (Set.range c) := by
    have : AddSubgroup.toIntSubmodule (TensorProduct.mk ℤ ℚ L 1 : L →+ ℚ ⊗[ℤ] L).range =
        Submodule.span ℤ (Set.range (b.baseChange ℚ)) := by
      rw [hL, AddSubgroup.toIntSubmodule_closure]
    rw [dualLattice, this, LinearMap.BilinForm.dualSubmodule_span_of_basis _ hB,
      Submodule.span_int_eq_addSubgroupClosure]
  -- the dual basis expresses `1 ⊗ b j` through the transposed rational Gram matrix
  have hc : c.toMatrix (b.baseChange ℚ) =
      (LinearMap.BilinForm.toMatrix (b.baseChange ℚ) (B.baseChange ℚ)).transpose := by
    ext i j
    simp [c, Module.Basis.toMatrix_apply, LinearMap.BilinForm.toMatrix_apply]
  have h := AddSubgroup.relIndex_eq_abs_det _ _ B.le_dualLattice (b.baseChange ℚ) c hL hdual
  rw [Module.Basis.det_apply, hc, Matrix.det_transpose,
    LinearMap.BilinForm.det_toMatrix_baseChange, ← dualIndex_def] at h
  rw [← Nat.cast_inj (R := ℚ), h]
  simp

/-- The zero lattice is self-dual: a form on a subsingleton group has dual index one. -/
theorem dualIndex_eq_one_of_subsingleton [Subsingleton L] : B.dualIndex = 1 :=
  AddSubgroup.relIndex_eq_one.2 fun x _ ↦ by
    rw [Subsingleton.elim x ((1 : ℚ) ⊗ₜ[ℤ] (0 : L))]
    exact ⟨0, rfl⟩

/-- If `L` is finite free over `ℤ` and the form is nondegenerate over `ℚ`, the dual lattice
contains the image of `L` with finite index. -/
theorem dualIndex_ne_zero [Module.Free ℤ L] [Module.Finite ℤ L]
    (hB : (B.baseChange ℚ).Nondegenerate) : B.dualIndex ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  rw [B.dualIndex_eq_natAbs_det hB b, Int.natAbs_ne_zero,
    ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero,
    ← LinearMap.BilinForm.nondegenerate_baseChange_iff (A := ℚ) _ b]
  exact hB

/-- A `ℤ`-valued bilinear form is **self-dual at `p`** when every `x ∈ L^#` has a multiple
`n • x ∈ L` with `n` not divisible by `p`. For `p` prime this says that `L` and its dual lattice
`L^#` agree after localizing at `p`. By `isSelfDualAt_iff_not_dvd_dualIndex`, when the dual index
is finite and `p` is prime, this holds exactly when `p ∤ [L^# : L]`. -/
def IsSelfDualAt (p : ℕ) : Prop :=
  ∀ x ∈ B.dualLattice, ∃ n : ℕ, ¬p ∣ n ∧ ∃ y : L, (1 : ℚ) ⊗ₜ[ℤ] y = n • x

/-- Self-duality at `p` unfolded: every element of the dual lattice has a multiple prime to `p`
in the image of `L`. -/
theorem isSelfDualAt_iff {p : ℕ} :
    B.IsSelfDualAt p ↔ ∀ x ∈ B.dualLattice, ∃ n : ℕ, ¬p ∣ n ∧ ∃ y : L, (1 : ℚ) ⊗ₜ[ℤ] y = n • x :=
  Iff.rfl

/-- A form is self-dual at every `p` not dividing its dual index. -/
theorem isSelfDualAt_of_not_dvd_dualIndex {p : ℕ} (hp : ¬p ∣ B.dualIndex) : B.IsSelfDualAt p :=
  fun _ hx ↦ ⟨B.dualIndex, hp, B.exists_tmul_eq_dualIndex_smul hx⟩

/-- A `ℤ`-valued bilinear form whose dual index `[L^# : L]` is finite is self-dual at a prime `p`
exactly when `p` does not divide `[L^# : L]`. By `dualIndex_ne_zero`, the index is finite when
`L` is finite free over `ℤ` and the form is nondegenerate over `ℚ`. -/
theorem isSelfDualAt_iff_not_dvd_dualIndex (h : B.dualIndex ≠ 0) {p : ℕ} (hp : p.Prime) :
    B.IsSelfDualAt p ↔ ¬p ∣ B.dualIndex := by
  refine ⟨fun hs hdvd ↦ ?_, B.isSelfDualAt_of_not_dvd_dualIndex⟩
  have := Fact.mk hp
  -- the dual index is the cardinality of the quotient `L^# / L`
  rw [dualIndex_def, AddSubgroup.relIndex] at h hdvd
  set H := (TensorProduct.mk ℤ ℚ L 1 : L →+ ℚ ⊗[ℤ] L).range.addSubgroupOf
    B.dualLattice.toAddSubgroup
  have : H.FiniteIndex := ⟨h⟩
  rw [AddSubgroup.index_eq_card] at hdvd
  -- by Cauchy, `L^# / L` has an element `x + L` of order `p`
  obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' (G := B.dualLattice.toAddSubgroup ⧸ H) p hdvd
  induction g using QuotientAddGroup.induction_on with | H x
  -- but some multiple `n • x ∈ L` has `n` prime to `p`, so `p ∣ n`, a contradiction
  obtain ⟨n, hpn, hn⟩ := hs x x.2
  refine hpn (hg ▸ addOrderOf_dvd_of_nsmul_eq_zero ?_)
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.mem_addSubgroupOf.2 hn

end LinearMap.BilinForm
