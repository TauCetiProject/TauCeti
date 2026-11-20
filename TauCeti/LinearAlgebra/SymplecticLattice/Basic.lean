/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.TensorProduct.Basis
import TauCeti.LinearAlgebra.BilinearForm.BaseChange

/-!
# Symplectic lattices with an action of a ring with involution

Let `O` be a ring with an involution `b ↦ star b`. A *symplectic `O`-lattice* is a left
`O`-module `L` with an alternating `ℤ`-bilinear pairing `⟨·,·⟩ : L × L → ℤ`, nondegenerate after
extending scalars to `ℚ`, for which the action of `b` is adjoint to the action of `star b`:
`⟨b • x, y⟩ = ⟨x, star b • y⟩`. These are the lattices of PEL data, where `O` is an order in a
semisimple `ℚ`-algebra with positive involution and the pairing takes values in the Tate twist
`ℤ(1) = 2π√−1 ℤ`; choosing `√−1` identifies `ℤ(1)` with `ℤ`, and nothing here depends on that
choice.

The *dual lattice* is `L^# = {x ∈ ℚ ⊗ L : ⟨x, L⟩ ⊆ ℤ}`, computed with the rational extension of
the pairing. It contains the image of `L`, is stable under the rational extension of the
`O`-action because the adjoint of `b` is `star b`, and contains it with finite index
`[L^# : L]`, the *dual index*. For a `ℤ`-basis of `L` the dual index is the absolute value of
the Gram determinant. The lattice is *self-dual at a prime `p`* when `L` and `L^#` agree after
localizing at `p` (equivalently after completing at `p`), which happens exactly when `p` does
not divide the dual index. These primes are the good primes of the lattice for the PEL
moduli problems.

## Main definitions

* `TauCeti.SymplecticOLattice O L`: an alternating `ℤ`-valued pairing on the `O`-module `L`,
  nondegenerate over `ℚ`, with `b` and `star b` adjoint.
* `TauCeti.SymplecticOLattice.ofIsAlt`: over `O = ℤ`, every alternating pairing that is
  nondegenerate over `ℚ` is a symplectic lattice.
* `TauCeti.SymplecticOLattice.dual`: the dual lattice `L^#` inside `ℚ ⊗[ℤ] L`.
* `TauCeti.SymplecticOLattice.dualIndex`: the index `[L^# : L]`.
* `TauCeti.SymplecticOLattice.IsSelfDualAt`: self-duality at a prime.

## Main results

* `TauCeti.SymplecticOLattice.baseChange_isAdjointPair`: the adjointness of `b` and `star b`
  persists over `ℚ`.
* `TauCeti.SymplecticOLattice.mem_dual_iff`: `x ∈ L^#` exactly when `⟨x, y⟩ ∈ ℤ` for all `y ∈ L`.
* `TauCeti.SymplecticOLattice.tmul_mem_dual`: the image of `L` lies in `L^#`.
* `TauCeti.SymplecticOLattice.baseChange_smul_mem_dual`: `L^#` is stable under `O`.
* `TauCeti.SymplecticOLattice.exists_tmul_eq_dualIndex_smul`: `[L^# : L] • L^#` lies in the image
  of `L`.
* `TauCeti.SymplecticOLattice.dualIndex_eq_natAbs_det`: `[L^# : L] = |det (⟨b i, b j⟩)|` for
  every `ℤ`-basis `b` of `L`.
* `TauCeti.SymplecticOLattice.dualIndex_eq_one_of_subsingleton`: the zero lattice has dual index
  one.
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
theorem form_smul_left (b : O) (x y : L) : Λ.form (b • x) y = Λ.form x (star b • y) :=
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
    | tmul r y => simp [Λ.form_smul_left]

/-- The **dual lattice** `L^# = {x ∈ ℚ ⊗ L : ⟨x, L⟩ ⊆ ℤ}` of a symplectic lattice, for the rational
extension of the pairing. -/
def dual : Submodule ℤ (ℚ ⊗[ℤ] L) :=
  -- The image of `L` is the additive range of `y ↦ 1 ⊗ₜ y`, made a `ℤ`-submodule through
  -- `AddSubgroup.toIntSubmodule`, so that every `ℤ`-module structure on `ℚ ⊗[ℤ] L` here is the
  -- canonical one of an additive group. The `ℤ`-module structure of a tensor product over `ℤ`
  -- agrees with it only propositionally, and `LinearMap.range (TensorProduct.mk ℤ ℚ L 1)` uses it.
  (Λ.form.baseChange ℚ).dualSubmodule
    (AddSubgroup.toIntSubmodule (TensorProduct.mk ℤ ℚ L 1 : L →+ ℚ ⊗[ℤ] L).range)

/-- A rational vector lies in the dual lattice exactly when its pairing with every lattice vector
is an integer. -/
theorem mem_dual_iff {x : ℚ ⊗[ℤ] L} :
    x ∈ Λ.dual ↔ ∀ y : L, ∃ n : ℤ, Λ.form.baseChange ℚ x (1 ⊗ₜ y) = n := by
  rw [dual, LinearMap.BilinForm.mem_dualSubmodule]
  refine ⟨fun h y ↦ ?_, fun h z hz ↦ ?_⟩
  · obtain ⟨n, hn⟩ := Submodule.mem_one.1 (h _ ⟨y, rfl⟩)
    exact ⟨n, by simpa using hn.symm⟩
  · obtain ⟨y, rfl⟩ := hz
    obtain ⟨n, hn⟩ := h y
    exact Submodule.mem_one.2 ⟨n, by simpa using hn.symm⟩

/-- The image of `L` in `ℚ ⊗ L` lies in the dual lattice `L^#`, since the pairing is integral. -/
@[simp]
theorem tmul_mem_dual (y : L) : (1 : ℚ) ⊗ₜ[ℤ] y ∈ Λ.dual :=
  Λ.mem_dual_iff.2 fun z ↦ ⟨Λ.form y z, by simp⟩

/-- The dual lattice is stable under the rational extension of the action of `O`: if
`⟨x, L⟩ ⊆ ℤ` then `⟨b • x, y⟩ = ⟨x, star b • y⟩ ∈ ℤ` for every `y ∈ L`. -/
theorem baseChange_smul_mem_dual (b : O) {x : ℚ ⊗[ℤ] L} (hx : x ∈ Λ.dual) :
    (DistribSMul.toLinearMap ℤ L b).baseChange ℚ x ∈ Λ.dual := by
  refine Λ.mem_dual_iff.2 fun y ↦ ?_
  rw [Λ.baseChange_isAdjointPair b, LinearMap.baseChange_tmul]
  exact Λ.mem_dual_iff.1 hx _

/-- The **dual index** `[L^# : L]` of a symplectic lattice: the index of the image of `L` in its
dual lattice. It is nonzero when `L` is finite free over `ℤ` (`dualIndex_ne_zero`). -/
noncomputable def dualIndex : ℕ :=
  (TensorProduct.mk ℤ ℚ L 1 : L →+ ℚ ⊗[ℤ] L).range.relIndex Λ.dual.toAddSubgroup

/-- Multiplication by the dual index carries the dual lattice into the image of `L`. -/
theorem exists_tmul_eq_dualIndex_smul {x : ℚ ⊗[ℤ] L} (hx : x ∈ Λ.dual) :
    ∃ y : L, (1 : ℚ) ⊗ₜ[ℤ] y = Λ.dualIndex • x := by
  simpa [dualIndex] using AddSubgroup.nsmul_relIndex_mem
    (TensorProduct.mk ℤ ℚ L 1 : L →+ ℚ ⊗[ℤ] L).range (K := Λ.dual.toAddSubgroup) hx

/-- The image of `L` in `ℚ ⊗ L` is the subgroup generated by the rational basis induced by a
`ℤ`-basis of `L`. -/
private theorem range_tmul_eq_closure {ι : Type*} [Finite ι] (b : Basis ι ℤ L) :
    (TensorProduct.mk ℤ ℚ L 1 : L →+ ℚ ⊗[ℤ] L).range =
      AddSubgroup.closure (Set.range (b.baseChange ℚ)) := by
  refine le_antisymm ?_ (AddSubgroup.closure_le _ |>.2 ?_)
  · cases nonempty_fintype ι
    rintro _ ⟨y, rfl⟩
    rw [← b.sum_repr y, map_sum]
    refine AddSubgroup.sum_mem _ fun i _ ↦ ?_
    rw [map_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range.2 ⟨i, by simp⟩)) _
  · rintro _ ⟨i, rfl⟩
    exact ⟨b i, by simp⟩

section Basis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The dual index is the Gram determinant.** For every `ℤ`-basis `b` of `L`,
`[L^# : L] = |det (⟨b i, b j⟩)|`. -/
theorem dualIndex_eq_natAbs_det (b : Basis ι ℤ L) :
    Λ.dualIndex = (LinearMap.BilinForm.toMatrix b Λ.form).det.natAbs := by
  set c := (Λ.form.baseChange ℚ).dualBasis Λ.nondegenerate (b.baseChange ℚ)
  have hL := range_tmul_eq_closure b
  have hdual : Λ.dual.toAddSubgroup = AddSubgroup.closure (Set.range c) := by
    have : AddSubgroup.toIntSubmodule (TensorProduct.mk ℤ ℚ L 1 : L →+ ℚ ⊗[ℤ] L).range =
        Submodule.span ℤ (Set.range (b.baseChange ℚ)) := by
      rw [hL, AddSubgroup.toIntSubmodule_closure]
    rw [dual, this, LinearMap.BilinForm.dualSubmodule_span_of_basis _ Λ.nondegenerate,
      Submodule.span_int_eq_addSubgroupClosure]
  -- the dual basis expresses `1 ⊗ b j` through the transposed rational Gram matrix
  have hc : c.toMatrix (b.baseChange ℚ) =
      (LinearMap.BilinForm.toMatrix (b.baseChange ℚ) (Λ.form.baseChange ℚ)).transpose := by
    ext i j
    simp [c, Module.Basis.toMatrix_apply, LinearMap.BilinForm.toMatrix_apply]
  have hle : (TensorProduct.mk ℤ ℚ L 1 : L →+ ℚ ⊗[ℤ] L).range ≤ Λ.dual.toAddSubgroup := by
    rintro _ ⟨y, rfl⟩
    exact Λ.tmul_mem_dual y
  have h := AddSubgroup.relIndex_eq_abs_det _ _ hle (b.baseChange ℚ) c hL hdual
  rw [Module.Basis.det_apply, hc, Matrix.det_transpose,
    LinearMap.BilinForm.det_toMatrix_baseChange] at h
  have : (Λ.dualIndex : ℚ) = ((LinearMap.BilinForm.toMatrix b Λ.form).det.natAbs : ℚ) := by
    rw [dualIndex, h, Nat.cast_natAbs, Int.cast_abs, algebraMap_int_eq, eq_intCast]
  exact_mod_cast this

end Basis

/-- The zero lattice is self-dual: a symplectic lattice on a subsingleton module has dual index
one. -/
theorem dualIndex_eq_one_of_subsingleton [Subsingleton L] : Λ.dualIndex = 1 := by
  rw [Λ.dualIndex_eq_natAbs_det (Basis.empty L : Basis (Fin 0) ℤ L), Matrix.det_isEmpty,
    Int.natAbs_one]

/-- If `L` is finite free over `ℤ`, the dual lattice contains the image of `L` with finite
index. -/
theorem dualIndex_ne_zero [Module.Free ℤ L] [Module.Finite ℤ L] : Λ.dualIndex ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  rw [Λ.dualIndex_eq_natAbs_det b, Int.natAbs_ne_zero,
    ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero,
    ← LinearMap.BilinForm.nondegenerate_baseChange_iff (A := ℚ) _ b]
  exact Λ.nondegenerate

/-- A symplectic lattice is **self-dual at `p`** when `L` and its dual lattice `L^#` agree after
localizing at `p`: every `x ∈ L^#` has a multiple `n • x ∈ L` with `n` prime to `p`. Equivalently
`L ⊗ ℤ_p = L^# ⊗ ℤ_p`; by `isSelfDualAt_iff_not_dvd_dualIndex` this holds at a prime `p` exactly
when `p ∤ [L^# : L]`. -/
def IsSelfDualAt (p : ℕ) : Prop :=
  ∀ x ∈ Λ.dual, ∃ n : ℕ, ¬p ∣ n ∧ ∃ y : L, (1 : ℚ) ⊗ₜ[ℤ] y = n • x

/-- A symplectic lattice is self-dual at every `p` not dividing its dual index. -/
theorem isSelfDualAt_of_not_dvd_dualIndex {p : ℕ} (hp : ¬p ∣ Λ.dualIndex) :
    Λ.IsSelfDualAt p :=
  fun _ hx ↦ ⟨Λ.dualIndex, hp, Λ.exists_tmul_eq_dualIndex_smul hx⟩

/-- A symplectic lattice that is finite free over `ℤ` is self-dual at a prime `p` exactly when `p`
does not divide its dual index `[L^# : L]`. -/
theorem isSelfDualAt_iff_not_dvd_dualIndex [Module.Free ℤ L] [Module.Finite ℤ L] {p : ℕ}
    (hp : p.Prime) : Λ.IsSelfDualAt p ↔ ¬p ∣ Λ.dualIndex := by
  refine ⟨fun h hdvd ↦ ?_, Λ.isSelfDualAt_of_not_dvd_dualIndex⟩
  have := Fact.mk hp
  set H := (TensorProduct.mk ℤ ℚ L 1 : L →+ ℚ ⊗[ℤ] L).range.addSubgroupOf Λ.dual.toAddSubgroup
  have : H.FiniteIndex := ⟨Λ.dualIndex_ne_zero⟩
  -- by Cauchy, `L^# / L` has an element `x + L` of order `p`
  obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' (G := Λ.dual.toAddSubgroup ⧸ H) p hdvd
  induction g using QuotientAddGroup.induction_on with | H x
  -- but some multiple `n • x ∈ L` has `n` prime to `p`, so `p ∣ n`, a contradiction
  obtain ⟨n, hpn, hn⟩ := h x x.2
  refine hpn (hg ▸ addOrderOf_dvd_of_nsmul_eq_zero ?_)
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.mem_addSubgroupOf.2 hn

end SymplecticOLattice

end TauCeti
