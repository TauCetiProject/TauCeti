/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.Killing.CompactIdeal
public import TauCeti.Algebra.Lie.Submodule.DirectSum
public import Mathlib.Algebra.Lie.Prod
import TauCeti.Algebra.Lie.Killing.Basic

/-!
# Cartan involutions and the simple ideals

A Cartan involution `θ` of a real semisimple Lie algebra `𝔤₀` preserves every simple ideal: the
Killing form `B` vanishes between two ideals with trivial intersection, while `B(x, θ x) < 0` for
`x ≠ 0`, so a nonzero ideal meets its image under `θ`. Conversely, when `𝔤₀` is finite-dimensional,
Cartan involutions of the summands of an internal direct sum of ideals, in particular of the simple
ideals, assemble into a Cartan involution of `𝔤₀`. Finally `θ` is the identity on the compact
ideal `LieAlgebra.compactIdeal`, the sum of the simple ideals on which the Killing form is negative
definite, and the `-1`-eigenspace `𝔭` of `θ` lies in the noncompact ideal
`LieAlgebra.noncompactIdeal`, the sum of the other simple ideals.

Simple ideals are the atoms of the lattice of Lie ideals, as in Mathlib's
`LieAlgebra.IsSemisimple`. The general material used here lives elsewhere: the vanishing of the
Killing form between ideals with trivial intersection (`LieIdeal.killingForm_eq_zero_of_disjoint`)
in `TauCeti/Algebra/Lie/Killing/Basic.lean`, the compact and noncompact ideals, with their
stability under every automorphism (`LieEquiv.map_compactIdeal`, `LieEquiv.map_noncompactIdeal`),
in `TauCeti/Algebra/Lie/Killing/CompactIdeal.lean`, the assembly `LieEquiv.ofIsInternal` of
automorphisms of the summands of an internal direct sum of Lie ideals in
`TauCeti/Algebra/Lie/Submodule/DirectSum.lean`, and `LieAlgebra.IsSemisimple.isInternal_atoms` in
`TauCeti/Algebra/Lie/Submodule/Decomposition.lean`.

## Main results

* `LieEquiv.IsCartanInvolution.map_eq_of_isAtom`: a Cartan involution preserves every simple
  ideal.
* `LieEquiv.isCartanInvolution_ofIsInternal`: Cartan involutions of the summands of an internal
  direct sum of ideals of a finite-dimensional Lie algebra assemble into a Cartan involution.
* `LieEquiv.IsCartanInvolution.forall_apply_eq_iff_of_isAtom`: a simple ideal is compact exactly
  when a Cartan involution fixes it pointwise.
* `LieEquiv.IsCartanInvolution.apply_eq_of_mem_compactIdeal`: a Cartan involution is the identity
  on the compact ideal.
* `LieEquiv.IsCartanInvolution.cartanP_le_noncompactIdeal`: `𝔭` lies in the noncompact ideal.
* `LieEquiv.not_isCartanInvolution_prodComm`: the flip of `L × L` is not a Cartan involution for
  nontrivial `L`.

## References

* J.-H. Eschenburg, *Lecture Notes on Symmetric Spaces*, §7.
* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Chapter VI, §2.
-/

public section

open LieAlgebra LieModule

namespace LieEquiv

/-! ### Cartan involutions preserve the simple ideals -/

section Preserve

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] {θ : L ≃ₗ⁅K⁆ L}

namespace IsCartanInvolution

/-- A nonzero Lie ideal meets its image under a Cartan involution. -/
theorem inf_map_ne_bot (hθ : θ.IsCartanInvolution) {I : LieIdeal K L} (hI : I ≠ ⊥) :
    I ⊓ I.map θ.toLieHom ≠ ⊥ := by
  intro h
  obtain ⟨x, hx, hx₀⟩ := (Submodule.ne_bot_iff I.toSubmodule).mp
    ((LieSubmodule.toSubmodule_eq_bot I).not.mpr hI)
  exact (hθ.killingForm_apply_apply_neg hx₀).ne
    (LieIdeal.killingForm_eq_zero_of_disjoint (disjoint_iff.mpr h) hx (LieIdeal.mem_map hx))

/-- A Cartan involution maps every simple ideal (an atom of the lattice of Lie ideals) into
itself. -/
theorem apply_mem_of_isAtom (hθ : θ.IsCartanInvolution) {I : LieIdeal K L} (hI : IsAtom I)
    {x : L} (hx : x ∈ I) : θ x ∈ I := by
  have hle : I ≤ I.map θ.toLieHom :=
    inf_eq_left.mp (((hI.le_iff).mp inf_le_left).resolve_left (hθ.inf_map_ne_bot hI.1))
  have := LieIdeal.mem_map_equiv.mp (hle hx)
  rwa [hθ.symm_apply] at this

/-- A Cartan involution maps every simple ideal (an atom of the lattice of Lie ideals) onto
itself. -/
theorem map_eq_of_isAtom (hθ : θ.IsCartanInvolution) {I : LieIdeal K L} (hI : IsAtom I) :
    I.map θ.toLieHom = I := by
  refine le_antisymm (LieIdeal.map_le_iff_le_comap.mpr fun x hx ↦ hθ.apply_mem_of_isAtom hI hx)
    fun x hx ↦ LieIdeal.mem_map_equiv.mpr ?_
  rw [hθ.symm_apply]
  exact hθ.apply_mem_of_isAtom hI hx

end IsCartanInvolution

end Preserve

/-! ### Assembling Cartan involutions of the summands of an internal direct sum -/

section IsCartanInvolutionOfIsInternal

variable {K L ι : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] [DecidableEq ι] {I : ι → LieIdeal K L}
  (h : DirectSum.IsInternal fun i ↦ (I i).toSubmodule) {θ : ∀ i, I i ≃ₗ⁅K⁆ I i}

/-- Cartan involutions of the summands of an internal direct sum of Lie ideals of a
finite-dimensional Lie algebra assemble into a Cartan involution. With
`LieAlgebra.IsSemisimple.isInternal_atoms` this applies to the simple ideals of a semisimple Lie
algebra. -/
theorem isCartanInvolution_ofIsInternal [FiniteDimensional K L]
    (hθ : ∀ i, (θ i).IsCartanInvolution) : (ofIsInternal h θ).IsCartanInvolution := by
  classical
  set f := ofIsInternal h θ
  refine isCartanInvolution_iff.mpr ⟨fun x ↦ ?_, fun x hx ↦ ?_⟩
  · have hθθ : (fun i ↦ (θ i).trans (θ i)) = fun _ ↦ LieEquiv.refl :=
      funext fun i ↦ LieEquiv.ext (hθ i).involutive
    rw [← LieEquiv.trans_apply, ofIsInternal_trans, hθθ, ofIsInternal_refl, LieEquiv.refl_apply]
  -- Write `x` as the sum of its components `d i ∈ I i`; the Killing form splits over them.
  set d := (DirectSum.lieModuleEquivOfIsInternal I h).symm x
  have hx' : ∑ i ∈ d.support, (d i : L) = x :=
    DirectSum.sum_support_lieModuleEquivOfIsInternal_symm h x
  have hsum : killingForm K L x (f x) =
      ∑ i ∈ d.support, killingForm K (I i) (d i) (θ i (d i)) := by
    rw [← hx', map_sum f, LieIdeal.killingForm_sum_sum (y := fun i ↦ f (d i))
      (fun i j hij ↦ h.lieSubmodule_disjoint hij) _ (fun i ↦ (d i).property)
      (fun i ↦ by rw [ofIsInternal_apply_coe]; exact (θ i _).property)]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [ofIsInternal_apply_coe, LieIdeal.killingForm_apply_apply_coe]
  rw [hsum]
  refine Finset.sum_neg (fun i hi ↦ (hθ i).killingForm_apply_apply_neg
    (DFinsupp.mem_support_iff.mp hi)) (Finset.nonempty_of_ne_empty fun hd0 ↦ ?_)
  exact hx (by rw [← hx', hd0, Finset.sum_empty])

end IsCartanInvolutionOfIsInternal

/-! ### The flip of `L × L` -/

/-- The swap of the factors of `L × L` is not a Cartan involution when `L` is nontrivial. -/
theorem not_isCartanInvolution_prodComm {K L : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [LieRing L] [LieAlgebra K L] [Nontrivial L] :
    ¬ (LieEquiv.prodComm (R := K) (L₁ := L) (L₂ := L)).IsCartanInvolution := by
  -- For `x ≠ 0` the flip sends `(x, 0)` into the ideal `0 × L`, which meets `L × 0` trivially and
  -- so is Killing orthogonal to it, whereas a Cartan involution has `B(v, θ v) < 0` for `v ≠ 0`.
  intro hθ
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  have hd : Disjoint (LieHom.snd K L L).ker (LieHom.fst K L L).ker :=
    disjoint_iff.mpr <| eq_bot_iff.mpr fun p hp ↦ by
      obtain ⟨h2, h1⟩ := (LieSubmodule.mem_inf _ _ _).mp hp
      exact (LieSubmodule.mem_bot _).mpr (Prod.ext (by simpa using h1) (by simpa using h2))
  exact (hθ.killingForm_apply_apply_neg (x := (x, 0)) (by simp [hx])).ne
    (LieIdeal.killingForm_eq_zero_of_disjoint hd (by simp) (by simp))

end LieEquiv

namespace LieEquiv.IsCartanInvolution

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] {θ : L ≃ₗ⁅K⁆ L}

/-- A simple ideal has negative definite Killing form exactly when a Cartan involution fixes it
pointwise. -/
theorem forall_apply_eq_iff_of_isAtom (hθ : θ.IsCartanInvolution) {I : LieIdeal K L}
    (hI : IsAtom I) :
    (∀ x ∈ I, θ x = x) ↔ ∀ x ∈ I, x ≠ 0 → killingForm K L x x < 0 := by
  refine ⟨fun h x hx hx₀ ↦ ?_, fun h x hx ↦ ?_⟩
  · simpa [h x hx] using hθ.killingForm_apply_apply_neg hx₀
  · -- `x - θ x` lies in `I ∩ 𝔭`, where the Killing form is both negative and positive definite.
    have hp : x - θ x ∈ θ.cartanP := mem_cartanP.mpr (by rw [map_sub, hθ.involutive x, neg_sub])
    have hpI : x - θ x ∈ I := sub_mem hx (hθ.apply_mem_of_isAtom hI hx)
    by_contra hne
    have hne' : x - θ x ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    exact (h _ hpI hne').asymm (hθ.killingForm_apply_self_pos_of_mem_cartanP hp hne')

/-- A Cartan involution is the identity on the compact ideal. -/
theorem apply_eq_of_mem_compactIdeal (hθ : θ.IsCartanInvolution) {x : L}
    (hx : x ∈ compactIdeal K L) : θ x = x := by
  have hle : (compactIdeal K L).toSubmodule ≤ θ.toLieHom.fixedSubalgebra.toSubmodule := by
    rw [compactIdeal_def, LieSubmodule.sSup_toSubmodule, sSup_le_iff]
    rintro _ ⟨I, ⟨hI, hIP⟩, rfl⟩ x hx
    exact (LieSubalgebra.mem_toSubmodule _).mpr <| LieHom.mem_fixedSubalgebra.mpr <|
      (hθ.forall_apply_eq_iff_of_isAtom hI).mpr hIP x hx
  exact LieHom.mem_fixedSubalgebra.mp ((LieSubalgebra.mem_toSubmodule _).mp (hle hx))

/-- The `-1`-eigenspace `𝔭` of a Cartan involution lies in the noncompact ideal. -/
theorem cartanP_le_noncompactIdeal (hθ : θ.IsCartanInvolution) :
    θ.cartanP ≤ (noncompactIdeal K L).toSubmodule := by
  have := hθ.isSemisimple
  intro x hx
  have hc := LieAlgebra.isCompl_compactIdeal_noncompactIdeal (K := K) (L := L)
  have htop : (compactIdeal K L).toSubmodule ⊔ (noncompactIdeal K L).toSubmodule = ⊤ := by
    rw [← LieSubmodule.sup_toSubmodule, hc.sup_eq_top, LieSubmodule.top_toSubmodule]
  obtain ⟨c, hcm, n, hn, rfl⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : x ∈ _)
  have hθn : θ n ∈ noncompactIdeal K L := by
    rw [← θ.map_noncompactIdeal]
    exact LieIdeal.mem_map hn
  -- `θ (c + n) = -(c + n)` and `θ c = c` give `2 c = -(n + θ n)`, in both ideals.
  have h2 : (2 : K) • c = -(n + θ n) := by
    have := mem_cartanP.mp hx
    rw [map_add, hθ.apply_eq_of_mem_compactIdeal hcm] at this
    linear_combination (norm := module) this
  have h2c : (2 : K) • c = 0 :=
    (LieSubmodule.mem_bot _).mp <| hc.disjoint.le_bot <| (LieSubmodule.mem_inf _ _ _).mpr
      ⟨SMulMemClass.smul_mem _ hcm, h2 ▸ neg_mem (add_mem hn hθn)⟩
  obtain rfl : c = 0 := (smul_eq_zero.mp h2c).resolve_left two_ne_zero
  simpa using hn

end LieEquiv.IsCartanInvolution
