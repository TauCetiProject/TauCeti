/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Lifting
import Mathlib.Topology.Instances.ZMod
import TauCeti.Topology.Algebra.Group.Heisenberg

/-!
# A non-unit obstruction to the peripheral product identity

For the basis of a free pro-`2` group of rank two, no conjugators make the peripheral defect
of exponent `2` belong to the second closed lower-central-series term. In particular, the
peripheral product identity cannot be extended from unit exponents to all `2`-adic integers.
This is an obstruction already in the class-two quotient, rather than only to an exact identity.

The detecting group is the Heisenberg group over `ℤ/2`: the two standard generators have
square `1`, but their product has nontrivial central square. Every continuous homomorphism
to this group kills the second closed lower-central-series term. The detection construction
follows the use of finite Heisenberg groups in
`TauCeti.Peripheral.not_isPeripheralAut_of_apply_basis_eq_inv`.

## Main results

* `TauCeti.Peripheral.level_two_eq_empty`: the second peripheral level at exponent `2` is empty.
* `TauCeti.Peripheral.not_exists_peripheral_identity_two`: even the normalized product with
  two conjugators cannot be trivial modulo the second closed lower-central-series term.
-/

public section

namespace TauCeti.Peripheral

variable {F : Type*} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
  [CompactSpace F] [TotallyDisconnectedSpace F]

/-- For a rank-two free pro-`2` group, the second peripheral level at the non-unit exponent `2`
is empty, even without normalizing the first conjugator. -/
@[simp]
theorem level_two_eq_empty (hF : IsProP 2 F) (e : F ≃ₜ* freeProP 2 (Fin 2)) :
    level hF (basis e) 2 2 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ⟨c, d⟩ hcd
  have hH : IsProP 2 (HeisenbergGroup (ZMod 2)) :=
    (HeisenbergGroup.isPGroup_zmod 2).isProP
  let a : HeisenbergGroup (ZMod 2) := ⟨1, 0, 0⟩
  let b : HeisenbergGroup (ZMod 2) := ⟨0, 1, 0⟩
  let f : F →ₜ* HeisenbergGroup (ZMod 2) :=
    (freeProP.lift hH ![a, b]).comp (e : F →ₜ* freeProP 2 (Fin 2))
  have hf (i : Fin 2) : f (basis e i) = ![a, b] i := by
    simp [f, ContinuousMonoidHom.comp_toFun]
  have hz : f (cusp (basis e)) = (a * b)⁻¹ := by
    rw [map_cusp, cusp_def]
    simp [Function.comp_def, hf, List.ofFn_succ]
  -- Functoriality sends a level-two defect into the trivial second term in the target.
  have hmap := (f : F →* HeisenbergGroup (ZMod 2)).map_closedLowerCentralSeries_le
    f.continuous 2 (Subgroup.mem_map.mpr ⟨_, (mem_level_iff ..).mp hcd, rfl⟩)
  rw [HeisenbergGroup.closedLowerCentralSeries_two_eq_bot, Subgroup.mem_bot] at hmap
  have ha : a ^ 2 = 1 := by
    ext <;> norm_num [a, pow_two]
    exact ZMod.natCast_self 2
  have hb : b ^ 2 = 1 := by
    ext <;> norm_num [b, pow_two]
    exact ZMod.natCast_self 2
  -- The generator squares disappear, independently of their conjugators.
  simp only [defect_def, hF.padicPow_ofNat, map_mul, map_inv, map_list_prod,
    List.map_ofFn, Function.comp_def, map_pow, MonoidHom.coe_ofClass] at hmap
  rw [hz] at hmap
  have hsq : (b⁻¹ * a⁻¹) ^ 2 = 1 :=
    (conj_eq_one_iff (a := (f d)⁻¹) (b := (b⁻¹ * a⁻¹) ^ 2)).mp
      (by simpa [hf, List.ofFn_succ, ha, hb] using hmap)
  have hcoord := congrArg HeisenbergGroup.z hsq
  -- The square of the cusp image has central coordinate `1` in `ℤ/2`.
  norm_num [a, b, pow_two] at hcoord

/-- At exponent `2`, no normalized peripheral product in a rank-two free pro-`2` group is
trivial even modulo the second closed lower-central-series term. -/
theorem not_exists_peripheral_identity_two (hF : IsProP 2 F)
    (e : F ≃ₜ* freeProP 2 (Fin 2)) :
    ¬ ∃ (c d : F),
      hF.padicPow (basis e 0) 2 * (c⁻¹ * hF.padicPow (basis e 1) 2 * c) *
        (d⁻¹ * hF.padicPow (cusp (basis e)) 2 * d) ∈ closedLowerCentralSeries F 2 := by
  rintro ⟨c, d, h⟩
  have hlev : (![1, c], d) ∈ level hF (basis e) 2 2 := by
    rw [mem_level_iff, defect_def]
    simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
      Fin.zero_eta, Fin.succ_zero_eq_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      inv_one, one_mul, mul_one] using h
  simp only [level_two_eq_empty hF e, Set.mem_empty_iff_false] at hlev

end TauCeti.Peripheral
