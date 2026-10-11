/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.SymmetricThree.CharThree
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.SymmetricThree.CharThree.Simple
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.PrimePart
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.SymmetricThree.CharThree.Induction
import TauCeti.GroupTheory.Perm.FinThree.Basic
import Mathlib.Data.ZMod.Basic

/-!
# The prime-to-three induction subgroup of S₃

Over any field of characteristic three, the classes induced from cyclic subgroups of order
prime to three form precisely the subgroup of virtual S₃-modules whose dimension is divisible
by three. In fact induction from any single point stabilizer already has this image.
The subgroup has index three, and a multiple of the trivial class belongs to it exactly when
its multiplier is divisible by three.

The calculation uses `TauCeti.symmetricThreeCharThreeSimpleClassBasis`, the permutation-class
formula `TauCeti.indK0_one_stabilizer_perm_fin_three_char_three`, and the projection formula
`TauCeti.indK0_mul_resK0`. All dimensions and multiplicities are integral; no assertion about
splitting representations or detecting them by modular traces is needed.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra MonoidalCategory

namespace TauCeti

variable (k : Type) [Field k] [CharP k 3]

local notation "G" => Equiv.Perm (Fin 3)
local notation "K₀" => ExactK0 (finiteModulesExactStructure k[G])
local notation "s" => fdRepK0RingEquiv k G
  (ExactK0.of (FDRep.ofLinearCharacter (signLinearCharacter k (Fin 3))))
local notation "I" => ⨆ (S : Subgroup G) (_ : IsCyclic S ∧ ¬ 3 ∣ Nat.card S),
  AddMonoidHom.range (indK0 k S)

private theorem three_nsmul_one_mem_range_indK0_stabilizer (a : Fin 3) :
    3 • (1 : K₀) ∈ (indK0 k (MulAction.stabilizer G a)).range := by
  let H := MulAction.stabilizer G a
  have hA : indK0 k H 1 = 2 • (1 : K₀) + s :=
    indK0_one_stabilizer_perm_fin_three_char_three k a
  have hAs : indK0 k H (resK0 k H.subtype s) = (2 • (1 : K₀) + s) * s := by
    simpa only [one_mul, hA] using indK0_mul_resK0 (1 :
      ExactK0 (finiteModulesExactStructure k[H])) s
  have hs : s * s = 1 := by
    simpa only [symmetricThreeCharThreeSimpleClassBasis_true] using
      symmetricThreeCharThreeSimpleClassBasis_true_mul_self k
  refine ⟨(2 : ℤ) • 1 - resK0 k H.subtype s, ?_⟩
  rw [map_sub, map_zsmul, hA, hAs]
  simp only [two_nsmul, add_mul, one_mul, hs]
  module

/-- In characteristic three, induction from any point stabilizer of S₃ has image exactly
the virtual classes of dimension divisible by three. -/
-- Apply before membership in a homomorphism range expands to an existential.
@[simp↓]
theorem mem_range_indK0_stabilizer_perm_fin_three_char_three_iff (a : Fin 3) (x : K₀) :
    x ∈ (indK0 k (MulAction.stabilizer G a)).range ↔ (3 : ℤ) ∣ finrankK0 k k[G] x := by
  have hindex : (MulAction.stabilizer G a).index = 3 := by
    rw [MulAction.index_stabilizer_of_transitive]
    simp
  constructor
  · intro hx
    simpa only [hindex, Nat.cast_ofNat] using
      index_dvd_finrankK0_of_mem_range_indK0 (MulAction.stabilizer G a) hx
  · intro hx
    -- Expand in the two simple classes and read dimension as the sum of their coefficients.
    let b := symmetricThreeCharThreeSimpleClassBasis k
    have hdim : finrankK0 k k[G] s = 1 := by
      rw [finrankK0_fdRepK0RingEquiv_of, FDRep.finrank_ofLinearCharacter]
      norm_num
    have hex : x = b.repr x false • (1 : K₀) + b.repr x true • s := by
      simpa only [b, Fintype.sum_bool,
        symmetricThreeCharThreeSimpleClassBasis_false,
        symmetricThreeCharThreeSimpleClassBasis_true, add_comm] using (b.sum_repr x).symm
    have hd : finrankK0 k k[G] x = b.repr x false + b.repr x true := by
      simpa only [map_add, map_zsmul, finrankK0_one, hdim, smul_eq_mul, mul_one] using
        congrArg (finrankK0 k k[G]) hex
    obtain ⟨n, hn⟩ := hx
    have hcoeff : b.repr x false = 2 * b.repr x true + 3 * (n - b.repr x true) := by
      rw [hd] at hn
      omega
    -- The induced permutation class and three times the trivial class generate this lattice.
    have hA : 2 • (1 : K₀) + s ∈ (indK0 k (MulAction.stabilizer G a)).range :=
      ⟨1, indK0_one_stabilizer_perm_fin_three_char_three k a⟩
    have hthree := three_nsmul_one_mem_range_indK0_stabilizer k a
    have heq : x = b.repr x true • (2 • (1 : K₀) + s) +
        (n - b.repr x true) • (3 • (1 : K₀)) := by
      calc
        x = b.repr x false • (1 : K₀) + b.repr x true • s := hex
        _ = _ := by rw [hcoeff]; module
    rw [heq]
    exact AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ hA _)
      (AddSubgroup.zsmul_mem _ hthree _)

/-- The cyclic prime-to-three induction subgroup of S₃ consists exactly of the virtual
classes whose integral dimension is divisible by three. A single point stabilizer suffices. -/
@[simp]
theorem mem_iSup_range_indK0_cyclic_coprime_perm_fin_three_char_three_iff (x : K₀) :
    x ∈ I ↔ (3 : ℤ) ∣ finrankK0 k k[G] x := by
  constructor
  · intro hx
    have h := ordProj_dvd_finrankK0_of_mem_iSup_range_indK0 (k := k)
      (by decide : Nat.Prime 3) (fun S hS ↦ hS.2) hx
    have hg : Nat.card G = 6 := by
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    exact (Int.natCast_dvd_natCast.mpr (Nat.dvd_ordProj_of_dvd Nat.card_pos.ne'
      (by decide) (by rw [hg]; decide))).trans h
  · intro hx
    let H := MulAction.stabilizer G (0 : Fin 3)
    have hcard : Nat.card H = 2 := card_stabilizer_perm_fin_three 0
    have hH : IsCyclic H := isCyclic_of_prime_card (p := 2) hcard
    exact AddSubgroup.mem_iSup_of_mem H (AddSubgroup.mem_iSup_of_mem
      ⟨hH, by rw [hcard]; decide⟩
      ((mem_range_indK0_stabilizer_perm_fin_three_char_three_iff k 0 x).mpr hx))

/-- The induction subgroup is the kernel of dimension reduced modulo three. Thus its
quotient records exactly the dimension obstruction to prime-to-three cyclic induction. -/
theorem iSup_range_indK0_cyclic_coprime_perm_fin_three_char_three_eq_ker :
    I = ((Int.castAddHom (ZMod 3)).comp (finrankK0 k k[G])).ker := by
  ext x
  simp only [mem_iSup_range_indK0_cyclic_coprime_perm_fin_three_char_three_iff,
    AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, Int.coe_castAddHom,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

/-- The cyclic prime-to-three induction subgroup of S₃ has index three in its exact
Grothendieck group over every field of characteristic three. -/
theorem index_iSup_range_indK0_cyclic_coprime_perm_fin_three_char_three : (I).index = 3 := by
  rw [iSup_range_indK0_cyclic_coprime_perm_fin_three_char_three_eq_ker,
    AddSubgroup.index_ker]
  have hf : Function.Surjective ((Int.castAddHom (ZMod 3)).comp (finrankK0 k k[G])) := by
    intro z
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective z
    refine ⟨n • (1 : K₀), ?_⟩
    have hd : finrankK0 k k[G] (n • (1 : K₀)) = n := by
      rw [map_zsmul, finrankK0_one]
      simp
    simpa only [AddMonoidHom.comp_apply, hd, Int.coe_castAddHom] using hn
  rw [AddMonoidHom.range_eq_top.mpr hf]
  simp

/-- A multiple of the trivial S₃-class is induced from cyclic subgroups of order prime
to three exactly when its multiplier is divisible by three. In particular the least
positive multiplier is three, and the trivial class itself is not induced. -/
theorem nsmul_one_mem_iSup_range_indK0_cyclic_coprime_perm_fin_three_char_three_iff (n : ℕ) :
    n • (1 : K₀) ∈ I ↔ 3 ∣ n := by
  rw [mem_iSup_range_indK0_cyclic_coprime_perm_fin_three_char_three_iff,
    map_nsmul, finrankK0_one]
  simpa using (Int.natCast_dvd_natCast (m := 3) (n := n))

end TauCeti
