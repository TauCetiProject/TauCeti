/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Topology.Sheaves.Stalks

/-!
# No zero divisors in presheaf stalks

If sections on a basis of open neighborhoods of a point have no zero divisors, the stalk
has no zero divisors. This applies to concrete categories whose objects carry a multiplication
and a zero preserved by the morphisms, and whose forgetful functor preserves filtered colimits;
neither the absorption laws `0 * a = 0 = a * 0`, a unit, associativity, commutativity, an addition
nor the sheaf condition is needed.
-/

public section

open CategoryTheory CategoryTheory.Limits Filter Opposite TopologicalSpace Topology

universe u v

namespace TopCat.Presheaf

variable {C : Type u} [Category.{v} C] [HasColimits.{v} C]
  {FC : C → C → Type*} {CC : C → Type v}
  [∀ R S, FunLike (FC R S) (CC R) (CC S)] [ConcreteCategory C FC]
  [∀ R, Mul (CC R)] [∀ R, Zero (CC R)] [∀ R S, MulHomClass (FC R S) (CC R) (CC S)]
  [∀ R S, ZeroHomClass (FC R S) (CC R) (CC S)]
  [PreservesFilteredColimits (forget C)] {X : TopCat.{v}}

/-- A presheaf stalk has no zero divisors if sections on a neighborhood basis do. -/
theorem noZeroDivisors_stalk_of_hasBasis (F : X.Presheaf C) (x : X)
    {ι : Sort*} {p : ι → Prop} {U : ι → Opens X}
    (hB : (𝓝 x).HasBasis p (fun i ↦ (U i : Set X)))
    (hF : ∀ i, p i → NoZeroDivisors (ToType (F.obj (op (U i))))) :
    NoZeroDivisors (ToType (F.stalk x)) := ⟨by
  intro a b hab
  obtain ⟨V, hxV, s, rfl⟩ := F.exists_germ_eq a
  obtain ⟨W, hWV, hxW, t, rfl⟩ := F.exists_le_germ_eq b hxV
  rw [← F.germ_res_apply (homOfLE hWV) x hxW s, ← map_mul,
    ← map_zero (ConcreteCategory.hom (F.germ W x hxW))] at hab
  obtain ⟨N, hxN, iW, jW, hN⟩ := F.germ_eq x hxW hxW _ 0 hab
  obtain ⟨i, hi, hiN⟩ := hB.mem_iff.mp (N.isOpen.mem_nhds hxN)
  have hxi : x ∈ U i := mem_of_mem_nhds (hB.mem_of_mem hi)
  have := hF i hi
  let k : U i ⟶ W := homOfLE hiN ≫ iW
  have hmul : F.map k.op (F.map (homOfLE hWV).op s) * F.map k.op t = 0 := by
    rw [← map_mul]
    simp only [k, op_comp, F.map_comp, ConcreteCategory.comp_apply, hN, map_zero]
  refine (eq_zero_or_eq_zero_of_mul_eq_zero hmul).imp (fun hs ↦ ?_) fun ht ↦ ?_
  · rw [← F.germ_res_apply (homOfLE hWV) x hxW s, ← F.germ_res_apply k x hxi, hs, map_zero]
  · rw [← F.germ_res_apply k x hxi t, ht, map_zero]⟩

end TopCat.Presheaf
