/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Subgroup.Simple
public import TauCeti.GroupTheory.Automorphism.PrimeOrder

/-!
# Simplicity from simple point stabilizers

In a faithful primitive action with a simple point stabilizer, a proper nontrivial
normal subgroup acts regularly. Conjugation then embeds the point stabilizer in the
automorphism group of that normal subgroup.

For degree `p + 1`, a prime-order obstruction can exclude this possibility.
-/

public section

namespace MulAction

variable {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]

/-- A point stabilizer acts faithfully by conjugation on a transitive normal subgroup. -/
theorem stabilizer_conjNormal_injective (N : Subgroup G) [N.Normal]
    [IsPretransitive N X] (x : X) :
    Function.Injective ((MulAut.conjNormal (H := N)).comp (stabilizer G x).subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro h hh
  change h = 1
  change MulAut.conjNormal (H := N) (h : G) = 1 at hh
  apply Subtype.ext
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro y
  obtain ⟨n, rfl⟩ := exists_smul_eq N x y
  have hcomm : (h : G) * (n : G) = (n : G) * (h : G) := by
    have hc := congrArg (fun f : MulAut N ↦ ((f n : N) : G)) hh
    simpa only [MulAut.conjNormal_apply, MulAut.one_apply,
      mul_inv_eq_iff_eq_mul] using hc
  change (h : G) • ((n : G) • x) = (1 : G) • ((n : G) • x)
  rw [← mul_smul, hcomm, mul_smul, mem_stabilizer_iff.mp h.property, one_smul]

end MulAction

namespace TauCeti

open MulAction

/-- A primitive group with a simple point stabilizer is simple if that stabilizer cannot
embed in the automorphism group of a regular normal subgroup. -/
theorem isSimpleGroup_of_simple_stabilizer
    {G X : Type*} [Group G] [Nontrivial G]
    [MulAction G X] [FaithfulSMul G X] [IsPreprimitive G X]
    (x : X) [IsSimpleGroup (stabilizer G x)]
    (hAut : ∀ (N : Subgroup G) [N.Normal], Nat.card N = Nat.card X →
      ¬ Function.Injective ((MulAut.conjNormal (H := N)).comp (stabilizer G x).subtype)) :
    IsSimpleGroup G := by
  refine ⟨fun N _ ↦ ?_⟩
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  have hfixed : fixedPoints N X ≠ Set.univ := by
    intro h
    apply hN
    apply bot_unique
    intro n hn
    change n = 1
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro y
    have hy : y ∈ fixedPoints N X := by rw [h]; trivial
    simpa only [one_smul, subgroup_smul_def] using (mem_fixedPoints.mp hy ⟨n, hn⟩)
  have : IsPretransitive N X := IsQuasiPreprimitive.isPretransitive_of_normal hfixed
  rcases Subgroup.Normal.eq_bot_or_eq_top (N.comap (stabilizer G x).subtype) with hi | hi
  · have hregular : Function.Injective (fun n : N ↦ n • x) := by
      intro a b hab
      change a • x = b • x at hab
      have hs : ((b⁻¹ * a : N) : G) ∈ stabilizer G x := by
        rw [mem_stabilizer_iff]
        change (b⁻¹ * a : N) • x = x
        rw [mul_smul, hab, inv_smul_smul]
      have hm : (⟨((b⁻¹ * a : N) : G), hs⟩ : stabilizer G x) ∈
          N.comap (stabilizer G x).subtype := (b⁻¹ * a).property
      rw [hi, Subgroup.mem_bot] at hm
      have hm' : b⁻¹ * a = 1 := by
        apply Subtype.ext
        exact congrArg (fun k : stabilizer G x ↦ (k : G)) hm
      exact (inv_mul_eq_one.mp hm').symm
    have hcard : Nat.card N = Nat.card X :=
      Nat.card_congr (Equiv.ofBijective (fun n : N ↦ n • x)
        ⟨hregular, fun y ↦ exists_smul_eq N x y⟩)
    exact False.elim (hAut N hcard (stabilizer_conjNormal_injective N x))
  · apply top_unique
    intro g _
    obtain ⟨n, hn⟩ := exists_smul_eq N x (g • x)
    have hs : (n : G)⁻¹ * g ∈ stabilizer G x := by
      rw [mem_stabilizer_iff, mul_smul, ← hn]
      exact inv_smul_smul (n : G) x
    have hm : (⟨(n : G)⁻¹ * g, hs⟩ : stabilizer G x) ∈
        N.comap (stabilizer G x).subtype := by rw [hi]; trivial
    have hg := N.mul_mem n.property hm
    change (n : G) * ((n : G)⁻¹ * g) ∈ N at hg
    simpa only [mul_inv_cancel_left] using hg

/-- A prime-order element in a simple stabilizer excludes regular normal subgroups when
the degree is one more than that prime and has two distinct prime divisors. -/
theorem isSimpleGroup_of_simple_stabilizer_prime
    {G X : Type*} [Group G] [Nontrivial G] [Finite G]
    [MulAction G X] [FaithfulSMul G X] [IsPreprimitive G X]
    (x : X) [IsSimpleGroup (stabilizer G x)]
    {p q r : ℕ} (hp : p.Prime) (hcard : Nat.card X = p + 1)
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hqdvd : q ∣ Nat.card X) (hrdvd : r ∣ Nat.card X)
    (a : stabilizer G x) (ha : orderOf a = p) : IsSimpleGroup G := by
  apply isSimpleGroup_of_simple_stabilizer x
  intro N _ hN hinj
  let f := (MulAut.conjNormal (H := N)).comp (stabilizer G x).subtype
  have hf : orderOf (f a) = p := (orderOf_injective f hinj a).trans ha
  exact MulAut.orderOf_ne_prime_of_card_eq_succ (f a) hp (hN.trans hcard)
    hq hr hqr (hN ▸ hqdvd) (hN ▸ hrdvd) hf

end TauCeti
