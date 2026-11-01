/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.GroupTheory.Index

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.GroupTheory.Perm.Cycle.Type
import TauCeti.GroupTheory.Index.Quotient

/-!
# Cokernels and primary components over a uniquely `n`-divisible subgroup of finite index

Let `G` be a commutative group and `n` a natural number, and write `G[n^∞]` for Mathlib's
`AddCommGroup.primaryComponent G n`, the subgroup of elements killed by some power of `n` (`n`
need not be prime). Suppose that `G` has a subgroup `U` of finite index on which multiplication by
`n` is bijective, as for the points of an elliptic curve over a local field, where `U` is the
kernel of reduction and `n` is prime to the residue characteristic. Then:

* `G[n^∞]` is finite, since it meets `U` trivially and so embeds in `G ⧸ U`;
* `G = n G + G[n^∞]`: every element is divisible by `n` up to an element of `G[n^∞]`.

Consequently, if `f : A → B` and `g : B → A` are homomorphisms of commutative groups with
`g ∘ f = n` and `f ∘ g = n`, and `B` has such a subgroup, then the cokernel of `f` is accounted for
by the `n`-primary components alone:

`[B : f(A)] · #A[n^∞] = #B[n^∞] · #ker(f)`.

For an isogeny `φ` of elliptic curves with dual `φ̂` and `n = deg φ`, this computes the ratio
`#coker(φ) / #ker(φ)` on local points at a place not dividing `deg φ`.

For a finite commutative group `A`, the order of `A[n^∞]` is the `n`-part of `#A`: its prime
factors divide `n`, and the index `[A : A[n^∞]]` is prime to `n` (both by Cauchy's theorem). So
finite groups of the same order have `n`-primary components of the same order.

## Main results

* `AddSubgroup.finite_primaryComponent_of_injective`: `G[n^∞]` is finite when `n` acts injectively
  on a subgroup of finite index.
* `AddSubgroup.range_nsmul_sup_primaryComponent_eq_top_of_surjective`: `n G + G[n^∞] = G` when `n`
  acts surjectively on a subgroup of finite index.
* `AddMonoidHom.index_range_mul_card_primaryComponent`: the cokernel formula above.
* `AddCommGroup.coprime_index_primaryComponent`: `[A : A[n^∞]]` is prime to `n`.
* `AddCommGroup.dvd_of_prime_dvd_natCard_primaryComponent`: a prime dividing `#A[n^∞]` divides `n`.
* `AddCommGroup.natCard_primaryComponent_dvd_of_natCard_dvd` and
  `AddCommGroup.natCard_primaryComponent_eq_of_natCard_eq`: for finite groups, `#A[n^∞]` only
  depends on `#A`.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.6 and X.4.
-/

public section

namespace AddSubgroup

variable {G : Type*} [AddCommGroup G]

/-- **The `n`-primary component is finite** when `n` acts injectively on a subgroup `U` of finite
index: it meets `U` trivially, so it embeds in the finite quotient `G ⧸ U`. -/
theorem finite_primaryComponent_of_injective (U : AddSubgroup G) [U.FiniteIndex] {n : ℕ}
    (hU : Function.Injective (fun x : U ↦ n • x)) :
    Finite (AddCommGroup.primaryComponent G n) := by
  refine Finite.of_injective (fun x ↦ ((x : G) : G ⧸ U)) fun x y h ↦ ?_
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp (sub_mem x.2 y.2)
  have : (⟨(x : G) - y, QuotientAddGroup.eq_iff_sub_mem.mp h⟩ : U) = 0 :=
    (smul_iterate (α := U) n k ▸ hU.iterate k) (Subtype.ext (by simpa using hk))
  exact Subtype.ext (sub_eq_zero.mp (congrArg Subtype.val this))

/-- **Divisibility up to the `n`-primary component**: if `n` acts surjectively on a subgroup `U` of
finite index, then `n G + G[n^∞] = G`. -/
theorem range_nsmul_sup_primaryComponent_eq_top_of_surjective (U : AddSubgroup G) [U.FiniteIndex]
    {n : ℕ} (hU : Function.Surjective (fun x : U ↦ n • x)) :
    (nsmulAddMonoidHom (α := G) n).range ⊔
      AddCommGroup.primaryComponent G n = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  -- in the finite quotient `G ⧸ U`, two of the classes of `nᵏ x` coincide
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ ↦ ((n ^ k • x : G) : G ⧸ U))
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm h.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
  -- so `nⁱ (x - n c) ∈ U` for `c = n^(j - i - 1) x`
  set c := n ^ (j - i - 1) • x
  have hmem : n ^ i • (x - n • c) ∈ U := by
    have hj : n ^ j • x = n ^ i • (n • c) := by
      rw [← mul_nsmul, ← mul_nsmul, ← pow_succ', ← pow_add]
      congr 2
      omega
    rw [nsmul_sub, ← hj, ← neg_sub, neg_mem_iff, ← QuotientAddGroup.eq_iff_sub_mem]
    exact h.symm
  -- write that element of `U` as `nⁱ d` with `d ∈ U`, and `d` as `n e` with `e ∈ U`
  obtain ⟨d, hd⟩ := (smul_iterate (α := U) n i ▸ hU.iterate i) ⟨_, hmem⟩
  obtain ⟨e, rfl⟩ := hU d
  have hd' : n ^ i • (x - n • c - n • (e : G)) = 0 := by
    have h' := congrArg Subtype.val hd
    simp only [AddSubgroup.coe_nsmul] at h'
    rw [nsmul_sub, ← h', sub_self]
  have hx : x = n • (c + e) + (x - n • c - n • (e : G)) := by
    rw [nsmul_add, sub_sub, add_sub_cancel]
  rw [hx]
  exact add_mem (mem_sup_left ⟨c + e, rfl⟩)
    (mem_sup_right (AddCommGroup.mem_primaryComponent.mpr ⟨i, hd'⟩))

end AddSubgroup

namespace AddMonoidHom

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- **The cokernel of a homomorphism invertible up to `n`**: let `f : A →+ B` and `g : B →+ A`
satisfy `g ∘ f = n` and `f ∘ g = n`, and suppose that `n` acts surjectively on a subgroup of
finite index of `B`. Then

`[B : f(A)] · #A[n^∞] = #B[n^∞] · #ker(f)`,

where `A[n^∞]` and `B[n^∞]` are the `n`-primary components. No finiteness is assumed of the
other quantities: infinite orders and indices are read as `0`. -/
theorem index_range_mul_card_primaryComponent (f : A →+ B) (g : B →+ A) {n : ℕ}
    (hgf : ∀ a, g (f a) = n • a) (hfg : ∀ b, f (g b) = n • b) (U : AddSubgroup B) [U.FiniteIndex]
    (hU : Function.Surjective (fun x : U ↦ n • x)) :
    f.range.index * Nat.card (AddCommGroup.primaryComponent A n) =
      Nat.card (AddCommGroup.primaryComponent B n) * Nat.card f.ker := by
  set T := AddCommGroup.primaryComponent B n
  -- the inverse image of `B[n^∞]` is `A[n^∞]`
  have hcomap : T.comap f = AddCommGroup.primaryComponent A n := by
    ext a
    rw [AddSubgroup.mem_comap, AddCommGroup.mem_primaryComponent,
      AddCommGroup.mem_primaryComponent]
    refine ⟨fun ⟨k, hk⟩ ↦ ⟨k + 1, ?_⟩, fun ⟨k, hk⟩ ↦ ⟨k, by rw [← map_nsmul, hk, map_zero]⟩⟩
    rw [pow_succ, mul_nsmul, ← hgf, map_nsmul, hk, map_zero]
  -- the image of `f` together with `B[n^∞]` is everything, as `f(A)` contains `n B`
  have hsup : f.range ⊔ T = ⊤ := by
    refine eq_top_iff.mpr ((U.range_nsmul_sup_primaryComponent_eq_top_of_surjective hU).ge.trans
      (sup_le_sup_right ?_ _))
    rintro _ ⟨b, rfl⟩
    exact ⟨g b, hfg b⟩
  have hmap : (f.range.map (QuotientAddGroup.mk' T)).index = 1 := by
    rw [AddSubgroup.index_map, QuotientAddGroup.ker_mk', hsup]
    simp [range_eq_top_of_surjective _ (QuotientAddGroup.mk'_surjective T)]
  have h := TauCeti.index_range_mul_card_comap (f := f) (S := T)
  rw [hcomap, hmap, one_mul] at h
  exact h

end AddMonoidHom

namespace AddCommGroup

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- **The index of the `n`-primary component is prime to `n`** whenever it is finite. -/
theorem coprime_index_primaryComponent (n : ℕ) [(primaryComponent A n).FiniteIndex] :
    (primaryComponent A n).index.Coprime n := by
  -- a prime `p ∣ n` dividing the index is the order of a class `x` modulo `A[n^∞]` (Cauchy), but
  -- then `p x`, hence `n x`, lies in `A[n^∞]`, and so does `x`
  refine Nat.coprime_of_dvd fun p hp hpi hpn ↦ ?_
  have := Fact.mk hp
  rw [AddSubgroup.index_eq_card] at hpi
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hpi
  induction x using QuotientAddGroup.induction_on with | H x => ?_
  obtain ⟨m, rfl⟩ := hpn
  obtain ⟨k, hk⟩ := mem_primaryComponent.mp <| (QuotientAddGroup.eq_zero_iff (p • x)).mp <| by
    rw [QuotientAddGroup.mk_nsmul, ← hx, addOrderOf_nsmul_eq_zero]
  have hx0 : (x : A ⧸ primaryComponent A (p * m)) = 0 :=
    (QuotientAddGroup.eq_zero_iff x).mpr <| mem_primaryComponent.mpr ⟨k + 1, by
      have : (p * m) ^ (k + 1) • x = m • (p * m) ^ k • p • x := by
        rw [smul_smul, smul_smul]
        ring_nf
      rw [this, hk, nsmul_zero]⟩
  rw [hx0, addOrderOf_zero] at hx
  exact hp.one_lt.ne hx

/-- **The order of the `n`-primary component has only prime factors dividing `n`** whenever it is
finite. -/
theorem dvd_of_prime_dvd_natCard_primaryComponent {n p : ℕ} [Finite (primaryComponent A n)]
    (hp : p.Prime) (h : p ∣ Nat.card (primaryComponent A n)) : p ∣ n := by
  have := Fact.mk hp
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p h
  obtain ⟨k, hk⟩ := mem_primaryComponent.mp x.2
  refine hp.dvd_of_dvd_pow (n := k) ?_
  rw [← hx]
  exact addOrderOf_dvd_of_nsmul_eq_zero (Subtype.ext hk)

/-- **The order of the `n`-primary component is monotone in the order of the group**: if
`#A ∣ #B` for finite commutative groups, then `#A[n^∞] ∣ #B[n^∞]`. -/
theorem natCard_primaryComponent_dvd_of_natCard_dvd [Finite A] [Finite B]
    (h : Nat.card A ∣ Nat.card B) (n : ℕ) :
    Nat.card (primaryComponent A n) ∣ Nat.card (primaryComponent B n) := by
  -- `#A[n^∞]` divides `#B = #B[n^∞] · [B : B[n^∞]]` and is prime to the index
  have hcop : (Nat.card (primaryComponent A n)).Coprime (primaryComponent B n).index :=
    Nat.coprime_of_dvd fun p hp hpA hpB ↦ hp.not_dvd_one <|
      (coprime_index_primaryComponent (A := B) n).gcd_eq_one ▸
        Nat.dvd_gcd hpB (dvd_of_prime_dvd_natCard_primaryComponent hp hpA)
  refine hcop.dvd_of_dvd_mul_right ?_
  rw [AddSubgroup.card_mul_index]
  exact (AddSubgroup.card_addSubgroup_dvd_card _).trans h

/-- **Finite commutative groups of the same order have `n`-primary components of the same
order.** -/
theorem natCard_primaryComponent_eq_of_natCard_eq [Finite A] [Finite B]
    (h : Nat.card A = Nat.card B) (n : ℕ) :
    Nat.card (primaryComponent A n) = Nat.card (primaryComponent B n) :=
  Nat.dvd_antisymm (natCard_primaryComponent_dvd_of_natCard_dvd h.dvd n)
    (natCard_primaryComponent_dvd_of_natCard_dvd h.symm.dvd n)

end AddCommGroup
