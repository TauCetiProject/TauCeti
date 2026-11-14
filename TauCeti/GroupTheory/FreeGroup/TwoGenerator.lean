/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Data.ZMod.Basic
import TauCeti.GroupTheory.FreeGroup.Basis
import TauCeti.GroupTheory.FreeGroup.Centralizer
import TauCeti.GroupTheory.FreeGroup.Hopfian
import TauCeti.GroupTheory.FreeGroup.Rank

/-!
# Two noncommuting elements of a free group generate a free group of rank two

Let `a` and `b` be elements of a free group `F`. If they do not commute, the homomorphism
`FreeGroup (Fin 2) →* F` sending the two generators to `a` and `b` is injective, so `a` and `b`
freely generate the subgroup they generate. Together with the description of commuting pairs as
powers of a common element (`IsFreeGroup.commute_iff_exists_common_zpow`), this shows that a
two-generated subgroup of a free group is trivial, infinite cyclic, or free of rank two.

The proof is the classical one. The subgroup `H = ⟨a, b⟩` is free by the Nielsen–Schreier theorem,
say on a basis `ι`. As `H` is the image of `FreeGroup (Fin 2)`, the basis `ι` has at most two
elements (`FreeGroupBasis.card_le_of_surjective`). It has at least two since `H` is not
commutative (`FreeGroupBasis.nontrivial_of_not_commute`). Hence the surjection
`FreeGroup (Fin 2) →* H` is one between free groups of the same finite rank, and it is injective
because free groups of finite rank are Hopfian
(`FreeGroupBasis.injective_of_surjective_of_card_le`).

If `a` and `b` do not commute, their centralizers generate their free product: the homomorphism
`C_F(a) ∗ C_F(b) →* F` induced by the two inclusions is injective. Indeed both centralizers are
cyclic (`IsFreeGroup.isCyclic_centralizer`), and their generators do not commute, so they freely
generate a free group of rank two.

For distinct basis elements `a` and `b` of a free group and `n ≠ 0`, the elements `aⁿ` and `b` do
not commute, so they freely generate the subgroup `⟨aⁿ, b⟩`. For `n ≠ 1` this subgroup does not
contain `a`, as it lies in the kernel of the map to `ℤ/n` sending `a` to `1` and the other basis
elements to `0`.

## Main results

* `FreeGroup.not_commute_of_injective_lift`: two elements of any group that freely generate a free
  group of rank two do not commute.
* `IsFreeGroup.injective_lift_iff_not_commute`: the homomorphism `FreeGroup (Fin 2) →* F` sending
  the generators to `a` and `b` is injective if and only if `a` and `b` do not commute.
* `IsFreeGroup.injective_lift_centralizer_subtype`: the centralizers of two elements of a free
  group that do not commute generate their free product.
* `FreeGroup.injective_lift_of_pow_of_ne`: for distinct basis elements `a`, `b` and `n ≠ 0`, the
  elements `aⁿ` and `b` freely generate a free group of rank two.
* `FreeGroup.of_notMem_closure_of_pow_of_ne`: for distinct basis elements `a`, `b` and `n ≠ 1`,
  the subgroup `⟨aⁿ, b⟩` does not contain `a`.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial group theory*, Springer (1977), Chapter I.
* A. I. Malcev, *On isomorphic matrix representations of infinite groups*, Mat. Sb. 8 (50)
  (1940), 405–422.
* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §5, proof of
  Lemma 21 (centralizers of noncommuting elements of a free group generate their free product).
-/

public section

/-- Two elements of a group that freely generate a free group of rank two do not commute, since
the two generators of `FreeGroup (Fin 2)` do not. -/
theorem FreeGroup.not_commute_of_injective_lift {G : Type*} [Group G] {a b : G}
    (h : Function.Injective (FreeGroup.lift ![a, b])) : ¬Commute a b := fun hab => by
  have : Commute (FreeGroup.of (0 : Fin 2)) (FreeGroup.of 1) := h (by simpa using hab.eq)
  exact absurd (FreeGroup.eq_of_commute_of_of this) (by decide)

namespace IsFreeGroup

variable {F : Type*} [Group F] [IsFreeGroup F]

/-- **Two noncommuting elements of a free group freely generate a free group of rank two.** -/
theorem injective_lift_of_not_commute {a b : F} (h : ¬Commute a b) :
    Function.Injective (FreeGroup.lift ![a, b]) := by
  set φ := FreeGroup.lift ![a, b]
  have hsurj : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  -- The range of `φ` is free by the Nielsen–Schreier theorem, on a basis of at least two elements.
  have := (basis φ.range).finite_of_surjective hsurj
  have hge : ¬Nat.card (Generators φ.range) ≤ 1 := by
    rw [Finite.card_le_one_iff_subsingleton, not_subsingleton_iff_nontrivial]
    exact (basis φ.range).nontrivial_of_not_commute (x := ⟨a, FreeGroup.of 0, by simp [φ]⟩)
      (y := ⟨b, FreeGroup.of 1, by simp [φ]⟩) fun hc => h (congrArg Subtype.val hc.eq)
  -- A surjection between free groups of the same finite rank is injective.
  exact MonoidHom.rangeRestrict_injective_iff.mp <|
    (basis φ.range).injective_of_surjective_of_card_le hsurj (by rw [Nat.card_fin]; omega)

/-- Elements `a` and `b` of a free group freely generate a free group of rank two if and only if
they do not commute. -/
theorem injective_lift_iff_not_commute {a b : F} :
    Function.Injective (FreeGroup.lift ![a, b]) ↔ ¬Commute a b :=
  ⟨FreeGroup.not_commute_of_injective_lift, injective_lift_of_not_commute⟩

open Subgroup in
/-- **Centralizers of noncommuting elements of a free group generate their free product.** If `x`
and `y` do not commute, the homomorphism `C_F(x) ∗ C_F(y) →* F` induced by the inclusions of the
two centralizers is injective. -/
theorem injective_lift_centralizer_subtype {x y : F} (hxy : ¬Commute x y) :
    Function.Injective
      (Monoid.Coprod.lift (centralizer {x}).subtype (centralizer {y}).subtype) := by
  -- The centralizers are cyclic, generated by `r` and `r'`, which do not commute.
  obtain ⟨r, hr⟩ := (isCyclic_centralizer (x := x)
    (by rintro rfl; exact hxy (.one_left y))).exists_generator
  obtain ⟨r', hr'⟩ := (isCyclic_centralizer (x := y)
    (by rintro rfl; exact hxy (.one_right x))).exists_generator
  have hrr' : ¬Commute (r : F) r' := fun hc => by
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 (hr ⟨x, mem_centralizer_singleton_iff.2 rfl⟩)
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 (hr' ⟨y, mem_centralizer_singleton_iff.2 rfl⟩)
    have hx : (r : F) ^ m = x := by simpa using congrArg Subtype.val hm
    have hy : (r' : F) ^ n = y := by simpa using congrArg Subtype.val hn
    exact hxy (hx ▸ hy ▸ hc.zpow_zpow m n)
  -- `FreeGroup (Fin 2) → ⟨r⟩ ∗ ⟨r'⟩` is onto, and its composite with the lift is injective.
  let ψ := FreeGroup.lift ![Monoid.Coprod.inl r, Monoid.Coprod.inr r']
  have hcomp : (Monoid.Coprod.lift (centralizer {x}).subtype (centralizer {y}).subtype).comp ψ =
      FreeGroup.lift ![(r : F), r'] := by
    ext i
    fin_cases i <;> simp [ψ]
  refine Function.Injective.of_comp_right (g := ψ) ?_ ?_
  · rw [← MonoidHom.coe_comp, hcomp]
    exact injective_lift_of_not_commute hrr'
  · rw [← MonoidHom.range_eq_top, eq_top_iff, ← Monoid.Coprod.range_inl_sup_range_inr,
      sup_le_iff]
    constructor
    · rintro _ ⟨a, rfl⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 (hr a)
      exact ⟨FreeGroup.of 0 ^ k, by simp [ψ]⟩
    · rintro _ ⟨a, rfl⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 (hr' a)
      exact ⟨FreeGroup.of 1 ^ k, by simp [ψ]⟩

end IsFreeGroup

namespace FreeGroup

variable {α : Type*} {a b : α} {n : ℕ}

/-- For distinct basis elements `a` and `b` of a free group and `n ≠ 0`, the elements `aⁿ` and `b`
freely generate a free group of rank two; its image is the subgroup `⟨aⁿ, b⟩`
(`FreeGroup.range_lift_eq_closure`). -/
theorem injective_lift_of_pow_of_ne (hab : a ≠ b) (hn : n ≠ 0) :
    Function.Injective (FreeGroup.lift ![of a ^ n, of b]) := by
  -- An element commuting with `b` is a power of `b`, and `aⁿ = bᵐ` forces `n = 0`.
  refine IsFreeGroup.injective_lift_of_not_commute fun h => ?_
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_of_commute h)
  have := eq_of_of_zpow_eq_of_zpow hab (n := n) (m := m) (by simpa using hm.symm)
  lia

/-- For distinct basis elements `a` and `b` of a free group and `n ≠ 1`, the element `a` does not
lie in the subgroup `⟨aⁿ, b⟩`. -/
theorem of_notMem_closure_of_pow_of_ne (hab : a ≠ b) (hn : n ≠ 1) :
    of a ∉ Subgroup.closure {of a ^ n, of b} := by
  classical
  -- `⟨aⁿ, b⟩` lies in the kernel of the map to `ℤ/n` sending `a` to `1` and the other basis
  -- elements to `0`, and `a` does not.
  let χ : FreeGroup α →* Multiplicative (ZMod n) :=
    FreeGroup.lift fun c => if c = a then Multiplicative.ofAdd 1 else 1
  have hle : Subgroup.closure {of a ^ n, of b} ≤ χ.ker := by
    simp [Subgroup.closure_le, Set.insert_subset_iff, χ, hab.symm, ← ofAdd_nsmul]
  exact fun h => absurd (hle h) (by simp [χ, ZMod.one_eq_zero_iff, hn])

end FreeGroup
