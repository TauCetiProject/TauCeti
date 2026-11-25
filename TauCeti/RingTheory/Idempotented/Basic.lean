/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Data.Finsupp.Pointwise
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.Algebra.Algebra.Unitization

/-!
# Idempotented algebras and their nondegenerate modules

A (not necessarily unital) ring `H` is *idempotented*, or *locally unital*, if every finite subset
of `H` admits an idempotent `e` with `e * x = x = x * e` for all `x` in the subset. Such an `H` is
the union of its corner rings `eHe`, each of which is unital with unit `e`. The basic example is
the Hecke algebra of locally constant compactly supported functions on a locally profinite group
with coefficients in a ring `A` in which the pro-orders of small compact open subgroups are
invertible: its local units are the normalised characteristic functions of those subgroups, and
its nondegenerate modules are the smooth representations of the group over `A`.

A left module over a nonunital `A`-algebra `H` is the same as a unital module over its forced
unitization `Unitization A H = A ⊕ H`, and we work with the latter. Such a module `M` is
*nondegenerate* if `H • M = M`. When `H` is idempotented this means that every `m : M` has a local
unit, an idempotent `e : H` with `e • m = m`, and then every finite subset of `M` has a common local
unit.

## Main definitions

* `TauCeti.IsIdempotented H`: every finite subset of `H` has an idempotent two-sided local unit.
* `TauCeti.nondegeneratePart A H M`: the submodule `H • M` spanned by the elements `h • m`.
* `TauCeti.IsNondegenerate A H M`: the module `M` satisfies `H • M = M`.

## Main results

* `TauCeti.IsIdempotented.iUnion_corner`: an idempotented ring is the union of its corners `eHe`,
  and these form a directed family (`TauCeti.IsIdempotented.directed_corner`).
* `TauCeti.IsIdempotented.subsingleton_of_mul_eq_zero`: a nontrivial ring with the zero
  multiplication is not idempotented.
* `TauCeti.mem_nondegeneratePart_iff`: over an idempotented `H`, the elements of `H • M` are
  exactly those fixed by some idempotent of `H`.
* `TauCeti.IsNondegenerate.exists_isIdempotentElem_forall_smul_eq`: finitely many elements of a
  nondegenerate module have a common idempotent local unit.
* `TauCeti.inl_smul_eq_inr_smul`: the scalar `a : A` acts on `m` as `a • e` for any local unit
  `e` of `m`. Hence (`TauCeti.IsNondegenerate.map_smul_of_map_inr_smul`) an additive map out of a
  nondegenerate module commuting with the action of `H` is linear over `Unitization A H`.
* `TauCeti.IsNondegenerate.of_injective`, `TauCeti.IsNondegenerate.of_surjective`: submodules
  and quotients of nondegenerate modules are nondegenerate.
* `TauCeti.isNondegenerate_iff_le_nondegeneratePart`: `H • M` is the largest nondegenerate
  submodule of `M`.
* `TauCeti.isNondegenerate_span_singleton`: the principal left ideals `He` are nondegenerate.

## References

* J. N. Bernstein, *Draft of: Representations of p-adic groups*, lectures written by K. E. Rumelhart
  (1992), Chapter I, §2.1.
* J. N. Bernstein, *Le "centre" de Bernstein*, edited by P. Deligne, in *Représentations des groupes
  réductifs sur un corps local*, Hermann, Paris (1984), §1.1–§1.2.
-/

public section

namespace TauCeti

/-- A multiplicative structure `H` is *idempotented* (or *locally unital*) if every finite subset
of `H` has a two-sided local unit which is idempotent: an `e` with `e * e = e` and
`e * x = x = x * e` for every `x` in the subset. -/
class IsIdempotented (H : Type*) [Mul H] : Prop where
  /-- Every finite subset has an idempotent two-sided local unit. -/
  exists_isIdempotentElem (s : Finset H) :
    ∃ e : H, IsIdempotentElem e ∧ ∀ x ∈ s, e * x = x ∧ x * e = x

namespace IsIdempotented

/-- A unital multiplicative structure is idempotented, with local unit `1`. -/
instance (priority := 100) of_mulOneClass (H : Type*) [MulOneClass H] : IsIdempotented H :=
  ⟨fun _ ↦ ⟨1, .one, fun x _ ↦ ⟨one_mul x, mul_one x⟩⟩⟩

variable {H : Type*} [Semigroup H] [IsIdempotented H]

/-- Every finite subset of an idempotented semigroup lies in the corner `eHe` of an idempotent. -/
theorem exists_subset_corner (s : Finset H) :
    ∃ e : H, IsIdempotentElem e ∧ (s : Set H) ⊆ Subsemigroup.corner e := by
  obtain ⟨e, he, hs⟩ := exists_isIdempotentElem s
  exact ⟨e, he, fun x hx ↦ (Subsemigroup.mem_corner_iff he).2 (hs x hx)⟩

/-- An idempotented semigroup is the union of its corners `eHe` over all idempotents `e`. -/
theorem iUnion_corner :
    ⋃ e : {e : H // IsIdempotentElem e}, (Subsemigroup.corner e.val : Set H) = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ?_
  obtain ⟨e, he, hx⟩ := exists_subset_corner {x}
  exact ⟨⟨e, he⟩, hx (by simp)⟩

/-- The corners `eHe` of an idempotented semigroup form a directed family. -/
theorem directed_corner :
    Directed (· ≤ ·) fun e : {e : H // IsIdempotentElem e} ↦ Subsemigroup.corner e.val := by
  classical
  rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩
  obtain ⟨f, hf, hs⟩ := exists_isIdempotentElem {e₁, e₂}
  have key : ∀ e, IsIdempotentElem e → f * e = e ∧ e * f = e →
      Subsemigroup.corner e ≤ Subsemigroup.corner f := by
    rintro e he ⟨hl, hr⟩ x hx
    obtain ⟨hxl, hxr⟩ := (Subsemigroup.mem_corner_iff he).1 hx
    refine (Subsemigroup.mem_corner_iff hf).2 ⟨?_, ?_⟩
    · rw [← hxl, ← mul_assoc, hl]
    · rw [← hxr, mul_assoc, hr]
  exact ⟨⟨f, hf⟩, key e₁ he₁ (hs e₁ (by simp)), key e₂ he₂ (hs e₂ (by simp))⟩

/-- An idempotented structure with zero multiplication is trivial: every `x` equals `e * x = 0`
for a local unit `e`. In particular a nonzero ring with the zero multiplication is not
idempotented. -/
theorem subsingleton_of_mul_eq_zero {H : Type*} [Mul H] [Zero H] [IsIdempotented H]
    (h : ∀ x y : H, x * y = 0) : Subsingleton H := by
  classical
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨e, -, he⟩ := exists_isIdempotentElem {x, y}
  rw [← (he x (by simp)).1, ← (he y (by simp)).1, h, h]

end IsIdempotented

/-- Finitely supported functions `ι →₀ R`, for `R` with `0` and `1`, are idempotented under
pointwise multiplication: the indicator function of a finite set containing the supports is a
local unit. When `R` is a ring, `ι →₀ R` is a nonunital ring, which has no unit when `ι` is
infinite and `R` is nontrivial. -/
instance (ι R : Type*) [MulZeroOneClass R] : IsIdempotented (ι →₀ R) := by
  classical
  refine ⟨fun s ↦ ⟨Finsupp.indicator (s.biUnion Finsupp.support) fun _ _ ↦ 1, ?_, ?_⟩⟩
  · ext i
    simp only [Finsupp.mul_apply, Finsupp.indicator_apply]
    split_ifs <;> simp
  · intro x hx
    have key : ∀ i, (Finsupp.indicator (s.biUnion Finsupp.support) fun _ _ ↦ (1 : R)) i = 1 ∨
        x i = 0 := by
      intro i
      rw [Finsupp.indicator_apply]
      split_ifs with hi
      · exact .inl rfl
      · exact .inr (Finsupp.notMem_support_iff.1 fun h ↦ hi (Finset.mem_biUnion.2 ⟨x, hx, h⟩))
    refine ⟨Finsupp.ext fun i ↦ ?_, Finsupp.ext fun i ↦ ?_⟩ <;>
      rcases key i with h | h <;> simp [Finsupp.mul_apply, h]

section Module

variable (A H : Type*) [CommSemiring A] [NonUnitalSemiring H] [Module A H]
  [IsScalarTower A H H] [SMulCommClass A H H]
  (M : Type*) [AddCommMonoid M] [Module (Unitization A H) M]

open Pointwise in
/-- The *nondegenerate part* `H • M` of a module `M` over the unitization `A ⊕ H` of a nonunital
`A`-algebra `H`: the submodule spanned by the elements `h • m` with `h : H` and `m : M`, that is,
the pointwise action of `H ⊆ A ⊕ H` on the submodule `⊤`. -/
def nondegeneratePart : Submodule (Unitization A H) M :=
  Set.range (Unitization.inr : H → Unitization A H) • (⊤ : Submodule (Unitization A H) M)

/-- A module `M` over the unitization `A ⊕ H` of a nonunital `A`-algebra `H` is *nondegenerate*
if `H • M = M`. -/
def IsNondegenerate : Prop :=
  nondegeneratePart A H M = ⊤

variable {A H M}

/-- A module is nondegenerate exactly when `H • M = M`. -/
theorem isNondegenerate_iff_nondegeneratePart_eq_top :
    IsNondegenerate A H M ↔ nondegeneratePart A H M = ⊤ :=
  Iff.rfl

/-- In a nondegenerate module `M`, the submodule `H • M` is everything. -/
theorem IsNondegenerate.nondegeneratePart_eq_top (hM : IsNondegenerate A H M) :
    nondegeneratePart A H M = ⊤ :=
  hM

/-- Every element `h • m` lies in `H • M`. -/
@[simp]
theorem inr_smul_mem_nondegeneratePart (h : H) (m : M) :
    (h : Unitization A H) • m ∈ nondegeneratePart A H M :=
  Submodule.mem_set_smul_of_mem_mem ⟨h, rfl⟩ Submodule.mem_top

/-- `H • M` is contained in a submodule `N` exactly when `N` contains every `h • m`. -/
theorem nondegeneratePart_le_iff {N : Submodule (Unitization A H) M} :
    nondegeneratePart A H M ≤ N ↔ ∀ (h : H) (m : M), (h : Unitization A H) • m ∈ N := by
  rw [nondegeneratePart, Submodule.set_smul_le_iff]
  exact ⟨fun hN h m ↦ hN ⟨h, rfl⟩ Submodule.mem_top, fun hN _ m ⟨h, hh⟩ _ ↦ hh ▸ hN h m⟩

/-- The nondegenerate part vanishes exactly when `H` acts by zero. -/
theorem nondegeneratePart_eq_bot_iff :
    nondegeneratePart A H M = ⊥ ↔ ∀ (h : H) (m : M), (h : Unitization A H) • m = 0 := by
  simp [← le_bot_iff, nondegeneratePart_le_iff]

/-- A module homomorphism maps the nondegenerate part into the nondegenerate part. -/
theorem map_nondegeneratePart_le {N : Type*} [AddCommMonoid N] [Module (Unitization A H) N]
    (f : M →ₗ[Unitization A H] N) :
    (nondegeneratePart A H M).map f ≤ nondegeneratePart A H N := by
  rw [Submodule.map_le_iff_le_comap, nondegeneratePart_le_iff]
  intro h m
  simp

/-- The image of a nondegenerate module under a surjective homomorphism is nondegenerate:
quotients of nondegenerate modules are nondegenerate. -/
theorem IsNondegenerate.of_surjective {N : Type*} [AddCommMonoid N] [Module (Unitization A H) N]
    (hM : IsNondegenerate A H M) (f : M →ₗ[Unitization A H] N) (hf : Function.Surjective f) :
    IsNondegenerate A H N := by
  rw [isNondegenerate_iff_nondegeneratePart_eq_top, eq_top_iff, ← LinearMap.range_eq_top.2 hf,
    LinearMap.range_eq_map, ← hM.nondegeneratePart_eq_top]
  exact map_nondegeneratePart_le f

/-- If `e • m = m` and `f * e = e`, then `f • m = m`. -/
theorem inr_smul_eq_of_mul_eq {e f : H} {m : M} (hm : (e : Unitization A H) • m = m)
    (hfe : f * e = e) : (f : Unitization A H) • m = m := by
  rw [← hm, smul_smul, ← Unitization.inr_mul, hfe]

/-- The scalar `a : A` acts on an element `m` as the element `a • e` of `H`, for any `e : H`
fixing `m`. Thus on nondegenerate modules the action of `A` is determined by that of `H`. -/
theorem inl_smul_eq_inr_smul {e : H} {m : M} (hm : (e : Unitization A H) • m = m) (a : A) :
    (Unitization.inl a : Unitization A H) • m = ((a • e : H) : Unitization A H) • m := by
  conv_lhs => rw [← hm]
  rw [smul_smul, Unitization.inl_mul_inr]

/-- An additive map out of a nondegenerate module which commutes with the action of `H` is
linear over the unitization `A ⊕ H`: the action of `A` is determined by that of `H`. -/
theorem IsNondegenerate.map_smul_of_map_inr_smul (hM : IsNondegenerate A H M) {N : Type*}
    [AddCommMonoid N] [Module (Unitization A H) N] (f : M →+ N)
    (hf : ∀ (h : H) (m : M), f ((h : Unitization A H) • m) = (h : Unitization A H) • f m)
    (r : Unitization A H) (m : M) : f (r • m) = r • f m := by
  have hm : m ∈ nondegeneratePart A H M := hM.nondegeneratePart_eq_top ▸ Submodule.mem_top
  induction m, hm using Submodule.set_smul_inductionOn generalizing r with
  | @smul₀ s x hs _ =>
    obtain ⟨h, rfl⟩ := hs
    rw [smul_smul, Unitization.mul_inr, hf, hf, ← Unitization.mul_inr, smul_smul]
  | @smul₁ s x _ hx => rw [smul_smul, hx, hx, smul_smul]
  | @add x y _ _ hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | zero => simp

variable [IsIdempotented H]

/-- Over an idempotented algebra `H`, an element lies in `H • M` exactly when some idempotent of
`H` fixes it. -/
theorem mem_nondegeneratePart_iff {m : M} :
    m ∈ nondegeneratePart A H M ↔
      ∃ e : H, IsIdempotentElem e ∧ (e : Unitization A H) • m = m := by
  classical
  refine ⟨fun hm ↦ ?_, fun ⟨e, _, he⟩ ↦ he ▸ inr_smul_mem_nondegeneratePart e m⟩
  induction m, hm using Submodule.set_smul_inductionOn with
  | @smul₀ r m hr _ =>
    obtain ⟨h, rfl⟩ := hr
    obtain ⟨f, hf, hfh⟩ := IsIdempotented.exists_isIdempotentElem {h}
    exact ⟨f, hf, by rw [smul_smul, ← Unitization.inr_mul, (hfh h (by simp)).1]⟩
  | @smul₁ r x _ hx =>
    obtain ⟨e, -, he⟩ := hx
    have hrx : r • x = ((r.fst • e + r.snd * e : H) : Unitization A H) • x := by
      rw [← Unitization.mul_inr, ← smul_smul, he]
    obtain ⟨f, hf, hfk⟩ := IsIdempotented.exists_isIdempotentElem {r.fst • e + r.snd * e}
    exact ⟨f, hf, by rw [hrx, smul_smul, ← Unitization.inr_mul, (hfk _ (by simp)).1]⟩
  | @add x y _ _ hx hy =>
    obtain ⟨e₁, -, he₁⟩ := hx
    obtain ⟨e₂, -, he₂⟩ := hy
    obtain ⟨f, hf, hs⟩ := IsIdempotented.exists_isIdempotentElem {e₁, e₂}
    refine ⟨f, hf, ?_⟩
    rw [smul_add, inr_smul_eq_of_mul_eq he₁ (hs e₁ (by simp)).1,
      inr_smul_eq_of_mul_eq he₂ (hs e₂ (by simp)).1]
  | zero => exact ⟨0, .zero, smul_zero _⟩

/-- Over an idempotented algebra `H`, a module is nondegenerate exactly when each of its elements
is fixed by some idempotent of `H`. -/
theorem isNondegenerate_iff :
    IsNondegenerate A H M ↔
      ∀ m : M, ∃ e : H, IsIdempotentElem e ∧ (e : Unitization A H) • m = m := by
  simp [isNondegenerate_iff_nondegeneratePart_eq_top, Submodule.eq_top_iff',
    mem_nondegeneratePart_iff]

/-- Finitely many elements of the nondegenerate part have a common idempotent local unit. -/
theorem exists_isIdempotentElem_forall_smul_eq_of_subset (s : Finset M)
    (hs : (s : Set M) ⊆ nondegeneratePart A H M) :
    ∃ e : H, IsIdempotentElem e ∧ ∀ m ∈ s, (e : Unitization A H) • m = m := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, .zero, by simp⟩
  | insert m s _ ih =>
    rw [Finset.coe_insert, Set.insert_subset_iff] at hs
    obtain ⟨e₁, -, he₁⟩ := ih hs.2
    obtain ⟨e₂, -, he₂⟩ := mem_nondegeneratePart_iff.1 hs.1
    obtain ⟨f, hf, hfe⟩ := IsIdempotented.exists_isIdempotentElem {e₁, e₂}
    refine ⟨f, hf, fun x hx ↦ ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact inr_smul_eq_of_mul_eq he₂ (hfe e₂ (by simp)).1
    · exact inr_smul_eq_of_mul_eq (he₁ x hx) (hfe e₁ (by simp)).1

/-- Finitely many elements of a nondegenerate module have a common idempotent local unit. -/
theorem IsNondegenerate.exists_isIdempotentElem_forall_smul_eq (hM : IsNondegenerate A H M)
    (s : Finset M) : ∃ e : H, IsIdempotentElem e ∧ ∀ m ∈ s, (e : Unitization A H) • m = m :=
  exists_isIdempotentElem_forall_smul_eq_of_subset s (by simp [hM.nondegeneratePart_eq_top])

/-- A module embedding into a nondegenerate module has nondegenerate source: submodules of
nondegenerate modules are nondegenerate. -/
theorem IsNondegenerate.of_injective {N : Type*} [AddCommMonoid N] [Module (Unitization A H) N]
    (hN : IsNondegenerate A H N) (f : M →ₗ[Unitization A H] N) (hf : Function.Injective f) :
    IsNondegenerate A H M := by
  rw [isNondegenerate_iff] at hN ⊢
  intro m
  obtain ⟨e, he, hem⟩ := hN (f m)
  exact ⟨e, he, hf (by rwa [_root_.map_smul])⟩

/-- The nondegenerate part of a module is itself nondegenerate. -/
theorem isNondegenerate_nondegeneratePart :
    IsNondegenerate A H (nondegeneratePart A H M) := by
  rw [isNondegenerate_iff]
  rintro ⟨m, hm⟩
  obtain ⟨e, he, hem⟩ := mem_nondegeneratePart_iff.1 hm
  exact ⟨e, he, Subtype.ext hem⟩

/-- A submodule is nondegenerate exactly when it is contained in the nondegenerate part:
`H • M` is the largest nondegenerate submodule of `M`. -/
theorem isNondegenerate_iff_le_nondegeneratePart (N : Submodule (Unitization A H) M) :
    IsNondegenerate A H N ↔ N ≤ nondegeneratePart A H M := by
  refine ⟨fun hN ↦ ?_, fun hN ↦ isNondegenerate_nondegeneratePart.of_injective
    (Submodule.inclusion hN) (Submodule.inclusion_injective hN)⟩
  intro m hm
  obtain ⟨e, -, he⟩ := isNondegenerate_iff.1 hN ⟨m, hm⟩
  have hem : (e : Unitization A H) • m = m := congrArg Subtype.val he
  rw [← hem]
  exact inr_smul_mem_nondegeneratePart e m

/-- The principal left ideal `He` generated by an element of an idempotented algebra is a
nondegenerate module. -/
theorem isNondegenerate_span_singleton (e : H) :
    IsNondegenerate A H (Ideal.span {(e : Unitization A H)}) := by
  rw [isNondegenerate_iff_le_nondegeneratePart, Ideal.span_singleton_le_iff_mem]
  simpa using inr_smul_mem_nondegeneratePart (A := A) e (1 : Unitization A H)

end Module

end TauCeti
