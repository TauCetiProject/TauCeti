/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Group.PiLex
public import TauCeti.Algebra.Order.Group.PiLex
public import TauCeti.Algebra.Order.Monoid.Submonoid
public import TauCeti.GroupTheory.LyndonLength.Basic

/-!
# Change of value group for Lyndon length functions

A Lyndon length function `l : G → Λ` can be composed with a homomorphism of ordered abelian groups
`φ : Λ → Λ'`: the composite `φ ∘ l` is again a Lyndon length function
(`TauCeti.LyndonLength.map`). Regularity is preserved by every `φ`, and freeness by every
injective `φ`. For injective `φ` the length function `l` is regular exactly when `φ ∘ l` is, and
`l` is free exactly when `φ ∘ l` is free and all its Gromov products lie in the image of `φ`.

In the other direction, a Lyndon length function `l : G → Λ` all of whose values lie in a subgroup
`S` of `Λ` (of any type of subgroups, such as a submodule) is a Lyndon length function with values
in `S` (`TauCeti.LyndonLength.codRestrict`). It is regular exactly when `l` is, and free exactly
when `l` is free and all Gromov products of `l` lie in `S`. The last condition cannot be dropped:
(L4) asks for the Gromov products to lie in the value group, and a Gromov product is only half of
an element of `S`.

These two operations are how a length function with values in a large ordered group, such as the
additive group of `ℤ[t]`, becomes one with values in a small one, such as `ℤⁿ` with the
lexicographic order: a finitely generated group whose length function takes values in `ℤ[t]` has
all its lengths in the subgroup of polynomials of bounded degree, which is `ℤⁿ` ordered
lexicographically.

As an example, the length function `k ↦ (0, …, 0, |k|, 0, …, 0)` on a factor of a lexicographic
product of linearly ordered abelian groups, with values in that product, is free and regular. For
`Lex (Fin 3 → ℤ)` this is the length function `k ↦ (0, 0, |k|)` on `ℤ`, whose values lie in a single
convex subgroup of `ℤ³`.

## Main definitions

* `TauCeti.LyndonLength.map`: the composite of a Lyndon length function with a homomorphism of
  ordered abelian groups.
* `TauCeti.LyndonLength.codRestrict`: a Lyndon length function with values in a subgroup `S`, as
  a length function with values in `S`.

## Main results

* `TauCeti.LyndonLength.IsRegular.map`, `TauCeti.LyndonLength.isRegular_map_iff`: regularity under
  change of value group.
* `TauCeti.LyndonLength.IsFree.map`, `TauCeti.LyndonLength.isFree_iff_isFree_map_and_mem_range`:
  freeness under change of value group along an injective homomorphism.
* `TauCeti.LyndonLength.map_codRestrict`: `l.codRestrict S h` composed with the inclusion
  `AddSubmonoidClass.orderedSubtype S` of `S` is `l`.
* `TauCeti.LyndonLength.coe_eq_gromovProduct_codRestrict_iff`: the Gromov products of the
  restriction to a subgroup are those of `l`.
* `TauCeti.LyndonLength.isRegular_codRestrict_iff`, `TauCeti.LyndonLength.isFree_codRestrict_iff`:
  regularity and freeness of the restriction to a subgroup.
* `TauCeti.LyndonLength.isFree_map_absLength_singleOrderAddMonoidHom`,
  `TauCeti.LyndonLength.isRegular_map_absLength_singleOrderAddMonoidHom`: the absolute value in
  one coordinate of a lexicographic product is free and regular.

## References

* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Groups with free regular length
  functions in `ℤⁿ`*, Trans. Amer. Math. Soc. 364 (2012), 2847–2882, §4.
* O. Kharlampovich, A. Myasnikov, D. Serbin, *Actions, length functions, and non-archimedean
  words*, Internat. J. Algebra Comput. 23 (2013), 325–455, §9 and §10.2.
* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), §1.
-/

public section

namespace TauCeti

namespace LyndonLength

variable {G H Λ Λ' Λ'' A : Type*} [Group G] [Group H] [AddCommGroup Λ] [LinearOrder Λ]
  [AddCommGroup Λ'] [LinearOrder Λ'] [AddCommGroup Λ''] [LinearOrder Λ''] [SetLike A Λ]
  [AddSubgroupClass A Λ]

/-! ### Composition with a homomorphism of ordered groups -/

/-- The composite `g ↦ φ (l g)` of a Lyndon length function with a homomorphism `φ` of ordered
abelian groups. -/
def map (l : LyndonLength G Λ) (φ : Λ →+o Λ') : LyndonLength G Λ' where
  toFun g := φ (l g)
  map_one' := (congrArg φ l.map_one').trans (map_zero φ)
  map_inv' g := congrArg φ (l.map_inv' g)
  eq_of_lt' g f h hlt := by
    simp only [← map_add, ← map_sub] at hlt ⊢
    exact congrArg φ (l.eq_of_lt' g f h ((OrderHomClass.mono φ).reflect_lt hlt))

@[simp]
theorem map_apply (l : LyndonLength G Λ) (φ : Λ →+o Λ') (g : G) : l.map φ g = φ (l g) :=
  (rfl)

@[simp]
theorem map_id (l : LyndonLength G Λ) : l.map (OrderAddMonoidHom.id Λ) = l :=
  (rfl)

theorem map_map (l : LyndonLength G Λ) (φ : Λ →+o Λ') (ψ : Λ' →+o Λ'') :
    (l.map φ).map ψ = l.map (ψ.comp φ) :=
  (rfl)

@[simp]
theorem map_zero (φ : Λ →+o Λ') : (0 : LyndonLength G Λ).map φ = 0 :=
  ext fun _ => _root_.map_zero φ

/-! ### Restriction of the value group to a subgroup -/

section codRestrict

/-- A Lyndon length function all of whose values lie in a subgroup `S` of the value group, as a
Lyndon length function with values in `S`. -/
def codRestrict (l : LyndonLength G Λ) (S : A) (h : ∀ g, l g ∈ S) :
    LyndonLength G S where
  toFun g := ⟨l g, h g⟩
  map_one' := Subtype.ext l.map_one'
  map_inv' g := Subtype.ext (l.map_inv' g)
  eq_of_lt' g f k hlt := Subtype.ext (l.eq_of_lt' g f k hlt)

variable {l : LyndonLength G Λ} {S : A} {h : ∀ g, l g ∈ S}

@[simp]
theorem coe_codRestrict_apply (g : G) : (l.codRestrict S h g : Λ) = l g :=
  (rfl)

/-- The restriction `l.codRestrict S h` composed with the inclusion of `S` is `l`. -/
@[simp]
theorem map_codRestrict : (l.codRestrict S h).map (AddSubmonoidClass.orderedSubtype S) = l :=
  ext fun _ => by simp

end codRestrict

/-! ### Regularity and freeness -/

variable [IsOrderedAddMonoid Λ] [IsOrderedAddMonoid Λ'] (l : LyndonLength G Λ) {φ : Λ →+o Λ'}
  {g f : G} {c : Λ}

theorem comap_map (φ : Λ →+o Λ') (ψ : H →* G) : (l.map φ).comap ψ = (l.comap ψ).map φ :=
  ext fun _ => by simp

/-- If `c` is the Gromov product `c(g, f)` of `l`, then `φ c` is that of `l.map φ`. -/
theorem coe_map_eq_gromovProduct_map (φ : Λ →+o Λ')
    (hc : (c : DivisibleHull Λ) = l.gromovProduct g f) :
    (φ c : DivisibleHull Λ') = (l.map φ).gromovProduct g f := by
  rw [coe_eq_gromovProduct_iff] at hc ⊢
  simp [← map_nsmul, hc]

/-- For injective `φ`, the element `φ c` is the Gromov product `c(g, f)` of `l.map φ` exactly
when `c` is that of `l`. -/
theorem coe_map_eq_gromovProduct_map_iff (hφ : Function.Injective φ) :
    (φ c : DivisibleHull Λ') = (l.map φ).gromovProduct g f ↔
      (c : DivisibleHull Λ) = l.gromovProduct g f := by
  refine ⟨fun hc => ?_, l.coe_map_eq_gromovProduct_map φ⟩
  rw [coe_eq_gromovProduct_iff] at hc ⊢
  exact hφ (by simpa using hc)

variable {l}

/-- Composition with a homomorphism of ordered groups preserves regularity. -/
theorem IsRegular.map (hl : l.IsRegular) (φ : Λ →+o Λ') : (l.map φ).IsRegular := by
  rw [isRegular_iff] at hl ⊢
  intro g f
  obtain ⟨u, g₁, f₁, hg, hf, hlg, hlf, hu⟩ := hl g f
  exact ⟨u, g₁, f₁, hg, hf, by simp [hlg], by simp [hlf], l.coe_map_eq_gromovProduct_map φ hu⟩

/-- A Lyndon length function is regular exactly when its composite with an injective homomorphism
of ordered groups is. -/
theorem isRegular_map_iff (hφ : Function.Injective φ) : (l.map φ).IsRegular ↔ l.IsRegular := by
  refine ⟨fun hl => ?_, fun hl => hl.map φ⟩
  rw [isRegular_iff] at hl ⊢
  intro g f
  obtain ⟨u, g₁, f₁, hg, hf, hlg, hlf, hu⟩ := hl g f
  exact ⟨u, g₁, f₁, hg, hf, hφ (by simpa using hlg), hφ (by simpa using hlf),
    (l.coe_map_eq_gromovProduct_map_iff hφ).1 hu⟩

/-- Composition with an injective homomorphism of ordered groups preserves freeness. -/
theorem IsFree.map (hl : l.IsFree) (hφ : Function.Injective φ) : (l.map φ).IsFree where
  exists_coe_eq_gromovProduct g f := by
    obtain ⟨c, hc⟩ := hl.exists_coe_eq_gromovProduct g f
    exact ⟨φ c, l.coe_map_eq_gromovProduct_map φ hc⟩
  lt_map_sq g hg := ((OrderHomClass.mono φ).strictMono_of_injective hφ) (hl.lt_map_sq g hg)

/-- For an injective homomorphism `φ` of ordered groups, a Lyndon length function `l` is free
exactly when `l.map φ` is free and all Gromov products of `l.map φ` lie in the image of `φ`. -/
theorem isFree_iff_isFree_map_and_mem_range (hφ : Function.Injective φ) :
    l.IsFree ↔ (l.map φ).IsFree ∧ ∀ g f, ∀ c' : Λ',
      (c' : DivisibleHull Λ') = (l.map φ).gromovProduct g f → c' ∈ Set.range φ := by
  refine ⟨fun hl => ⟨hl.map hφ, fun g f c' hc' => ?_⟩, fun ⟨hl, hc⟩ => ⟨fun g f => ?_, fun g hg =>
    (OrderHomClass.mono φ).reflect_lt (hl.lt_map_sq g hg)⟩⟩
  · obtain ⟨c, hc⟩ := hl.exists_coe_eq_gromovProduct g f
    exact ⟨c, DivisibleHull.coe_injective ((l.coe_map_eq_gromovProduct_map φ hc).trans hc'.symm)⟩
  · obtain ⟨c', hc'⟩ := hl.exists_coe_eq_gromovProduct g f
    obtain ⟨c, rfl⟩ := hc g f c' hc'
    exact ⟨c, (l.coe_map_eq_gromovProduct_map_iff hφ).1 hc'⟩

variable {S : A} {h : ∀ g, l g ∈ S}

theorem comap_codRestrict (ψ : H →* G) :
    (l.codRestrict S h).comap ψ = (l.comap ψ).codRestrict S fun g => by simpa using h (ψ g) :=
  ext fun _ => Subtype.ext (by simp)

/-- An element `c` of `S` is the Gromov product `c(g, f)` of `l.codRestrict S h` exactly when it is
that of `l`. -/
theorem coe_eq_gromovProduct_codRestrict_iff {c : S} :
    (c : DivisibleHull S) = (l.codRestrict S h).gromovProduct g f ↔
      ((c : Λ) : DivisibleHull Λ) = l.gromovProduct g f := by
  simpa only [map_codRestrict, AddSubmonoidClass.coe_orderedSubtype] using
    (coe_map_eq_gromovProduct_map_iff (l.codRestrict S h)
      (AddSubmonoidClass.orderedSubtype_injective S)).symm

/-- A Lyndon length function with values in a subgroup `S` is regular as a length function with
values in `S` exactly when it is regular. -/
@[simp]
theorem isRegular_codRestrict_iff : (l.codRestrict S h).IsRegular ↔ l.IsRegular := by
  simpa only [map_codRestrict] using (isRegular_map_iff (l := l.codRestrict S h)
    (AddSubmonoidClass.orderedSubtype_injective S)).symm

/-- A Lyndon length function with values in a subgroup `S` is free as a length function with
values in `S` exactly when it is free and all its Gromov products lie in `S`. -/
theorem isFree_codRestrict_iff :
    (l.codRestrict S h).IsFree ↔ l.IsFree ∧ ∀ g f, ∀ c : Λ,
      (c : DivisibleHull Λ) = l.gromovProduct g f → c ∈ S := by
  rw [isFree_iff_isFree_map_and_mem_range (AddSubmonoidClass.orderedSubtype_injective S),
    map_codRestrict]
  simp

/-- A free Lyndon length function whose values and Gromov products lie in a subgroup `S` is free
as a length function with values in `S`. -/
theorem IsFree.codRestrict (hl : l.IsFree) (h : ∀ g, l g ∈ S)
    (hc : ∀ g f, ∀ c : Λ, (c : DivisibleHull Λ) = l.gromovProduct g f → c ∈ S) :
    (l.codRestrict S h).IsFree :=
  isFree_codRestrict_iff.2 ⟨hl, hc⟩

/-! ### Example: the absolute value in one coordinate of a lexicographic product -/

section Lex

variable {ι : Type*} (α : ι → Type*) [LinearOrder ι] [DecidableEq ι] [WellFoundedLT ι]
  [∀ j, AddCommGroup (α j)] [∀ j, LinearOrder (α j)] [∀ j, IsOrderedAddMonoid (α j)] (i : ι)

/-- The length function `a ↦ (0, …, 0, |a|, 0, …, 0)` on the factor `α i` of a family of linearly
ordered abelian groups, with values in the lexicographic product `Lex (∀ j, α j)` and with `|a|` in
the coordinate `i`, is free. For `α = fun _ => ℤ` and `i = 2` in `Lex (Fin 3 → ℤ)` this is
`k ↦ (0, 0, |k|)`. -/
theorem isFree_map_absLength_singleOrderAddMonoidHom :
    ((absLength (α i)).map (Pi.Lex.singleOrderAddMonoidHom α i)).IsFree :=
  isFree_absLength.map (Pi.Lex.singleOrderAddMonoidHom_injective i)

/-- The length function `a ↦ (0, …, 0, |a|, 0, …, 0)` on the factor `α i` of a family of linearly
ordered abelian groups, with values in the lexicographic product `Lex (∀ j, α j)` and with `|a|` in
the coordinate `i`, is regular. -/
theorem isRegular_map_absLength_singleOrderAddMonoidHom :
    ((absLength (α i)).map (Pi.Lex.singleOrderAddMonoidHom α i)).IsRegular :=
  isRegular_absLength.map _

end Lex

end LyndonLength

end TauCeti
