/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index

/-!
# Index comparisons under injective endomorphisms and finite products

Let `G` be a group, `H` a subgroup of finite index, and `f : G →* G` an injective endomorphism
mapping `H` into itself. Comparing the two subgroup chains `f(H) ≤ H ≤ G` and `f(H) ≤ f(G) ≤ G`
shows that `f(H)` has the same index in `H` as `f(G)` has in `G`: since `f` is injective,
`[G : f(H)] = [G : H] * [G : f(G)]`, while `[G : f(H)] = [H : f(H)] * [G : H]`, and the finite
nonzero factor `[G : H]` cancels. Equivalently, if `g : H →* H` is the restriction of `f` to `H`,
the coset spaces `H ⧸ g.range` and `G ⧸ f.range` have the same `Nat.card` and one is finite
exactly when the other is.

We also record the `FiniteIndex` instance on `Subgroup.pi` along a finite set of coordinates.

## Main results

* `Subgroup.instFiniteIndexPi`, `AddSubgroup.instFiniteIndexPi`: `Subgroup.pi I H` has finite index
  whenever `I` is finite and each `H i` has finite index.
* `Subgroup.relIndex_map_eq_index_range`, `AddSubgroup.relIndex_map_eq_index_range`: for an
  injective endomorphism `f` stabilizing a finite-index subgroup `H`,
  `(H.map f).relIndex H = f.range.index`.
* `Subgroup.index_range_eq_of_comp_subtype`, `Subgroup.finite_quotient_range_iff_of_comp_subtype`,
  `Subgroup.natCard_quotient_range_eq_of_comp_subtype` (and additive forms): comparing the range of
  a restricted endomorphism `g : H →* H` with that of `f : G →* G`.
-/

public section

namespace Subgroup

section Pi

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]

/-- A product subgroup constrained on finitely many coordinates by finite-index subgroups has
finite index. -/
@[to_additive
/-- A product additive subgroup constrained on finitely many coordinates by finite-index additive
subgroups has finite index. -/]
instance instFiniteIndexPi (I : Set ι) [Finite I] (H : ∀ i, Subgroup (G i))
    [∀ i, (H i).FiniteIndex] : (Subgroup.pi I H).FiniteIndex := by
  have hpi : Subgroup.pi I H = ⨅ i : I, (H i.1).comap (Pi.evalMonoidHom G i.1) := by
    ext x
    simp [Subgroup.mem_pi]
  rw [hpi]
  exact finiteIndex_iInf fun i ↦ inferInstance

end Pi

section Endomorphism

variable {G : Type*} [Group G] (H : Subgroup G)

/-- **Index invariance under an injective endomorphism.** If `f : G →* G` is injective and maps a
finite-index subgroup `H` into itself, then the index of `f(H)` inside `H` equals the index of
`f(G)` inside `G`. Both are `0` when the quotients are infinite. -/
@[to_additive
/-- **Index invariance under an injective additive endomorphism.** If `f : G →+ G` is injective and
maps a finite-index additive subgroup `H` into itself, then the index of `f(H)` inside `H` equals
the index of `f(G)` inside `G`. Both are `0` when the quotients are infinite. -/]
theorem relIndex_map_eq_index_range [H.FiniteIndex] {f : G →* G} (hf : Function.Injective f)
    (hH : H.map f ≤ H) : (H.map f).relIndex H = f.range.index := by
  have hmul : (H.map f).relIndex H * H.index = f.range.index * H.index := by
    rw [relIndex_mul_index hH, H.index_map_of_injective hf, mul_comm]
  exact mul_right_cancel₀ H.index_ne_zero hmul

variable {H}

/-- If `g : H →* H` agrees with `f : G →* G` along `H.subtype`, the range of `g` is the preimage in
`H` of `H.map f`. -/
@[to_additive
/-- If `g : H →+ H` agrees with `f : G →+ G` along `H.subtype`, the range of `g` is the preimage in
`H` of `H.map f`. -/]
theorem range_eq_subgroupOf_map {g : H →* H} {f : G →* G}
    (hgf : f.comp H.subtype = H.subtype.comp g) :
    g.range = (H.map f).subgroupOf H := by
  ext y
  have hval (x : H) : f x = g x := DFunLike.congr_fun hgf x
  simp only [MonoidHom.mem_range, mem_subgroupOf, mem_map]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, hval x⟩
  · rintro ⟨z, hz, hzy⟩
    exact ⟨⟨z, hz⟩, Subtype.ext ((hval ⟨z, hz⟩).symm.trans hzy)⟩

/-- If an injective endomorphism `f : G →* G` restricts to `g : H →* H` on a finite-index subgroup
`H`, then `g.range` inside `H` and `f.range` inside `G` have the same index. -/
@[to_additive
/-- If an injective endomorphism `f : G →+ G` restricts to `g : H →+ H` on a finite-index additive
subgroup `H`, then `g.range` inside `H` and `f.range` inside `G` have the same index. -/]
theorem index_range_eq_of_comp_subtype [H.FiniteIndex] {g : H →* H} {f : G →* G}
    (hf : Function.Injective f) (hgf : f.comp H.subtype = H.subtype.comp g) :
    g.range.index = f.range.index := by
  have hmap : H.map f ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    have hval : f x = g ⟨x, hx⟩ := DFunLike.congr_fun hgf ⟨x, hx⟩
    exact hval ▸ (g ⟨x, hx⟩).2
  rw [range_eq_subgroupOf_map hgf, ← relIndex, H.relIndex_map_eq_index_range hf hmap]

/-- Under an injective endomorphism `f` restricting to `g` on a finite-index subgroup `H`, `g.range`
has finite index in `H` if and only if `f.range` has finite index in `G`. -/
@[to_additive
/-- Under an injective endomorphism `f` restricting to `g` on a finite-index additive subgroup `H`,
`g.range` has finite index in `H` if and only if `f.range` has finite index in `G`. -/]
theorem finiteIndex_range_iff_of_comp_subtype [H.FiniteIndex] {g : H →* H} {f : G →* G}
    (hf : Function.Injective f) (hgf : f.comp H.subtype = H.subtype.comp g) :
    g.range.FiniteIndex ↔ f.range.FiniteIndex := by
  rw [finiteIndex_iff, finiteIndex_iff, index_range_eq_of_comp_subtype hf hgf]

/-- Under an injective endomorphism `f` restricting to `g` on a finite-index subgroup `H`, the
coset space `H ⧸ g.range` is finite if and only if `G ⧸ f.range` is finite. -/
@[to_additive
/-- Under an injective endomorphism `f` restricting to `g` on a finite-index additive subgroup `H`,
the quotient `H ⧸ g.range` is finite if and only if `G ⧸ f.range` is finite. -/]
theorem finite_quotient_range_iff_of_comp_subtype [H.FiniteIndex] {g : H →* H} {f : G →* G}
    (hf : Function.Injective f) (hgf : f.comp H.subtype = H.subtype.comp g) :
    Finite (H ⧸ g.range) ↔ Finite (G ⧸ f.range) := by
  rw [← finiteIndex_iff_finite_quotient, ← finiteIndex_iff_finite_quotient,
    finiteIndex_range_iff_of_comp_subtype hf hgf]

/-- Under an injective endomorphism `f` restricting to `g` on a finite-index subgroup `H`, the coset
spaces `H ⧸ g.range` and `G ⧸ f.range` have the same cardinality (`0` when infinite). -/
@[to_additive
/-- Under an injective endomorphism `f` restricting to `g` on a finite-index additive subgroup `H`,
the quotients `H ⧸ g.range` and `G ⧸ f.range` have the same cardinality (`0` when infinite). -/]
theorem natCard_quotient_range_eq_of_comp_subtype [H.FiniteIndex] {g : H →* H} {f : G →* G}
    (hf : Function.Injective f) (hgf : f.comp H.subtype = H.subtype.comp g) :
    Nat.card (H ⧸ g.range) = Nat.card (G ⧸ f.range) :=
  index_range_eq_of_comp_subtype hf hgf

end Endomorphism

end Subgroup
