/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.Pushforward
public import TauCeti.Topology.LocallyFinsupp.Comap
import TauCeti.AlgebraicGeometry.ResidueDegree
import TauCeti.AlgebraicGeometry.Scheme.LocalDimension

/-!
# Restriction of cycles to an open subscheme, and the localization sequence for cycles

Let `k` be a field and `j : U ⟶ X` an open immersion of schemes locally of finite type over `k`.
The restriction of a cycle `α` on `X` to `U` is `α ∘ j`, which sends `[V]` to `[V ∩ U]`: the flat
pullback along the open immersion `j`, of relative dimension zero. Over a field, `j` preserves the
dimension of points (`TauCeti.AlgebraicGeometry.height_apply_of_isOpenImmersion`, since its
residue degrees are one), so restriction sends `n`-cycles to `n`-cycles.

* `Chow.cyclesRestrict k j`: the restriction `Z_n(X) →+ Z_n(U)`, with `Chow.cyclesRestrict_id`
  and `Chow.cyclesRestrict_comp`.
* `Chow.cyclesRestrict_cyclesMap`: for `j` quasi-compact, restriction is a left inverse of
  pushforward along `j`; hence restriction is surjective (`Chow.cyclesRestrict_surjective`).
* `Chow.range_cyclesPushforward_eq_ker_cyclesRestrict`: for a closed immersion `i : Z ⟶ X` whose
  image is the complement of the image of `j`, the sequence
  `Z_n(Z) → Z_n(X) → Z_n(U) → 0` of pushforward and restriction is exact in the middle. This is
  the cycle-level form of the localization sequence of Fulton, *Intersection Theory*,
  Proposition 1.8, and [Stacks, Lemma 42.19.3](https://stacks.math.columbia.edu/tag/02RX).
-/

public section

open AlgebraicGeometry Order CategoryTheory

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable (k : Type u) [Field k] {X U V : Scheme.{u}}
  [X.Over (Spec (.of k))] [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [LocallyOfFiniteType (U ↘ Spec (.of k))]
  [LocallyOfFiniteType (V ↘ Spec (.of k))]

/-- Over a field, restricting an `n`-cycle along an open immersion gives an `n`-cycle. -/
lemma comap_mem_cyclesOfDimension (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    {n : ℤ} {α : AlgebraicCycle X ℤ} (hα : α ∈ cyclesOfDimension X n) :
    Function.locallyFinsupp.comap j j.continuous j.isOpenEmbedding.injective α ∈
      cyclesOfDimension U n := by
  rw [mem_cyclesOfDimension_iff, Function.locallyFinsupp.support_comap]
  intro u hu
  simpa only [mem_pointsOfDimension, height_apply_of_isOpenImmersion k j] using
    mem_cyclesOfDimension_iff.mp hα hu

/-- The restriction `Z_n(X) →+ Z_n(U)`, `α ↦ α ∘ j`, of `n`-cycles along an open immersion over a
field: the flat pullback along `j`, sending `[V]` to `[V ∩ U]`. -/
noncomputable def cyclesRestrict (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    {n : ℤ} : cyclesOfDimension X n →+ cyclesOfDimension U n :=
  AddMonoidHom.mk'
    (fun α ↦ ⟨Function.locallyFinsupp.comap j j.continuous j.isOpenEmbedding.injective
      (α : AlgebraicCycle X ℤ), comap_mem_cyclesOfDimension k j α.2⟩)
    fun _ _ ↦ Subtype.ext (Function.locallyFinsupp.comap_add _ _ _ _ _)

variable {k}

/-- The coefficient of a restriction at `u` is the coefficient of the cycle at `j u`. -/
@[simp]
lemma cyclesRestrict_apply (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))] {n : ℤ}
    (α : cyclesOfDimension X n) (u : U) :
    (cyclesRestrict k j α : AlgebraicCycle U ℤ) u = (α : AlgebraicCycle X ℤ) (j u) :=
  Function.locallyFinsupp.comap_apply _ _ _ _ _

variable (k)

/-- Restriction along the identity is the identity. -/
@[simp]
lemma cyclesRestrict_id {n : ℤ} : cyclesRestrict k (𝟙 X) (n := n) = AddMonoidHom.id _ := by
  ext α : 1
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  rw [cyclesRestrict_apply, AddMonoidHom.id_apply]
  rfl

/-- Restriction is functorial: `(j' ≫ j)^* = j'^* ∘ j^*`. -/
lemma cyclesRestrict_comp (j' : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion j'] [IsOpenImmersion j]
    [j'.IsOver (Spec (.of k))] [j.IsOver (Spec (.of k))] {n : ℤ} :
    cyclesRestrict k (j' ≫ j) (n := n) = (cyclesRestrict k j').comp (cyclesRestrict k j) := by
  ext α : 1
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun v ↦ ?_)
  rw [AddMonoidHom.comp_apply, cyclesRestrict_apply, cyclesRestrict_apply, cyclesRestrict_apply,
    Scheme.Hom.comp_apply]

/-- Restriction along a quasi-compact open immersion is a left inverse of pushforward along it. -/
@[simp]
lemma cyclesRestrict_cyclesMap (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of k))] {n : ℤ} (β : cyclesOfDimension U n) :
    cyclesRestrict k j (cyclesMap k j β) = β := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun u ↦ ?_)
  rw [cyclesRestrict_apply, cyclesMap_apply, ← Set.image_singleton,
    j.isOpenEmbedding.injective.preimage_image, finsum_mem_singleton,
    Scheme.Hom.residueDegree_eq_one_of_surjectiveOnStalks, Nat.cast_one, mul_one]

/-- Restriction of cycles along a quasi-compact open immersion is surjective. -/
lemma cyclesRestrict_surjective (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of k))] {n : ℤ} :
    Function.Surjective (cyclesRestrict k j (n := n)) :=
  fun β ↦ ⟨cyclesMap k j β, cyclesRestrict_cyclesMap k j β⟩

/-- A cycle restricts to zero on `U` exactly when it is supported off the image of `U`. -/
lemma cyclesRestrict_eq_zero_iff (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    {n : ℤ} {α : cyclesOfDimension X n} :
    cyclesRestrict k j α = 0 ↔ (α : AlgebraicCycle X ℤ).support ⊆ (Set.range j)ᶜ := by
  refine ⟨fun h x hx ⟨u, hu⟩ ↦ hx ?_, fun h ↦ Subtype.ext
    (Function.locallyFinsuppWithin.ext fun u ↦ ?_)⟩
  · rw [← hu, ← cyclesRestrict_apply (k := k), h]
    rfl
  · rw [cyclesRestrict_apply]
    by_contra hu
    exact h hu ⟨u, rfl⟩

/-- **The localization sequence for cycles.** If the image of a closed immersion `i : Z ⟶ X` is the
complement of the image of an open immersion `j : U ⟶ X`, then a cycle on `X` restricts to zero
on `U` exactly when it is pushed forward from `Z`: the sequence `Z_n(Z) → Z_n(X) → Z_n(U)` is
exact (Fulton, *Intersection Theory*, Proposition 1.8; Stacks, Lemma 42.19.3 (02RX)). -/
@[stacks 02RX]
lemma range_cyclesPushforward_eq_ker_cyclesRestrict {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (hij : Set.range i = (Set.range j)ᶜ) {n : ℤ} :
    (cyclesPushforward i (k := n)).range = (cyclesRestrict k j (n := n)).ker := by
  ext α
  rw [mem_range_cyclesPushforward_iff, AddMonoidHom.mem_ker, cyclesRestrict_eq_zero_iff, hij]

end TauCeti.AlgebraicGeometry.Chow
