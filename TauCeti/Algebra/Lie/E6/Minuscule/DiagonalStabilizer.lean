/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.CrossProduct
public import TauCeti.Algebra.Lie.E6.Minuscule.SeedCoordinates

/-!
# The diagonal stabilizer of the E₆ cubic coefficients

Over every commutative ring, the diagonal matrices preserving the trilinear coefficients
`TauCeti.E6Minuscule.cubicForm` are exactly the minuscule weight-torus matrices. This includes
finite and nonreduced rings: the nonzero integral coefficients are units, so their preservation
is equivalent to the product of the three corresponding diagonal entries being one.

The proof uses rigidity of the cross product on the doubled module: extend a diagonal function
on the minuscule weights by its inverse on the dual weights. Preservation of the cubic
coefficients is then precisely multiplicativity along that cross product. Six minuscule weights
form an integral basis, which recovers the torus parameter uniquely.

This computes a diagonal stabilizer, not the stabilizer of the form among all matrices. Nor does
it assert that every point of the minuscule carrier preserves the form. Together with that
invariance and a schematic torus-centralizer calculation, it supplies the diagonal-intersection
step in recognizing the carrier's weight torus.

## References

* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*,
  Chapters 5 and 7.
* The rigidity argument and the six-coordinate recovery follow
  `TauCeti.Algebra.Lie.E6.DoubledMinuscule.CrossProduct` and
  `TauCeti.Algebra.Lie.E6.DoubledMinuscule.MaximalTorus`.
-/

public section

namespace TauCeti.E6Minuscule

open TauCeti.DynkinType

private def doubledValues {G : Type*} [Group G] (t : Fin 27 → G) : Fin 54 → G :=
  fun a => Sum.elim t (fun b => (t b)⁻¹) (E6DoubledMinuscule.matrixIndexEquiv.symm a)

private theorem doubledValues_multiplicative {G : Type*} [CommGroup G]
    {t : Fin 27 → G}
    (ht : ∀ a b c, cubicForm a b c ≠ 0 → t a * t b * t c = 1) :
    ∀ k i j, E6DoubledMinuscule.crossProductMatrix k i j ≠ 0 →
      doubledValues t i = doubledValues t k * doubledValues t j := by
  intro k i j h
  simp only [E6DoubledMinuscule.crossProductMatrix_apply] at h
  unfold doubledValues
  generalize E6DoubledMinuscule.matrixIndexEquiv.symm k = k' at h ⊢
  generalize E6DoubledMinuscule.matrixIndexEquiv.symm i = i' at h ⊢
  generalize E6DoubledMinuscule.matrixIndexEquiv.symm j = j' at h ⊢
  rcases k' with k | k <;> rcases i' with i | i <;> rcases j' with j | j <;>
    simp only [E6DoubledMinuscule.crossProductCoefficient_inl_inl_inl,
      E6DoubledMinuscule.crossProductCoefficient_inl_inl_inr,
      E6DoubledMinuscule.crossProductCoefficient_inl_inr_inl,
      E6DoubledMinuscule.crossProductCoefficient_inl_inr_inr,
      E6DoubledMinuscule.crossProductCoefficient_inr_inl_inl,
      E6DoubledMinuscule.crossProductCoefficient_inr_inl_inr,
      E6DoubledMinuscule.crossProductCoefficient_inr_inr_inl,
      E6DoubledMinuscule.crossProductCoefficient_inr_inr_inr, ne_eq,
      not_true_eq_false] at h
  · exact (eq_inv_iff_mul_eq_one.mpr (ht k j i h)).symm
  · simpa [mul_inv_rev, mul_comm] using
      (eq_inv_iff_mul_eq_one.mpr (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using ht k j i h) :
          t i = (t k * t j)⁻¹)

/-- A unit multiplier on the 27 minuscule weight lines satisfies every cubic triad relation
exactly when it is evaluation at a unique point of the rank-six weight torus. -/
theorem existsUnique_torusCharacter_iff_cubicForm {A : Type*} [CommRing A] (t : Fin 27 → Aˣ) :
    (∃! s : Fin 6 → Aˣ, ∀ a, torusCharacter s (e6MinusculeWeight a) = t a) ↔
      ∀ a b c, cubicForm a b c ≠ 0 → t a * t b * t c = 1 := by
  have hchar (s : Fin 6 → Aˣ) :
      ∀ a b c, cubicForm a b c ≠ 0 →
        torusCharacter s (e6MinusculeWeight a) *
          torusCharacter s (e6MinusculeWeight b) *
            torusCharacter s (e6MinusculeWeight c) = 1 := by
    intro a b c h
    rw [← torusCharacter_add, ← torusCharacter_add,
      (cubicForm_ne_zero_iff a b c).mp h, torusCharacter_zero]
  constructor
  · rintro ⟨s, hs, _⟩ a b c h
    simpa only [hs] using hchar s a b c h
  · intro ht
    let s := torusParameterOfSeedValues t
    have hseed := torusCharacter_torusParameterOfSeedValues t
    have heq := E6DoubledMinuscule.eq_of_eq_mul_of_crossProductMatrix_ne_zero
      (doubledValues_multiplicative (hchar s)) (doubledValues_multiplicative ht)
      (by simpa only [doubledValues, Equiv.symm_apply_apply, Sum.elim_inl] using hseed)
    refine ⟨s, (fun a => ?_), ?_⟩
    · simpa only [doubledValues, Equiv.symm_apply_apply, Sum.elim_inl] using
        congrFun heq (E6DoubledMinuscule.matrixIndexEquiv (.inl a))
    · intro u hu
      apply torusCharacterHom_injective span_range_e6MinusculeWeight_eq_top
      funext a
      simp only [torusCharacterHom_apply, hu]
      simpa only [doubledValues, Equiv.symm_apply_apply, Sum.elim_inl] using
        (congrFun heq (E6DoubledMinuscule.matrixIndexEquiv (.inl a))).symm

/-- Over every commutative ring, an invertible diagonal matrix preserves the cubic coefficients
if and only if it is a minuscule weight-torus matrix. No assumption on the characteristic or
reducedness of the coefficient ring is needed. -/
theorem diagGL_mem_map_weightTorusPoints_iff {A : Type*} [CommRing A] (t : Fin 27 → Aˣ) :
    diagGL t ∈ ((weightTorusPoints A).range).map (points A).subtype ↔
      ∀ a b c, (cubicForm a b c : A) * t a * t b * t c = (cubicForm a b c : A) := by
  have htriad : (∀ a b c, (cubicForm a b c : A) * t a * t b * t c =
        (cubicForm a b c : A)) ↔
      ∀ a b c, cubicForm a b c ≠ 0 → t a * t b * t c = 1 := by
    constructor
    · intro h a b c hne
      apply Units.ext
      rcases cubicForm_eq_neg_one_or_eq_zero_or_eq_one a b c with hc | hc | hc
      · simpa [hc, mul_assoc] using h a b c
      · exact False.elim (hne hc)
      · simpa [hc, mul_assoc] using h a b c
    · intro h a b c
      by_cases hc : cubicForm a b c = 0
      · simp [hc]
      · have he := congrArg Units.val (h a b c hc)
        simpa only [Units.val_mul, Units.val_one, mul_assoc, mul_one] using
          congrArg (fun x : A => (cubicForm a b c : A) * x) he
  rw [htriad, ← existsUnique_torusCharacter_iff_cubicForm]
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, hs⟩
    rw [Subgroup.coe_subtype, coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, weightTable_weight] at hs
    have he : ∀ a, torusCharacter s (e6MinusculeWeight a) = t a :=
      fun a => congrFun (diagGL_injective hs) a
    refine ⟨s, he, fun u hu => ?_⟩
    exact torusCharacterHom_injective span_range_e6MinusculeWeight_eq_top
      (by ext a; simp only [torusCharacterHom_apply, he, hu])
  · rintro ⟨s, hs, _⟩
    refine ⟨weightTorusPoints A s, ⟨s, rfl⟩, ?_⟩
    rw [Subgroup.coe_subtype, coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, weightTable_weight]
    congr 1
    funext a
    exact hs a

end TauCeti.E6Minuscule
