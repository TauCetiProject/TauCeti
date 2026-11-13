/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Norm.Valence
public import TauCeti.NumberTheory.ModularForms.WithCenter

/-!
# Vanishing orders on the effective quotient `Γ \ ℍ`

For a subgroup `Γ ≤ SL(2, ℤ)`, the real matrix image `(Γ : Subgroup (GL (Fin 2) ℝ))` and the
effective Fuchsian image `Γ.map sl2zToPSL2R ≤ PSL(2, ℝ)` induce the same orbit relation on the
upper half-plane `ℍ`: the centre `{±I}` of `SL(2, ℤ)` acts trivially. Their point stabilisers,
however, differ by `{±I} ∩ Γ`, which has order `2` when `-1 ∈ Γ` and `1` when `-1 ∉ Γ`. Since
`[±Γ : Γ]` takes the complementary values `1` and `2`, the product `[±Γ : Γ] · |{±I} ∩ Γ|` is
identically `2`.

Consequently, descending the vanishing order of a modular form to the effective quotient
`MulAction.orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ` — the interior of the compactified modular
curve `(Γ.map sl2zToPSL2R).CompactifiedQuotient` — and weighting each orbit `P` by the reciprocal
`1 / e_P` of its effective stabiliser order `e_P = cardStabilizerOnOrbit P` divides the matrix
weighted order `2 · ord_P f / |Stab_Γ P|` by the uniform factor `[±Γ : Γ]`.

## Main definitions

* `TauCeti.ModularForm.subgroupOrbitEquivEffectiveOrbit`: the canonical equivalence between the
  matrix orbit space `(Γ : Subgroup (GL (Fin 2) ℝ)) \ ℍ` and the effective orbit space
  `(Γ.map sl2zToPSL2R) \ ℍ`.
* `TauCeti.ModularForm.orderOfVanishingOnEffectiveOrbit`: the vanishing order descended to the
  effective orbit space.
* `TauCeti.ModularForm.weightedOrderOfVanishingOnEffectiveOrbit`: the projective weighted order
  `ord_P f / e_P` on the effective orbit space.

## Main results

* `TauCeti.ModularForm.relIndex_withCenter_mul_card_center_subgroupOf`: for every `Γ ≤ SL(2, ℤ)`,
  `[±Γ : Γ] · |{±I} ∩ Γ| = 2`.
* `TauCeti.ModularForm.cardStabilizerOnOrbit_eq_card_center_mul_effective`: the matrix stabiliser
  order on an orbit is `|{±I} ∩ Γ|` times the effective stabiliser order `e_P`.
* `TauCeti.ModularForm.orderOfVanishingOnEffectiveOrbit_modularForm_mul` and
  `TauCeti.ModularForm.weightedOrderOfVanishingOnEffectiveOrbit_modularForm_mul`: additivity under
  products of nonzero modular forms.
* `TauCeti.ModularForm.hasFiniteSupport_orderOfVanishingOnEffectiveOrbit` and
  `TauCeti.ModularForm.hasFiniteSupport_weightedOrderOfVanishingOnEffectiveOrbit`: finite support
  on the effective orbit space.
* `TauCeti.ModularForm.finsum_weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_withCenter_mul`:
  the matrix interior divisor sum is `[±Γ : Γ]` times the projective interior divisor sum.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §§3.2–3.3.
-/

public noncomputable section

open MulAction UpperHalfPlane

open scoped MatrixGroups ModularForm Modular

namespace TauCeti.ModularForm

section CenterAndOrbits

variable {Γ : Subgroup SL(2, ℤ)}

/-- When `-I ∈ Γ`, adjoining the centre does not enlarge `Γ`, so `[±Γ : Γ] = 1`. -/
theorem relIndex_withCenter_eq_one_of_neg_one_mem (h : (-1 : SL(2, ℤ)) ∈ Γ) :
    Γ.relIndex Γ.withCenter = 1 := by
  have hΓ : Γ.withCenter = Γ := Subgroup.withCenter_eq_self_iff.mpr fun c hc ↦ by
    rcases Matrix.SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hc with rfl | rfl
    · exact Γ.one_mem
    · exact h
  rw [hΓ, Subgroup.relIndex_self]

/-- For every `Γ ≤ SL(2, ℤ)`, the relative index `[±Γ : Γ]` is `1` or `2`. -/
theorem relIndex_withCenter_eq_one_or_two (Γ : Subgroup SL(2, ℤ)) :
    Γ.relIndex Γ.withCenter = 1 ∨ Γ.relIndex Γ.withCenter = 2 := by
  by_cases h : (-1 : SL(2, ℤ)) ∈ Γ
  · exact Or.inl (relIndex_withCenter_eq_one_of_neg_one_mem h)
  · exact Or.inr (relIndex_withCenter_eq_two_of_neg_one_notMem h)

/-- The relative index `[±Γ : Γ]` is always positive. -/
theorem relIndex_withCenter_pos (Γ : Subgroup SL(2, ℤ)) :
    0 < Γ.relIndex Γ.withCenter := by
  rcases relIndex_withCenter_eq_one_or_two Γ with h | h <;> omega

/-- The relative index `[±Γ : Γ]` is nonzero. -/
theorem relIndex_withCenter_ne_zero (Γ : Subgroup SL(2, ℤ)) :
    Γ.relIndex Γ.withCenter ≠ 0 :=
  (relIndex_withCenter_pos Γ).ne'

/-- **The centre-index dichotomy in product form**: for every subgroup `Γ ≤ SL(2, ℤ)`, the product
`[±Γ : Γ] · |{±I} ∩ Γ|` equals `2`, with no case split left for downstream consumers. -/
theorem relIndex_withCenter_mul_card_center_subgroupOf (Γ : Subgroup SL(2, ℤ)) :
    Γ.relIndex Γ.withCenter * Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) = 2 := by
  by_cases h : (-1 : SL(2, ℤ)) ∈ Γ
  · rw [relIndex_withCenter_eq_one_of_neg_one_mem h,
      (Matrix.SpecialLinearGroup.card_center_subgroupOf_eq_two_iff Γ).mpr h]
  · rw [relIndex_withCenter_eq_two_of_neg_one_notMem h,
      (Matrix.SpecialLinearGroup.card_center_subgroupOf_eq_one_iff Γ).mpr h]

private lemma orbitRel_subgroup_iff_effective (Γ : Subgroup SL(2, ℤ)) {z w : ℍ} :
    orbitRel (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ z w ↔ orbitRel (Γ.map sl2zToPSL2R) ℍ z w := by
  rw [Subgroup.orbitRel_map_sl2zToPSL2R_iff, orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨⟨_, g, hg, rfl⟩, h⟩
    exact ⟨g, hg, by simpa only [Subgroup.smul_def, MulAction.compHom_smul_def] using h⟩
  · rintro ⟨g, hg, h⟩
    exact ⟨⟨Matrix.SpecialLinearGroup.mapGL ℝ g, Subgroup.mem_map_of_mem _ hg⟩,
      by simpa only [Subgroup.smul_def, MulAction.compHom_smul_def] using h⟩

/-- The canonical equivalence between the matrix orbit space `(Γ : Subgroup (GL (Fin 2) ℝ)) \ ℍ`
and the effective Fuchsian orbit space `(Γ.map sl2zToPSL2R) \ ℍ`: the two actions have identical
orbits on `ℍ`. -/
def subgroupOrbitEquivEffectiveOrbit (Γ : Subgroup SL(2, ℤ)) :
    orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ ≃
      orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ where
  toFun := Quotient.map' id fun _ _ h ↦ (orbitRel_subgroup_iff_effective Γ).mp h
  invFun := Quotient.map' id fun _ _ h ↦ (orbitRel_subgroup_iff_effective Γ).mpr h
  left_inv o := Quotient.inductionOn' o fun _ ↦ rfl
  right_inv P := Quotient.inductionOn' P fun _ ↦ rfl

@[simp]
theorem subgroupOrbitEquivEffectiveOrbit_mk (Γ : Subgroup SL(2, ℤ)) (z : ℍ) :
    subgroupOrbitEquivEffectiveOrbit Γ (Quotient.mk'' z) = Quotient.mk'' z :=
  (rfl)

@[simp]
theorem subgroupOrbitEquivEffectiveOrbit_symm_mk (Γ : Subgroup SL(2, ℤ)) (z : ℍ) :
    (subgroupOrbitEquivEffectiveOrbit Γ).symm (Quotient.mk'' z) = Quotient.mk'' z :=
  (rfl)

/-- The matrix image `(Γ : Subgroup (GL (Fin 2) ℝ))` has the same point stabiliser orders as `Γ`
itself, since `mapGL ℝ` is injective. -/
theorem card_stabilizer_mapGL_eq (Γ : Subgroup SL(2, ℤ)) (z : ℍ) :
    Nat.card (stabilizer (Γ : Subgroup (GL (Fin 2) ℝ)) z) = Nat.card (stabilizer Γ z) := by
  have h := TauCeti.card_stabilizer_eq_card_ker_mul_card_stabilizer
    ((Matrix.SpecialLinearGroup.mapGL ℝ).subgroupMap Γ)
    (MonoidHom.subgroupMap_surjective _ _) z
    fun g ↦ by simp [Subgroup.smul_def, MulAction.compHom_smul_def]
  rw [Subgroup.ker_subgroupMap,
    (MonoidHom.ker_eq_bot_iff _).mpr Matrix.SpecialLinearGroup.mapGL_injective] at h
  simpa using h.symm

/-- **The stabiliser order in `Γ` splits off `{±I} ∩ Γ` above the effective image in `PSL(2, ℝ)`.**
This is the `PSL(2, ℝ)` counterpart of
`TauCeti.ModularGroup.card_stabilizer_eq_card_center_mul_card_stabilizer_psl`, stated directly on
`Γ.map sl2zToPSL2R`. -/
theorem card_stabilizer_eq_card_center_mul_card_stabilizer_effective
    (Γ : Subgroup SL(2, ℤ)) (z : ℍ) :
    Nat.card (stabilizer Γ z) =
      Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) *
        Nat.card (stabilizer (Γ.map sl2zToPSL2R) z) := by
  have h := TauCeti.card_stabilizer_eq_card_ker_mul_card_stabilizer
    (sl2zToPSL2R.subgroupMap Γ) (MonoidHom.subgroupMap_surjective _ _) z
    fun g ↦ by simp [Subgroup.smul_def]
  rwa [Subgroup.ker_subgroupMap, sl2zToPSL2R_ker] at h

/-- Orbitwise form of the stabiliser splitting: the matrix stabiliser order on `o` is
`|{±I} ∩ Γ|` times the effective stabiliser order `e_P` on the corresponding `PSL(2, ℝ)`-orbit. -/
theorem cardStabilizerOnOrbit_eq_card_center_mul_effective
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    cardStabilizerOnOrbit o =
      Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) *
        cardStabilizerOnOrbit (subgroupOrbitEquivEffectiveOrbit Γ o) := by
  induction o using Quotient.inductionOn' with
  | h z =>
    rw [subgroupOrbitEquivEffectiveOrbit_mk, cardStabilizerOnOrbit_mk, cardStabilizerOnOrbit_mk,
      card_stabilizer_mapGL_eq, card_stabilizer_eq_card_center_mul_card_stabilizer_effective]

/-- Every point orbit of `Γ.map sl2zToPSL2R` in `ℍ` has finite, nonempty stabiliser, so its
effective stabiliser order `e_P` is nonzero. -/
theorem cardStabilizerOnOrbit_effective_ne_zero
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    cardStabilizerOnOrbit P ≠ 0 := by
  intro h0
  have h := cardStabilizerOnOrbit_eq_card_center_mul_effective (Γ := Γ)
    ((subgroupOrbitEquivEffectiveOrbit Γ).symm P)
  rw [Equiv.apply_symm_apply, h0, mul_zero] at h
  exact cardStabilizerOnOrbit_ne_zero _ h

/-- The effective stabiliser order `e_P` is positive on every orbit in `(Γ.map sl2zToPSL2R) \ ℍ`. -/
theorem cardStabilizerOnOrbit_effective_pos
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    0 < cardStabilizerOnOrbit P :=
  Nat.pos_of_ne_zero (cardStabilizerOnOrbit_effective_ne_zero P)

end CenterAndOrbits

section Order

variable {Γ : Subgroup SL(2, ℤ)} {k k₁ k₂ : ℤ}
variable {F : Type*} [FunLike F ℍ ℂ]

/-- The vanishing order of a slash-invariant form on `Γ`, descended to the effective orbit space
`(Γ.map sl2zToPSL2R) \ ℍ`. -/
def orderOfVanishingOnEffectiveOrbit
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) : ℤ :=
  orderOfVanishingOnSubgroupOrbit f ((subgroupOrbitEquivEffectiveOrbit Γ).symm P)

@[simp]
theorem orderOfVanishingOnEffectiveOrbit_mk
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (z : ℍ) :
    orderOfVanishingOnEffectiveOrbit f
        (Quotient.mk'' z : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) =
      orderOfVanishingAt f z := by
  rw [orderOfVanishingOnEffectiveOrbit, subgroupOrbitEquivEffectiveOrbit_symm_mk,
    orderOfVanishingOnSubgroupOrbit_mk]

/-- Transporting a matrix orbit along `subgroupOrbitEquivEffectiveOrbit` preserves its vanishing
order. -/
@[simp]
theorem orderOfVanishingOnEffectiveOrbit_subgroupOrbitEquivEffectiveOrbit
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    orderOfVanishingOnEffectiveOrbit f (subgroupOrbitEquivEffectiveOrbit Γ o) =
      orderOfVanishingOnSubgroupOrbit f o := by
  rw [orderOfVanishingOnEffectiveOrbit, Equiv.symm_apply_apply]

/-- The vanishing order of a modular form on an effective orbit is nonnegative. -/
theorem orderOfVanishingOnEffectiveOrbit_nonneg
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    0 ≤ orderOfVanishingOnEffectiveOrbit f P :=
  orderOfVanishingOnSubgroupOrbit_nonneg f _

@[simp]
theorem orderOfVanishingOnEffectiveOrbit_zero
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit (0 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) P = 0 := by
  induction P using Quotient.inductionOn' with
  | h z => simp

/-- **Additivity on products**: for nonzero modular forms `f` and `g` of weights `k₁` and `k₂` on
`Γ`, the vanishing order of `f.mul g` on each effective orbit is the sum of their orders. -/
theorem orderOfVanishingOnEffectiveOrbit_modularForm_mul
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : f ≠ 0) (hg : g ≠ 0) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit (f.mul g) P =
      orderOfVanishingOnEffectiveOrbit f P + orderOfVanishingOnEffectiveOrbit g P := by
  induction P using Quotient.inductionOn' with
  | h z =>
    have hf' : (⇑f : ℍ → ℂ) ≠ 0 := fun h ↦ hf (DFunLike.ext' h)
    have hg' : (⇑g : ℍ → ℂ) ≠ 0 := fun h ↦ hg (DFunLike.ext' h)
    simp only [orderOfVanishingOnEffectiveOrbit_mk, _root_.ModularForm.coe_mul]
    exact orderOfVanishingAt_mul (ModularFormClass.holo f) (ModularFormClass.holo g) hf' hg' z

/-- A modular form for a finite-index subgroup `Γ ≤ SL(2, ℤ)` has nonzero vanishing order on only
finitely many effective orbits in `(Γ.map sl2zToPSL2R) \ ℍ`. -/
theorem hasFiniteSupport_orderOfVanishingOnEffectiveOrbit [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    Function.HasFiniteSupport (orderOfVanishingOnEffectiveOrbit (Γ := Γ) (k := k) f) := by
  refine ((hasFiniteSupport_orderOfVanishingOnSubgroupOrbit f).image
    (subgroupOrbitEquivEffectiveOrbit Γ)).subset fun P hP ↦ ?_
  exact ⟨(subgroupOrbitEquivEffectiveOrbit Γ).symm P, hP, Equiv.apply_symm_apply _ _⟩

/-- **The projective weighted vanishing order on an effective orbit**: `ord_P f / e_P`, where
`e_P = cardStabilizerOnOrbit P` is the order of the point stabiliser in `Γ.map sl2zToPSL2R`. -/
def weightedOrderOfVanishingOnEffectiveOrbit
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) : ℚ :=
  (orderOfVanishingOnEffectiveOrbit f P : ℚ) / (cardStabilizerOnOrbit P : ℚ)

theorem weightedOrderOfVanishingOnEffectiveOrbit_def
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit f P =
      (orderOfVanishingOnEffectiveOrbit f P : ℚ) / (cardStabilizerOnOrbit P : ℚ) :=
  (rfl)

@[simp]
theorem weightedOrderOfVanishingOnEffectiveOrbit_mk
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (z : ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit f
        (Quotient.mk'' z : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) =
      (orderOfVanishingAt ⇑f z : ℚ) / (Nat.card (stabilizer (Γ.map sl2zToPSL2R) z) : ℚ) := by
  rw [weightedOrderOfVanishingOnEffectiveOrbit_def, orderOfVanishingOnEffectiveOrbit_mk,
    cardStabilizerOnOrbit_mk]

/-- Multiplying the projective weighted order by the effective stabiliser order `e_P` recovers the
plain vanishing order on `P`. -/
theorem cardStabilizerOnOrbit_mul_weightedOrderOfVanishingOnEffectiveOrbit
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    (cardStabilizerOnOrbit P : ℚ) * weightedOrderOfVanishingOnEffectiveOrbit f P =
      (orderOfVanishingOnEffectiveOrbit f P : ℚ) := by
  rw [weightedOrderOfVanishingOnEffectiveOrbit_def]
  exact mul_div_cancel₀ _ (by exact_mod_cast cardStabilizerOnOrbit_effective_ne_zero P)

/-- The projective weighted vanishing order of a modular form is nonnegative. -/
theorem weightedOrderOfVanishingOnEffectiveOrbit_nonneg
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    0 ≤ weightedOrderOfVanishingOnEffectiveOrbit f P := by
  rw [weightedOrderOfVanishingOnEffectiveOrbit_def]
  exact div_nonneg (by exact_mod_cast orderOfVanishingOnEffectiveOrbit_nonneg f P) (by positivity)

@[simp]
theorem weightedOrderOfVanishingOnEffectiveOrbit_zero
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit
      (0 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) P = 0 := by
  simp [weightedOrderOfVanishingOnEffectiveOrbit_def]

/-- Additivity of the projective weighted order on products of nonzero modular forms. -/
theorem weightedOrderOfVanishingOnEffectiveOrbit_modularForm_mul
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : f ≠ 0) (hg : g ≠ 0) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit (f.mul g) P =
      weightedOrderOfVanishingOnEffectiveOrbit f P +
        weightedOrderOfVanishingOnEffectiveOrbit g P := by
  rw [weightedOrderOfVanishingOnEffectiveOrbit_def, weightedOrderOfVanishingOnEffectiveOrbit_def,
    weightedOrderOfVanishingOnEffectiveOrbit_def,
    orderOfVanishingOnEffectiveOrbit_modularForm_mul f g hf hg P, Int.cast_add, add_div]

/-- Only finitely many effective orbits carry nonzero projective weighted order. -/
theorem hasFiniteSupport_weightedOrderOfVanishingOnEffectiveOrbit [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    Function.HasFiniteSupport
      (weightedOrderOfVanishingOnEffectiveOrbit (Γ := Γ) (k := k) f) := by
  refine (hasFiniteSupport_orderOfVanishingOnEffectiveOrbit f).subset fun P hP ↦ ?_
  simp only [Function.mem_support, ne_eq] at hP ⊢
  exact fun h0 ↦ hP (by rw [weightedOrderOfVanishingOnEffectiveOrbit_def, h0]; simp)

/-- **Local comparison of matrix and projective interior weights.** At every orbit `o`, the matrix
weighted order `2 · ord f / |Stab_Γ o|` is `[±Γ : Γ]` times the projective weighted order
`ord f / e_P` on the corresponding effective orbit `P`. -/
theorem weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_withCenter_mul
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    weightedOrderOfVanishingOnSubgroupOrbit f o =
      (Γ.relIndex Γ.withCenter : ℚ) *
        weightedOrderOfVanishingOnEffectiveOrbit f (subgroupOrbitEquivEffectiveOrbit Γ o) := by
  set P := subgroupOrbitEquivEffectiveOrbit Γ o
  have he : (cardStabilizerOnOrbit P : ℚ) ≠ 0 := by
    exact_mod_cast cardStabilizerOnOrbit_effective_ne_zero P
  have hstab : (cardStabilizerOnOrbit o : ℚ) =
      (Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) : ℚ) *
        (cardStabilizerOnOrbit P : ℚ) := by
    exact_mod_cast cardStabilizerOnOrbit_eq_card_center_mul_effective o
  have hprod : (Γ.relIndex Γ.withCenter : ℚ) *
      (Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) : ℚ) = 2 := by
    exact_mod_cast relIndex_withCenter_mul_card_center_subgroupOf Γ
  have hcz : (Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) : ℚ) ≠ 0 :=
    right_ne_zero_of_mul (by rw [hprod]; norm_num)
  rw [weightedOrderOfVanishingOnSubgroupOrbit_def, weightedOrderOfVanishingOnEffectiveOrbit_def,
    orderOfVanishingOnEffectiveOrbit_subgroupOrbitEquivEffectiveOrbit, hstab, ← hprod]
  field_simp

/-- **Global comparison of matrix and projective interior divisor sums.** Summing over `(Γ \ ℍ)` in
the matrix convention multiplies the projective interior divisor sum over
`(Γ.map sl2zToPSL2R) \ ℍ` by `[±Γ : Γ]`. -/
theorem finsum_weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_withCenter_mul
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    (∑ᶠ o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
        weightedOrderOfVanishingOnSubgroupOrbit f o) =
      (Γ.relIndex Γ.withCenter : ℚ) *
        ∑ᶠ P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ,
          weightedOrderOfVanishingOnEffectiveOrbit f P := by
  simp_rw [weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_withCenter_mul f]
  rw [← finsum_comp_equiv (subgroupOrbitEquivEffectiveOrbit Γ), mul_finsum]

end Order

end TauCeti.ModularForm

end
