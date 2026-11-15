/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Norm.Valence
public import TauCeti.NumberTheory.ModularForms.WithCenter
import TauCeti.Analysis.Complex.Fuchsian.ProperAction
import TauCeti.Topology.Algebra.ConstMulAction
import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# Vanishing orders on the effective quotient `Γ \ ℍ`

For a subgroup `Γ ≤ SL(2, ℤ)`, the real matrix image `(Γ : Subgroup (GL (Fin 2) ℝ))` and the
effective Fuchsian image `Γ.map sl2zToPSL2R ≤ PSL(2, ℝ)` induce the same orbit relation on the
upper half-plane `ℍ`: the centre `{±I}` of `SL(2, ℤ)` acts trivially. Their point stabilisers,
however, differ by `{±I} ∩ Γ`, which has order `2` when `-1 ∈ Γ` and `1` when `-1 ∉ Γ`. Since
`[±Γ : Γ]` takes the complementary values `1` and `2`, the product `[±Γ : Γ] · |{±I} ∩ Γ|` is
identically `2` (`Subgroup.relIndex_withCenter_mul_card_center_subgroupOf_eq_two`).

Consequently, descending the vanishing order of a modular form to the effective quotient
`MulAction.orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ` — the interior of the compactified modular
curve `(Γ.map sl2zToPSL2R).CompactifiedQuotient` — and weighting each orbit `P` by the reciprocal
`1 / e_P` of its effective stabiliser order `e_P = cardStabilizerOnOrbit P` divides the matrix
weighted order `2 · ord_P f / |Stab_Γ P|` by the uniform factor `[±Γ : Γ]`.

## Main definitions

* `Subgroup.subgroupOrbitEquivEffectiveOrbit`: the canonical equivalence between the matrix orbit
  space `(Γ : Subgroup (GL (Fin 2) ℝ)) \ ℍ` and the effective orbit space
  `(Γ.map sl2zToPSL2R) \ ℍ`.
* `TauCeti.ModularForm.orderOfVanishingOnEffectiveOrbit`: the vanishing order descended to the
  effective orbit space.
* `TauCeti.ModularForm.weightedOrderOfVanishingOnEffectiveOrbit`: the projective weighted order
  `ord_P f / e_P` on the effective orbit space.

## Main results

* `TauCeti.ModularForm.cardStabilizerOnOrbit_eq_card_center_mul_effective`: the matrix stabiliser
  order on an orbit is `|{±I} ∩ Γ|` times the effective stabiliser order `e_P`.
* `TauCeti.ModularForm.orderOfVanishingOnEffectiveOrbit_eq_zero_iff` and
  `TauCeti.ModularForm.orderOfVanishingOnEffectiveOrbit_pos_iff`: zero-detection on effective
  orbits for nonzero modular forms.
* `TauCeti.ModularForm.orderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul`,
  `ModularForm.orderOfVanishingOnEffectiveOrbit_mul`, and their power, finite-product, and weighted
  counterparts: additivity and scaling under products and powers of modular forms.
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

namespace Subgroup

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

/-- `subgroupOrbitEquivEffectiveOrbit` acts as the identity on orbit representatives. -/
@[simp]
theorem subgroupOrbitEquivEffectiveOrbit_mk (Γ : Subgroup SL(2, ℤ)) (z : ℍ) :
    Γ.subgroupOrbitEquivEffectiveOrbit (Quotient.mk'' z) = Quotient.mk'' z :=
  (rfl)

/-- `subgroupOrbitEquivEffectiveOrbit.symm` acts as the identity on orbit representatives. -/
@[simp]
theorem subgroupOrbitEquivEffectiveOrbit_symm_mk (Γ : Subgroup SL(2, ℤ)) (z : ℍ) :
    Γ.subgroupOrbitEquivEffectiveOrbit.symm (Quotient.mk'' z) = Quotient.mk'' z :=
  (rfl)

end Subgroup

namespace TauCeti.ModularForm

section CenterAndOrbits

variable {Γ : Subgroup SL(2, ℤ)}

/-- Orbitwise form of the stabiliser splitting: the matrix stabiliser order on `o` is
`|{±I} ∩ Γ|` times the effective stabiliser order `e_P` on the corresponding `PSL(2, ℝ)`-orbit. -/
theorem cardStabilizerOnOrbit_eq_card_center_mul_effective
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    cardStabilizerOnOrbit o =
      Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) *
        cardStabilizerOnOrbit (Γ.subgroupOrbitEquivEffectiveOrbit o) := by
  induction o using Quotient.inductionOn' with
  | h z =>
    rw [Subgroup.subgroupOrbitEquivEffectiveOrbit_mk, cardStabilizerOnOrbit_mk,
      cardStabilizerOnOrbit_mk, Γ.card_stabilizer_mapGL,
      Γ.card_stabilizer_eq_card_center_mul_card_stabilizer_effective]

end CenterAndOrbits

section Order

variable {Γ : Subgroup SL(2, ℤ)} {k k₁ k₂ k₃ : ℤ}
variable {F F₁ F₂ F₃ : Type*} [FunLike F ℍ ℂ] [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ] [FunLike F₃ ℍ ℂ]

/-- The vanishing order of a slash-invariant form on `Γ`, descended to the effective orbit space
`(Γ.map sl2zToPSL2R) \ ℍ`. -/
def orderOfVanishingOnEffectiveOrbit
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) : ℤ :=
  orderOfVanishingOnSubgroupOrbit f (Γ.subgroupOrbitEquivEffectiveOrbit.symm P)

/-- Unfolding `orderOfVanishingOnEffectiveOrbit` across module boundaries. -/
theorem orderOfVanishingOnEffectiveOrbit_def
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit f P =
      orderOfVanishingOnSubgroupOrbit f (Γ.subgroupOrbitEquivEffectiveOrbit.symm P) :=
  (rfl)

/-- Evaluating `orderOfVanishingOnEffectiveOrbit` on the orbit of `z` gives `orderOfVanishingAt`. -/
@[simp]
theorem orderOfVanishingOnEffectiveOrbit_mk
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (z : ℍ) :
    orderOfVanishingOnEffectiveOrbit f
        (Quotient.mk'' z : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) =
      orderOfVanishingAt f z := by
  rw [orderOfVanishingOnEffectiveOrbit_def, Subgroup.subgroupOrbitEquivEffectiveOrbit_symm_mk,
    orderOfVanishingOnSubgroupOrbit_mk]

/-- Transporting a matrix orbit along `Subgroup.subgroupOrbitEquivEffectiveOrbit` preserves its
vanishing order. -/
@[simp]
theorem orderOfVanishingOnEffectiveOrbit_subgroupOrbitEquivEffectiveOrbit
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    orderOfVanishingOnEffectiveOrbit f (Γ.subgroupOrbitEquivEffectiveOrbit o) =
      orderOfVanishingOnSubgroupOrbit f o := by
  rw [orderOfVanishingOnEffectiveOrbit_def, Equiv.symm_apply_apply]

/-- The vanishing order of a modular form on an effective orbit is nonnegative. -/
theorem orderOfVanishingOnEffectiveOrbit_nonneg
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    0 ≤ orderOfVanishingOnEffectiveOrbit f P :=
  orderOfVanishingOnSubgroupOrbit_nonneg f _

/-- The zero form has vanishing order `0` on every effective orbit. -/
@[simp]
theorem orderOfVanishingOnEffectiveOrbit_zero
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] [Zero F] [IsZeroApply F]
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit (0 : F) P = 0 := by
  induction P using Quotient.inductionOn' with
  | h z => simp [FunLike.coe_zero]

/-- Scaling a slash-invariant form by a nonzero complex constant leaves its vanishing order on each
effective orbit unchanged. -/
@[simp]
theorem orderOfVanishingOnEffectiveOrbit_smul
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] [SMul ℂ F] [IsSMulApply ℂ F]
    {c : ℂ} (hc : c ≠ 0) (f : F) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit (c • f) P = orderOfVanishingOnEffectiveOrbit f P := by
  induction P using Quotient.inductionOn' with
  | h z => simp [FunLike.coe_smul, hc]

/-- For a nonzero modular form `f`, the vanishing order on an effective orbit `P` is zero if and
only if `f` is nonvanishing at every point representing `P`. -/
theorem orderOfVanishingOnEffectiveOrbit_eq_zero_iff
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit f P = 0 ↔
      ∀ z : ℍ, (Quotient.mk'' z : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) = P → f z ≠ 0 := by
  induction P using Quotient.inductionOn' with
  | h z₀ =>
    rw [orderOfVanishingOnEffectiveOrbit_mk, orderOfVanishingAt_eq_zero_iff
      (ModularFormClass.holo f) hf]
    refine ⟨fun hz₀ z hz ↦ ?_, fun h ↦ h z₀ rfl⟩
    have hord : orderOfVanishingAt f z = 0 := by
      rw [← orderOfVanishingOnEffectiveOrbit_mk (Γ := Γ), hz, orderOfVanishingOnEffectiveOrbit_mk]
      exact (orderOfVanishingAt_eq_zero_iff (ModularFormClass.holo f) hf).mpr hz₀
    exact (orderOfVanishingAt_eq_zero_iff (ModularFormClass.holo f) hf).mp hord

/-- For a nonzero modular form `f`, the vanishing order on an effective orbit `P` is positive if
and only if `f` vanishes at a point representing `P`. -/
theorem orderOfVanishingOnEffectiveOrbit_pos_iff
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    0 < orderOfVanishingOnEffectiveOrbit f P ↔
      ∃ z : ℍ, (Quotient.mk'' z : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) = P ∧ f z = 0 := by
  rw [(orderOfVanishingOnEffectiveOrbit_nonneg f P).lt_iff_ne, ne_comm]
  simpa only [not_forall, Classical.not_not, exists_prop] using
    (orderOfVanishingOnEffectiveOrbit_eq_zero_iff hf P).not

/-- **Additivity on products (`ModularFormClass` form)**: if `fg` is a slash-invariant form whose
underlying function is `f * g` for nonzero modular forms `f` and `g`, its vanishing order on each
effective orbit is the sum of their orders. -/
theorem orderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul
    [ModularFormClass F₁ (Γ : Subgroup (GL (Fin 2) ℝ)) k₁]
    [ModularFormClass F₂ (Γ : Subgroup (GL (Fin 2) ℝ)) k₂]
    [SlashInvariantFormClass F₃ (Γ : Subgroup (GL (Fin 2) ℝ)) k₃]
    (f : F₁) (g : F₂) (fg : F₃) (hfg : ⇑fg = ⇑f * ⇑g)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) (hg : (⇑g : ℍ → ℂ) ≠ 0)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit fg P =
      orderOfVanishingOnEffectiveOrbit f P + orderOfVanishingOnEffectiveOrbit g P := by
  induction P using Quotient.inductionOn' with
  | h z =>
    simp only [orderOfVanishingOnEffectiveOrbit_mk, hfg]
    exact orderOfVanishingAt_mul (ModularFormClass.holo f) (ModularFormClass.holo g) hf hg z

/-- **Power scaling (`ModularFormClass` form)**: if `fn` has underlying function `f ^ n` for a
modular form `f`, its vanishing order on each effective orbit is `n` times that of `f`. -/
theorem orderOfVanishingOnEffectiveOrbit_eq_mul_of_coe_eq_pow
    [ModularFormClass F₁ (Γ : Subgroup (GL (Fin 2) ℝ)) k₁]
    [SlashInvariantFormClass F₂ (Γ : Subgroup (GL (Fin 2) ℝ)) k₂]
    (f : F₁) (n : ℕ) (fn : F₂) (hfn : ⇑fn = ⇑f ^ n)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit fn P = n * orderOfVanishingOnEffectiveOrbit f P := by
  induction P using Quotient.inductionOn' with
  | h z =>
    simp only [orderOfVanishingOnEffectiveOrbit_mk, hfn]
    exact orderOfVanishingAt_pow (ModularFormClass.holo f) n z

/-- **Finite-product additivity (`ModularFormClass` form)**: if `fp` has underlying function
`∏ i ∈ s, g i` for nonzero modular forms `g i`, its vanishing order on each effective orbit is the
sum of their orders. -/
theorem orderOfVanishingOnEffectiveOrbit_eq_sum_of_coe_eq_prod {ι : Type*} {s : Finset ι}
    {kᵢ : ι → ℤ} {G : ι → Type*} [∀ i, FunLike (G i) ℍ ℂ]
    [∀ i, ModularFormClass (G i) (Γ : Subgroup (GL (Fin 2) ℝ)) (kᵢ i)]
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (g : (i : ι) → G i) (fp : F) (hfp : ⇑fp = ∏ i ∈ s, ⇑(g i))
    (hg : ∀ i ∈ s, (⇑(g i) : ℍ → ℂ) ≠ 0)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit fp P =
      ∑ i ∈ s, orderOfVanishingOnEffectiveOrbit (g i) P := by
  induction P using Quotient.inductionOn' with
  | h z =>
    simp only [orderOfVanishingOnEffectiveOrbit_mk, hfp]
    exact orderOfVanishingAt_prod (fun i _ ↦ ModularFormClass.holo (g i)) hg z

/-- **Additivity on products**: for nonzero modular forms `f` and `g` of weights `k₁` and `k₂` on
`Γ`, the vanishing order of `f.mul g` on each effective orbit is the sum of their orders. -/
theorem _root_.ModularForm.orderOfVanishingOnEffectiveOrbit_mul
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : f ≠ 0) (hg : g ≠ 0) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit (f.mul g) P =
      orderOfVanishingOnEffectiveOrbit f P + orderOfVanishingOnEffectiveOrbit g P :=
  orderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul f g (f.mul g)
    (_root_.ModularForm.coe_mul f g)
    (fun h ↦ hf (DFunLike.ext' h)) (fun h ↦ hg (DFunLike.ext' h)) P

/-- Vanishing orders on effective orbits scale under `ModularForm.pow`. -/
theorem _root_.ModularForm.orderOfVanishingOnEffectiveOrbit_pow
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit (f.pow n) P = n * orderOfVanishingOnEffectiveOrbit f P :=
  orderOfVanishingOnEffectiveOrbit_eq_mul_of_coe_eq_pow f n (f.pow n)
    (_root_.ModularForm.coe_pow f n) P

/-- Vanishing orders on effective orbits sum over `ModularForm.prod` of nonzero forms. -/
theorem _root_.ModularForm.orderOfVanishingOnEffectiveOrbit_prod {ι : Type*} {s : Finset ι}
    {kᵢ : ι → ℤ} (m : ℤ) (hm : m = ∑ i ∈ s, kᵢ i)
    (g : (i : ι) → ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (kᵢ i))
    (hg : ∀ i ∈ s, g i ≠ 0) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit (_root_.ModularForm.prod m hm g) P =
      ∑ i ∈ s, orderOfVanishingOnEffectiveOrbit (g i) P :=
  orderOfVanishingOnEffectiveOrbit_eq_sum_of_coe_eq_prod g (_root_.ModularForm.prod m hm g)
    (by simp) (fun i hi h ↦ hg i hi (DFunLike.ext' h)) P

/-- Additivity on `CuspForm.mulModularForm` for nonzero forms. -/
theorem _root_.CuspForm.orderOfVanishingOnEffectiveOrbit_mulModularForm
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : f ≠ 0) (hg : g ≠ 0) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    orderOfVanishingOnEffectiveOrbit (f.mulModularForm g) P =
      orderOfVanishingOnEffectiveOrbit f P + orderOfVanishingOnEffectiveOrbit g P :=
  orderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul f g (f.mulModularForm g)
    (_root_.CuspForm.coe_mulModularForm f g)
    (fun h ↦ hf (DFunLike.ext' h)) (fun h ↦ hg (DFunLike.ext' h)) P

/-- A modular form for a finite-index subgroup `Γ ≤ SL(2, ℤ)` has nonzero vanishing order on only
finitely many effective orbits in `(Γ.map sl2zToPSL2R) \ ℍ`. -/
theorem hasFiniteSupport_orderOfVanishingOnEffectiveOrbit [Γ.FiniteIndex]
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) :
    Function.HasFiniteSupport (orderOfVanishingOnEffectiveOrbit (Γ := Γ) (k := k) f) := by
  refine ((hasFiniteSupport_orderOfVanishingOnSubgroupOrbit f).image
    Γ.subgroupOrbitEquivEffectiveOrbit).subset fun P hP ↦ ?_
  exact ⟨Γ.subgroupOrbitEquivEffectiveOrbit.symm P, hP, Equiv.apply_symm_apply _ _⟩

/-- **The projective weighted vanishing order on an effective orbit**: `ord_P f / e_P`, where
`e_P = cardStabilizerOnOrbit P` is the order of the point stabiliser in `Γ.map sl2zToPSL2R`. -/
def weightedOrderOfVanishingOnEffectiveOrbit
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) : ℚ :=
  (orderOfVanishingOnEffectiveOrbit f P : ℚ) / (cardStabilizerOnOrbit P : ℚ)

/-- Unfolding `weightedOrderOfVanishingOnEffectiveOrbit` across module boundaries. -/
theorem weightedOrderOfVanishingOnEffectiveOrbit_def
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit f P =
      (orderOfVanishingOnEffectiveOrbit f P : ℚ) / (cardStabilizerOnOrbit P : ℚ) :=
  (rfl)

/-- Evaluating `weightedOrderOfVanishingOnEffectiveOrbit` on the orbit of `z` divides
`orderOfVanishingAt` by the effective stabiliser order at `z`. -/
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
  exact mul_div_cancel₀ _ (by exact_mod_cast TauCeti.cardStabilizerOnOrbit_ne_zero P)

/-- The projective weighted vanishing order of a modular form is nonnegative. -/
theorem weightedOrderOfVanishingOnEffectiveOrbit_nonneg
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    0 ≤ weightedOrderOfVanishingOnEffectiveOrbit f P := by
  rw [weightedOrderOfVanishingOnEffectiveOrbit_def]
  exact div_nonneg (by exact_mod_cast orderOfVanishingOnEffectiveOrbit_nonneg f P) (by positivity)

/-- The zero form has projective weighted vanishing order `0` on every effective orbit. -/
@[simp]
theorem weightedOrderOfVanishingOnEffectiveOrbit_zero
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] [Zero F] [IsZeroApply F]
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit (0 : F) P = 0 := by
  simp [weightedOrderOfVanishingOnEffectiveOrbit_def]

/-- Scaling a slash-invariant form by a nonzero complex constant leaves its projective weighted
order unchanged. -/
@[simp]
theorem weightedOrderOfVanishingOnEffectiveOrbit_smul
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] [SMul ℂ F] [IsSMulApply ℂ F]
    {c : ℂ} (hc : c ≠ 0) (f : F) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit (c • f) P =
      weightedOrderOfVanishingOnEffectiveOrbit f P := by
  simp [weightedOrderOfVanishingOnEffectiveOrbit_def, hc]

/-- For a nonzero modular form `f`, the projective weighted order on `P` vanishes if and only if
`f` is nonvanishing on `P`. -/
theorem weightedOrderOfVanishingOnEffectiveOrbit_eq_zero_iff
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit f P = 0 ↔
      ∀ z : ℍ, (Quotient.mk'' z : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) = P → f z ≠ 0 := by
  have he : (cardStabilizerOnOrbit P : ℚ) ≠ 0 := by
    exact_mod_cast TauCeti.cardStabilizerOnOrbit_ne_zero P
  rw [weightedOrderOfVanishingOnEffectiveOrbit_def, div_eq_zero_iff, or_iff_left he,
    Int.cast_eq_zero, orderOfVanishingOnEffectiveOrbit_eq_zero_iff hf P]

/-- For a nonzero modular form `f`, the projective weighted order on `P` is positive if and only if
`f` vanishes at a point representing `P`. -/
theorem weightedOrderOfVanishingOnEffectiveOrbit_pos_iff
    [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] {f : F} (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    0 < weightedOrderOfVanishingOnEffectiveOrbit f P ↔
      ∃ z : ℍ, (Quotient.mk'' z : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) = P ∧ f z = 0 := by
  have he : (0 : ℚ) < (cardStabilizerOnOrbit P : ℚ) := by
    exact_mod_cast TauCeti.cardStabilizerOnOrbit_pos P
  rw [weightedOrderOfVanishingOnEffectiveOrbit_def, div_pos_iff_of_pos_right he, Int.cast_pos,
    orderOfVanishingOnEffectiveOrbit_pos_iff hf P]

/-- Additivity of the projective weighted order on products (`ModularFormClass` form). -/
theorem weightedOrderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul
    [ModularFormClass F₁ (Γ : Subgroup (GL (Fin 2) ℝ)) k₁]
    [ModularFormClass F₂ (Γ : Subgroup (GL (Fin 2) ℝ)) k₂]
    [SlashInvariantFormClass F₃ (Γ : Subgroup (GL (Fin 2) ℝ)) k₃]
    (f : F₁) (g : F₂) (fg : F₃) (hfg : ⇑fg = ⇑f * ⇑g)
    (hf : (⇑f : ℍ → ℂ) ≠ 0) (hg : (⇑g : ℍ → ℂ) ≠ 0)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit fg P =
      weightedOrderOfVanishingOnEffectiveOrbit f P +
        weightedOrderOfVanishingOnEffectiveOrbit g P := by
  rw [weightedOrderOfVanishingOnEffectiveOrbit_def, weightedOrderOfVanishingOnEffectiveOrbit_def,
    weightedOrderOfVanishingOnEffectiveOrbit_def,
    orderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul f g fg hfg hf hg P, Int.cast_add,
    add_div]

/-- Power scaling of the projective weighted order (`ModularFormClass` form). -/
theorem weightedOrderOfVanishingOnEffectiveOrbit_eq_mul_of_coe_eq_pow
    [ModularFormClass F₁ (Γ : Subgroup (GL (Fin 2) ℝ)) k₁]
    [SlashInvariantFormClass F₂ (Γ : Subgroup (GL (Fin 2) ℝ)) k₂]
    (f : F₁) (n : ℕ) (fn : F₂) (hfn : ⇑fn = ⇑f ^ n)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit fn P =
      n * weightedOrderOfVanishingOnEffectiveOrbit f P := by
  rw [weightedOrderOfVanishingOnEffectiveOrbit_def, weightedOrderOfVanishingOnEffectiveOrbit_def,
    orderOfVanishingOnEffectiveOrbit_eq_mul_of_coe_eq_pow f n fn hfn P, Int.cast_mul,
    Int.cast_natCast, mul_div_assoc]

/-- Finite-product additivity of the projective weighted order (`ModularFormClass` form). -/
theorem weightedOrderOfVanishingOnEffectiveOrbit_eq_sum_of_coe_eq_prod {ι : Type*} {s : Finset ι}
    {kᵢ : ι → ℤ} {G : ι → Type*} [∀ i, FunLike (G i) ℍ ℂ]
    [∀ i, ModularFormClass (G i) (Γ : Subgroup (GL (Fin 2) ℝ)) (kᵢ i)]
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (g : (i : ι) → G i) (fp : F) (hfp : ⇑fp = ∏ i ∈ s, ⇑(g i))
    (hg : ∀ i ∈ s, (⇑(g i) : ℍ → ℂ) ≠ 0)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit fp P =
      ∑ i ∈ s, weightedOrderOfVanishingOnEffectiveOrbit (g i) P := by
  simp only [weightedOrderOfVanishingOnEffectiveOrbit_def,
    orderOfVanishingOnEffectiveOrbit_eq_sum_of_coe_eq_prod g fp hfp hg P, Int.cast_sum,
    Finset.sum_div]

/-- Additivity of the projective weighted order on products of nonzero modular forms. -/
theorem _root_.ModularForm.weightedOrderOfVanishingOnEffectiveOrbit_mul
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : f ≠ 0) (hg : g ≠ 0) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit (f.mul g) P =
      weightedOrderOfVanishingOnEffectiveOrbit f P +
        weightedOrderOfVanishingOnEffectiveOrbit g P :=
  weightedOrderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul f g (f.mul g)
    (_root_.ModularForm.coe_mul f g)
    (fun h ↦ hf (DFunLike.ext' h)) (fun h ↦ hg (DFunLike.ext' h)) P

/-- Projective weighted vanishing orders scale under `ModularForm.pow`. -/
theorem _root_.ModularForm.weightedOrderOfVanishingOnEffectiveOrbit_pow
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ)
    (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit (f.pow n) P =
      n * weightedOrderOfVanishingOnEffectiveOrbit f P :=
  weightedOrderOfVanishingOnEffectiveOrbit_eq_mul_of_coe_eq_pow f n (f.pow n)
    (_root_.ModularForm.coe_pow f n) P

/-- Projective weighted vanishing orders sum over `ModularForm.prod` of nonzero forms. -/
theorem _root_.ModularForm.weightedOrderOfVanishingOnEffectiveOrbit_prod {ι : Type*}
    {s : Finset ι} {kᵢ : ι → ℤ} (m : ℤ) (hm : m = ∑ i ∈ s, kᵢ i)
    (g : (i : ι) → ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (kᵢ i))
    (hg : ∀ i ∈ s, g i ≠ 0) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit (_root_.ModularForm.prod m hm g) P =
      ∑ i ∈ s, weightedOrderOfVanishingOnEffectiveOrbit (g i) P :=
  weightedOrderOfVanishingOnEffectiveOrbit_eq_sum_of_coe_eq_prod g
    (_root_.ModularForm.prod m hm g) (by simp) (fun i hi h ↦ hg i hi (DFunLike.ext' h)) P

/-- Additivity of the projective weighted order on `CuspForm.mulModularForm`. -/
theorem _root_.CuspForm.weightedOrderOfVanishingOnEffectiveOrbit_mulModularForm
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₁)
    (g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k₂)
    (hf : f ≠ 0) (hg : g ≠ 0) (P : orbitRel.Quotient (Γ.map sl2zToPSL2R) ℍ) :
    weightedOrderOfVanishingOnEffectiveOrbit (f.mulModularForm g) P =
      weightedOrderOfVanishingOnEffectiveOrbit f P +
        weightedOrderOfVanishingOnEffectiveOrbit g P :=
  weightedOrderOfVanishingOnEffectiveOrbit_eq_add_of_coe_eq_mul f g (f.mulModularForm g)
    (_root_.CuspForm.coe_mulModularForm f g)
    (fun h ↦ hf (DFunLike.ext' h)) (fun h ↦ hg (DFunLike.ext' h)) P

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
        weightedOrderOfVanishingOnEffectiveOrbit f (Γ.subgroupOrbitEquivEffectiveOrbit o) := by
  set P := Γ.subgroupOrbitEquivEffectiveOrbit o
  have he : (cardStabilizerOnOrbit P : ℚ) ≠ 0 := by
    exact_mod_cast TauCeti.cardStabilizerOnOrbit_ne_zero P
  have hstab : (cardStabilizerOnOrbit o : ℚ) =
      (Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) : ℚ) *
        (cardStabilizerOnOrbit P : ℚ) := by
    exact_mod_cast cardStabilizerOnOrbit_eq_card_center_mul_effective o
  have hprod : (Γ.relIndex Γ.withCenter : ℚ) *
      (Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) : ℚ) = 2 := by
    exact_mod_cast Γ.relIndex_withCenter_mul_card_center_subgroupOf_eq_two
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
  rw [← finsum_comp_equiv Γ.subgroupOrbitEquivEffectiveOrbit, mul_finsum]

end Order

end TauCeti.ModularForm

end
