/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import TauCeti.Algebra.AddCircle
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Character
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Delta
import TauCeti.RepresentationTheory.Homological.TateCohomology.Connecting.GroupHomology
import TauCeti.RepresentationTheory.Homological.TateCohomology.Connecting.LowDegree
import TauCeti.RepresentationTheory.Coinduced

/-!
# The low-degree Tate pairing with a character class

For a finite group `G` of order `n`, the cup product pairs its additive abelianization,
identified with `Ĥ⁻²(G, ℤ)` (`TauCeti.TateCohomology.HNegTwoAddEquivAbelianization`), with the
connecting class `δχ ∈ Ĥ²(G, ℤ)` of a character `χ : Gᵃᵇ → ℚ/ℤ`, landing in
`Ĥ⁰(G, ℤ) = ℤ/nℤ`. This file computes the pairing: for `σ ∈ Gᵃᵇ`, the product `σ ∪ δχ` is the
class of `-k`, for any integer `k` with `k / n ≡ χ(σ) (mod 1)`
(`TauCeti.TateCohomology.map_leftUnitor_cup_characterConnectingClass`). In other words, the
pairing `Gᵃᵇ × Hom(Gᵃᵇ, ℚ/ℤ) → (1/n)ℤ/ℤ` that it induces is `(σ, χ) ↦ -χ(σ)`.

The computation has three steps.

* For `x ∈ Ĥ⁻²(G, ℤ)`, the class `x ∪ δχ` is the Tate connecting map of the sequence
  `0 → ℤ → ℚ → ℚ/ℤ → 0`, tensored on the left with `ℤ`, applied to the degree `(-2, 1)` product
  `x ∪ χ` with the degree-one class of `χ`. The sign is positive because `x` has even degree
  (`TauCeti.TateCohomology.cup_characterConnectingClass_eq_tateδ`).
* The degree `(-2, 1)` product is evaluation of the character up to sign: `σ ∪ χ` is the class in
  `Ĥ⁻¹(G, ℤ ⊗ ℚ/ℤ)` of `1 ⊗ (-χ(σ))` (`TauCeti.TateCohomology.cup_character_eq_HNegOneπ`). The
  product is defined by shifting `χ` to the invariant `g ↦ χ(g)` of the first upward dimension
  shift of `ℚ/ℤ` (`TauCeti.TateCohomology.characterDimensionShift`), so `σ ∪ χ` is the connecting
  map of the upward shifting sequence applied to the image of `σ`. Through first homology, the
  class of `σ = g` is the cycle `[g] ⊗ (1 ⊗ (h ↦ χ(h)))`, whose boundary, computed with the
  homological differential `[g] ⊗ m ↦ g⁻¹ • m - m`, is the constant function `h ↦ -χ(g)`. This is
  where the sign comes from.
* The connecting map `Ĥ⁻¹(G, ℤ ⊗ ℚ/ℤ) → Ĥ⁰(G, ℤ ⊗ ℤ)` lifts `1 ⊗ (-χ(σ)) = 1 ⊗ (-k/n)` to
  `ℤ ⊗ ℚ` and takes its norm, which is `1 ⊗ (-k)`.

This is the low-degree normalization through which a character detects the Artin map of a class
formation. Its Nakayama isomorphism is induced by cup product with the fundamental class in degree
`-2`, and Artin reciprocity is the inverse of that isomorphism.

## Main results

* `TauCeti.TateCohomology.cup_characterConnectingClass_eq_tateδ`: `x ∪ δχ` is the tensored
  connecting map applied to the degree `(-2, 1)` product `x ∪ χ`.
* `TauCeti.TateCohomology.cup_character_eq_HNegOneπ`: for `σ ∈ Gᵃᵇ`, the degree `(-2, 1)` product
  `σ ∪ χ` is the class of `1 ⊗ (-χ(σ))` in `Ĥ⁻¹(G, ℤ ⊗ ℚ/ℤ)`.
* `TauCeti.TateCohomology.map_leftUnitor_cup_characterConnectingClass`: for `σ ∈ Gᵃᵇ`, the
  product `σ ∪ δχ ∈ Ĥ⁰(G, ℤ)` is `-k` times the class of `1` whenever `k / |G| ≡ χ(σ) (mod 1)`.
* `TauCeti.TateCohomology.toRatAddCircle_map_leftUnitor_cup_characterConnectingClass`: under
  the canonical embedding `Ĥ⁰(G, ℤ) = ℤ/|G|ℤ → ℚ/ℤ`, this product is `-χ(σ)`.

## References

* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter IV (Atiyah–Wall),
  §7.
* E. Artin and J. Tate, *Class Field Theory*, Chapter XIV, §3.
* J.-P. Serre, *Local Fields*, Chapter XI, §3.
-/

public noncomputable section

open CategoryTheory MonoidalCategory Rep groupHomology

namespace TauCeti.TateCohomology

variable (G : Type) [Group G] [Fintype G]

/-- Cup product with the connecting class `δχ` is the connecting map of the tensored
sequence applied to the degree `(-2, 1)` cup product with the character class. The sign is positive
because the left degree is even. -/
theorem cup_characterConnectingClass_eq_tateδ
    (x : tateCohomology (Rep.trivial ℤ G ℤ) (-2))
    (χ : Additive (Abelianization G) →+ AddCircle (1 : ℚ)) :
    cup (Rep.trivial ℤ G ℤ) (Rep.ratAddCircleShortComplex G).X₁ (-2) 2 0 (by omega) x
        (characterConnectingClass G χ) =
      _root_.TateCohomology.δ
        (shortExact_map_tensorLeft_of_flat
          (Rep.ratAddCircleShortComplex_shortExact G) (Rep.trivial ℤ G ℤ)) (-1)
        (cup (Rep.trivial ℤ G ℤ) (Rep.ratAddCircleShortComplex G).X₃
          (-2) 1 (-1) (by omega) x
          (Rep.fromGroupCohomology (Rep.ratAddCircleShortComplex G).X₃ 1
            ((groupCohomology.H1IsoOfIsTrivial (Rep.ratAddCircleShortComplex G).X₃).inv
              (χ.comp Abelianization.of.toAdditive)))) := by
  rw [characterConnectingClass_eq_tateδ]
  have h := cup_δ_of_flat (Rep.trivial ℤ G ℤ)
    (Rep.ratAddCircleShortComplex_shortExact G) (p := (-2)) (q := 1) (n := (-1))
    (by omega) x
    (Rep.fromGroupCohomology (Rep.ratAddCircleShortComplex G).X₃ 1
      ((groupCohomology.H1IsoOfIsTrivial (Rep.ratAddCircleShortComplex G).X₃).inv
        (χ.comp Abelianization.of.toAdditive)))
  rw [Int.negOnePow_even _ (by use (-1); norm_num), one_smul] at h
  norm_num at h ⊢
  exact h

/-- For `σ ∈ Gᵃᵇ`, the elementary tensor `1 ⊗ χ(σ)` of the trivial representation
`ℤ ⊗ ℚ/ℤ` has norm zero, because `|G| • σ = 0`. -/
private theorem one_tmul_mem_ker_norm (σ : Additive (Abelianization G))
    (χ : Additive (Abelianization G) →+ AddCircle (1 : ℚ)) :
    ((1 : ℤ) ⊗ₜ[ℤ] χ σ : (Rep.trivial ℤ G ℤ ⊗ (Rep.ratAddCircleShortComplex G).X₃).V) ∈
      LinearMap.ker (Rep.trivial ℤ G ℤ ⊗ (Rep.ratAddCircleShortComplex G).X₃).ρ.norm := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul σ)
  obtain rfl : Additive.ofMul (Abelianization.of g) = σ := congrArg Additive.ofMul hg
  rw [LinearMap.mem_ker]
  simp only [tensor_V, Representation.norm, tensor_ρ, Representation.tprod_apply,
    LinearMap.coe_sum, Finset.sum_apply, TensorProduct.map_tmul, Representation.trivial_apply,
    Finset.sum_const, Finset.card_univ]
  rw [← TensorProduct.tmul_smul, ← map_nsmul, ← ofMul_pow, ← map_pow, pow_card_eq_one, map_one,
    ofMul_one, map_zero, TensorProduct.tmul_zero]

-- The function `f : h ↦ χ(h)` in the representation coinduced from `ℚ/ℤ` satisfies
-- `g⁻¹ • f - f = -χ(g)`, a constant function: `(g⁻¹ • f)(h) = χ(h g⁻¹) = χ(h) - χ(g)`.
omit [Fintype G] in
private theorem coindBot_ρ_inv_sub_character (g : G)
    (χ : Additive (Abelianization G) →+ AddCircle (1 : ℚ)) :
    (coindBot ℤ G (AddCircle (1 : ℚ))).ρ g⁻¹
        ((coindBotEquivPi ℤ G (AddCircle (1 : ℚ))).symm fun h ↦
          χ (Additive.ofMul (Abelianization.of h))) -
      (coindBotEquivPi ℤ G (AddCircle (1 : ℚ))).symm
        (fun h ↦ χ (Additive.ofMul (Abelianization.of h))) =
      -(coindBotUnit (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).hom
        (χ (Additive.ofMul (Abelianization.of g))) := by
  apply (coindBotEquivPi ℤ G (AddCircle (1 : ℚ))).injective
  rw [map_sub, map_neg]
  funext h
  rw [Pi.sub_apply, Pi.neg_apply, coindBotEquivPi_apply, Representation.coind_apply_coe_apply,
    coindBotEquivPi_apply, coindBotEquivPi_apply, coindBotUnit_hom_apply_coe]
  simp only [coindBotEquivPi_symm_apply_coe, Representation.trivial_apply]
  rw [map_mul, ofMul_mul, map_add, map_inv, ofMul_inv, map_neg]
  abel

-- The homological connecting map of the upward shifting sequence of `ℚ/ℤ`, tensored on the left
-- with `ℤ`, sends the class of the cycle `[g] ⊗ (1 ⊗ c)`, where `c` is the image of `h ↦ χ(h)`, to
-- the class of `1 ⊗ (-χ(g))`: the cycle lifts to `[g] ⊗ (1 ⊗ f)` with `f : h ↦ χ(h)` coinduced,
-- whose boundary `1 ⊗ (g⁻¹ • f - f)` is `1 ⊗ (-χ(g))`.
omit [Fintype G] in
private theorem δ₀_character
    (hS : ((ShortComplex.mk (coindBotUnit (Rep.ratAddCircleShortComplex G).X₃)
      (dimensionShiftUpπ (Rep.ratAddCircleShortComplex G).X₃)
      (coindBotUnit_comp_dimensionShiftUpπ _)).map (tensorLeft (Rep.trivial ℤ G ℤ))).ShortExact)
    (g : G) (χ : Additive (Abelianization G) →+ AddCircle (1 : ℚ)) :
    groupHomology.δ hS 1 0 rfl (H1π _ (mapCycles₁ (MonoidHom.id G)
        (Rep.tensorInvariant (Rep.trivial ℤ G ℤ) (characterDimensionShift G χ))
        ((cycles₁IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).inv (Finsupp.single g 1)))) =
      groupHomology.H0π _ ((1 : ℤ) ⊗ₜ[ℤ] (-χ (Additive.ofMul (Abelianization.of g)))) := by
  let f : coindBot ℤ G (AddCircle (1 : ℚ)) :=
    (coindBotEquivPi ℤ G (AddCircle (1 : ℚ))).symm fun h ↦
      χ (Additive.ofMul (Abelianization.of h))
  refine δ₀_apply hS _ (Finsupp.single g ((1 : ℤ) ⊗ₜ[ℤ] f)) ?_
    ((1 : ℤ) ⊗ₜ[ℤ] (-χ (Additive.ofMul (Abelianization.of g)))) ?_
  · erw [coe_mapCycles₁, cycles₁IsoOfIsTrivial_inv_apply]
    simp only [chainsMap₁, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, MonoidHom.id_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
    congr 1
    erw [Rep.tensorInvariant_hom_apply]
    simp only [ShortComplex.map_g, curriedTensor_obj_map, hom_whiskerLeft,
      Representation.IntertwiningMap.coe_toLinearMap]
    rw [coe_characterDimensionShift]
    exact Representation.IntertwiningMap.lTensor_apply _ _ _
  · rw [d₁₀_single]
    simp only [ShortComplex.map_X₂, ShortComplex.map_f, curriedTensor_obj_obj, tensor_V,
      ShortComplex.map_X₁, tensor_ρ, curriedTensor_obj_map, hom_whiskerLeft,
      Representation.IntertwiningMap.lTensor_apply, map_neg, Representation.tprod_apply,
      Representation.coind_apply, TensorProduct.map_tmul, Representation.trivial_apply]
    rw [← TensorProduct.tmul_sub]
    exact congrArg _ (coindBot_ρ_inv_sub_character G g χ).symm

/-- **The degree `(-2, 1)` cup product with a character is evaluation, up to sign.** For
`σ ∈ Gᵃᵇ = Ĥ⁻²(G, ℤ)` and a character `χ : Gᵃᵇ → ℚ/ℤ`, read as a class in `Ĥ¹(G, ℚ/ℤ)`, the
product `σ ∪ χ` is the class of the norm-zero element `1 ⊗ (-χ(σ))` in `Ĥ⁻¹(G, ℤ ⊗ ℚ/ℤ)`. -/
theorem cup_character_eq_HNegOneπ (σ : Additive (Abelianization G))
    (χ : Additive (Abelianization G) →+ AddCircle (1 : ℚ)) :
    cup (Rep.trivial ℤ G ℤ) (Rep.ratAddCircleShortComplex G).X₃ (-2) 1 (-1) (by omega)
        (HNegTwoAddEquivAbelianization.symm σ)
        (Rep.fromGroupCohomology (Rep.ratAddCircleShortComplex G).X₃ 1
          ((groupCohomology.H1IsoOfIsTrivial (Rep.ratAddCircleShortComplex G).X₃).inv
            (χ.comp Abelianization.of.toAdditive))) =
      HNegOneπ _ ⟨(1 : ℤ) ⊗ₜ[ℤ] (-χ σ), by
        rw [TensorProduct.tmul_neg]
        exact neg_mem (one_tmul_mem_ker_norm G σ χ)⟩ := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul σ)
  obtain rfl : Additive.ofMul (Abelianization.of g) = σ := congrArg Additive.ofMul hg
  -- Shift `χ` to the invariant `g ↦ χ(g)` of the upward dimension shift of `ℚ/ℤ`; the cup product
  -- with `σ` is then the tensored connecting map applied to the image of `σ`.
  rw [← dimensionShiftUpIso_characterDimensionShift]
  refine (cup_dimensionShiftUpIso_hom (Rep.trivial ℤ G ℤ) (Rep.ratAddCircleShortComplex G).X₃
    (p := -2) (q := 0) (r' := -2) (r := -1) le_rfl (by omega) (by omega) _ _).trans ?_
  rw [cup_zero_right]
  erw [cupH0_H0π]
  rw [Int.negOnePow_even _ (by decide), one_smul]
  -- Compare both sides in `H₀(G, ℤ ⊗ ℚ/ℤ)`, into which `Ĥ⁻¹` injects.
  apply (ModuleCat.mono_iff_injective (toGroupHomology _ 0)).mp inferInstance
  rw [← ConcreteCategory.comp_apply (HNegOneπ _), HNegOneπ_comp_toGroupHomology]
  have hS := dimensionShiftUpSES_tensorLeft_shortExact (Rep.ratAddCircleShortComplex G).X₃
    (Rep.trivial ℤ G ℤ)
  rw [dimensionShiftUpSES_def] at hS
  erw [tensorDimensionShiftUpIso_hom]
  refine (ConcreteCategory.congr_hom (δ_comp_toGroupHomology hS 0) _).trans ?_
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  have hmap := ConcreteCategory.congr_hom (tateCohomologyFunctor_map_comp_toGroupHomology
    (Rep.tensorInvariant (Rep.trivial ℤ G ℤ) (characterDimensionShift G χ)) 1)
    (HNegTwoAddEquivAbelianization.symm (Additive.ofMul (Abelianization.of g)))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hmap
  erw [hmap]
  rw [toGroupHomology_eq_negSuccIso_hom, HNegTwoAddEquivAbelianization_symm_of, negSuccIso_hom]
  erw [Iso.inv_hom_id_apply]
  rw [H1π_comp_map_apply]
  exact δ₀_character G hS g χ

/-- **The Tate pairing of `Gᵃᵇ` with a character class.** For `σ ∈ Gᵃᵇ = Ĥ⁻²(G, ℤ)`, a character
`χ : Gᵃᵇ → ℚ/ℤ` and an integer `k` with `k / |G| ≡ χ(σ) (mod 1)`, the cup product `σ ∪ δχ`,
read in `Ĥ⁰(G, ℤ)` through the left unitor, is `-k` times the class of `1`. -/
theorem map_leftUnitor_cup_characterConnectingClass (σ : Additive (Abelianization G))
    (χ : Additive (Abelianization G) →+ AddCircle (1 : ℚ)) (k : ℤ)
    (hk : (((k : ℚ) / Nat.card G : ℚ) : AddCircle (1 : ℚ)) = χ σ) :
    (tateCohomologyFunctor 0).map (λ_ (Rep.trivial ℤ G ℤ)).hom
        (cup (Rep.trivial ℤ G ℤ) (Rep.trivial ℤ G ℤ) (-2) 2 0 (by omega)
          (HNegTwoAddEquivAbelianization.symm σ) (characterConnectingClass G χ)) =
      (-k) • trivialTateHZeroOne G := by
  rw [Nat.card_eq_fintype_card] at hk
  erw [cup_characterConnectingClass_eq_tateδ]
  rw [cup_character_eq_HNegOneπ]
  have hS := shortExact_map_tensorLeft_of_flat (Rep.ratAddCircleShortComplex_shortExact G)
    (Rep.trivial ℤ G ℤ)
  have hcard : (Fintype.card G : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  -- The connecting map lifts `1 ⊗ (-χ(σ))` to `1 ⊗ (-k / |G|)` and takes its norm `1 ⊗ (-k)`.
  have hδ := δ_neg_one_HNegOneπ hS
    ⟨(1 : ℤ) ⊗ₜ[ℤ] (-χ σ), by
        rw [TensorProduct.tmul_neg]
        exact neg_mem (one_tmul_mem_ker_norm G σ χ)⟩
    ((1 : ℤ) ⊗ₜ[ℤ] (-((k : ℚ) / Fintype.card G))) ?_
    ⟨(1 : ℤ) ⊗ₜ[ℤ] (-k), fun _ ↦ by simp [Representation.tprod_apply]⟩ ?_
  · erw [hδ, H0π_comp_tateCohomologyFunctor_map_apply]
    apply (H0LinearEquivTrivialIntZModCard G).injective
    rw [map_zsmul, H0LinearEquivTrivialIntZModCard_trivialTateHZeroOne]
    erw [H0LinearEquivTrivialIntZModCard_H0π]
    rw [zsmul_one]
    exact congrArg Int.cast (one_smul ℤ (-k))
  · dsimp only
    rw [← hk, ← QuotientAddGroup.mk_neg]
    rfl
  · rw [ShortComplex.map_f, curriedTensor_obj_map, hom_whiskerLeft,
      Representation.IntertwiningMap.lTensor_apply, ratAddCircleShortComplex_f_hom_apply]
    simp only [ShortComplex.map_X₂, curriedTensor_obj_obj, tensor_V, Int.cast_neg,
      Representation.norm, tensor_ρ, Representation.tprod_apply, LinearMap.coe_sum,
      Finset.sum_apply, TensorProduct.map_tmul, Representation.trivial_apply, Finset.sum_const,
      Finset.card_univ]
    rw [← TensorProduct.tmul_smul, nsmul_eq_mul, mul_neg, mul_div_cancel₀ _ hcard]

/-- Under the canonical embedding `Ĥ⁰(G, ℤ) = ℤ/|G|ℤ → ℚ/ℤ`, the Tate pairing of
`σ ∈ Gᵃᵇ` with the connecting class of a character `χ` is the negative evaluation `-χ(σ)`. -/
@[simp]
theorem toRatAddCircle_map_leftUnitor_cup_characterConnectingClass
    (σ : Additive (Abelianization G))
    (χ : Additive (Abelianization G) →+ AddCircle (1 : ℚ)) :
    ZMod.toRatAddCircle (Nat.card G)
        (H0LinearEquivTrivialIntZModCard G
          ((tateCohomologyFunctor 0).map (λ_ (Rep.trivial ℤ G ℤ)).hom
            (cup (Rep.trivial ℤ G ℤ) (Rep.trivial ℤ G ℤ) (-2) 2 0 (by omega)
              (HNegTwoAddEquivAbelianization.symm σ) (characterConnectingClass G χ)))) =
      -χ σ := by
  have hχ : χ σ ∈ AddSubgroup.torsionBy (AddCircle (1 : ℚ)) (Nat.card G : ℤ) := by
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul]
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul σ)
    obtain rfl : Additive.ofMul (Abelianization.of g) = σ := congrArg Additive.ofMul hg
    rw [← ofMul_pow, ← map_pow, pow_card_eq_one', map_one, ofMul_one, map_zero]
  rw [← ZMod.toRatAddCircle_range] at hχ
  obtain ⟨z, hz⟩ := hχ
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  have hk : (((k : ℚ) / Nat.card G : ℚ) : AddCircle (1 : ℚ)) = χ σ := by simpa using hz
  rw [map_leftUnitor_cup_characterConnectingClass G σ χ k hk, map_zsmul,
    H0LinearEquivTrivialIntZModCard_trivialTateHZeroOne]
  calc
    ZMod.toRatAddCircle (Nat.card G) ((-k : ℤ) • (1 : ZMod (Nat.card G))) =
        -ZMod.toRatAddCircle (Nat.card G) ((k : ℤ) • (1 : ZMod (Nat.card G))) := by
      rw [neg_zsmul, map_neg]
    _ = -ZMod.toRatAddCircle (Nat.card G) (k : ZMod (Nat.card G)) := by rw [zsmul_one]
    _ = -χ σ := congrArg Neg.neg hz

end TauCeti.TateCohomology
