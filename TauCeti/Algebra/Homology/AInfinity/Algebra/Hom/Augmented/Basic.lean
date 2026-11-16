/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Augmented.BarProjection
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Unital
import TauCeti.LinearAlgebra.TensorCoalgebra.Grading

/-!
# Morphisms of augmented `A∞` algebras

Let `(A, ε)` be an augmented `A∞` algebra with augmentation ideal `ker ε`, and let `C` be a
strictly unital `A∞` algebra.  Restriction along `reducedAlgebraInclusion : ker ε ⟶ A` sends any
strictly unital `A∞` morphism `A ⟶ C` to a nonunital `A∞` morphism `ker ε ⟶ C`.

This file shows that restriction is a bijection
(`TauCeti.AInfinityAlgebra.Augmentation.strictlyUnitalHomEquiv`): every nonunital `A∞` morphism
`g : ker ε ⟶ C` extends uniquely to a strictly unital `A∞` morphism `A ⟶ C`, whose Taylor map
sends a word `z` to `ε (letter z) • e_C + g.taylor (map reducedPart z)`.  The proof uses the
bar-projection identity `map_reducedPart_comp_barDifferential` and the degenerate-word splitting
from `TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Augmented.BarProjection`.

An `A∞` morphism `f : A ⟶ B` between augmented `A∞` algebras is **augmented**
(`TauCeti.AInfinityHom.IsAugmented`) when `ε_B ∘ f.taylor = ε_A ∘ letter`, meaning that its linear
part commutes with the augmentations and every higher component lands in the augmentation ideal of
`B`.  Restricting `strictlyUnitalHomEquiv` to augmented morphisms yields the equivalence
(`TauCeti.AInfinityAlgebra.Augmentation.augmentedHomEquiv`) between strictly unital augmented `A∞`
morphisms `A ⟶ B` and nonunital `A∞` morphisms `ker ε_A ⟶ ker ε_B`.

## Main definitions

* `TauCeti.AInfinityAlgebra.Augmentation.strictlyUnitalHomEquiv`: strictly unital `A∞` morphisms
  out of an augmented `A∞` algebra correspond bijectively to `A∞` morphisms out of its augmentation
  ideal.
* `TauCeti.AInfinityHom.IsAugmented`: compatibility of an `A∞` morphism with augmentations.
* `TauCeti.AInfinityAlgebra.Augmentation.augmentedHomEquiv`: strictly unital augmented `A∞`
  morphisms between augmented `A∞` algebras correspond bijectively to `A∞` morphisms between their
  augmentation ideals.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Section 3.2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

namespace AInfinityAlgebra.Augmentation

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒞 : AInfinityAlgebra R C}

/-- The scalar projection `Tᶜ(sA) ⟶ R` extracting the augmentation of the single-letter
component. -/
private noncomputable def scalarPart (ε : 𝒜.Augmentation) : ReducedTensorWords R A →ₗ[R] R :=
  ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A

/-- The linear map forming the two-letter tensor word `[a, b]` from `a ⊗ₜ b`. -/
private noncomputable def pairWord (R : Type uR) (M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] : M ⊗[R] M →ₗ[R] ReducedTensorWords R M :=
  TensorProduct.lift ((ReducedTensorWords.prepend R M).compl₂ (ReducedTensorWords.ofLetter R M))

private theorem pairWord_tmul {M : Type*} [AddCommGroup M] [Module R M] (a b : M) :
    pairWord R M (a ⊗ₜ[R] b) =
      ReducedTensorWords.of R M (2 : ℕ+) (PiTensorProduct.tprod R ![a, b]) := by
  simp [pairWord, ReducedTensorWords.prepend_ofLetter]

/-- On unit-containing degenerate words of a strictly unital `A∞` algebra, the Taylor map vanishes
in all arities other than two and therefore factors through `pairWord ∘ (letter ⊗ letter) ∘ Δ`. -/
private theorem taylor_eq_pairWord_of_mem_degenerateWords {eC : C} (hC : 𝒞.StrictUnit eC)
    {w : ReducedTensorWords R C} (hw : w ∈ ReducedTensorWords.degenerateWords R C eC) :
    𝒞.taylor w = 𝒞.taylor (pairWord R C
      (TensorProduct.map (ReducedTensorWords.letter R C) (ReducedTensorWords.letter R C)
        (ReducedTensorWords.deconcatenation R C w))) := by
  let S : Submodule R (ReducedTensorWords R C) :=
    LinearMap.eqLocus 𝒞.taylor (𝒞.taylor ∘ₗ pairWord R C ∘ₗ
      TensorProduct.map (ReducedTensorWords.letter R C) (ReducedTensorWords.letter R C) ∘ₗ
        ReducedTensorWords.deconcatenation R C)
  suffices h : ReducedTensorWords.degenerateWords R C eC ≤ S from h hw
  rw [ReducedTensorWords.degenerateWords_le_iff]
  intro n x hx
  change 𝒞.taylor (ReducedTensorWords.of R C n (PiTensorProduct.tprod R x)) =
    𝒞.taylor (pairWord R C
      (TensorProduct.map (ReducedTensorWords.letter R C) (ReducedTensorWords.letter R C)
        (ReducedTensorWords.deconcatenation R C
          (ReducedTensorWords.of R C n (PiTensorProduct.tprod R x)))))
  by_cases hn : n.1 = 2
  · obtain ⟨k, hk⟩ := n
    simp only at hn
    subst k
    have hx' : x = ![x 0, x 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hx']
    change 𝒞.taylor (ReducedTensorWords.of R C (2 : ℕ+) (PiTensorProduct.tprod R ![x 0, x 1])) =
      𝒞.taylor (pairWord R C
        (TensorProduct.map (ReducedTensorWords.letter R C) (ReducedTensorWords.letter R C)
          (ReducedTensorWords.deconcatenation R C
            (ReducedTensorWords.of R C (2 : ℕ+) (PiTensorProduct.tprod R ![x 0, x 1])))))
    rw [ReducedTensorWords.deconcatenation_of_two, TensorProduct.map_tmul,
      ReducedTensorWords.letter_ofLetter, ReducedTensorWords.letter_ofLetter, pairWord_tmul]
  · rw [hC.taylor_of_tprod_eq_zero n hn x hx,
      ReducedTensorWords.map_letter_letter_deconcatenation_of_ne_two n hn x, map_zero, map_zero]


/-! ### Strictly unital `A∞` morphisms out of an augmented `A∞` algebra -/

/-- The Taylor map of the unique strictly unital extension of `g : ker ε ⟶ C` to `A ⟶ C`. -/
private noncomputable def extendTaylor (ε : 𝒜.Augmentation) (eC : C)
    (g : AInfinityHom ε.reducedAlgebra 𝒞) : ReducedTensorWords R A →ₗ[R] C :=
  LinearMap.toSpanSingleton R C eC ∘ₗ ε.scalarPart +
    g.taylor ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart

private theorem extendTaylor_apply (ε : 𝒜.Augmentation) (eC : C)
    (g : AInfinityHom ε.reducedAlgebra 𝒞) (z : ReducedTensorWords R A) :
    ε.extendTaylor eC g z =
      ε (ReducedTensorWords.letter R A z) • eC +
        g.taylor (ReducedTensorWords.map (R := R) ε.reducedPart z) := (rfl)

private theorem extendTaylor_comp_map_subtype (ε : 𝒜.Augmentation) (eC : C)
    (g : AInfinityHom ε.reducedAlgebra 𝒞) :
    ε.extendTaylor eC g ∘ₗ ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype =
      g.taylor := by
  refine LinearMap.ext fun z ↦ ?_
  simp only [LinearMap.comp_apply, extendTaylor_apply,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R A), ReducedTensorWords.letter_comp_map,
    LinearMap.comp_apply, Submodule.subtype_apply,
    (ε.mem_augmentationIdeal).1 (ReducedTensorWords.letter R _ z).2, zero_smul, zero_add,
    ← LinearMap.comp_apply (ReducedTensorWords.map (R := R) ε.reducedPart),
    ← ReducedTensorWords.map_comp, ε.reducedPart_comp_subtype, ReducedTensorWords.map_id,
    LinearMap.id_apply]

private theorem coalgHom_extendTaylor_comp_map_subtype (ε : 𝒜.Augmentation) (eC : C)
    (g : AInfinityHom ε.reducedAlgebra 𝒞) :
    ReducedTensorWords.coalgHom R (ε.extendTaylor eC g) ∘ₗ
        ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype = g.barMap := by
  have hcoalg : ReducedTensorWords.IsCoalgHom R
      (ReducedTensorWords.coalgHom R (ε.extendTaylor eC g) ∘ₗ
        ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype) :=
    (ReducedTensorWords.isCoalgHom_coalgHom _).comp (ReducedTensorWords.isCoalgHom_map _)
  rw [hcoalg.eq_coalgHom, g.barMap_eq_coalgHom, ← LinearMap.comp_assoc,
    ReducedTensorWords.letter_comp_coalgHom, ε.extendTaylor_comp_map_subtype]

private theorem isHomogeneous_extendTaylor (ε : 𝒜.Augmentation) {eC : C} (hC : 𝒞.StrictUnit eC)
    (g : AInfinityHom ε.reducedAlgebra 𝒞) :
    LinearMap.IsHomogeneous (ε.extendTaylor eC g)
      (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1)) (𝒞.grading.shift 1).piece 0 := by
  have h2 : LinearMap.IsHomogeneous (g.taylor ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart)
      (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1)) (𝒞.grading.shift 1).piece 0 := by
    simpa only [add_zero] using
      g.isHomogeneous_taylor.comp
        (ReducedTensorWords.isHomogeneous_map _ _ ε.isHomogeneous_reducedPart_shift)
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  rw [add_zero, extendTaylor_apply]
  refine Submodule.add_mem _ ?_ (by simpa only [add_zero, LinearMap.comp_apply] using h2.map_mem hz)
  have hl : ReducedTensorWords.letter R A z ∈ 𝒜.grading.piece (D + 1) := by
    have h := (ReducedTensorWords.isHomogeneous_letter (𝒜.grading.shift 1)).map_mem hz
    rwa [add_zero, InternalGrading.shift_piece] at h
  by_cases hD : D + 1 = 0
  · have hD' : D = -1 := by omega
    subst hD'
    exact Submodule.smul_mem _ _ hC.mem_shift_one_piece
  · rw [ε.map_of_mem_ne_zero (D + 1) _ hl hD, zero_smul]
    exact Submodule.zero_mem _

private theorem extendTaylor_of_tprod_eq_zero (ε : 𝒜.Augmentation) (eC : C)
    (g : AInfinityHom ε.reducedAlgebra 𝒞) (n : {n : ℕ // 0 < n}) (hn : n.1 ≠ 1)
    (x : Fin n.1 → A) (hx : ∃ i, x i = ε.unit) :
    ε.extendTaylor eC g (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)) = 0 := by
  obtain ⟨i, hi⟩ := hx
  have hne : n ≠ (1 : {k : ℕ // 0 < k}) := fun h ↦ hn (congrArg Subtype.val h)
  have hπ : ReducedTensorWords.map (R := R) ε.reducedPart
      (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)) = 0 := by
    rw [ReducedTensorWords.map_of_tprod,
      (PiTensorProduct.tprod R).map_coord_zero i (by rw [hi, ε.reducedPart_unit]), map_zero]
  rw [extendTaylor_apply, ReducedTensorWords.letter_of_of_ne_one R A hne, hπ, map_zero, zero_smul,
    map_zero, add_zero]

private theorem taylor_comp_coalgHom_extendTaylor (ε : 𝒜.Augmentation) {eC : C}
    (hC : 𝒞.StrictUnit eC) (g : AInfinityHom ε.reducedAlgebra 𝒞) :
    𝒞.taylor ∘ₗ ReducedTensorWords.coalgHom R (ε.extendTaylor eC g) =
      ε.extendTaylor eC g ∘ₗ 𝒜.barDifferential := by
  set π := ReducedTensorWords.map (R := R) ε.reducedPart
  set τ := ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1)
  have hgtwist (w : ReducedTensorWords R ε.augmentationIdeal) :
      𝒞.grading.koszulTwist 1 (g.taylor w) =
        -g.taylor (ReducedTensorWords.map (R := R)
          ((ε.reducedAlgebra.grading.shift 1).koszulTwist 1) w) := by
    have h := g.isHomogeneous_taylor
    rw [← ReducedTensorWords.grading_piece] at h
    have h1 := h.koszulTwist_apply 1 w
    rw [InternalGrading.koszulTwist_one_shift_one, ReducedTensorWords.koszulTwist_grading] at h1
    simp only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.neg_apply] at h1
    calc
      𝒞.grading.koszulTwist 1 (g.taylor w) = - -𝒞.grading.koszulTwist 1 (g.taylor w) :=
        (neg_neg _).symm
      _ = -g.taylor (ReducedTensorWords.map (R := R)
          ((ε.reducedAlgebra.grading.shift 1).koszulTwist 1) w) := congrArg Neg.neg h1
  have hπtwist (x : ReducedTensorWords R A) :
      ReducedTensorWords.map (R := R) ((ε.reducedAlgebra.grading.shift 1).koszulTwist 1) (π x) =
        π (τ x) := by
    have h := (ReducedTensorWords.isHomogeneous_map _ _
      ε.isHomogeneous_reducedPart_shift).map_koszulTwist_comp 1
    simpa only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.comp_apply] using LinearMap.congr_fun h x
  -- Evaluate `𝒞.taylor ∘ pairWord ∘ (t ⊗ t)` on a general tensor `w : Tᶜ(sA) ⊗ Tᶜ(sA)`.
  have hpair (w : ReducedTensorWords R A ⊗[R] ReducedTensorWords R A) :
      𝒞.taylor (pairWord R C (TensorProduct.map (ε.extendTaylor eC g) (ε.extendTaylor eC g) w)) =
        (LinearMap.mul' R R (TensorProduct.map ε.scalarPart ε.scalarPart w)) • eC +
        g.taylor ((TensorProduct.lid R _).toLinearMap (TensorProduct.map ε.scalarPart π w)) +
        (-1 : R) • g.taylor ((TensorProduct.rid R _).toLinearMap
          (TensorProduct.map (π ∘ₗ τ) ε.scalarPart w)) +
        𝒞.taylor (pairWord R C
          (TensorProduct.map g.taylor g.taylor (TensorProduct.map π π w))) := by
    induction w using TensorProduct.inductionOn with
    | tmul x y =>
      have hL (c : C) : 𝒞.taylor (pairWord R C (eC ⊗ₜ[R] c)) = c := by
        rw [pairWord_tmul, hC.taylor_of_two_unit_left]
      have hR (c : C) : 𝒞.taylor (pairWord R C (c ⊗ₜ[R] eC)) = 𝒞.grading.koszulTwist 1 c := by
        rw [pairWord_tmul, hC.taylor_of_two_unit_right]
      simp only [TensorProduct.map_tmul, extendTaylor_apply, TensorProduct.add_tmul,
        TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_add,
        map_smul, hR, hL, hgtwist, 𝒞.grading.koszulTwist_apply_of_mem_zero hC.degree_zero,
        LinearMap.mul'_apply, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
        TensorProduct.rid_tmul, LinearMap.comp_apply, scalarPart, smul_add, smul_smul, smul_neg,
        neg_mul, one_mul, neg_smul, mul_comm (ε (ReducedTensorWords.letter R A y))]
      rw [← hπtwist x]
      dsimp only [π]
      abel
    | add u v hu hv =>
      simp only [map_add, add_smul, smul_add, hu, hv]
      abel
  refine LinearMap.ext fun z ↦ ?_
  set z₀ := ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype (π z)
  set zd := z - z₀
  have hz : z = z₀ + zd := (add_sub_cancel _ _).symm
  -- First, check the reduced part `z₀ = map subtype (π z)`.
  have h0 : 𝒞.taylor (ReducedTensorWords.coalgHom R (ε.extendTaylor eC g) z₀) =
      ε.extendTaylor eC g (𝒜.barDifferential z₀) := by
    have hL : ReducedTensorWords.coalgHom R (ε.extendTaylor eC g) z₀ = g.barMap (π z) :=
      LinearMap.congr_fun (ε.coalgHom_extendTaylor_comp_map_subtype eC g) (π z)
    have hR : 𝒜.barDifferential z₀ =
        ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype
          (ε.reducedAlgebra.barDifferential (π z)) := by
      have h := LinearMap.congr_fun ε.reducedAlgebraInclusion.barDifferential_comp_barMap (π z)
      simpa only [LinearMap.comp_apply, barMap_reducedAlgebraInclusion] using h
    rw [hL, hR, ← LinearMap.comp_apply 𝒞.taylor, g.taylor_comp_barMap, LinearMap.comp_apply,
      ← LinearMap.comp_apply (ε.extendTaylor eC g), ε.extendTaylor_comp_map_subtype]
  -- Second, check the degenerate part `zd`, on which `π zd = 0`.
  have hπd : π zd = 0 := by
    simp only [zd, z₀, map_sub, π,
      ← LinearMap.comp_apply (ReducedTensorWords.map (R := R) ε.reducedPart),
      ← ReducedTensorWords.map_comp, ε.reducedPart_comp_subtype, ReducedTensorWords.map_id,
      LinearMap.id_apply, sub_self]
  have hd_mem : zd ∈ ReducedTensorWords.degenerateWords R A ε.unit :=
    ε.sub_map_subtype_map_reducedPart_mem_degenerateWords z
  have hcd_mem : ReducedTensorWords.coalgHom R (ε.extendTaylor eC g) zd ∈
      ReducedTensorWords.degenerateWords R C eC := by
    refine ReducedTensorWords.coalgHom_mem_degenerateWords (ε.extendTaylor eC g) ?_
      (ε.extendTaylor_of_tprod_eq_zero eC g) hd_mem
    simp [extendTaylor_apply]
  have hd : 𝒞.taylor (ReducedTensorWords.coalgHom R (ε.extendTaylor eC g) zd) =
      ε.extendTaylor eC g (𝒜.barDifferential zd) := by
    rw [taylor_eq_pairWord_of_mem_degenerateWords hC hcd_mem,
      (ReducedTensorWords.isCoalgHom_coalgHom _).deconcatenation_apply,
      ← LinearMap.comp_apply (TensorProduct.map _ _), ← TensorProduct.map_comp,
      ReducedTensorWords.letter_comp_coalgHom, hpair]
    have hππ : TensorProduct.map π π (ReducedTensorWords.deconcatenation R A zd) = 0 := by
      rw [← (ReducedTensorWords.isCoalgHom_map ε.reducedPart).deconcatenation_apply, hπd, map_zero]
    rw [hππ, map_zero, map_zero, map_zero, add_zero]
    have hε : ε (𝒜.taylor zd) = LinearMap.mul' R R
        (TensorProduct.map ε.scalarPart ε.scalarPart
          (ReducedTensorWords.deconcatenation R A zd)) :=
      LinearMap.congr_fun ε.comp_taylor zd
    have hb := LinearMap.congr_fun ε.map_reducedPart_comp_barDifferential zd
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] at hb
    rw [hπd, map_zero, zero_add] at hb
    rw [extendTaylor_apply, ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
      𝒜.letter_comp_barDifferential, hε, hb, map_add, map_smul]
    simp only [scalarPart]
    abel
  simp only [LinearMap.comp_apply]
  rw [hz, map_add, map_add, map_add, map_add, h0, hd]

/-- The unique strictly unital `A∞` morphism `A ⟶ C` extending a nonunital `A∞` morphism
`g : ker ε ⟶ C`. -/
private noncomputable def extendStrictlyUnital (ε : 𝒜.Augmentation) {eC : C}
    (hC : 𝒞.StrictUnit eC) (g : AInfinityHom ε.reducedAlgebra 𝒞) :
    {f : AInfinityHom 𝒜 𝒞 // f.IsStrictlyUnital ε.isStrictUnit hC} :=
  ⟨AInfinityHom.ofTaylor (ε.extendTaylor eC g) (ε.isHomogeneous_extendTaylor hC g)
      (ε.taylor_comp_coalgHom_extendTaylor hC g),
    { map_unit := by
        simp [AInfinityHom.linearPart_apply, extendTaylor_apply]
      component_eq_zero := by
        intro n hn x hx
        rcases Nat.eq_zero_or_pos n with rfl | hnpos
        · simp
        · rw [AInfinityHom.component_apply _ n hnpos, AInfinityHom.taylor_ofTaylor]
          obtain ⟨i, hi⟩ := hx
          exact ε.extendTaylor_of_tprod_eq_zero eC g ⟨n, hnpos⟩ hn _
            ⟨i, by rw [hi, 𝒜.grading.koszulTwist_apply_of_mem_zero ε.isStrictUnit.degree_zero]⟩ }⟩

private theorem taylor_extendStrictlyUnital (ε : 𝒜.Augmentation) {eC : C}
    (hC : 𝒞.StrictUnit eC) (g : AInfinityHom ε.reducedAlgebra 𝒞) :
    (ε.extendStrictlyUnital hC g).val.taylor = ε.extendTaylor eC g := by
  simp [extendStrictlyUnital]

/-- **Strictly unital `A∞` morphisms out of an augmented `A∞` algebra are determined by their
restriction to the augmentation ideal.**

Restriction along `reducedAlgebraInclusion` establishes a bijection between strictly unital `A∞`
morphisms `A ⟶ C` into any strictly unital `A∞` algebra `C` and nonunital `A∞` morphisms
`ker ε ⟶ C`. -/
noncomputable def strictlyUnitalHomEquiv (ε : 𝒜.Augmentation) {eC : C} (hC : 𝒞.StrictUnit eC) :
    {f : AInfinityHom 𝒜 𝒞 // f.IsStrictlyUnital ε.isStrictUnit hC} ≃
      AInfinityHom ε.reducedAlgebra 𝒞 where
  toFun f := f.val.comp ε.reducedAlgebraInclusion.toAInfinityHom
  invFun g := ε.extendStrictlyUnital hC g
  left_inv := fun ⟨f, hf⟩ ↦ by
    apply Subtype.ext
    apply AInfinityHom.ext
    refine LinearMap.ext fun z ↦ ?_
    set π := ReducedTensorWords.map (R := R) ε.reducedPart
    set z₀ := ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype (π z)
    set zd := z - z₀
    have hz : z = z₀ + zd := (add_sub_cancel _ _).symm
    have h0 :
        (ε.extendStrictlyUnital hC
          (f.comp ε.reducedAlgebraInclusion.toAInfinityHom)).val.taylor z₀ = f.taylor z₀ := by
      rw [taylor_extendStrictlyUnital, ← LinearMap.comp_apply (ε.extendTaylor eC _),
        ε.extendTaylor_comp_map_subtype, AInfinityHom.taylor_comp, LinearMap.comp_apply,
        AInfinityStrictHom.barMap_toAInfinityHom, barMap_reducedAlgebraInclusion]
    have hπd : π zd = 0 := by
      simp only [zd, z₀, map_sub, π,
        ← LinearMap.comp_apply (ReducedTensorWords.map (R := R) ε.reducedPart),
        ← ReducedTensorWords.map_comp, ε.reducedPart_comp_subtype, ReducedTensorWords.map_id,
        LinearMap.id_apply, sub_self]
    have hred_letter : ε.reducedPart (ReducedTensorWords.letter R A zd) = 0 := by
      rw [← LinearMap.comp_apply ε.reducedPart, ← ReducedTensorWords.letter_comp_map,
        LinearMap.comp_apply, hπd, map_zero]
    have hletter : ReducedTensorWords.letter R A zd =
        ε (ReducedTensorWords.letter R A zd) • ε.unit := by
      have h := congrArg Subtype.val hred_letter
      rw [coe_reducedPart, Submodule.coe_zero, sub_eq_zero] at h
      exact h
    have hd :
        (ε.extendStrictlyUnital hC
          (f.comp ε.reducedAlgebraInclusion.toAInfinityHom)).val.taylor zd = f.taylor zd := by
      rw [taylor_extendStrictlyUnital, extendTaylor_apply, hπd, map_zero, add_zero,
        hf.taylor_eq_linearPart_letter (ε.sub_map_subtype_map_reducedPart_mem_degenerateWords z)]
      conv_rhs => rw [hletter, map_smul, hf.map_unit]
    rw [hz, map_add, map_add, h0, hd]
  right_inv g := by
    apply AInfinityHom.ext
    rw [AInfinityHom.taylor_comp, taylor_extendStrictlyUnital,
      AInfinityStrictHom.barMap_toAInfinityHom, barMap_reducedAlgebraInclusion,
      ε.extendTaylor_comp_map_subtype]

/-- The forward direction of `strictlyUnitalHomEquiv` restricts along `reducedAlgebraInclusion`. -/
@[simp]
theorem strictlyUnitalHomEquiv_apply (ε : 𝒜.Augmentation) {eC : C} (hC : 𝒞.StrictUnit eC)
    (f : {f : AInfinityHom 𝒜 𝒞 // f.IsStrictlyUnital ε.isStrictUnit hC}) :
    ε.strictlyUnitalHomEquiv hC f = f.val.comp ε.reducedAlgebraInclusion.toAInfinityHom := (rfl)

/-- The Taylor map of the unique strictly unital extension of `g : ker ε ⟶ C`. -/
@[simp]
theorem taylor_strictlyUnitalHomEquiv_symm (ε : 𝒜.Augmentation) {eC : C} (hC : 𝒞.StrictUnit eC)
    (g : AInfinityHom ε.reducedAlgebra 𝒞) (z : ReducedTensorWords R A) :
    ((ε.strictlyUnitalHomEquiv hC).symm g).val.taylor z =
      ε (ReducedTensorWords.letter R A z) • eC +
        g.taylor (ReducedTensorWords.map (R := R) ε.reducedPart z) := by
  simp [strictlyUnitalHomEquiv, taylor_extendStrictlyUnital, extendTaylor_apply]

/-- The linear part of the unique strictly unital extension of `g : ker ε ⟶ C`. -/
theorem linearPart_strictlyUnitalHomEquiv_symm (ε : 𝒜.Augmentation) {eC : C} (hC : 𝒞.StrictUnit eC)
    (g : AInfinityHom ε.reducedAlgebra 𝒞) (a : A) :
    ((ε.strictlyUnitalHomEquiv hC).symm g).val.linearPart a =
      ε a • eC + g.linearPart (ε.reducedPart a) := by
  rw [AInfinityHom.linearPart_apply, taylor_strictlyUnitalHomEquiv_symm,
    ReducedTensorWords.letter_ofLetter, ReducedTensorWords.map_ofLetter,
    AInfinityHom.linearPart_apply]

end AInfinityAlgebra.Augmentation

/-! ### Augmented `A∞` morphisms -/

namespace AInfinityHom

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒞 : AInfinityAlgebra R C}

/-- An `A∞` morphism `f : A ⟶ B` between augmented `A∞` algebras is **augmented** when
`εB ∘ f.taylor = εA ∘ letter`, that is, its linear part commutes with the augmentations and every
higher Taylor component takes values in the augmentation ideal of `B`. -/
def IsAugmented (f : AInfinityHom 𝒜 ℬ) (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation) : Prop :=
  εB.toLinearMap ∘ₗ f.taylor = εA.toLinearMap ∘ₗ ReducedTensorWords.letter R A

/-- Unfolding `IsAugmented` to its Taylor-map equation. -/
theorem isAugmented_def (f : AInfinityHom 𝒜 ℬ) (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation) :
    f.IsAugmented εA εB ↔
      εB.toLinearMap ∘ₗ f.taylor = εA.toLinearMap ∘ₗ ReducedTensorWords.letter R A := Iff.rfl

/-- An augmented `A∞` morphism commutes with the augmentations on its linear part. -/
theorem IsAugmented.map_linearPart {f : AInfinityHom 𝒜 ℬ} {εA : 𝒜.Augmentation}
    {εB : ℬ.Augmentation} (hf : f.IsAugmented εA εB) (a : A) :
    εB (f.linearPart a) = εA a := by
  have h := LinearMap.congr_fun hf (ReducedTensorWords.ofLetter R A a)
  simpa only [LinearMap.comp_apply, AInfinityHom.linearPart_apply,
    ReducedTensorWords.letter_ofLetter] using h

/-- An augmented `A∞` morphism annihilates the target augmentation in every arity other than one. -/
theorem IsAugmented.map_component_eq_zero {f : AInfinityHom 𝒜 ℬ} {εA : 𝒜.Augmentation}
    {εB : ℬ.Augmentation} (hf : f.IsAugmented εA εB) {n : ℕ} (hn : n ≠ 1) (x : Fin n → A) :
    εB (f.component n x) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · simp
  · rw [f.component_apply n hnpos]
    have h := LinearMap.congr_fun hf (ReducedTensorWords.of R A ⟨n, hnpos⟩ (PiTensorProduct.tprod R
      fun i ↦ 𝒜.grading.koszulTwist ((n : ℤ) - 1 - i) (x i)))
    have hne : (⟨n, hnpos⟩ : {k : ℕ // 0 < k}) ≠ 1 := fun h1 ↦ hn (congrArg Subtype.val h1)
    simpa only [LinearMap.comp_apply, ReducedTensorWords.letter_of_of_ne_one R A hne,
      map_zero] using h

/-- Componentwise characterization of augmented `A∞` morphisms. -/
theorem isAugmented_iff (f : AInfinityHom 𝒜 ℬ) (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation) :
    f.IsAugmented εA εB ↔
      (∀ a, εB (f.linearPart a) = εA a) ∧ ∀ n, n ≠ 1 → ∀ x, εB (f.component n x) = 0 := by
  refine ⟨fun hf ↦ ⟨hf.map_linearPart, fun _ hn x ↦ hf.map_component_eq_zero hn x⟩, ?_⟩
  rintro ⟨h1, hhigher⟩
  refine ReducedTensorWords.linearMap_ext R A fun n x ↦ ?_
  by_cases hn1 : n.1 = 1
  · obtain ⟨k, hk⟩ := n
    simp only at hn1
    subst k
    have hof : ReducedTensorWords.of R A ⟨1, hk⟩ (PiTensorProduct.tprod R x) =
        ReducedTensorWords.ofLetter R A (x 0) := by
      rw [ReducedTensorWords.of_tprod_eq_subword R hk,
        ReducedTensorWords.subword_one R A x (by omega)]
      rfl
    rw [hof]
    simpa only [LinearMap.comp_apply, ReducedTensorWords.letter_ofLetter,
      ← AInfinityHom.linearPart_apply] using h1 (x 0)
  · have hne : n ≠ (1 : {k : ℕ // 0 < k}) := fun h ↦ hn1 (congrArg Subtype.val h)
    have htwist : f.component n.1
        (fun i ↦ 𝒜.grading.koszulTwist ((n.1 : ℤ) - 1 - i) (x i)) =
        f.taylor (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)) := by
      rw [f.component_apply n.1 n.2]
      simp only [InternalGrading.koszulTwist_koszulTwist]
    simp only [LinearMap.comp_apply, ReducedTensorWords.letter_of_of_ne_one R A hne, map_zero]
    rw [← htwist]
    exact hhigher n.1 hn1 _

/-- The identity `A∞` morphism is augmented. -/
@[simp]
theorem isAugmented_id (ε : 𝒜.Augmentation) : (AInfinityHom.id 𝒜).IsAugmented ε ε := by
  rw [IsAugmented, taylor_id]

/-- Composition preserves augmented `A∞` morphisms. -/
theorem IsAugmented.comp {g : AInfinityHom ℬ 𝒞} {f : AInfinityHom 𝒜 ℬ} {εA : 𝒜.Augmentation}
    {εB : ℬ.Augmentation} {εC : 𝒞.Augmentation} (hg : g.IsAugmented εB εC)
    (hf : f.IsAugmented εA εB) : (g.comp f).IsAugmented εA εC := by
  rw [IsAugmented, taylor_comp, ← LinearMap.comp_assoc, hg, LinearMap.comp_assoc, ← f.taylor_def,
    hf]

/-- A strict `A∞` morphism is augmented if and only if its linear part commutes with the
augmentations. -/
theorem IsStrict.isAugmented_iff {f : AInfinityHom 𝒜 ℬ} (hf : f.IsStrict)
    (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation) :
    f.IsAugmented εA εB ↔ ∀ a, εB (f.linearPart a) = εA a := by
  rw [AInfinityHom.isAugmented_iff]
  refine ⟨And.left, fun h ↦ ⟨h, fun n hn x ↦ ?_⟩⟩
  rw [← hf.toAInfinityHom_toStrictHom,
    AInfinityStrictHom.component_toAInfinityHom_eq_zero _ hn, zero_apply, map_zero]

end AInfinityHom

/-! ### Equivalence between augmented `A∞` morphisms and morphisms of augmentation ideals -/

namespace AInfinityAlgebra.Augmentation

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B}

/-- The unique strictly unital extension of `g : ker ε ⟶ B` is augmented if and only if every Taylor
component of `g` lands in the augmentation ideal of `B`. -/
theorem isAugmented_strictlyUnitalHomEquiv_symm_iff (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation)
    (g : AInfinityHom εA.reducedAlgebra ℬ) :
    ((εA.strictlyUnitalHomEquiv εB.isStrictUnit).symm g).val.IsAugmented εA εB ↔
      εB.toLinearMap ∘ₗ g.taylor = 0 := by
  constructor
  · intro h
    refine LinearMap.ext fun w ↦ ?_
    have hw := LinearMap.congr_fun h
      (ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype w)
    simp only [LinearMap.comp_apply, taylor_strictlyUnitalHomEquiv_symm,
      ← LinearMap.comp_apply (ReducedTensorWords.letter R A), ReducedTensorWords.letter_comp_map,
      LinearMap.comp_apply, Submodule.subtype_apply,
      (εA.mem_augmentationIdeal).1 (ReducedTensorWords.letter R _ w).2, zero_smul, zero_add,
      ← LinearMap.comp_apply (ReducedTensorWords.map (R := R) εA.reducedPart),
      ← ReducedTensorWords.map_comp, εA.reducedPart_comp_subtype, ReducedTensorWords.map_id,
      LinearMap.id_apply] at hw
    exact hw
  · intro hg
    refine LinearMap.ext fun z ↦ ?_
    simp only [LinearMap.comp_apply, taylor_strictlyUnitalHomEquiv_symm, map_add, map_smul,
      εB.map_unit, smul_eq_mul, mul_one, ← LinearMap.comp_apply εB.toLinearMap, hg,
      LinearMap.zero_apply, add_zero]

/-- An `A∞` morphism into `ℬ` whose Taylor map annihilates `εB` factors into the reduced
augmentation ideal `εB.reducedAlgebra`. -/
private noncomputable def codRestrictReduced {𝒳 : AInfinityAlgebra R C}
    (εB : ℬ.Augmentation) (g : AInfinityHom 𝒳 ℬ) (hg : εB.toLinearMap ∘ₗ g.taylor = 0) :
    AInfinityHom 𝒳 εB.reducedAlgebra :=
  have hsub : εB.augmentationIdeal.subtype ∘ₗ (εB.reducedPart ∘ₗ g.taylor) = g.taylor := by
    refine LinearMap.ext fun z ↦ ?_
    have hz : εB (g.taylor z) = 0 := LinearMap.congr_fun hg z
    simp [coe_reducedPart, hz]
  have hbar : ReducedTensorWords.map (R := R) εB.augmentationIdeal.subtype ∘ₗ
      ReducedTensorWords.coalgHom R (εB.reducedPart ∘ₗ g.taylor) = g.barMap := by
    rw [ReducedTensorWords.map_comp_coalgHom, hsub, g.barMap_eq_coalgHom]
  AInfinityHom.ofTaylor (εB.reducedPart ∘ₗ g.taylor)
    (by simpa only [add_zero] using εB.isHomogeneous_reducedPart_shift.comp g.isHomogeneous_taylor)
    (by
      rw [reducedAlgebra_taylor, LinearMap.comp_assoc, LinearMap.comp_assoc, hbar,
        g.taylor_comp_barMap, LinearMap.comp_assoc])

private theorem taylor_codRestrictReduced {𝒳 : AInfinityAlgebra R C}
    (εB : ℬ.Augmentation) (g : AInfinityHom 𝒳 ℬ) (hg : εB.toLinearMap ∘ₗ g.taylor = 0) :
    (codRestrictReduced εB g hg).taylor = εB.reducedPart ∘ₗ g.taylor := by
  simp [codRestrictReduced]

/-- **Strictly unital augmented `A∞` morphisms correspond bijectively to `A∞` morphisms between the
augmentation ideals.** -/
noncomputable def augmentedHomEquiv (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation) :
    {f : AInfinityHom 𝒜 ℬ //
      f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit ∧ f.IsAugmented εA εB} ≃
      AInfinityHom εA.reducedAlgebra εB.reducedAlgebra where
  toFun f :=
    codRestrictReduced εB (εA.strictlyUnitalHomEquiv εB.isStrictUnit ⟨f.val, f.property.1⟩) <| by
      rw [← isAugmented_strictlyUnitalHomEquiv_symm_iff]
      have hEq : ((εA.strictlyUnitalHomEquiv εB.isStrictUnit).symm
          (εA.strictlyUnitalHomEquiv εB.isStrictUnit ⟨f.val, f.property.1⟩)).val = f.val :=
        congrArg Subtype.val
          ((εA.strictlyUnitalHomEquiv εB.isStrictUnit).symm_apply_apply ⟨f.val, f.property.1⟩)
      rw [hEq]
      exact f.property.2
  invFun h :=
    let f := (εA.strictlyUnitalHomEquiv εB.isStrictUnit).symm
      (εB.reducedAlgebraInclusion.toAInfinityHom.comp h)
    ⟨f.val, f.property, (isAugmented_strictlyUnitalHomEquiv_symm_iff εA εB _).2 <| by
      refine LinearMap.ext fun w ↦ ?_
      rw [LinearMap.comp_apply, AInfinityStrictHom.taylor_toAInfinityHom_comp,
        LinearMap.comp_apply, toLinearMap_reducedAlgebraInclusion, Submodule.subtype_apply,
        LinearMap.zero_apply]
      exact (εB.mem_augmentationIdeal).1 (h.taylor w).2⟩
  left_inv := fun ⟨f, hsu, haug⟩ ↦ by
    apply Subtype.ext
    have haug_g : εB.toLinearMap ∘ₗ
        (εA.strictlyUnitalHomEquiv εB.isStrictUnit ⟨f, hsu⟩).taylor = 0 := by
      rw [← isAugmented_strictlyUnitalHomEquiv_symm_iff]
      have hEq : ((εA.strictlyUnitalHomEquiv εB.isStrictUnit).symm
          (εA.strictlyUnitalHomEquiv εB.isStrictUnit ⟨f, hsu⟩)).val = f :=
        congrArg Subtype.val
          ((εA.strictlyUnitalHomEquiv εB.isStrictUnit).symm_apply_apply ⟨f, hsu⟩)
      rw [hEq]
      exact haug
    have hcomp : εB.reducedAlgebraInclusion.toAInfinityHom.comp
        (codRestrictReduced εB (εA.strictlyUnitalHomEquiv εB.isStrictUnit ⟨f, hsu⟩) haug_g) =
        εA.strictlyUnitalHomEquiv εB.isStrictUnit ⟨f, hsu⟩ := by
      apply AInfinityHom.ext
      refine LinearMap.ext fun w ↦ ?_
      rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, taylor_codRestrictReduced]
      have hw : εB ((εA.strictlyUnitalHomEquiv εB.isStrictUnit ⟨f, hsu⟩).taylor w) = 0 :=
        LinearMap.congr_fun haug_g w
      simp only [LinearMap.comp_apply, toLinearMap_reducedAlgebraInclusion, Submodule.subtype_apply,
        coe_reducedPart, hw, zero_smul, sub_zero]
    have h1 : (εA.strictlyUnitalHomEquiv εB.isStrictUnit).symm
        (εB.reducedAlgebraInclusion.toAInfinityHom.comp
          (codRestrictReduced εB (εA.strictlyUnitalHomEquiv εB.isStrictUnit ⟨f, hsu⟩) haug_g)) =
        ⟨f, hsu⟩ :=
      (congrArg (εA.strictlyUnitalHomEquiv εB.isStrictUnit).symm hcomp).trans
        ((εA.strictlyUnitalHomEquiv εB.isStrictUnit).symm_apply_apply ⟨f, hsu⟩)
    have h2 := congrArg Subtype.val h1
    exact h2
  right_inv h := by
    apply AInfinityHom.ext
    refine LinearMap.ext fun w ↦ ?_
    rw [taylor_codRestrictReduced, LinearMap.comp_apply, strictlyUnitalHomEquiv_apply]
    have hEq : (((εA.strictlyUnitalHomEquiv εB.isStrictUnit).symm
        (εB.reducedAlgebraInclusion.toAInfinityHom.comp h)).val.comp
          εA.reducedAlgebraInclusion.toAInfinityHom) =
        εB.reducedAlgebraInclusion.toAInfinityHom.comp h :=
      (εA.strictlyUnitalHomEquiv εB.isStrictUnit).apply_symm_apply _
    rw [hEq, AInfinityStrictHom.taylor_toAInfinityHom_comp, LinearMap.comp_apply,
      toLinearMap_reducedAlgebraInclusion, Submodule.subtype_apply, εB.reducedPart_coe]

/-- The forward direction of `augmentedHomEquiv` agrees with restriction along
`reducedAlgebraInclusion` after postcomposition with `reducedAlgebraInclusion`. -/
@[simp]
theorem reducedAlgebraInclusion_comp_augmentedHomEquiv (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation)
    (f : {f : AInfinityHom 𝒜 ℬ //
      f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit ∧ f.IsAugmented εA εB}) :
    εB.reducedAlgebraInclusion.toAInfinityHom.comp (εA.augmentedHomEquiv εB f) =
      f.val.comp εA.reducedAlgebraInclusion.toAInfinityHom := by
  have h := congrArg (fun x ↦ x.val.comp εA.reducedAlgebraInclusion.toAInfinityHom)
    ((εA.augmentedHomEquiv εB).left_inv f)
  simpa only [augmentedHomEquiv, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk,
    ← strictlyUnitalHomEquiv_apply, Equiv.apply_symm_apply] using h

/-- The inverse of `augmentedHomEquiv` extends `reducedAlgebraInclusion ∘ h` via
`strictlyUnitalHomEquiv`. -/
@[simp]
theorem augmentedHomEquiv_symm_val (εA : 𝒜.Augmentation) (εB : ℬ.Augmentation)
    (h : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    ((εA.augmentedHomEquiv εB).symm h).val =
      ((εA.strictlyUnitalHomEquiv εB.isStrictUnit).symm
        (εB.reducedAlgebraInclusion.toAInfinityHom.comp h)).val := (rfl)

end AInfinityAlgebra.Augmentation

end TauCeti
