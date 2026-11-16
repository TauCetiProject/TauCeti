/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Augmentation
public import TauCeti.Algebra.Homology.AInfinity.Algebra.DG
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Unital
public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation
public import TauCeti.LinearAlgebra.TensorCoalgebra.Splice

/-!
# Strictly unital `A∞` morphisms out of an augmented `A∞` algebra

For an augmented `A∞` algebra `(A, ε)` with augmentation ideal `A⁺ = ker ε` and any `A∞` algebra
`B` with a strict unit `eB`, restriction along the strict inclusion `A⁺ ⟶ A` identifies the
strictly unital `A∞` morphisms `A ⟶ B` with all nonunital `A∞` morphisms `A⁺ ⟶ B`:

`{f : AInfinityHom A B // f.IsStrictlyUnital} ≃ AInfinityHom A⁺ B`.

Given a nonunital morphism `g : A⁺ ⟶ B`, its strictly unital extension sends a reduced tensor word
`z` in `Tᶜ(sA)` to `g.taylor (Tᶜ(π) z) + ε (letter z) • eB`, where `π : A → A⁺` subtracts the
scalar part.  On words whose letters lie in `A⁺` this recovers `g.taylor`, while on degenerate
words containing the strict unit of `A` the bar-differential equation reduces to the boundary and
interior cancellations of the binary unit laws `m₂(e, y) = y` and `m₂(y, e) = y`.

The file also records the strict inclusion `A⁺ ⟶ A`, the strict unital augmentation morphism
`A ⟶ R`, the augmentation-preservation criterion for strictly unital morphisms, and the bridge
from an augmented DG algebra (`TauCeti.DGAlgAugmentation`) to an augmented `A∞` algebra.

## Main definitions

* `TauCeti.AInfinityAlgebra.Augmentation.reducedInclusion`: the strict `A∞` inclusion `A⁺ ⟶ A`.
* `TauCeti.AInfinityAlgebra.Augmentation.toAInfinityStrictHom` and
  `TauCeti.AInfinityAlgebra.Augmentation.toAInfinityStrictUnitalHom`: the augmentation as a strict
  (strictly unital) `A∞` morphism `A ⟶ R`.
* `TauCeti.AInfinityAlgebra.Augmentation.strictlyUnitalHomEquiv`: the bijection between strictly
  unital `A∞` morphisms `A ⟶ B` and nonunital `A∞` morphisms `A⁺ ⟶ B`.
* `TauCeti.DGAlgAugmentation.toAInfinityAugmentation`: an augmented DG algebra as an augmented
  `A∞` algebra.

## Main results

* `TauCeti.AInfinityAlgebra.Augmentation.strictlyUnitalHomEquiv_symm_comp_strict`: naturality of
  the strictly unital extension under post-composition by strictly unital strict `A∞` morphisms.
* `TauCeti.AInfinityAlgebra.Augmentation.comp_toAInfinityStrictHom_eq_iff`: a strictly unital `A∞`
  morphism between augmented `A∞` algebras commutes with the augmentations precisely when the
  Taylor components of its restriction to `A⁺` land in the target augmentation ideal.
* `TauCeti.DGAlgHom.isStrictlyUnital_toAInfinityHom`: every DG algebra morphism is strictly unital
  when regarded as an `A∞` morphism.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
* K. Lefèvre-Hasegawa, *Sur les `A∞`-catégories*, Chapter 3.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uB uC

namespace AInfinityAlgebra.Augmentation

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒞 : AInfinityAlgebra R C}

/-! ### The reduced inclusion and the augmentation as strict morphisms -/

/-- The inclusion of the reduced augmentation ideal as a strict `A∞` morphism `A⁺ ⟶ A`. -/
noncomputable def reducedInclusion (ε : 𝒜.Augmentation) :
    AInfinityStrictHom ε.reducedAlgebra 𝒜 where
  toLinearMap := ε.augmentationIdeal.subtype
  map_mem' ha := by simpa [reducedAlgebra_grading, reducedGrading_piece] using ha
  map_m' n := by
    ext x
    simp

@[simp]
theorem reducedInclusion_toLinearMap (ε : 𝒜.Augmentation) :
    ε.reducedInclusion.toLinearMap = ε.augmentationIdeal.subtype := (rfl)

@[simp]
theorem coe_reducedInclusion (ε : 𝒜.Augmentation) (x : ε.augmentationIdeal) :
    ε.reducedInclusion x = (x : A) := (rfl)

/-- The augmentation of an `A∞` algebra as a strict `A∞` morphism to the trivially graded ground
ring. -/
noncomputable def toAInfinityStrictHom (ε : 𝒜.Augmentation) :
    AInfinityStrictHom 𝒜 (isDGAlgebra_trivialGrading R).toIsNonUnitalDGAlgebra.toAInfinityAlgebra
    where
  toLinearMap := ε.toLinearMap
  map_mem' {p a} ha := by
    by_cases hp : p = 0
    · subst hp
      simp
    · simp [ε.map_of_mem_ne_zero p a ha hp]
  map_m' n := by
    ext x
    rcases n with _ | _ | _ | n
    · simp
    · have hx : x = ![x 0] := by
        funext i
        fin_cases i
        rfl
      rw [hx]
      simp
    · have hx : x = ![x 0, x 1] := by
        funext i
        fin_cases i <;> rfl
      rw [hx]
      simp
    · simp

@[simp]
theorem toAInfinityStrictHom_toLinearMap (ε : 𝒜.Augmentation) :
    ε.toAInfinityStrictHom.toLinearMap = ε.toLinearMap := (rfl)

@[simp]
theorem coe_toAInfinityStrictHom (ε : 𝒜.Augmentation) :
    ⇑ε.toAInfinityStrictHom = ε := (rfl)

/-- The augmentation of an `A∞` algebra as a strictly unital strict `A∞` morphism to the ground
ring. -/
noncomputable def toAInfinityStrictUnitalHom (ε : 𝒜.Augmentation) :
    AInfinityStrictUnitalHom ε.isStrictUnit (isDGAlgebra_trivialGrading R).strictUnit_one where
  toAInfinityStrictHom := ε.toAInfinityStrictHom
  map_unit' := ε.map_unit

@[simp]
theorem toAInfinityStrictHom_toAInfinityStrictUnitalHom (ε : 𝒜.Augmentation) :
    ε.toAInfinityStrictUnitalHom.toAInfinityStrictHom = ε.toAInfinityStrictHom := (rfl)

/-! ### Homogeneity and unit-vanishing of the reduced-part projection -/

/-- The reduced-part projection annihilates the strict unit. -/
@[simp]
theorem reducedPart_unit (ε : 𝒜.Augmentation) : ε.reducedPart ε.unit = 0 := by
  apply Subtype.ext
  simp [coe_reducedPart]

/-- The reduced-part projection has degree zero. -/
theorem isHomogeneous_reducedPart (ε : 𝒜.Augmentation) :
    LinearMap.IsHomogeneous ε.reducedPart 𝒜.grading.piece ε.reducedGrading.piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p a ha
  rw [add_zero, reducedGrading_piece, Submodule.mem_comap, Submodule.subtype_apply, coe_reducedPart]
  by_cases hp : p = 0
  · subst hp
    exact (𝒜.grading.piece 0).sub_mem ha ((𝒜.grading.piece 0).smul_mem _ ε.isStrictUnit.degree_zero)
  · rw [ε.map_of_mem_ne_zero p a ha hp, zero_smul, sub_zero]
    exact ha

/-- The reduced-part projection has degree zero for the suspended gradings. -/
private theorem isHomogeneous_reducedPart_shift (ε : 𝒜.Augmentation) :
    LinearMap.IsHomogeneous ε.reducedPart (𝒜.grading.shift 1).piece
      (ε.reducedAlgebra.grading.shift 1).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p a ha
  rw [InternalGrading.shift_piece] at ha
  rw [add_zero, reducedAlgebra_grading, InternalGrading.shift_piece]
  simpa only [add_zero] using ε.isHomogeneous_reducedPart.map_mem ha

/-! ### Spanning decomposition of the bar coalgebra -/

/-- Every reduced tensor word over an augmented `A∞` algebra is a sum of a word with letters in
the augmentation ideal and a degenerate word containing the strict unit. -/
private theorem sup_range_map_subtype_degenerateWords (ε : 𝒜.Augmentation) :
    LinearMap.range (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype) ⊔
      ReducedTensorWords.degenerateWords R A ε.unit = ⊤ := by
  set S := LinearMap.range (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype) ⊔
    ReducedTensorWords.degenerateWords R A ε.unit
  refine top_unique ?_
  rw [← ReducedTensorWords.iSup_range_of R A, iSup_le_iff]
  intro n
  rw [LinearMap.range_le_iff_comap]
  refine top_unique fun t ht ↦ ?_
  clear ht
  induction t using PiTensorProduct.induction_on with
  | add u v hu hv => simpa only [Submodule.mem_comap, map_add] using S.add_mem hu hv
  | smul_tprod r x =>
    rw [Submodule.mem_comap, map_smul]
    refine S.smul_mem r ?_
    -- Replace the first `k` letters inductively, splitting each into its reduced and scalar parts.
    have hrec : ∀ k (y : Fin n.1 → A), (∀ j : Fin n.1, k ≤ j.1 → y j ∈ ε.augmentationIdeal) →
        ReducedTensorWords.of R A n (PiTensorProduct.tprod R y) ∈ S := by
      intro k
      induction k with
      | zero =>
        intro y hy
        refine Submodule.mem_sup_left ?_
        refine ⟨ReducedTensorWords.of R ε.augmentationIdeal n
          (PiTensorProduct.tprod R fun j ↦ ⟨y j, hy j (Nat.zero_le _)⟩), ?_⟩
        rw [ReducedTensorWords.map_of_tprod]
        rfl
      | succ k ih =>
        intro y hy
        by_cases hk : k < n.1
        · classical
          set i : Fin n.1 := ⟨k, hk⟩
          have hsplit : y i = (ε.reducedPart (y i) : A) + ε (y i) • ε.unit := by
            rw [coe_reducedPart, sub_add_cancel]
          have hupd : y = Function.update y i ((ε.reducedPart (y i) : A) + ε (y i) • ε.unit) := by
            rw [← hsplit, Function.update_eq_self]
          rw [hupd, (PiTensorProduct.tprod R).map_update_add, map_add]
          refine S.add_mem (ih _ fun j hj ↦ ?_) ?_
          · by_cases hji : j = i
            · subst hji
              simp
            · rw [Function.update_of_ne hji]
              exact hy j (by have : j.1 ≠ k := fun h ↦ hji (Fin.ext h); omega)
          · exact Submodule.mem_sup_right <|
              ReducedTensorWords.of_tprod_mem_degenerateWords_of_eq_smul n _ (i := i)
                (c := ε (y i)) (by simp)
        · exact ih y fun j hj ↦ hy j (by omega)
    exact hrec n.1 x fun j hj ↦ absurd hj (Nat.not_le_of_gt j.isLt)

/-- Applying `ReducedTensorWords.map ε.reducedPart` annihilates all degenerate words. -/
private theorem map_reducedPart_eq_zero_of_mem_degenerateWords (ε : 𝒜.Augmentation)
    {z : ReducedTensorWords R A} (hz : z ∈ ReducedTensorWords.degenerateWords R A ε.unit) :
    ReducedTensorWords.map (R := R) ε.reducedPart z = 0 := by
  suffices hle : ReducedTensorWords.degenerateWords R A ε.unit ≤
      LinearMap.ker (ReducedTensorWords.map (R := R) ε.reducedPart) from hle hz
  rw [ReducedTensorWords.degenerateWords_le_iff]
  rintro n x ⟨i, hi⟩
  rw [LinearMap.mem_ker, ReducedTensorWords.map_of_tprod,
    (PiTensorProduct.tprod R).map_coord_zero i (by simp [hi]), map_zero]

/-! ### The strictly unital extension of a nonunital morphism `A⁺ ⟶ B` -/

/-- The suspended binary product on `B`, sending `x ⊗ y` to `m₂(σ x, y)`. -/
private noncomputable def suspendedMul (ℬ : AInfinityAlgebra R B) : B ⊗[R] B →ₗ[R] B :=
  TensorProduct.lift (ℬ.mul.comp (ℬ.grading.koszulTwist 1))

private theorem suspendedMul_tmul (ℬ : AInfinityAlgebra R B) (x y : B) :
    suspendedMul ℬ (x ⊗ₜ[R] y) = ℬ.m 2 ![ℬ.grading.koszulTwist 1 x, y] := by
  simp [suspendedMul]

/-- On degenerate words in a strictly unital target `B`, the Taylor map retains only the binary
term, factored through deconcatenation and the letter projection. -/
private theorem taylor_eq_suspendedMul_of_mem_degenerateWords {eB : B} (hB : ℬ.StrictUnit eB)
    {w : ReducedTensorWords R B} (hw : w ∈ ReducedTensorWords.degenerateWords R B eB) :
    ℬ.taylor w = suspendedMul ℬ (TensorProduct.map (ReducedTensorWords.letter R B)
      (ReducedTensorWords.letter R B) (ReducedTensorWords.deconcatenation R B w)) := by
  suffices hle : ReducedTensorWords.degenerateWords R B eB ≤
      LinearMap.ker (ℬ.taylor - suspendedMul ℬ ∘ₗ
        TensorProduct.map (ReducedTensorWords.letter R B) (ReducedTensorWords.letter R B) ∘ₗ
          ReducedTensorWords.deconcatenation R B) by
    exact sub_eq_zero.mp (hle hw)
  rw [ReducedTensorWords.degenerateWords_le_iff]
  rintro ⟨m, hm⟩ y hy
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.comp_apply,
    LinearMap.comp_apply]
  by_cases hm2 : m = 2
  · subst hm2
    have hy' : y = ![y 0, y 1] := by
      funext j
      fin_cases j <;> rfl
    rw [hy']
    -- Match `(⟨2, hm⟩ : {n : ℕ // 0 < n})` with `(2 : ℕ+)`.
    change ℬ.taylor (ReducedTensorWords.of R B (2 : ℕ+) (PiTensorProduct.tprod R ![y 0, y 1])) =
      suspendedMul ℬ (TensorProduct.map (ReducedTensorWords.letter R B)
        (ReducedTensorWords.letter R B)
        (ReducedTensorWords.deconcatenation R B
          (ReducedTensorWords.of R B (2 : ℕ+) (PiTensorProduct.tprod R ![y 0, y 1]))))
    rw [ℬ.taylor_of_two, ReducedTensorWords.deconcatenation_of_two, TensorProduct.map_tmul,
      ReducedTensorWords.letter_ofLetter, ReducedTensorWords.letter_ofLetter, suspendedMul_tmul]
  · rw [hB.taylor_of_tprod_eq_zero ⟨m, hm⟩ hm2 y hy, ReducedTensorWords.of_tprod_eq_subword R hm y,
      ReducedTensorWords.deconcatenation_subword, map_sum, map_sum]
    symm
    refine Finset.sum_eq_zero fun c hc ↦ ?_
    rw [Finset.mem_Ioo] at hc
    rw [TensorProduct.map_tmul]
    by_cases hc1 : c = 1
    · rw [ReducedTensorWords.letter_subword_of_ne_one R B y (0 + c) (by omega),
        TensorProduct.tmul_zero, map_zero]
    · rw [ReducedTensorWords.letter_subword_of_ne_one R B y 0 hc1, TensorProduct.zero_tmul,
        map_zero]

/-- The candidate Taylor map extending `g : A⁺ ⟶ B` to a strictly unital morphism `A ⟶ B`. -/
private noncomputable def extendTaylor (ε : 𝒜.Augmentation) (eB : B)
    (g : AInfinityHom ε.reducedAlgebra ℬ) : ReducedTensorWords R A →ₗ[R] B :=
  g.taylor ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart +
    LinearMap.toSpanSingleton R B eB ∘ₗ ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A

private theorem extendTaylor_ofLetter_unit (ε : 𝒜.Augmentation) (eB : B)
    (g : AInfinityHom ε.reducedAlgebra ℬ) :
    extendTaylor ε eB g (ReducedTensorWords.ofLetter R A ε.unit) = eB := by
  simp [extendTaylor, ReducedTensorWords.map_ofLetter]

private theorem extendTaylor_of_tprod_eq_zero (ε : 𝒜.Augmentation) (eB : B)
    (g : AInfinityHom ε.reducedAlgebra ℬ) (n : {n : ℕ // 0 < n}) (hn : n.1 ≠ 1)
    (x : Fin n.1 → A) (hx : ∃ i, x i = ε.unit) :
    extendTaylor ε eB g (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)) = 0 := by
  have h1 : ReducedTensorWords.map (R := R) ε.reducedPart
      (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)) = 0 :=
    ε.map_reducedPart_eq_zero_of_mem_degenerateWords
      (ReducedTensorWords.of_tprod_mem_degenerateWords n x hx)
  have h2 : ReducedTensorWords.letter R A
      (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)) = 0 := by
    rw [ReducedTensorWords.of_tprod_eq_subword R n.2 x,
      ReducedTensorWords.letter_subword_of_ne_one R A x 0 hn]
  simp [extendTaylor, h1, h2]

private theorem extendTaylor_subword_eq_zero_of_ne_one (ε : 𝒜.Augmentation) (eB : B)
    (g : AInfinityHom ε.reducedAlgebra ℬ) {n a b : ℕ} (x : Fin n → A) (hb : b ≠ 1)
    (hx : ∃ i : Fin n, a ≤ i.1 ∧ i.1 < a + b ∧ x i = ε.unit) :
    extendTaylor ε eB g (ReducedTensorWords.subword R x a b) = 0 := by
  rw [ReducedTensorWords.apply_eq_comp_letter_of_mem_degenerateWords (extendTaylor ε eB g)
    (extendTaylor_of_tprod_eq_zero ε eB g)
    (ReducedTensorWords.subword_mem_degenerateWords x hx),
    ReducedTensorWords.letter_subword_of_ne_one R A x a hb, map_zero, map_zero]

private theorem isHomogeneous_extendTaylor (ε : 𝒜.Augmentation) {eB : B}
    (hB : ℬ.StrictUnit eB) (g : AInfinityHom ε.reducedAlgebra ℬ) :
    LinearMap.IsHomogeneous (extendTaylor ε eB g)
      (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1)) (ℬ.grading.shift 1).piece 0 := by
  have h1 : LinearMap.IsHomogeneous (g.taylor ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart)
      (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1)) (ℬ.grading.shift 1).piece 0 := by
    simpa only [add_zero] using g.isHomogeneous_taylor.comp
      (ReducedTensorWords.isHomogeneous_map (𝒜.grading.shift 1)
        (ε.reducedAlgebra.grading.shift 1) ε.isHomogeneous_reducedPart_shift)
  have h2 : LinearMap.IsHomogeneous
      (LinearMap.toSpanSingleton R B eB ∘ₗ ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A)
      (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1)) (ℬ.grading.shift 1).piece 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro p z hz
    rw [add_zero, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
    have hl : ReducedTensorWords.letter R A z ∈ 𝒜.grading.piece (p + 1) := by
      have := (ReducedTensorWords.isHomogeneous_letter (𝒜.grading.shift 1)).map_mem hz
      rwa [add_zero, InternalGrading.shift_piece] at this
    by_cases hp : p + 1 = 0
    · have hp' : p = -1 := by omega
      subst hp'
      exact ((ℬ.grading.shift 1).piece (-1)).smul_mem _ hB.mem_shift_one_piece
    · rw [ε.map_of_mem_ne_zero (p + 1) _ hl hp, zero_smul]
      exact Submodule.zero_mem _
  exact h1.add h2

private theorem extendTaylor_comp_map_subtype (ε : 𝒜.Augmentation) (eB : B)
    (g : AInfinityHom ε.reducedAlgebra ℬ) :
    extendTaylor ε eB g ∘ₗ ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype =
      g.taylor := by
  have hsub : ε.reducedPart ∘ₗ ε.augmentationIdeal.subtype = LinearMap.id :=
    LinearMap.ext ε.reducedPart_coe
  refine LinearMap.ext fun z ↦ ?_
  simp only [extendTaylor, LinearMap.comp_apply, LinearMap.add_apply,
    ← LinearMap.comp_apply (ReducedTensorWords.map (R := R) ε.reducedPart),
    ← ReducedTensorWords.map_comp, hsub, ReducedTensorWords.map_id, LinearMap.id_apply,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R A), ReducedTensorWords.letter_comp_map,
    LinearMap.comp_apply, Submodule.subtype_apply,
    (ε.mem_augmentationIdeal).mp (ReducedTensorWords.letter R ε.augmentationIdeal z).2,
    map_zero, add_zero]

private theorem coalgHom_extendTaylor_comp_map_subtype (ε : 𝒜.Augmentation) (eB : B)
    (g : AInfinityHom ε.reducedAlgebra ℬ) :
    ReducedTensorWords.coalgHom R (extendTaylor ε eB g) ∘ₗ
        ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype =
      g.barMap := by
  refine ((ReducedTensorWords.isCoalgHom_coalgHom _).comp
    (ReducedTensorWords.isCoalgHom_map _)).eq_of_letter_comp_eq g.isCoalgHom_barMap ?_
  rw [← LinearMap.comp_assoc, ReducedTensorWords.letter_comp_coalgHom,
    extendTaylor_comp_map_subtype, g.taylor_def]

/-- On degenerate words, the left-hand side of the component equation for `extendTaylor` reduces to
`suspendedMul ℬ` applied to the deconcatenation. -/
private theorem taylor_coalgHom_extendTaylor_of_mem_degenerateWords (ε : 𝒜.Augmentation) {eB : B}
    (hB : ℬ.StrictUnit eB) (g : AInfinityHom ε.reducedAlgebra ℬ) {z : ReducedTensorWords R A}
    (hz : z ∈ ReducedTensorWords.degenerateWords R A ε.unit) :
    ℬ.taylor (ReducedTensorWords.coalgHom R (extendTaylor ε eB g) z) =
      suspendedMul ℬ (TensorProduct.map (extendTaylor ε eB g) (extendTaylor ε eB g)
        (ReducedTensorWords.deconcatenation R A z)) := by
  have hmem : ReducedTensorWords.coalgHom R (extendTaylor ε eB g) z ∈
      ReducedTensorWords.degenerateWords R B eB :=
    ReducedTensorWords.coalgHom_mem_degenerateWords (extendTaylor ε eB g)
      (extendTaylor_ofLetter_unit ε eB g) (extendTaylor_of_tprod_eq_zero ε eB g) hz
  rw [taylor_eq_suspendedMul_of_mem_degenerateWords hB hmem,
    (ReducedTensorWords.isCoalgHom_coalgHom _).deconcatenation_apply,
    ← LinearMap.comp_apply (TensorProduct.map _ _), ← TensorProduct.map_comp,
    ReducedTensorWords.letter_comp_coalgHom]

/-- Evaluating the right-hand side of the component equation for `extendTaylor` on a homogeneous
degenerate word of length `k + 2` leaves only the arity-two unit collapses adjacent to the unit
position `i`. -/
private theorem extendTaylor_barDifferential_degenerate_summand (ε : 𝒜.Augmentation) (eB : B)
    (g : AInfinityHom ε.reducedAlgebra ℬ) {k : ℕ} (x : Fin (k + 2) → A) (i : Fin (k + 2))
    (hi : x i = ε.unit) {p d : ℕ}
    (hnot : ¬(d = 2 ∧ ((p = i.1 ∧ i.1 < k + 1) ∨ (p + 1 = i.1 ∧ 0 < i.1)))) :
    extendTaylor ε eB g
      (ReducedTensorWords.splice R x 0 (k + 2) p d
        (𝒜.taylor (ReducedTensorWords.subword R x p d))) = 0 := by
  by_cases hfit : 0 < d ∧ p + d ≤ k + 2
  swap
  · rw [ReducedTensorWords.splice_eq_zero_of_not_fits R _ _ hfit, map_zero]
  rcases hfit with ⟨hd0, hpd⟩
  by_cases hblock : p ≤ i.1 ∧ i.1 < p + d
  · rcases hblock with ⟨hpi, hipd⟩
    have hd2 : d ≠ 2 := by
      intro hd
      subst hd
      exact hnot ⟨rfl, by omega⟩
    rw [ReducedTensorWords.subword_eq_of_tprod R x hd0 hpd,
      ε.isStrictUnit.taylor_of_tprod_eq_zero ⟨d, hd0⟩ hd2 _
        ⟨⟨i.1 - p, by dsimp only; omega⟩, by
          rw [← hi]; exact congrArg x (Fin.ext (by simp; omega))⟩,
      ReducedTensorWords.splice_zero, map_zero]
  · obtain ⟨y, ⟨j, hj⟩, hy⟩ := ReducedTensorWords.exists_splice_eq_of_tprod R x hpd
      (𝒜.taylor (ReducedTensorWords.subword R x p d)) hblock
    have hlen : k + 2 + 1 - d ≠ 1 := by
      have : i.1 < k + 2 := i.isLt
      omega
    rw [hy]
    exact extendTaylor_of_tprod_eq_zero ε eB g ⟨k + 2 + 1 - d, by omega⟩ hlen y ⟨j, hj.trans hi⟩

/-- Helper computing the `p = m, d = 2` summand when `x ⟨m + 1, _⟩ = ε.unit`. -/
private theorem extendTaylor_barDifferential_term_pred (ε : 𝒜.Augmentation) (eB : B)
    (g : AInfinityHom ε.reducedAlgebra ℬ) {k m : ℕ} (hm : m + 1 < k + 2)
    (x : Fin (k + 2) → A) (𝒟 : Fin (k + 2) → ℤ)
    (hx : ∀ j, x j ∈ (𝒜.grading.shift 1).piece (𝒟 j)) (hi : x ⟨m + 1, hm⟩ = ε.unit) :
    (((1 * ∑ j ∈ Finset.range m, if h : j < k + 2 then 𝒟 ⟨j, h⟩ else 0).negOnePow : ℤ) : R) •
        extendTaylor ε eB g
          (ReducedTensorWords.splice R x 0 (k + 2) m 2
            (𝒜.taylor (ReducedTensorWords.subword R x m 2))) =
      ((((∑ j ∈ Finset.range (m + 1), if h : j < k + 2 then 𝒟 ⟨j, h⟩ else 0) + 1).negOnePow :
        ℤ) : R) •
        extendTaylor ε eB g
          (ReducedTensorWords.splice R x 0 (k + 2) m 2 (x ⟨m, by omega⟩)) := by
  have hsub : ReducedTensorWords.subword R x m 2 =
      ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![x ⟨m, by omega⟩, ε.unit]) := by
    rw [ReducedTensorWords.subword_eq_of_tprod R x two_pos (by omega)]
    refine ReducedTensorWords.of_tprod_congr R A two_pos rfl fun j ↦ ?_
    fin_cases j
    · simp
    · simpa using hi
  have hxm : x ⟨m, by omega⟩ ∈ 𝒜.grading.piece (𝒟 ⟨m, by omega⟩ + 1) := by
    simpa only [InternalGrading.shift_piece] using hx ⟨m, by omega⟩
  rw [hsub, ε.isStrictUnit.taylor_of_two_unit_right,
    𝒜.grading.koszulTwist_apply_of_mem hxm 1, ReducedTensorWords.splice_smul, map_smul, smul_smul]
  congr 1
  rw [one_mul, one_mul, Finset.sum_range_succ, dite_eq_left (by omega : m < k + 2),
    ← Int.cast_mul, ← Units.val_mul, ← Int.negOnePow_add, add_assoc]

/-- Helper computing the `p = m, d = 2` summand when `x ⟨m, _⟩ = ε.unit` and `m < k + 1`. -/
private theorem extendTaylor_barDifferential_term_succ (ε : 𝒜.Augmentation) {k m : ℕ}
    (hm : m < k + 1) (x : Fin (k + 2) → A) (hi : x ⟨m, by omega⟩ = ε.unit) :
    𝒜.taylor (ReducedTensorWords.subword R x m 2) = x ⟨m + 1, by omega⟩ := by
  have hsub : ReducedTensorWords.subword R x m 2 =
      ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![ε.unit, x ⟨m + 1, by omega⟩])
      := by
    rw [ReducedTensorWords.subword_eq_of_tprod R x two_pos (by omega)]
    refine ReducedTensorWords.of_tprod_congr R A two_pos rfl fun j ↦ ?_
    fin_cases j
    · simpa using hi
    · rfl
  rw [hsub, ε.isStrictUnit.taylor_of_two_unit_left]

/-- All terms in the deconcatenation sum vanish except at `c = 1` when `i = 0` and at `c = k + 1`
when `i = k + 1`. -/
private theorem suspendedMul_deconcatenation_summand_eq_zero (ε : 𝒜.Augmentation) (eB : B)
    (g : AInfinityHom ε.reducedAlgebra ℬ) {k : ℕ} (x : Fin (k + 2) → A) (i : Fin (k + 2))
    (hi : x i = ε.unit) {c : ℕ} (hc : c ∈ Finset.Ioo 0 (k + 2))
    (hne : ¬((c = 1 ∧ i.1 = 0) ∨ (c = k + 1 ∧ i.1 = k + 1))) :
    suspendedMul ℬ (extendTaylor ε eB g (ReducedTensorWords.subword R x 0 c) ⊗ₜ[R]
      extendTaylor ε eB g (ReducedTensorWords.subword R x c (k + 2 - c))) = 0 := by
  rw [Finset.mem_Ioo] at hc
  by_cases hic : i.1 < c
  · have hc1 : c ≠ 1 := fun h ↦ hne (Or.inl ⟨h, by omega⟩)
    rw [extendTaylor_subword_eq_zero_of_ne_one ε eB g x hc1 ⟨i, by omega, by omega, hi⟩,
      TensorProduct.zero_tmul, map_zero]
  · have hrc1 : k + 2 - c ≠ 1 := fun h ↦ hne (Or.inr ⟨by omega, by have := i.isLt; omega⟩)
    rw [extendTaylor_subword_eq_zero_of_ne_one ε eB g x hrc1 ⟨i, by omega, by omega, hi⟩,
      TensorProduct.tmul_zero, map_zero]

/-- Left-edge case (`i = 0`) of `extendTaylor_component_eq_on_degenerate_add_two`. -/
private theorem extendTaylor_component_eq_on_degenerate_zero (ε : 𝒜.Augmentation) {eB : B}
    (hB : ℬ.StrictUnit eB) (g : AInfinityHom ε.reducedAlgebra ℬ) (k : ℕ)
    (x : Fin (k + 2) → A) (𝒟 : Fin (k + 2) → ℤ) (i : Fin (k + 2))
    (hi : x i = ε.unit) (hi0 : i.1 = 0) :
    ∑ c ∈ Finset.Ioo 0 (k + 2),
        suspendedMul ℬ (extendTaylor ε eB g (ReducedTensorWords.subword R x 0 c) ⊗ₜ[R]
          extendTaylor ε eB g (ReducedTensorWords.subword R x c (k + 2 - c))) =
      ∑ p ∈ Finset.range (k + 2), ∑ d ∈ Finset.range (k + 3),
        (((1 * ∑ j ∈ Finset.range p, if h : j < k + 2 then 𝒟 ⟨j, h⟩ else 0).negOnePow : ℤ) : R) •
          extendTaylor ε eB g
            (ReducedTensorWords.splice R x 0 (k + 2) p d
              (𝒜.taylor (ReducedTensorWords.subword R x p d))) := by
  have hx0 : x ⟨0, by omega⟩ = ε.unit := by rw [← hi]; congr 1; exact Fin.ext hi0.symm
  rw [Finset.sum_eq_single 1
      (fun c hc hc1 ↦ suspendedMul_deconcatenation_summand_eq_zero ε eB g x i hi hc (by omega))
      (fun h ↦ absurd (Finset.mem_Ioo.mpr ⟨by omega, by omega⟩) h),
    Finset.sum_eq_single 0 (fun p _ hp0 ↦ Finset.sum_eq_zero fun d _ ↦ by
      rw [extendTaylor_barDifferential_degenerate_summand ε eB g x i hi (by omega), smul_zero])
      (fun h ↦ absurd (Finset.mem_range.mpr (by omega)) h),
    Finset.sum_eq_single 2 (fun d _ hd2 ↦ by
      rw [extendTaylor_barDifferential_degenerate_summand ε eB g x i hi (by omega), smul_zero])
      (fun h ↦ absurd (Finset.mem_range.mpr (by omega)) h),
    ReducedTensorWords.subword_one R A x (by omega), hx0, extendTaylor_ofLetter_unit,
    suspendedMul_tmul, ℬ.grading.koszulTwist_apply_of_mem_zero hB.degree_zero, hB.binary_left,
    extendTaylor_barDifferential_term_succ ε (by omega) x hx0,
    ReducedTensorWords.splice_two_succ_eq_subword R (by omega) rfl x]
  simp

/-- Right-edge case (`i = k + 1`) of `extendTaylor_component_eq_on_degenerate_add_two`. -/
private theorem extendTaylor_component_eq_on_degenerate_last (ε : 𝒜.Augmentation) {eB : B}
    (hB : ℬ.StrictUnit eB) (g : AInfinityHom ε.reducedAlgebra ℬ) (k : ℕ)
    (x : Fin (k + 2) → A) (𝒟 : Fin (k + 2) → ℤ) (i : Fin (k + 2))
    (hx : ∀ j, x j ∈ (𝒜.grading.shift 1).piece (𝒟 j)) (hi : x i = ε.unit) (hil : i.1 = k + 1) :
    ∑ c ∈ Finset.Ioo 0 (k + 2),
        suspendedMul ℬ (extendTaylor ε eB g (ReducedTensorWords.subword R x 0 c) ⊗ₜ[R]
          extendTaylor ε eB g (ReducedTensorWords.subword R x c (k + 2 - c))) =
      ∑ p ∈ Finset.range (k + 2), ∑ d ∈ Finset.range (k + 3),
        (((1 * ∑ j ∈ Finset.range p, if h : j < k + 2 then 𝒟 ⟨j, h⟩ else 0).negOnePow : ℤ) : R) •
          extendTaylor ε eB g
            (ReducedTensorWords.splice R x 0 (k + 2) p d
              (𝒜.taylor (ReducedTensorWords.subword R x p d))) := by
  have hxl : x ⟨k + 1, by omega⟩ = ε.unit := by rw [← hi]; congr 1; exact Fin.ext hil.symm
  have hsub1 : k + 2 - (k + 1) = 1 := by omega
  rw [Finset.sum_eq_single (k + 1)
      (fun c hc hcl ↦ suspendedMul_deconcatenation_summand_eq_zero ε eB g x i hi hc (by omega))
      (fun h ↦ absurd (Finset.mem_Ioo.mpr ⟨by omega, by omega⟩) h),
    Finset.sum_eq_single k (fun p _ hpk ↦ Finset.sum_eq_zero fun d _ ↦ by
      rw [extendTaylor_barDifferential_degenerate_summand ε eB g x i hi (by omega), smul_zero])
      (fun h ↦ absurd (Finset.mem_range.mpr (by omega)) h),
    Finset.sum_eq_single 2 (fun d _ hd2 ↦ by
      rw [extendTaylor_barDifferential_degenerate_summand ε eB g x i hi (by omega), smul_zero])
      (fun h ↦ absurd (Finset.mem_range.mpr (by omega)) h),
    hsub1, ReducedTensorWords.subword_one R A x (by omega), hxl, extendTaylor_ofLetter_unit,
    suspendedMul_tmul, hB.binary_right,
    extendTaylor_barDifferential_term_pred ε eB g (by omega) x 𝒟 hx hxl,
    ReducedTensorWords.splice_two_pred_eq_subword R rfl x]
  have hmem : ReducedTensorWords.subword R x 0 (k + 1) ∈
      ReducedTensorWords.gradedPiece (𝒜.grading.shift 1)
        (∑ j ∈ Finset.range (k + 1), if h : j < k + 2 then 𝒟 ⟨j, h⟩ else 0) := by
    simpa only [Nat.zero_add] using
      ReducedTensorWords.subword_mem_gradedPiece (G := 𝒜.grading.shift 1) x
        (𝒟 := fun j ↦ if h : j < k + 2 then 𝒟 ⟨j, h⟩ else 0)
        (fun j ↦ by simpa only [dite_eq_left j.isLt] using hx j) 0 (k + 1)
  have htmem : extendTaylor ε eB g (ReducedTensorWords.subword R x 0 (k + 1)) ∈
      ℬ.grading.piece
        ((∑ j ∈ Finset.range (k + 1), if h : j < k + 2 then 𝒟 ⟨j, h⟩ else 0) + 1) := by
    have := (isHomogeneous_extendTaylor ε hB g).map_mem hmem
    rwa [add_zero, InternalGrading.shift_piece] at this
  rw [ℬ.grading.koszulTwist_apply_of_mem htmem 1, one_mul]

/-- Interior case (`0 < i < k + 1`) of `extendTaylor_component_eq_on_degenerate_add_two`. -/
private theorem extendTaylor_component_eq_on_degenerate_mid (ε : 𝒜.Augmentation) {eB : B}
    (g : AInfinityHom ε.reducedAlgebra ℬ) (k : ℕ)
    (x : Fin (k + 2) → A) (𝒟 : Fin (k + 2) → ℤ) (i : Fin (k + 2))
    (hx : ∀ j, x j ∈ (𝒜.grading.shift 1).piece (𝒟 j)) (hi : x i = ε.unit)
    (hi0 : i.1 ≠ 0) (hil : i.1 ≠ k + 1) :
    ∑ c ∈ Finset.Ioo 0 (k + 2),
        suspendedMul ℬ (extendTaylor ε eB g (ReducedTensorWords.subword R x 0 c) ⊗ₜ[R]
          extendTaylor ε eB g (ReducedTensorWords.subword R x c (k + 2 - c))) =
      ∑ p ∈ Finset.range (k + 2), ∑ d ∈ Finset.range (k + 3),
        (((1 * ∑ j ∈ Finset.range p, if h : j < k + 2 then 𝒟 ⟨j, h⟩ else 0).negOnePow : ℤ) : R) •
          extendTaylor ε eB g
            (ReducedTensorWords.splice R x 0 (k + 2) p d
              (𝒜.taylor (ReducedTensorWords.subword R x p d))) := by
  have hlt : i.1 < k + 1 := by have := i.isLt; omega
  obtain ⟨m, hm⟩ : ∃ m, i.1 = m + 1 := ⟨i.1 - 1, by omega⟩
  have hxm1 : x ⟨m + 1, by omega⟩ = ε.unit := by rw [← hi]; congr 1; exact Fin.ext hm.symm
  have hinner (p : ℕ) :
      ∑ d ∈ Finset.range (k + 3),
        (((1 * ∑ j ∈ Finset.range p, if h : j < k + 2 then 𝒟 ⟨j, h⟩ else 0).negOnePow : ℤ) : R) •
          extendTaylor ε eB g
            (ReducedTensorWords.splice R x 0 (k + 2) p d
              (𝒜.taylor (ReducedTensorWords.subword R x p d))) =
        (((1 * ∑ j ∈ Finset.range p, if h : j < k + 2 then 𝒟 ⟨j, h⟩ else 0).negOnePow : ℤ) : R) •
          extendTaylor ε eB g
            (ReducedTensorWords.splice R x 0 (k + 2) p 2
              (𝒜.taylor (ReducedTensorWords.subword R x p 2))) :=
    Finset.sum_eq_single 2 (fun d _ hd2 ↦ by
      rw [extendTaylor_barDifferential_degenerate_summand ε eB g x i hi (by omega), smul_zero])
      (fun h ↦ absurd (Finset.mem_range.mpr (by omega)) h)
  rw [Finset.sum_eq_zero fun c hc ↦
        suspendedMul_deconcatenation_summand_eq_zero ε eB g x i hi hc (by omega),
      Finset.sum_eq_add m (m + 1) (by omega)
        (fun p _ hp ↦ Finset.sum_eq_zero fun d _ ↦ by
          rw [extendTaylor_barDifferential_degenerate_summand ε eB g x i hi (by omega), smul_zero])
        (fun h ↦ absurd (Finset.mem_range.mpr (by omega)) h)
        (fun h ↦ absurd (Finset.mem_range.mpr (by omega)) h),
      hinner m, hinner (m + 1),
      extendTaylor_barDifferential_term_pred ε eB g (by omega) x 𝒟 hx hxm1,
      extendTaylor_barDifferential_term_succ ε (by omega) x hxm1,
      ReducedTensorWords.splice_two_succ_eq_splice_two_pred R (by omega) (by omega) x]
  simp only [Nat.add_sub_cancel, one_mul, ← add_smul, Int.negOnePow_succ, Units.val_neg,
    Int.cast_neg, neg_add_cancel, zero_smul]

/-- The component equation for `extendTaylor` on homogeneous degenerate words of length `k + 2`. -/
private theorem extendTaylor_component_eq_on_degenerate_add_two (ε : 𝒜.Augmentation) {eB : B}
    (hB : ℬ.StrictUnit eB) (g : AInfinityHom ε.reducedAlgebra ℬ) (k : ℕ)
    (x : Fin (k + 2) → A) (𝒟 : Fin (k + 2) → ℤ) (i : Fin (k + 2))
    (hx : ∀ j, x j ∈ (𝒜.grading.shift 1).piece (𝒟 j)) (hi : x i = ε.unit) :
    suspendedMul ℬ (TensorProduct.map (extendTaylor ε eB g) (extendTaylor ε eB g)
        (ReducedTensorWords.deconcatenation R A
          (ReducedTensorWords.of R A ⟨k + 2, by omega⟩ (PiTensorProduct.tprod R x)))) =
      extendTaylor ε eB g
        (𝒜.barDifferential
          (ReducedTensorWords.of R A ⟨k + 2, by omega⟩ (PiTensorProduct.tprod R x))) := by
  rw [ReducedTensorWords.of_tprod_eq_subword R (by omega : 0 < k + 2) x,
    ReducedTensorWords.deconcatenation_subword, map_sum, map_sum,
    ← ReducedTensorWords.of_tprod_eq_subword R (by omega : 0 < k + 2) x,
    𝒜.barDifferential_def,
    ReducedTensorWords.gradedCoderiv_of_tprod_of_homogeneous _ _ 1 (by omega) x 𝒟 hx, map_sum]
  simp only [Nat.zero_add, TensorProduct.map_tmul, map_sum, map_smul]
  rcases eq_or_ne i.1 0 with hi0 | hi0
  · exact extendTaylor_component_eq_on_degenerate_zero ε hB g k x 𝒟 i hi hi0
  · rcases eq_or_ne i.1 (k + 1) with hil | hil
    · exact extendTaylor_component_eq_on_degenerate_last ε hB g k x 𝒟 i hx hi hil
    · exact extendTaylor_component_eq_on_degenerate_mid ε g k x 𝒟 i hx hi hi0 hil

/-- The component equation for `extendTaylor` holds on the entire bar coalgebra `Tᶜ(sA)`. -/
private theorem extendTaylor_component_eq (ε : 𝒜.Augmentation) {eB : B}
    (hB : ℬ.StrictUnit eB) (g : AInfinityHom ε.reducedAlgebra ℬ) :
    ℬ.taylor ∘ₗ ReducedTensorWords.coalgHom R (extendTaylor ε eB g) =
      extendTaylor ε eB g ∘ₗ 𝒜.barDifferential := by
  set K := LinearMap.ker
    (ℬ.taylor ∘ₗ ReducedTensorWords.coalgHom R (extendTaylor ε eB g) -
      extendTaylor ε eB g ∘ₗ 𝒜.barDifferential)
  suffices htop : ⊤ ≤ K from LinearMap.ext fun z ↦ sub_eq_zero.mp (htop Submodule.mem_top)
  rw [← ε.sup_range_map_subtype_degenerateWords, sup_le_iff]
  constructor
  · rw [LinearMap.range_le_iff_comap]
    refine top_unique fun z _ ↦ ?_
    rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
      LinearMap.comp_apply, LinearMap.comp_apply,
      ← LinearMap.comp_apply (ReducedTensorWords.coalgHom _ _),
      coalgHom_extendTaylor_comp_map_subtype, ← LinearMap.comp_apply ℬ.taylor, g.taylor_comp_barMap]
    have hbar := LinearMap.congr_fun ε.reducedInclusion.barDifferential_comp_barMap z
    rw [AInfinityStrictHom.barMap_def, reducedInclusion_toLinearMap, LinearMap.comp_apply,
      LinearMap.comp_apply] at hbar
    rw [hbar, ← LinearMap.comp_apply (extendTaylor ε eB g), extendTaylor_comp_map_subtype,
      LinearMap.comp_apply]
  · rw [ReducedTensorWords.degenerateWords_le_iff_of_mem_piece (𝒜.grading.shift 1)
      ε.isStrictUnit.mem_shift_one_piece]
    rintro ⟨n, hn⟩ x 𝒟 i hx hi _
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.comp_apply,
      LinearMap.comp_apply,
      taylor_coalgHom_extendTaylor_of_mem_degenerateWords ε hB g
        (ReducedTensorWords.of_tprod_mem_degenerateWords ⟨n, hn⟩ x ⟨i, hi⟩)]
    rcases n with _ | _ | k
    · exact absurd hn (Nat.lt_irrefl 0)
    · have hx0 : x ⟨0, Nat.one_pos⟩ = ε.unit := by
        rw [← hi]
        exact congrArg x (Fin.ext (Nat.eq_zero_of_le_zero (Nat.lt_succ_iff.mp i.isLt)).symm)
      have hof : ReducedTensorWords.of R A ⟨1, hn⟩ (PiTensorProduct.tprod R x) =
          ReducedTensorWords.ofLetter R A ε.unit := by
        rw [ReducedTensorWords.of_tprod_eq_subword R hn x,
          ReducedTensorWords.subword_one R A x Nat.one_pos, hx0]
      rw [hof, ReducedTensorWords.deconcatenation_ofLetter, map_zero, map_zero,
        𝒜.barDifferential_ofLetter, ε.isStrictUnit.unary_eq_zero, map_zero, map_zero]
    · exact extendTaylor_component_eq_on_degenerate_add_two ε hB g k x 𝒟 i hx hi

/-- The strictly unital `A∞` morphism `A ⟶ B` extending a nonunital morphism `g : A⁺ ⟶ B`. -/
private noncomputable def extendHom (ε : 𝒜.Augmentation) {eB : B} (hB : ℬ.StrictUnit eB)
    (g : AInfinityHom ε.reducedAlgebra ℬ) :
    {f : AInfinityHom 𝒜 ℬ // f.IsStrictlyUnital ε.isStrictUnit hB} :=
  ⟨AInfinityHom.ofTaylor (extendTaylor ε eB g) (isHomogeneous_extendTaylor ε hB g)
      (extendTaylor_component_eq ε hB g),
    ⟨by
        rw [AInfinityHom.linearPart_apply, AInfinityHom.taylor_ofTaylor,
          extendTaylor_ofLetter_unit],
      fun {n} hn x hx ↦ by
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · simp
        · rw [AInfinityHom.component_apply _ n hpos, AInfinityHom.taylor_ofTaylor]
          obtain ⟨i, hi⟩ := hx
          exact extendTaylor_of_tprod_eq_zero ε eB g ⟨n, hpos⟩ hn _
            ⟨i, by rw [hi, 𝒜.grading.koszulTwist_apply_of_mem_zero ε.isStrictUnit.degree_zero]⟩⟩⟩

/-! ### The equivalence between strictly unital morphisms `A ⟶ B` and morphisms `A⁺ ⟶ B` -/

/-- **Strictly unital `A∞` morphisms out of an augmented `A∞` algebra are determined by their
restriction to the augmentation ideal.**  For an augmented `A∞` algebra `(A, ε)` and any `A∞`
algebra `B` with a strict unit, restriction along `A⁺ ⟶ A` gives a bijection between strictly
unital `A∞` morphisms `A ⟶ B` and arbitrary nonunital `A∞` morphisms `A⁺ ⟶ B`. -/
noncomputable def strictlyUnitalHomEquiv (ε : 𝒜.Augmentation) {eB : B} (hB : ℬ.StrictUnit eB) :
    {f : AInfinityHom 𝒜 ℬ // f.IsStrictlyUnital ε.isStrictUnit hB} ≃
      AInfinityHom ε.reducedAlgebra ℬ where
  toFun f := f.1.comp ε.reducedInclusion.toAInfinityHom
  invFun g := extendHom ε hB g
  left_inv f := by
    apply Subtype.ext
    apply AInfinityHom.ext
    dsimp only [extendHom]
    rw [AInfinityHom.taylor_ofTaylor]
    set K := LinearMap.ker (extendTaylor ε eB (f.1.comp ε.reducedInclusion.toAInfinityHom) -
      f.1.taylor)
    suffices htop : ⊤ ≤ K from LinearMap.ext fun z ↦ sub_eq_zero.mp (htop Submodule.mem_top)
    rw [← ε.sup_range_map_subtype_degenerateWords, sup_le_iff]
    constructor
    · rw [LinearMap.range_le_iff_comap]
      refine top_unique fun z _ ↦ ?_
      rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
        ← LinearMap.comp_apply (extendTaylor _ _ _), extendTaylor_comp_map_subtype,
        AInfinityHom.taylor_comp, AInfinityStrictHom.barMap_toAInfinityHom,
        AInfinityStrictHom.barMap_def, reducedInclusion_toLinearMap, LinearMap.comp_apply]
    · rw [ReducedTensorWords.degenerateWords_le_iff]
      rintro ⟨n, hn⟩ x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      by_cases hn1 : n = 1
      · subst hn1
        obtain ⟨i, hi⟩ := hx
        have hx0 : x ⟨0, Nat.one_pos⟩ = ε.unit := by
          rw [← hi]; congr 1; exact Subsingleton.elim _ _
        have hof : ReducedTensorWords.of R A ⟨1, hn⟩ (PiTensorProduct.tprod R x) =
            ReducedTensorWords.ofLetter R A ε.unit := by
          rw [ReducedTensorWords.of_tprod_eq_subword R hn x,
            ReducedTensorWords.subword_one R A x Nat.one_pos, hx0]
        rw [hof, extendTaylor_ofLetter_unit, ← AInfinityHom.linearPart_apply, f.2.map_unit]
      · rw [extendTaylor_of_tprod_eq_zero ε eB _ ⟨n, hn⟩ hn1 x hx,
          f.2.taylor_of_tprod_eq_zero ⟨n, hn⟩ hn1 x hx]
  right_inv g := by
    apply AInfinityHom.ext
    dsimp only [extendHom]
    rw [AInfinityHom.taylor_comp, AInfinityStrictHom.barMap_toAInfinityHom,
      AInfinityStrictHom.barMap_def, reducedInclusion_toLinearMap,
      AInfinityHom.taylor_ofTaylor, extendTaylor_comp_map_subtype]

@[simp]
theorem strictlyUnitalHomEquiv_apply (ε : 𝒜.Augmentation) {eB : B} (hB : ℬ.StrictUnit eB)
    (f : {f : AInfinityHom 𝒜 ℬ // f.IsStrictlyUnital ε.isStrictUnit hB}) :
    ε.strictlyUnitalHomEquiv hB f = f.1.comp ε.reducedInclusion.toAInfinityHom := (rfl)

/-- The Taylor map of the strictly unital extension of `g : A⁺ ⟶ B`. -/
@[simp]
theorem taylor_strictlyUnitalHomEquiv_symm (ε : 𝒜.Augmentation) {eB : B} (hB : ℬ.StrictUnit eB)
    (g : AInfinityHom ε.reducedAlgebra ℬ) :
    ((ε.strictlyUnitalHomEquiv hB).symm g).1.taylor =
      g.taylor ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart +
        LinearMap.toSpanSingleton R B eB ∘ₗ ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A := by
  simp [strictlyUnitalHomEquiv, extendHom, extendTaylor]

/-- On the augmentation ideal, the linear part of the strictly unital extension agrees with the
linear part of `g`. -/
theorem linearPart_strictlyUnitalHomEquiv_symm_coe (ε : 𝒜.Augmentation) {eB : B}
    (hB : ℬ.StrictUnit eB) (g : AInfinityHom ε.reducedAlgebra ℬ) (x : ε.augmentationIdeal) :
    ((ε.strictlyUnitalHomEquiv hB).symm g).1.linearPart x = g.linearPart x := by
  rw [AInfinityHom.linearPart_apply, taylor_strictlyUnitalHomEquiv_symm]
  simp [ReducedTensorWords.map_ofLetter, (ε.mem_augmentationIdeal).mp x.2]

/-- On the strict unit, the linear part of the strictly unital extension sends the source unit to
the target unit. -/
theorem linearPart_strictlyUnitalHomEquiv_symm_unit (ε : 𝒜.Augmentation) {eB : B}
    (hB : ℬ.StrictUnit eB) (g : AInfinityHom ε.reducedAlgebra ℬ) :
    ((ε.strictlyUnitalHomEquiv hB).symm g).1.linearPart ε.unit = eB :=
  ((ε.strictlyUnitalHomEquiv hB).symm g).2.map_unit

/-- The strictly unital extension is natural under post-composition by strictly unital strict `A∞`
morphisms. -/
theorem strictlyUnitalHomEquiv_symm_comp_strict (ε : 𝒜.Augmentation) {eB : B} {eC : C}
    (hB : ℬ.StrictUnit eB) (hC : 𝒞.StrictUnit eC) (φ : AInfinityStrictUnitalHom hB hC)
    (g : AInfinityHom ε.reducedAlgebra ℬ) :
    ((ε.strictlyUnitalHomEquiv hC).symm (φ.toAInfinityStrictHom.toAInfinityHom.comp g)).1 =
      φ.toAInfinityStrictHom.toAInfinityHom.comp ((ε.strictlyUnitalHomEquiv hB).symm g).1 := by
  refine AInfinityHom.ext (LinearMap.ext fun z ↦ ?_)
  rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, taylor_strictlyUnitalHomEquiv_symm,
    taylor_strictlyUnitalHomEquiv_symm, AInfinityStrictHom.taylor_toAInfinityHom_comp]
  simp [AInfinityStrictHom.coe_toLinearMap, φ.map_unit']

/-! ### Preservation of augmentations -/

/-- A strictly unital `A∞` morphism `f : A ⟶ B` between augmented `A∞` algebras commutes with the
augmentations if and only if the Taylor components of its restriction `A⁺ ⟶ B` vanish under the
target augmentation. -/
theorem comp_toAInfinityStrictHom_eq_iff (ε : 𝒜.Augmentation) (εB : ℬ.Augmentation)
    (f : {f : AInfinityHom 𝒜 ℬ // f.IsStrictlyUnital ε.isStrictUnit εB.isStrictUnit}) :
    εB.toAInfinityStrictHom.toAInfinityHom.comp f.1 = ε.toAInfinityStrictHom.toAInfinityHom ↔
      εB.toLinearMap ∘ₗ (ε.strictlyUnitalHomEquiv εB.isStrictUnit f).taylor = 0 := by
  have hε0 : ε.toLinearMap ∘ₗ ε.augmentationIdeal.subtype = 0 :=
    LinearMap.ext fun x ↦ (ε.mem_augmentationIdeal).mp x.2
  have hcomp_red : (ε.toAInfinityStrictHom.toAInfinityHom.comp
      ε.reducedInclusion.toAInfinityHom).taylor = 0 := by
    rw [AInfinityStrictHom.taylor_toAInfinityHom_comp, AInfinityStrictHom.taylor_toAInfinityHom,
      toAInfinityStrictHom_toLinearMap, reducedInclusion_toLinearMap, ← LinearMap.comp_assoc, hε0,
      LinearMap.zero_comp]
  constructor
  · intro h
    have h' := congrArg (fun k ↦ (k.comp ε.reducedInclusion.toAInfinityHom).taylor) h
    rw [AInfinityHom.comp_assoc, AInfinityStrictHom.taylor_toAInfinityHom_comp,
      toAInfinityStrictHom_toLinearMap, hcomp_red] at h'
    exact h'
  · intro h
    let lhs : {k : AInfinityHom 𝒜
        (isDGAlgebra_trivialGrading R).toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
        k.IsStrictlyUnital ε.isStrictUnit (isDGAlgebra_trivialGrading R).strictUnit_one} :=
      ⟨εB.toAInfinityStrictHom.toAInfinityHom.comp f.1,
        εB.toAInfinityStrictUnitalHom.isStrictlyUnital_toAInfinityHom.comp f.2⟩
    let rhs : {k : AInfinityHom 𝒜
        (isDGAlgebra_trivialGrading R).toIsNonUnitalDGAlgebra.toAInfinityAlgebra //
        k.IsStrictlyUnital ε.isStrictUnit (isDGAlgebra_trivialGrading R).strictUnit_one} :=
      ⟨ε.toAInfinityStrictHom.toAInfinityHom,
        ε.toAInfinityStrictUnitalHom.isStrictlyUnital_toAInfinityHom⟩
    suffices hlhs : lhs = rhs from congrArg Subtype.val hlhs
    apply (ε.strictlyUnitalHomEquiv (isDGAlgebra_trivialGrading R).strictUnit_one).injective
    apply AInfinityHom.ext
    rw [strictlyUnitalHomEquiv_apply, strictlyUnitalHomEquiv_apply, AInfinityHom.comp_assoc,
      AInfinityStrictHom.taylor_toAInfinityHom_comp, toAInfinityStrictHom_toLinearMap, hcomp_red]
    exact h

end AInfinityAlgebra.Augmentation

/-! ### DG algebra morphisms and augmented DG algebras as `A∞` data -/

namespace DGAlgHom

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B] {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

/-- A morphism of DG algebras, regarded as an `A∞` morphism, is strictly unital. -/
@[simp]
theorem isStrictlyUnital_toAInfinityHom (f : DGAlgHom hA hB) :
    f.toNonUnitalDGAlgHom.toAInfinityStrictHom.toAInfinityHom.IsStrictlyUnital
      hA.strictUnit_one hB.strictUnit_one := by
  simpa only [← DGAlgHom.toAInfinityStrictHom_toAInfinityStrictUnitalHom] using
    f.toAInfinityStrictUnitalHom.isStrictlyUnital_toAInfinityHom

end DGAlgHom

namespace DGAlgAugmentation

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}

/-- An augmentation of a DG algebra induces an augmentation of its associated `A∞` algebra. -/
noncomputable def toAInfinityAugmentation (e : DGAlgAugmentation h) :
    h.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.Augmentation where
  unit := 1
  isStrictUnit := h.strictUnit_one
  toLinearMap := e.toGradedAlgHom.toAlgHom.toLinearMap
  map_unit := map_one e
  map_of_mem_ne_zero p a ha hp := by
    have ha' : a ∈ 𝒜 p := by simpa using ha
    have he : e a ∈ trivialGrading R R p := GradedFunLike.map_mem e ha'
    rcases (mem_trivialGrading_iff R R).mp he with rfl | h0
    · exact absurd rfl hp
    · exact h0
  map_binary x y := by simp
  map_m_of_ne_two n hn hn2 x := by
    rcases n with _ | _ | _ | n
    · exact absurd hn (Nat.lt_irrefl 0)
    · simp
    · exact absurd rfl hn2
    · simp

@[simp]
theorem toAInfinityAugmentation_unit (e : DGAlgAugmentation h) :
    e.toAInfinityAugmentation.unit = 1 := (rfl)

@[simp]
theorem toAInfinityAugmentation_toLinearMap (e : DGAlgAugmentation h) :
    e.toAInfinityAugmentation.toLinearMap = e.toGradedAlgHom.toAlgHom.toLinearMap := (rfl)

/-- Evaluating the associated `A∞` augmentation agrees with evaluating the DG augmentation. -/
theorem toAInfinityAugmentation_apply (e : DGAlgAugmentation h) (a : A) :
    e.toAInfinityAugmentation a = e a := (rfl)

@[simp]
theorem toAInfinityAugmentation_toAInfinityStrictHom (e : DGAlgAugmentation h) :
    e.toAInfinityAugmentation.toAInfinityStrictHom =
      e.toNonUnitalDGAlgHom.toAInfinityStrictHom := by
  ext a
  simp

/-- The augmentation ideal of the associated `A∞` augmentation coincides with the DG augmentation
ideal. -/
theorem mem_toAInfinityAugmentation_augmentationIdeal (e : DGAlgAugmentation h) {a : A} :
    a ∈ e.toAInfinityAugmentation.augmentationIdeal ↔ a ∈ e.augmentationIdeal := by
  rw [AInfinityAlgebra.Augmentation.mem_augmentationIdeal, toAInfinityAugmentation_apply,
    mem_augmentationIdeal]

end DGAlgAugmentation

end TauCeti
