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

For an augmented `A∞` algebra `(A, ε)` with augmentation ideal `A⁺ = ker ε`, we package the
inclusion `reducedInclusion : A⁺ ⟶ A` and the augmentation itself (`toAInfinityStrictHom`,
`toAInfinityStrictUnitalHom`) as strict `A∞` morphisms.  For any `A∞` algebra `B` with a strict
unit, restriction along `A⁺ ⟶ A` gives a bijection `strictlyUnitalHomEquiv` between strictly
unital `A∞` morphisms `A ⟶ B` and nonunital `A∞` morphisms `A⁺ ⟶ B`, together with the
augmentation-preservation criterion `comp_toAInfinityStrictHom_eq_iff`.  We also convert any
DG algebra augmentation into an `A∞` augmentation (`DGAlgAugmentation.toAInfinityAugmentation`).

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
* K. Lefèvre-Hasegawa, *Sur les `A∞`-catégories*, Chapter 3.
-/

public section

open scoped TensorProduct

namespace TauCeti

open ReducedTensorWords (of ofLetter letter subword splice deconcatenation coalgHom
  degenerateWords gradedPiece map_ofLetter map_of_tprod of_tprod_eq_subword
  letter_subword_of_ne_one subword_one subword_eq_of_tprod of_tprod_congr deconcatenation_subword
  deconcatenation_ofLetter isCoalgHom_coalgHom isCoalgHom_map letter_comp_coalgHom
  degenerateWords_le_iff coalgHom_mem_degenerateWords of_tprod_mem_degenerateWords)
open InternalGrading (shift_piece)
open AInfinityHom (linearPart_apply taylor_ofTaylor taylor_comp)
open AInfinityStrictHom (taylor_toAInfinityHom taylor_toAInfinityHom_comp barMap_toAInfinityHom
  barMap_def)

universe uR uA uB uC

namespace AInfinityAlgebra.Augmentation

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒞 : AInfinityAlgebra R C}
  (ε : 𝒜.Augmentation)

/-- The inclusion of the reduced augmentation ideal as a strict `A∞` morphism `A⁺ ⟶ A`. -/
noncomputable def reducedInclusion : AInfinityStrictHom ε.reducedAlgebra 𝒜 where
  toLinearMap := ε.augmentationIdeal.subtype
  map_mem' ha := by simpa [reducedAlgebra_grading, reducedGrading_piece] using ha
  map_m' _ := by ext x; simp

@[simp] theorem reducedInclusion_toLinearMap :
    ε.reducedInclusion.toLinearMap = ε.augmentationIdeal.subtype := (rfl)

@[simp] theorem coe_reducedInclusion (x : ε.augmentationIdeal) : ε.reducedInclusion x = (x : A) :=
  (rfl)

/-- The bar differential commutes with the induced map on words of the reduced inclusion. -/
theorem barDifferential_comp_map_reducedInclusion :
    𝒜.barDifferential ∘ₗ ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype =
      ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype ∘ₗ
        ε.reducedAlgebra.barDifferential := by
  simpa [barMap_def] using ε.reducedInclusion.barDifferential_comp_barMap

/-- The augmentation of an `A∞` algebra as a strict `A∞` morphism to the ground ring. -/
noncomputable def toAInfinityStrictHom : AInfinityStrictHom 𝒜
    (isDGAlgebra_trivialGrading R).toIsNonUnitalDGAlgebra.toAInfinityAlgebra where
  toLinearMap := ε.toLinearMap
  map_mem' {p a} ha := by
    rcases eq_or_ne p 0 with rfl | hp
    exacts [by simp, by simp [ε.map_of_mem_ne_zero p a ha hp]]
  map_m'
    | 0 | _ + 3 => by ext; simp
    | 1 => by ext x; rw [show x = ![x 0] from funext fun i ↦ by fin_cases i; rfl]; simp
    | 2 => by ext x; rw [show x = ![x 0, x 1] from funext fun i ↦ by fin_cases i <;> rfl]; simp

@[simp] theorem toAInfinityStrictHom_toLinearMap :
    ε.toAInfinityStrictHom.toLinearMap = ε.toLinearMap := (rfl)

@[simp] theorem coe_toAInfinityStrictHom : ⇑ε.toAInfinityStrictHom = ε := (rfl)

/-- The augmentation of an `A∞` algebra as a strictly unital strict `A∞` morphism to `R`. -/
noncomputable def toAInfinityStrictUnitalHom :
    AInfinityStrictUnitalHom ε.isStrictUnit (isDGAlgebra_trivialGrading R).strictUnit_one where
  toAInfinityStrictHom := ε.toAInfinityStrictHom
  map_unit' := ε.map_unit

@[simp] theorem toAInfinityStrictHom_toAInfinityStrictUnitalHom :
    ε.toAInfinityStrictUnitalHom.toAInfinityStrictHom = ε.toAInfinityStrictHom := (rfl)

@[simp] theorem reducedPart_unit : ε.reducedPart ε.unit = 0 := by ext; simp [coe_reducedPart]

theorem isHomogeneous_reducedPart :
    LinearMap.IsHomogeneous ε.reducedPart 𝒜.grading.piece ε.reducedGrading.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun p a ha ↦ by
    rw [add_zero, reducedGrading_piece, Submodule.mem_comap, Submodule.subtype_apply,
      coe_reducedPart]
    rcases eq_or_ne p 0 with rfl | hp
    exacts [Submodule.sub_mem _ ha (Submodule.smul_mem _ _ ε.isStrictUnit.degree_zero),
      by rwa [ε.map_of_mem_ne_zero p a ha hp, zero_smul, sub_zero]]

private theorem linearMap_eq_of_eq_on_subtype_degenerate {N : Type*} [AddCommGroup N] [Module R N]
    {f g : ReducedTensorWords R A →ₗ[R] N}
    (hsub : f ∘ₗ ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype =
      g ∘ₗ ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype)
    (hdeg : degenerateWords R A ε.unit ≤ LinearMap.ker (f - g)) : f = g := by
  refine ReducedTensorWords.linearMap_ext R A fun n x ↦ ?_
  suffices ∀ k (y : Fin n.1 → A), (∀ j : Fin n.1, k ≤ j.1 → y j ∈ ε.augmentationIdeal) →
      f (of R A n (PiTensorProduct.tprod R y)) = g (of R A n (PiTensorProduct.tprod R y)) from
    this n.1 x fun j hj ↦ absurd hj (Nat.not_le_of_gt j.isLt)
  intro k
  induction k with
  | zero =>
    intro y hy; simpa [map_of_tprod] using LinearMap.congr_fun hsub
      (of R ε.augmentationIdeal n (PiTensorProduct.tprod R fun j ↦ ⟨y j, hy j (Nat.zero_le _)⟩))
  | succ k ih =>
    intro y hy; by_cases hk : k < n.1
    · classical
      rw [show y = Function.update y ⟨k, hk⟩ ((ε.reducedPart (y ⟨k, hk⟩) : A) +
          ε (y ⟨k, hk⟩) • ε.unit) by rw [coe_reducedPart, sub_add_cancel, Function.update_eq_self],
        (PiTensorProduct.tprod R).map_update_add, map_add, map_add, map_add]
      refine congrArg₂ (· + ·) (ih _ fun j hj ↦ ?_)
        (sub_eq_zero.mp (hdeg (ReducedTensorWords.of_tprod_mem_degenerateWords_of_eq_smul
          n _ (i := ⟨k, hk⟩) (c := ε (y ⟨k, hk⟩)) (by simp))))
      rcases eq_or_ne j ⟨k, hk⟩ with rfl | hji
      · simp
      · rw [Function.update_of_ne hji]; exact hy j (by simp [Fin.ext_iff] at hji; omega)
    · exact ih y fun j hj ↦ hy j (by omega)

private noncomputable def suspendedMul (ℬ : AInfinityAlgebra R B) : B ⊗[R] B →ₗ[R] B :=
  TensorProduct.lift (ℬ.mul.comp (ℬ.grading.koszulTwist 1))

private theorem suspendedMul_tmul (ℬ : AInfinityAlgebra R B) (x y : B) :
    suspendedMul ℬ (x ⊗ₜ[R] y) = ℬ.m 2 ![ℬ.grading.koszulTwist 1 x, y] := by simp [suspendedMul]

private theorem taylor_eq_suspendedMul_of_mem_degenerateWords {eB : B} (hB : ℬ.StrictUnit eB)
    {w : ReducedTensorWords R B} (hw : w ∈ degenerateWords R B eB) :
    ℬ.taylor w = suspendedMul ℬ
      (TensorProduct.map (letter R B) (letter R B) (deconcatenation R B w)) := by
  refine sub_eq_zero.mp ((degenerateWords_le_iff (S := LinearMap.ker (ℬ.taylor -
    suspendedMul ℬ ∘ₗ TensorProduct.map (letter R B) (letter R B) ∘ₗ deconcatenation R B)).2
    fun ⟨m, hm⟩ y hy ↦ ?_) hw)
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.comp_apply]
  rcases eq_or_ne m 2 with rfl | hm2
  · rw [show of R B ⟨2, hm⟩ (PiTensorProduct.tprod R y) =
        of R B (2 : ℕ+) (PiTensorProduct.tprod R ![y 0, y 1]) from
      congrArg _ (congrArg _ (funext fun j ↦ by fin_cases j <;> rfl)),
      ℬ.taylor_of_two, ReducedTensorWords.deconcatenation_of_two]; simp [suspendedMul_tmul]
  · rw [hB.taylor_of_tprod_eq_zero ⟨m, hm⟩ hm2 y hy, of_tprod_eq_subword R hm y,
      deconcatenation_subword, map_sum, map_sum]
    refine (Finset.sum_eq_zero fun c hc ↦ ?_).symm
    rcases Finset.mem_Ioo.1 hc with ⟨_, _⟩; rw [TensorProduct.map_tmul]
    rcases eq_or_ne c 1 with rfl | hc1
    exacts [by simp [letter_subword_of_ne_one R B y 1 (b := m - 1) (by omega)],
      by simp [letter_subword_of_ne_one R B y 0 hc1]]

private noncomputable def extendTaylor (eB : B) (g : AInfinityHom ε.reducedAlgebra ℬ) :
    ReducedTensorWords R A →ₗ[R] B :=
  g.taylor ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart +
    LinearMap.toSpanSingleton R B eB ∘ₗ ε.toLinearMap ∘ₗ letter R A

private theorem extendTaylor_ofLetter_unit (eB : B) (g : AInfinityHom ε.reducedAlgebra ℬ) :
    extendTaylor ε eB g (ofLetter R A ε.unit) = eB := by simp [extendTaylor, map_ofLetter]

private theorem extendTaylor_of_tprod_eq_zero (eB : B) (g : AInfinityHom ε.reducedAlgebra ℬ)
    (n : {n : ℕ // 0 < n}) (hn : n.1 ≠ 1) (x : Fin n.1 → A) (hx : ∃ i, x i = ε.unit) :
    extendTaylor ε eB g (of R A n (PiTensorProduct.tprod R x)) = 0 := by
  obtain ⟨i, hi⟩ := hx
  rw [extendTaylor, LinearMap.add_apply, LinearMap.comp_apply, map_of_tprod,
    (PiTensorProduct.tprod R).map_coord_zero i (by simp [hi])]
  simp [of_tprod_eq_subword R n.2 x, letter_subword_of_ne_one R A x 0 hn]

private theorem isHomogeneous_extendTaylor {eB : B} (hB : ℬ.StrictUnit eB)
    (g : AInfinityHom ε.reducedAlgebra ℬ) :
    LinearMap.IsHomogeneous (extendTaylor ε eB g)
      (gradedPiece (𝒜.grading.shift 1)) (ℬ.grading.shift 1).piece 0 := by
  have h1 := g.isHomogeneous_taylor.comp (ReducedTensorWords.isHomogeneous_map _ _
    (ε.reducedAlgebra_grading ▸
      LinearMap.isHomogeneous_shift_piece_iff.2 ε.isHomogeneous_reducedPart))
  rw [add_zero] at h1; refine h1.add (LinearMap.isHomogeneous_def.2 fun p z hz ↦ ?_)
  have hl : letter R A z ∈ 𝒜.grading.piece (p + 1) := by
    simpa [shift_piece] using (ReducedTensorWords.isHomogeneous_letter _).map_mem hz
  rcases eq_or_ne (p + 1) 0 with hp | hp
  · simpa [show p = -1 by omega] using
      ((ℬ.grading.shift 1).piece (-1)).smul_mem _ hB.mem_shift_one_piece
  · simp [ε.map_of_mem_ne_zero (p + 1) _ hl hp]

private theorem extendTaylor_comp_map_subtype (eB : B) (g : AInfinityHom ε.reducedAlgebra ℬ) :
    extendTaylor ε eB g ∘ₗ ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype =
      g.taylor := by
  rw [extendTaylor, LinearMap.add_comp, LinearMap.comp_assoc, ← ReducedTensorWords.map_comp,
    ε.reducedPart_comp_subtype, ReducedTensorWords.map_id, LinearMap.comp_id, LinearMap.comp_assoc,
    LinearMap.comp_assoc, ReducedTensorWords.letter_comp_map,
    ← LinearMap.comp_assoc (h := ε.toLinearMap), ε.toLinearMap_comp_subtype, LinearMap.zero_comp,
    LinearMap.comp_zero, add_zero]

private theorem of_tprod_one_eq_ofLetter (hn : 0 < 1) (x : Fin 1 → A) {i : Fin 1}
    (hi : x i = ε.unit) : of R A ⟨1, hn⟩ (PiTensorProduct.tprod R x) = ofLetter R A ε.unit := by
  rw [of_tprod_eq_subword R hn x, subword_one R A x Nat.one_pos, ← hi,
    Subsingleton.elim (⟨0, hn⟩ : Fin 1) i]

section DegenerateWord

/-- Total shifted degree of the prefix before index `p` (Koszul sign exponent). -/
private def prefixDeg {k : ℕ} (𝒟 : Fin (k + 2) → ℤ) (p : ℕ) : ℤ :=
  ∑ j ∈ Finset.range p, if h : j < k + 2 then 𝒟 ⟨j, h⟩ else 0

variable {eB : B} (g : AInfinityHom ε.reducedAlgebra ℬ) {k : ℕ} (x : Fin (k + 2) → A)
  {i : Fin (k + 2)}

private theorem extendTaylor_subword_eq_zero (hi : x i = ε.unit) {a b : ℕ} (hb : b ≠ 1)
    (h : a ≤ i.1 ∧ i.1 < a + b) : extendTaylor ε eB g (subword R x a b) = 0 := by
  rw [ReducedTensorWords.apply_eq_comp_letter_of_mem_degenerateWords _
    (extendTaylor_of_tprod_eq_zero ε eB g) (ReducedTensorWords.subword_mem_degenerateWords x
    ⟨i, h.1, h.2, hi⟩), letter_subword_of_ne_one R A x a hb, map_zero, map_zero]

private theorem subword_two_eq_of_tprod {m : ℕ} (hm : m + 1 < k + 2) :
    subword R x m 2 =
      of R A (2 : ℕ+) (PiTensorProduct.tprod R ![x ⟨m, by omega⟩, x ⟨m + 1, hm⟩]) := by
  rw [subword_eq_of_tprod R x two_pos (by omega)]
  exact of_tprod_congr R A two_pos rfl fun j ↦ by fin_cases j <;> simp

private theorem extendTaylor_splice_taylor_eq_zero (hi : x i = ε.unit) {p d : ℕ}
    (hnot : ¬(d = 2 ∧ ((p = i.1 ∧ i.1 < k + 1) ∨ (p + 1 = i.1 ∧ 0 < i.1)))) :
    extendTaylor ε eB g (splice R x 0 (k + 2) p d (𝒜.taylor (subword R x p d))) = 0 := by
  by_cases hfit : 0 < d ∧ p + d ≤ k + 2
  · by_cases hblock : p ≤ i.1 ∧ i.1 < p + d
    · rw [subword_eq_of_tprod R x hfit.1 hfit.2, ε.isStrictUnit.taylor_of_tprod_eq_zero ⟨d, hfit.1⟩
        (fun hd ↦ hnot ⟨hd, by dsimp only at hd; omega⟩) _ ⟨⟨i.1 - p, by dsimp only; omega⟩,
          by rw [← hi]; exact congrArg x (Fin.ext (by simp; omega))⟩,
        ReducedTensorWords.splice_zero, map_zero]
    · obtain ⟨y, ⟨j, hj⟩, hy⟩ := ReducedTensorWords.exists_splice_eq_of_tprod R x hfit.2 _ hblock
      rw [hy]; exact extendTaylor_of_tprod_eq_zero ε eB g ⟨k + 2 + 1 - d, by omega⟩
        (by dsimp only; have := i.isLt; by_cases hp : p ≤ i.1 <;> omega) y ⟨j, hj.trans hi⟩
  · rw [ReducedTensorWords.splice_eq_zero_of_not_fits R _ _ hfit, map_zero]

private theorem extendTaylor_splice_two_unit_right (𝒟 : Fin (k + 2) → ℤ)
    (hx : ∀ j, x j ∈ (𝒜.grading.shift 1).piece (𝒟 j)) {m : ℕ} (hm : m + 1 < k + 2)
    (hxi : x ⟨m + 1, hm⟩ = ε.unit) :
    (((prefixDeg 𝒟 m).negOnePow : ℤ) : R) •
        extendTaylor ε eB g (splice R x 0 (k + 2) m 2 (𝒜.taylor (subword R x m 2))) =
      ((((prefixDeg 𝒟 (m + 1)) + 1).negOnePow : ℤ) : R) •
        extendTaylor ε eB g (splice R x 0 (k + 2) m 2 (x ⟨m, by omega⟩)) := by
  rw [subword_two_eq_of_tprod x hm, hxi, ε.isStrictUnit.taylor_of_two_unit_right,
    𝒜.grading.koszulTwist_apply_of_mem (by simpa only [shift_piece] using hx ⟨m, by omega⟩) 1,
    ReducedTensorWords.splice_smul, map_smul, smul_smul]; congr 1
  rw [prefixDeg, prefixDeg, one_mul, Finset.sum_range_succ, dite_eq_left (by omega : m < k + 2),
    ← Int.cast_mul, ← Units.val_mul, ← Int.negOnePow_add, add_assoc]

private theorem suspendedMul_extendTaylor_deconcat_eq_zero (hi : x i = ε.unit) {c : ℕ}
    (hc : c ∈ Finset.Ioo 0 (k + 2))
    (hne : ¬((c = 1 ∧ i.1 = 0) ∨ (c = k + 1 ∧ i.1 = k + 1))) :
    suspendedMul ℬ (extendTaylor ε eB g (subword R x 0 c) ⊗ₜ[R]
      extendTaylor ε eB g (subword R x c (k + 2 - c))) = 0 := by
  rcases Finset.mem_Ioo.1 hc with ⟨_, _⟩; have := i.isLt
  by_cases hic : i.1 < c
  · simp [extendTaylor_subword_eq_zero ε g x hi (a := 0) (b := c)
      (fun h ↦ hne (Or.inl ⟨h, by omega⟩)) ⟨by omega, by omega⟩]
  · simp [extendTaylor_subword_eq_zero ε g x hi (a := c) (b := k + 2 - c)
      (fun h ↦ hne (Or.inr ⟨by omega, by omega⟩)) ⟨by omega, by omega⟩]

private theorem extendTaylor_component_eq_on_degenerate_add_two (hB : ℬ.StrictUnit eB)
    (𝒟 : Fin (k + 2) → ℤ) (hx : ∀ j, x j ∈ (𝒜.grading.shift 1).piece (𝒟 j)) (hi : x i = ε.unit) :
    suspendedMul ℬ (TensorProduct.map (extendTaylor ε eB g) (extendTaylor ε eB g)
        (deconcatenation R A (of R A ⟨k + 2, by omega⟩ (PiTensorProduct.tprod R x)))) =
      extendTaylor ε eB g
        (𝒜.barDifferential (of R A ⟨k + 2, by omega⟩ (PiTensorProduct.tprod R x))) := by
  let F := extendTaylor ε eB g
  let term (p d : ℕ) := (((prefixDeg 𝒟 p).negOnePow : ℤ) : R) •
    F (splice R x 0 (k + 2) p d (𝒜.taylor (subword R x p d)))
  have hxeq {j : Fin (k + 2)} (hj : i.1 = j.1) : x j = ε.unit := hi ▸ congrArg x (Fin.ext hj.symm)
  rw [of_tprod_eq_subword R (by omega : 0 < k + 2) x, deconcatenation_subword, map_sum, map_sum,
    ← of_tprod_eq_subword R (by omega : 0 < k + 2) x, 𝒜.barDifferential_def,
    ReducedTensorWords.gradedCoderiv_of_tprod_of_homogeneous _ _ 1 (by omega) x 𝒟 hx, map_sum]
  simp only [Nat.zero_add, one_mul, TensorProduct.map_tmul, map_sum, map_smul]
  have hinner (p : ℕ) : ∑ d ∈ Finset.range (k + 3), term p d = term p 2 :=
    Finset.sum_eq_single_of_mem 2 (by simp) fun d _ hd2 ↦ by
      dsimp only [term, F]; rw [extendTaylor_splice_taylor_eq_zero ε g x hi (by omega), smul_zero]
  have hzero (p : ℕ) (hp : ¬((p = i.1 ∧ i.1 < k + 1) ∨ (p + 1 = i.1 ∧ 0 < i.1))) :
      ∑ d ∈ Finset.range (k + 3), term p d = 0 := Finset.sum_eq_zero fun d _ ↦ by
    dsimp only [term, F]; rw [extendTaylor_splice_taylor_eq_zero ε g x hi (by tauto), smul_zero]
  change _ = ∑ p ∈ Finset.range (k + 2), ∑ d ∈ Finset.range (k + 3), term p d
  rcases eq_or_ne i.1 0 with hi0 | hi0
  · -- Unit at `0`: only cut `c = 1` and splice `(0, 2)` survive, via `binary_left`.
    rw [Finset.sum_eq_single_of_mem 1 (by simp)
        (fun c hc hc1 ↦ suspendedMul_extendTaylor_deconcat_eq_zero ε g x hi hc (by omega)),
      Finset.sum_eq_single_of_mem 0 (by simp) (fun p _ hp0 ↦ hzero p (by omega)),
      hinner 0, subword_one R A x (by omega), hxeq hi0, extendTaylor_ofLetter_unit,
      suspendedMul_tmul, ℬ.grading.koszulTwist_apply_of_mem_zero hB.degree_zero, hB.binary_left]
    dsimp only [term, F]; rw [subword_two_eq_of_tprod x (by omega), hxeq hi0,
      ε.isStrictUnit.taylor_of_two_unit_left,
      ReducedTensorWords.splice_two_succ_eq_subword R (by omega) rfl x]; simp [prefixDeg]
  · rcases eq_or_ne i.1 (k + 1) with hil | hil
    · -- Unit at `k + 1`: only cut `k + 1` and splice `(k, 2)` survive, via `binary_right`.
      rw [Finset.sum_eq_single_of_mem (k + 1) (by simp)
          (fun c hc hcl ↦ suspendedMul_extendTaylor_deconcat_eq_zero ε g x hi hc (by omega)),
        Finset.sum_eq_single_of_mem k (by simp) (fun p _ hpk ↦ hzero p (by omega)),
        hinner k, show k + 2 - (k + 1) = 1 by omega, subword_one R A x (by omega), hxeq hil,
        extendTaylor_ofLetter_unit, suspendedMul_tmul, hB.binary_right]
      dsimp only [term, F]; rw [extendTaylor_splice_two_unit_right ε g x 𝒟 hx (by omega) (hxeq hil),
        ReducedTensorWords.splice_two_pred_eq_subword R rfl x]
      have htmem : F (subword R x 0 (k + 1)) ∈ ℬ.grading.piece (prefixDeg 𝒟 (k + 1) + 1) := by
        simpa [shift_piece, Nat.zero_add, prefixDeg] using
          (isHomogeneous_extendTaylor ε hB g).map_mem (ReducedTensorWords.subword_mem_gradedPiece
            (G := 𝒜.grading.shift 1) x (fun j ↦ if h : j < k + 2 then 𝒟 ⟨j, h⟩ else 0)
            (fun j ↦ by simpa only [dite_eq_left j.isLt] using hx j) 0 (k + 1))
      rw [ℬ.grading.koszulTwist_apply_of_mem htmem 1, one_mul]
    · -- Interior unit (`m + 1`): LHS vanishes; splices `(m, 2)` and `(m + 1, 2)` cancel.
      have := i.isLt; obtain ⟨m, hm⟩ : ∃ m, i.1 = m + 1 := ⟨i.1 - 1, by omega⟩
      rw [Finset.sum_eq_zero fun c hc ↦
          suspendedMul_extendTaylor_deconcat_eq_zero ε g x hi hc (by omega),
        Finset.sum_eq_add m (m + 1) (by omega) (fun p _ hp ↦ hzero p (by omega))
          (fun h ↦ by simp at h; omega) (fun h ↦ by simp at h; omega),
        hinner m, hinner (m + 1)]
      dsimp only [term, F]; rw [extendTaylor_splice_two_unit_right ε g x 𝒟 hx (by omega) (hxeq hm),
        subword_two_eq_of_tprod x (by omega), hxeq (j := ⟨m + 1, by omega⟩) hm,
        ε.isStrictUnit.taylor_of_two_unit_left,
        ReducedTensorWords.splice_two_succ_eq_splice_two_pred R (by omega) (by omega) x]
      simp [Int.negOnePow_succ]

end DegenerateWord

private theorem extendTaylor_component_eq {eB : B} (hB : ℬ.StrictUnit eB)
    (g : AInfinityHom ε.reducedAlgebra ℬ) :
    ℬ.taylor ∘ₗ coalgHom R (extendTaylor ε eB g) = extendTaylor ε eB g ∘ₗ 𝒜.barDifferential := by
  refine linearMap_eq_of_eq_on_subtype_degenerate ε ?_ ?_
  · have hcoalg : coalgHom R (extendTaylor ε eB g) ∘ₗ
        ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype = g.barMap :=
      ((isCoalgHom_coalgHom _).comp (isCoalgHom_map _)).eq_of_letter_comp_eq g.isCoalgHom_barMap <|
        by rw [← LinearMap.comp_assoc, letter_comp_coalgHom, extendTaylor_comp_map_subtype,
          g.taylor_def]
    rw [LinearMap.comp_assoc, hcoalg, g.taylor_comp_barMap, LinearMap.comp_assoc,
      ε.barDifferential_comp_map_reducedInclusion, ← LinearMap.comp_assoc,
      extendTaylor_comp_map_subtype]
  · rw [ReducedTensorWords.degenerateWords_le_iff_of_mem_piece (𝒜.grading.shift 1)
      ε.isStrictUnit.mem_shift_one_piece]
    rintro ⟨n, hn⟩ x 𝒟 i hx hi _
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.comp_apply]
    rw [taylor_eq_suspendedMul_of_mem_degenerateWords hB (coalgHom_mem_degenerateWords _
          (extendTaylor_ofLetter_unit ε eB g) (extendTaylor_of_tprod_eq_zero ε eB g)
          (of_tprod_mem_degenerateWords ⟨n, hn⟩ x ⟨i, hi⟩)),
      (isCoalgHom_coalgHom _).deconcatenation_apply, ← LinearMap.comp_apply (TensorProduct.map _ _),
      ← TensorProduct.map_comp, letter_comp_coalgHom]
    match n with
    | 0 => omega
    | 1 => rw [of_tprod_one_eq_ofLetter ε hn x hi]
           simp [𝒜.barDifferential_ofLetter, ε.isStrictUnit.unary_eq_zero]
    | _ + 2 => exact extendTaylor_component_eq_on_degenerate_add_two ε g x hB 𝒟 hx hi

/-- Strictly unital `A∞` morphisms `A ⟶ B` correspond to nonunital `A∞` morphisms `A⁺ ⟶ B`. -/
noncomputable def strictlyUnitalHomEquiv {eB : B} (hB : ℬ.StrictUnit eB) :
    {f : AInfinityHom 𝒜 ℬ // f.IsStrictlyUnital ε.isStrictUnit hB} ≃
      AInfinityHom ε.reducedAlgebra ℬ where
  toFun f := f.1.comp ε.reducedInclusion.toAInfinityHom
  invFun g := ⟨AInfinityHom.ofTaylor (extendTaylor ε eB g) (isHomogeneous_extendTaylor ε hB g)
      (extendTaylor_component_eq ε hB g),
    ⟨by rw [linearPart_apply, taylor_ofTaylor, extendTaylor_ofLetter_unit],
      fun {n} hn x ⟨i, hi⟩ ↦ by
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        exacts [by simp, by
          rw [AInfinityHom.component_apply _ n hpos, taylor_ofTaylor]
          exact extendTaylor_of_tprod_eq_zero ε eB g ⟨n, hpos⟩ hn _
            ⟨i, by rw [hi, 𝒜.grading.koszulTwist_apply_of_mem_zero ε.isStrictUnit.degree_zero]⟩]⟩⟩
  left_inv f := Subtype.ext <| AInfinityHom.ext <| by
    rw [taylor_ofTaylor]
    refine linearMap_eq_of_eq_on_subtype_degenerate ε (by
        simp [extendTaylor_comp_map_subtype, taylor_comp, barMap_toAInfinityHom, barMap_def])
      (degenerateWords_le_iff.2 fun ⟨n, hn⟩ x hx ↦ ?_)
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    rcases eq_or_ne n 1 with rfl | hn1
    · obtain ⟨_, hi⟩ := hx; rw [of_tprod_one_eq_ofLetter ε hn x hi, extendTaylor_ofLetter_unit,
        ← linearPart_apply, f.2.map_unit]
    · rw [extendTaylor_of_tprod_eq_zero ε eB _ ⟨n, hn⟩ hn1 x hx,
        f.2.taylor_of_tprod_eq_zero ⟨n, hn⟩ hn1 x hx]
  right_inv g := AInfinityHom.ext <| by
    simp [taylor_comp, barMap_toAInfinityHom, barMap_def, extendTaylor_comp_map_subtype]

@[simp] theorem strictlyUnitalHomEquiv_apply {eB : B} (hB : ℬ.StrictUnit eB)
    (f : {f : AInfinityHom 𝒜 ℬ // f.IsStrictlyUnital ε.isStrictUnit hB}) :
    ε.strictlyUnitalHomEquiv hB f = f.1.comp ε.reducedInclusion.toAInfinityHom := (rfl)

@[simp] theorem taylor_strictlyUnitalHomEquiv_symm {eB : B} (hB : ℬ.StrictUnit eB)
    (g : AInfinityHom ε.reducedAlgebra ℬ) :
    ((ε.strictlyUnitalHomEquiv hB).symm g).1.taylor =
      g.taylor ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart +
        LinearMap.toSpanSingleton R B eB ∘ₗ ε.toLinearMap ∘ₗ letter R A := by
  simp [strictlyUnitalHomEquiv, extendTaylor]

theorem linearPart_strictlyUnitalHomEquiv_symm_coe {eB : B} (hB : ℬ.StrictUnit eB)
    (g : AInfinityHom ε.reducedAlgebra ℬ) (x : ε.augmentationIdeal) :
    ((ε.strictlyUnitalHomEquiv hB).symm g).1.linearPart x = g.linearPart x := by
  simp [linearPart_apply, map_ofLetter, ε.mem_augmentationIdeal.mp x.2]

theorem linearPart_strictlyUnitalHomEquiv_symm_unit {eB : B} (hB : ℬ.StrictUnit eB)
    (g : AInfinityHom ε.reducedAlgebra ℬ) :
    ((ε.strictlyUnitalHomEquiv hB).symm g).1.linearPart ε.unit = eB :=
  ((ε.strictlyUnitalHomEquiv hB).symm g).2.map_unit

theorem strictlyUnitalHomEquiv_symm_comp_strict {eB : B} {eC : C} (hB : ℬ.StrictUnit eB)
    (hC : 𝒞.StrictUnit eC) (φ : AInfinityStrictUnitalHom hB hC)
    (g : AInfinityHom ε.reducedAlgebra ℬ) :
    ((ε.strictlyUnitalHomEquiv hC).symm (φ.toAInfinityStrictHom.toAInfinityHom.comp g)).1 =
      φ.toAInfinityStrictHom.toAInfinityHom.comp ((ε.strictlyUnitalHomEquiv hB).symm g).1 :=
  AInfinityHom.ext <| LinearMap.ext fun _ ↦ by
    rw [taylor_toAInfinityHom_comp, taylor_strictlyUnitalHomEquiv_symm,
      taylor_strictlyUnitalHomEquiv_symm, taylor_toAInfinityHom_comp]
    simp [AInfinityStrictHom.coe_toLinearMap, φ.map_unit']

/-- A strictly unital morphism preserves augmentations iff its restriction vanishes under `εB`. -/
theorem comp_toAInfinityStrictHom_eq_iff (εB : ℬ.Augmentation)
    (f : {f : AInfinityHom 𝒜 ℬ // f.IsStrictlyUnital ε.isStrictUnit εB.isStrictUnit}) :
    εB.toAInfinityStrictHom.toAInfinityHom.comp f.1 = ε.toAInfinityStrictHom.toAInfinityHom ↔
      εB.toLinearMap ∘ₗ (ε.strictlyUnitalHomEquiv εB.isStrictUnit f).taylor = 0 := by
  have hcomp_red : (ε.toAInfinityStrictHom.toAInfinityHom.comp
      ε.reducedInclusion.toAInfinityHom).taylor = 0 := by
    rw [taylor_toAInfinityHom_comp, taylor_toAInfinityHom]
    simp [← LinearMap.comp_assoc, ε.toLinearMap_comp_subtype]
  refine ⟨fun h ↦ by
      have h' := congrArg (fun k ↦ (k.comp ε.reducedInclusion.toAInfinityHom).taylor) h
      rwa [AInfinityHom.comp_assoc, taylor_toAInfinityHom_comp, toAInfinityStrictHom_toLinearMap,
        hcomp_red] at h',
    fun h ↦ congrArg Subtype.val <|
      (ε.strictlyUnitalHomEquiv (isDGAlgebra_trivialGrading R).strictUnit_one).injective
        (a₁ := ⟨εB.toAInfinityStrictHom.toAInfinityHom.comp f.1,
          εB.toAInfinityStrictUnitalHom.isStrictlyUnital_toAInfinityHom.comp f.2⟩)
        (a₂ := ⟨ε.toAInfinityStrictHom.toAInfinityHom,
          ε.toAInfinityStrictUnitalHom.isStrictlyUnital_toAInfinityHom⟩) <|
      AInfinityHom.ext <| by rwa [strictlyUnitalHomEquiv_apply, strictlyUnitalHomEquiv_apply,
        AInfinityHom.comp_assoc, taylor_toAInfinityHom_comp, toAInfinityStrictHom_toLinearMap,
        hcomp_red]⟩

end AInfinityAlgebra.Augmentation

namespace DGAlgAugmentation

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  (e : DGAlgAugmentation h)

/-- An augmentation of a DG algebra induces an augmentation of its associated `A∞` algebra. -/
noncomputable def toAInfinityAugmentation :
    h.toIsNonUnitalDGAlgebra.toAInfinityAlgebra.Augmentation where
  unit := 1; isStrictUnit := h.strictUnit_one
  toLinearMap := e.toGradedAlgHom.toAlgHom.toLinearMap; map_unit := map_one e
  map_of_mem_ne_zero _ _ ha hp := e.map_eq_zero_of_mem_ne_zero (by simpa using ha) hp
  map_binary _ _ := by simp
  map_m_of_ne_two n _ _ _ := by rcases n with _ | _ | _ | _ <;> [omega; simp; contradiction; simp]

@[simp] theorem toAInfinityAugmentation_unit : e.toAInfinityAugmentation.unit = 1 := (rfl)

@[simp] theorem toAInfinityAugmentation_toLinearMap :
    e.toAInfinityAugmentation.toLinearMap = e.toGradedAlgHom.toAlgHom.toLinearMap := (rfl)

theorem toAInfinityAugmentation_apply (a : A) : e.toAInfinityAugmentation a = e a := (rfl)

@[simp] theorem toAInfinityAugmentation_toAInfinityStrictHom :
    e.toAInfinityAugmentation.toAInfinityStrictHom = e.toNonUnitalDGAlgHom.toAInfinityStrictHom :=
  by ext a; simp

theorem mem_toAInfinityAugmentation_augmentationIdeal {a : A} :
    a ∈ e.toAInfinityAugmentation.augmentationIdeal ↔ a ∈ e.augmentationIdeal := by simp

end DGAlgAugmentation

end TauCeti
