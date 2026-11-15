/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Augmented
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Unital

/-!
# Lifting `A∞` morphisms along augmentation splittings

Given augmented `A∞` algebras `(A, ε_A)` and `(B, ε_B)`, restricting a strictly unital augmented
`A∞` morphism `f : A ⟶ B` to the augmentation ideals produces a nonunital `A∞` morphism
`f_red : ker ε_A ⟶ ker ε_B` (`TauCeti.AInfinityHom.IsAugmented.reducedHom`).

Conversely, any `A∞` morphism `g : ker ε_A ⟶ ker ε_B` extends along the canonical splittings
`A ≅ R ⊕ ker ε_A` and `B ≅ R ⊕ ker ε_B` to a strictly unital augmented `A∞` morphism `A ⟶ B`
(`TauCeti.AInfinityAlgebra.Augmentation.liftHom`), whose suspended Taylor map adds the scalar
augmentation functional `ε_B.unitHom ∘ ε_A ∘ letter` on length-one words to `g.taylor` on reduced
bar projections.  These two operations are mutually inverse, establishing a canonical bijection
between strictly unital augmented `A∞` morphisms `A ⟶ B` and arbitrary `A∞` morphisms
`ker ε_A ⟶ ker ε_B` (`TauCeti.AInfinityAlgebra.Augmentation.strictlyUnitalAugmentedHomEquiv`).

## Main definitions

* `TauCeti.AInfinityAlgebra.Augmentation.liftHom`: the strictly unital augmented extension `A ⟶ B`
  of an `A∞` morphism `ker ε_A ⟶ ker ε_B`.
* `TauCeti.AInfinityAlgebra.Augmentation.strictlyUnitalAugmentedHomEquiv`: the bijection between
  strictly unital augmented `A∞` morphisms `A ⟶ B` and `A∞` morphisms `ker ε_A ⟶ ker ε_B`.

## Main results

* `TauCeti.AInfinityAlgebra.Augmentation.isStrictlyUnital_liftHom` and
  `TauCeti.AInfinityAlgebra.Augmentation.isAugmented_liftHom`: `liftHom` is strictly unital and
  augmented.
* `TauCeti.AInfinityAlgebra.Augmentation.reducedHom_liftHom` and
  `TauCeti.AInfinityAlgebra.Augmentation.liftHom_reducedHom`: `reducedHom` and `liftHom` are
  mutually inverse.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
* B. Keller, *A-infinity algebras, modules and functor categories*, Contemporary Mathematics 406
  (2006), Section 4.
-/

public section

open TensorProduct

namespace TauCeti

universe uR uA uB

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}

namespace AInfinityAlgebra.Augmentation

open ReducedTensorWords

private theorem of_tprod_sub_of_tprod_reducedPart_mem_degenerateWords (εA : AA.Augmentation)
    (n : {k : ℕ // 0 < k}) (x : Fin n.1 → A) :
    of R A n (PiTensorProduct.tprod R x) -
      of R A n (PiTensorProduct.tprod R
        (fun i ↦ (εA.augmentationIdeal.subtype ∘ₗ εA.reducedPart) (x i))) ∈
      degenerateWords R A εA.unit := by
  set ρ := εA.augmentationIdeal.subtype ∘ₗ εA.reducedPart
  let w : ℕ → Fin n.1 → A := fun k i ↦ if i.1 < k then ρ (x i) else x i
  suffices hk : ∀ k ≤ n.1,
      of R A n (PiTensorProduct.tprod R x) - of R A n (PiTensorProduct.tprod R (w k)) ∈
        degenerateWords R A εA.unit by
    simpa [w, Fin.isLt] using hk n.1 le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    simp [w]
  | succ k ih =>
    intro hk
    have hupd : w k = Function.update (w (k + 1)) ⟨k, hk⟩
        (εA (x ⟨k, hk⟩) • εA.unit + w (k + 1) ⟨k, hk⟩) := by
      ext i
      by_cases hik : i = ⟨k, hk⟩
      · subst hik
        simp [w, ρ]
      · have hik' : i.1 ≠ k := Fin.val_ne_of_ne hik
        have hiff : i.1 < k ↔ i.1 < k + 1 := by omega
        simp [w, hik, hiff]
    rw [← sub_add_sub_cancel (of R A n (PiTensorProduct.tprod R x))
      (of R A n (PiTensorProduct.tprod R (w k)))]
    refine Submodule.add_mem _ (ih (by omega)) ?_
    rw [hupd, (PiTensorProduct.tprod R).map_update_add, Function.update_eq_self, map_add,
      add_sub_cancel_right]
    exact of_tprod_mem_degenerateWords_of_eq_smul n _ (i := ⟨k, hk⟩)
      (c := εA (x ⟨k, hk⟩)) (by simp)

/-- Every bar word differs from its letterwise projection onto `ker ε` by a degenerate word
containing `ε.unit`. -/
private theorem sub_map_reducedPart_mem_degenerateWords (εA : AA.Augmentation)
    (z : ReducedTensorWords R A) :
    z - ReducedTensorWords.map (R := R) (εA.augmentationIdeal.subtype ∘ₗ εA.reducedPart) z ∈
      degenerateWords R A εA.unit := by
  set ρ := εA.augmentationIdeal.subtype ∘ₗ εA.reducedPart
  suffices hle : (⊤ : Submodule R (ReducedTensorWords R A)) ≤
      (degenerateWords R A εA.unit).comap
        (LinearMap.id - ReducedTensorWords.map (R := R) ρ) from
    hle Submodule.mem_top
  rw [← iSup_range_of R A, iSup_le_iff]
  intro n
  rintro _ ⟨t, rfl⟩
  induction t using PiTensorProduct.induction_on with
  | add u v hu hv =>
    rw [map_add]
    exact Submodule.add_mem _ hu hv
  | smul_tprod c x =>
    rw [map_smul]
    refine Submodule.smul_mem _ c ?_
    rw [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, map_of_tprod]
    exact of_tprod_sub_of_tprod_reducedPart_mem_degenerateWords εA n x

/-- On degenerate words for a strict unit `e_B`, the suspended Taylor map `BB.taylor` reads only
the two-letter cut via `BB.mul` and the degree-one Koszul twist. -/
private theorem taylor_eq_of_mem_degenerateWords {eB : B} (hB : BB.StrictUnit eB)
    {u : ReducedTensorWords R B} (hu : u ∈ degenerateWords R B eB) :
    BB.taylor u =
      TensorProduct.lift BB.mul
        (TensorProduct.map (BB.grading.koszulTwist 1 ∘ₗ letter R B) (letter R B)
          (deconcatenation R B u)) := by
  let rhs : ReducedTensorWords R B →ₗ[R] B :=
    TensorProduct.lift BB.mul ∘ₗ
      TensorProduct.map (BB.grading.koszulTwist 1 ∘ₗ letter R B) (letter R B) ∘ₗ
        deconcatenation R B
  suffices hle : degenerateWords R B eB ≤ LinearMap.ker (BB.taylor - rhs) by
    exact sub_eq_zero.1 (hle hu)
  rw [degenerateWords_le_iff]
  rintro ⟨m, hm⟩ y ⟨i, hi⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rcases lt_trichotomy m 2 with hm1 | rfl | hm3
  · have hm' : m = 1 := by omega
    subst hm'
    have hi0 : i = ⟨0, hm⟩ := Subsingleton.elim _ _
    rw [of_tprod_eq_subword R hm, subword_one R B y hm, ← hi0, hi, BB.taylor_ofLetter,
      hB.unary_eq_zero]
    simp [rhs]
  · have hw : of R B ⟨2, hm⟩ (PiTensorProduct.tprod R y) =
        of R B (2 : ℕ+) (PiTensorProduct.tprod R ![y ⟨0, by simp⟩, y ⟨0 + 1, by simp⟩]) :=
      (of_tprod_eq_subword R hm y).trans (subword_two_eq R y (by simp))
    rw [hw]
    simp [rhs, BB.taylor_of_two, deconcatenation_of_two]
  · rw [hB.taylor_of_tprod_eq_zero ⟨m, hm⟩ (by simp; omega) y ⟨i, hi⟩]
    simp only [rhs, LinearMap.comp_apply]
    rw [of_tprod_eq_subword R hm, deconcatenation_subword, map_sum, map_sum, eq_comm]
    refine Finset.sum_eq_zero fun c hc ↦ ?_
    rw [Finset.mem_Ioo] at hc
    rw [TensorProduct.map_tmul]
    by_cases hc1 : c = 1
    · rw [letter_subword_of_ne_one R B y (0 + c) (by omega), TensorProduct.tmul_zero, map_zero]
    · rw [LinearMap.comp_apply, letter_subword_of_ne_one R B y 0 hc1, map_zero,
        TensorProduct.zero_tmul, map_zero]

/-- Evaluating `BB.taylor ∘ coalgHom R F` on a word with the source unit at position `j` leaves
only the boundary collapses at `j = 0` or `j = n`. -/
private theorem taylor_coalgHom_of_tprod_eq_unit {eA : A} {eB : B}
    (hB : BB.StrictUnit eB) {F : ReducedTensorWords R A →ₗ[R] B}
    (he : F (ofLetter R A eA) = eB)
    (hF : ∀ (m : {k : ℕ // 0 < k}), m.1 ≠ 1 → ∀ y : Fin m.1 → A,
      (∃ i, y i = eA) → F (of R A m (PiTensorProduct.tprod R y)) = 0)
    {n : ℕ} (x : Fin (n + 1) → A) (j : Fin (n + 1)) (hj : x j = eA) :
    BB.taylor (coalgHom R F (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x))) =
      (if j.1 = 0 ∧ 0 < n then F (subword R x 1 n) else 0) +
        (if j.1 = n ∧ 0 < n then BB.grading.koszulTwist 1 (F (subword R x 0 n)) else 0) := by
  have hdeg := coalgHom_mem_degenerateWords F he hF
    (of_tprod_mem_degenerateWords (R := R) ⟨n + 1, n.succ_pos⟩ x ⟨j, hj⟩)
  have hc := LinearMap.congr_fun (isCoalgHom_iff.1 (isCoalgHom_coalgHom F))
    (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x))
  simp only [LinearMap.comp_apply] at hc
  rw [taylor_eq_of_mem_degenerateWords hB hdeg, hc, TensorProduct.map_map,
    LinearMap.comp_assoc, letter_comp_coalgHom, of_tprod_eq_subword R n.succ_pos,
    deconcatenation_subword, map_sum, map_sum]
  have hvanish (a c) (hc : 1 < c) (_ : a + c ≤ n + 1) (haj : a ≤ j.1) (hjc : j.1 < a + c) :
      F (subword R x a c) = 0 := by
    rw [apply_eq_comp_letter_of_mem_degenerateWords F hF
      (subword_mem_degenerateWords x ⟨j, haj, hjc, hj⟩),
      letter_subword_of_ne_one R A x a (by omega), map_zero, map_zero]
  have hterm : ∀ c ∈ Finset.Ioo 0 (n + 1),
      TensorProduct.lift BB.mul
          (TensorProduct.map (BB.grading.koszulTwist 1 ∘ₗ F) F
            (subword R x 0 c ⊗ₜ[R] subword R x (0 + c) (n + 1 - c))) =
        (if c = 1 ∧ (j.1 = 0 ∧ 0 < n) then F (subword R x 1 n) else 0) +
        (if c = n ∧ (j.1 = n ∧ 0 < n) then
          BB.grading.koszulTwist 1 (F (subword R x 0 n)) else 0) := by
    intro c hc
    rw [Finset.mem_Ioo] at hc
    have hjn := j.isLt
    simp only [TensorProduct.map_tmul, TensorProduct.lift.tmul, LinearMap.comp_apply,
      AInfinityAlgebra.mul_apply, zero_add]
    by_cases hjc : j.1 < c
    · by_cases hc1 : c = 1
      · subst hc1
        have hj0 : (⟨0, n.succ_pos⟩ : Fin (n + 1)) = j := Fin.ext (by simp; omega)
        simp (disch := omega) only [true_and, ite_eq_left, ite_eq_right, add_zero]
        rw [subword_one R A x n.succ_pos, hj0, hj, he,
          BB.grading.koszulTwist_apply_of_mem_zero hB.degree_zero, hB.binary_left]
        exact congrArg (fun k ↦ F (subword R x 1 k)) (by omega)
      · rw [hvanish 0 c (by omega) (by omega) (by omega) (by omega), map_zero, BB.m_two_zero_left]
        simp (disch := omega) only [ite_eq_right, add_zero]
    · by_cases hcn : c = n
      · subst hcn
        have hjn' : (⟨c, by omega⟩ : Fin (c + 1)) = j := Fin.ext (by simp; omega)
        have hlen : c + 1 - c = 1 := by omega
        simp (disch := omega) only [true_and, ite_eq_right, ite_eq_left, zero_add]
        rw [hlen, subword_one R A x (by omega), hjn', hj, he, hB.binary_right]
      · rw [hvanish c (n + 1 - c) (by omega) (by omega) (by omega) (by omega),
          BB.m_two_zero_right]
        simp (disch := omega) only [ite_eq_right, add_zero]
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq', Finset.mem_Ioo]
  congr 1 <;> split_ifs <;> first | rfl | omega

/-- Each `(p, d)` summand of `G (AA.barDifferential ...)` for a linear map `G` vanishing on
degenerate words is supported on the two length-two collapses around `e_A`. -/
private theorem sign_smul_apply_splice_taylor {M : Type*} [AddCommGroup M] [Module R M]
    {eA : A} (hA : AA.StrictUnit eA) {G : ReducedTensorWords R A →ₗ[R] M}
    (hGe : degenerateWords R A eA ≤ LinearMap.ker G) {n : ℕ} (x : Fin (n + 1) → A)
    (𝒟 : Fin (n + 1) → ℤ)
    (hx : ∀ i, x i ∈ (AA.grading.shift 1).piece (𝒟 i)) (j : Fin (n + 1))
    (hj : x j = eA) (p : ℕ) (hp : p ∈ Finset.range (n + 1)) (d : ℕ)
    (hd : d ∈ Finset.range (n + 1 + 1)) :
    (((∑ i ∈ Finset.range p,
          if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0).negOnePow : ℤ) : R) •
        G (splice R x 0 (n + 1) p d (AA.taylor (subword R x p d))) =
      (if p = j.1 ∧ d = 2 ∧ j.1 + 1 ≤ n then
        negOnePowCast R
            (∑ i ∈ Finset.range j.1, if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0) •
          G (splice R x 0 (n + 1) j.1 2
            (if h : j.1 + 1 < n + 1 then x ⟨j.1 + 1, h⟩ else 0)) else 0) +
      (if p = j.1 - 1 ∧ d = 2 ∧ 1 ≤ j.1 then
        negOnePowCast R
            (∑ i ∈ Finset.range (j.1 - 1), if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0) •
          negOnePowCast R (𝒟 ⟨j.1 - 1, by omega⟩ + 1) •
          G (splice R x 0 (n + 1) (j.1 - 1) 2 (x ⟨j.1 - 1, by omega⟩)) else 0) := by
  have hjn := j.isLt
  rw [Finset.mem_range] at hp hd
  by_cases hfit : 0 < d ∧ p + d ≤ n + 1
  swap
  · simp (disch := omega) only [splice_eq_zero_of_not_fits R _ _ hfit, map_zero, smul_zero,
      ite_eq_right, add_zero]
  by_cases hblock : p ≤ j.1 ∧ j.1 < p + d
  swap
  · obtain ⟨y, ⟨k, hk⟩, hy⟩ := exists_splice_eq_of_tprod R x hfit.2
      (AA.taylor (subword R x p d)) hblock
    simp (disch := omega) only [hy,
      LinearMap.mem_ker.mp
        (hGe (of_tprod_mem_degenerateWords ⟨n + 1 + 1 - d, by omega⟩ y ⟨k, hk.trans hj⟩)),
      smul_zero, ite_eq_right, add_zero]
  by_cases hd2 : d = 2
  swap
  · have hzero : AA.taylor (subword R x p d) = 0 := by
      rw [subword_eq_of_tprod R x hfit.1 hfit.2]
      exact hA.taylor_of_tprod_eq_zero ⟨d, hfit.1⟩ hd2 _
        ⟨⟨j.1 - p, by dsimp only; omega⟩,
          by rw [← hj]; exact congrArg x (Fin.ext (by simp; omega))⟩
    simp (disch := omega) only [hzero, splice_zero, map_zero, smul_zero, ite_eq_right, add_zero]
  subst hd2
  rcases Nat.lt_or_ge p j.1 with hpj | hpj
  · obtain rfl : p = j.1 - 1 := by omega
    simp (disch := omega) only [true_and, ite_eq_right, ite_eq_left, zero_add]
    rw [subword_two_eq R x hfit.2]
    have hj' : (⟨j.1 - 1 + 1, by omega⟩ : Fin (n + 1)) = j := Fin.ext (by simp; omega)
    rw [hj', hj, hA.taylor_of_two_unit_right,
      AA.grading.koszulTwist_one_apply_of_mem
        (by simpa [InternalGrading.shift_piece] using hx ⟨j.1 - 1, by omega⟩),
      splice_smul, map_smul]
    simp only [negOnePowCast_eq_intCast]
  · obtain rfl : p = j.1 := by omega
    simp (disch := omega) only [true_and, ite_eq_right, ite_eq_left, add_zero]
    rw [subword_two_eq R x hfit.2, Fin.eta, hj, hA.taylor_of_two_unit_left,
      negOnePowCast_eq_intCast, dite_eq_left (by omega)]

/-- Applying a suspended-degree-zero map `G : Tᶜ(sA) → B` that vanishes on degenerate words to
`AA.barDifferential` of a homogeneous word with `x j = e_A` leaves only the boundary terms. -/
private theorem apply_barDifferential_of_tprod_eq_unit {eA : A} (hA : AA.StrictUnit eA)
    {G : ReducedTensorWords R A →ₗ[R] B}
    (hG : LinearMap.IsHomogeneous G (gradedPiece (AA.grading.shift 1))
      (BB.grading.shift 1).piece 0)
    (hGe : degenerateWords R A eA ≤ LinearMap.ker G) {n : ℕ} (x : Fin (n + 1) → A)
    (𝒟 : Fin (n + 1) → ℤ)
    (hx : ∀ i, x i ∈ (AA.grading.shift 1).piece (𝒟 i)) (j : Fin (n + 1))
    (hj : x j = eA) :
    G (AA.barDifferential (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x))) =
      (if j.1 = 0 ∧ 0 < n then G (subword R x 1 n) else 0) +
        (if j.1 = n ∧ 0 < n then BB.grading.koszulTwist 1 (G (subword R x 0 n)) else 0) := by
  have hjn := j.isLt
  rw [AA.barDifferential_def, gradedCoderiv_of_tprod_of_homogeneous _ _ 1 _ x 𝒟 hx]
  simp only [map_sum, map_smul, one_mul]
  rw [Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun d hd ↦
    sign_smul_apply_splice_taylor hA hGe x 𝒟 hx j hj p hp d hd]
  simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_range]
  set S : ℕ → ℤ :=
    fun p ↦ ∑ i ∈ Finset.range p, if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0 with hS
  have hSsucc (p : ℕ) (hp : p < n + 1) : S (p + 1) = S p + 𝒟 ⟨p, hp⟩ := by
    simp only [hS, Finset.sum_range_succ, dite_eq_left hp]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rcases Nat.eq_zero_or_pos j.1 with hj0 | hj0
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, add_zero]
    rw [dite_eq_left (by omega), splice_two_succ_eq_subword R hn hj0 x, hj0,
      Finset.sum_range_zero, negOnePowCast_zero, one_smul]
  rcases Nat.lt_or_ge j.1 n with hjlt | hjge
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, add_zero]
    rw [dite_eq_left (by omega), splice_two_succ_eq_splice_two_pred R hj0 hjlt x,
      smul_smul, ← negOnePowCast_add, ← add_smul]
    have hsign : negOnePowCast R (S j.1) +
        negOnePowCast R (S (j.1 - 1) + (𝒟 ⟨j.1 - 1, by omega⟩ + 1)) = 0 := by
      have hs := hSsucc (j.1 - 1) (by omega)
      rw [Nat.sub_add_cancel hj0] at hs
      rw [hs, ← add_assoc, negOnePowCast_add (R := R) _ 1, negOnePowCast_one, mul_neg_one,
        add_neg_cancel]
    simp only [hS] at hsign
    rw [hsign, zero_smul]
  · simp (disch := omega) only [ite_eq_right, ite_eq_left, zero_add]
    rw [splice_two_pred_eq_subword R (by omega) x, smul_smul, ← negOnePowCast_add]
    have hsub := subword_mem_gradedPiece x (fun i ↦ if h : i < n + 1 then 𝒟 ⟨i, h⟩ else 0)
      (fun i ↦ by simpa only [Fin.is_lt, dite_true, Fin.eta] using hx i) 0 n
    have hdeg : G (subword R x 0 n) ∈ BB.grading.piece (S n + 1) := by
      simpa [hS, InternalGrading.shift_piece] using hG.map_mem hsub
    rw [BB.grading.koszulTwist_one_apply_of_mem hdeg, ← negOnePowCast_eq_intCast]
    congr 1
    have hSn : S n = S (j.1 - 1) + 𝒟 ⟨j.1 - 1, by omega⟩ := by
      rw [← hSsucc]
      congr 1
      omega
    simp only [hS] at hSn ⊢
    rw [hSn, add_assoc]

/-- Evaluating the scalar Taylor functional `(ε_B.unitHom ∘ ε_A ∘ letter)` on
`AA.barDifferential` of a word with `x j = ε_A.unit` matches the boundary formula. -/
private theorem scalarTaylor_barDifferential_of_tprod_eq_unit (εA : AA.Augmentation)
    (εB : BB.Augmentation) {n : ℕ} (x : Fin (n + 1) → A) (j : Fin (n + 1))
    (hj : x j = εA.unit) :
    (εB.unitHom ∘ₗ εA.toLinearMap ∘ₗ letter R A)
        (AA.barDifferential (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x))) =
      (if j.1 = 0 ∧ 0 < n then
        (εB.unitHom ∘ₗ εA.toLinearMap ∘ₗ letter R A) (subword R x 1 n) else 0) +
      (if j.1 = n ∧ 0 < n then
        BB.grading.koszulTwist 1
          ((εB.unitHom ∘ₗ εA.toLinearMap ∘ₗ letter R A) (subword R x 0 n)) else 0) := by
  have hekosz : ∀ a : A, εA (AA.grading.koszulTwist 1 a) = εA a := by
    have h : εA.toLinearMap ∘ₗ AA.grading.koszulTwist 1 = εA.toLinearMap := by
      refine AA.grading.linearMap_ext fun p a ha ↦ ?_
      rw [LinearMap.comp_apply]
      by_cases hp : p = 0
      · subst hp
        rw [AA.grading.koszulTwist_apply_of_mem_zero ha]
      · rw [εA.map_of_mem_ne_zero p _ (AA.grading.koszulTwist_mem_piece ha 1) hp,
          εA.map_of_mem_ne_zero p a ha hp]
    exact LinearMap.congr_fun h
  have hl := LinearMap.congr_fun AA.letter_comp_barDifferential
    (of R A ⟨n + 1, n.succ_pos⟩ (PiTensorProduct.tprod R x))
  simp only [LinearMap.comp_apply] at hl ⊢
  rw [hl]
  rcases n with _ | _ | n
  · rw [of_tprod_eq_subword R Nat.one_pos, subword_one R A x Nat.one_pos]
    have hj0 : (⟨0, Nat.one_pos⟩ : Fin 1) = j := Subsingleton.elim _ _
    rw [hj0, hj, AA.taylor_ofLetter, εA.isStrictUnit.unary_eq_zero, map_zero, map_zero]
    simp
  · have hw : of R A ⟨2, Nat.succ_pos 1⟩ (PiTensorProduct.tprod R x) =
        of R A (2 : ℕ+) (PiTensorProduct.tprod R ![x ⟨0, by simp⟩, x ⟨0 + 1, by simp⟩]) :=
      (of_tprod_eq_subword R (Nat.succ_pos 1) x).trans (subword_two_eq R x (by simp))
    rw [hw]
    fin_cases j
    · simp only [Fin.zero_eta] at hj ⊢
      rw [hj, εA.isStrictUnit.taylor_of_two_unit_left, subword_one R A x (by omega),
        letter_ofLetter]
      simp
    · simp only [Fin.mk_one] at hj ⊢
      have hx1 : x ⟨0 + 1, by simp⟩ = εA.unit := hj
      rw [hx1, εA.isStrictUnit.taylor_of_two_unit_right, hekosz]
      simp [subword_one R A x (a := 0) (by omega), unitHom_apply,
        BB.grading.koszulTwist_apply_of_mem_zero εB.isStrictUnit.degree_zero]
  · rw [εA.isStrictUnit.taylor_of_tprod_eq_zero ⟨n + 3, by omega⟩ (by simp) x ⟨j, hj⟩,
      map_zero, map_zero, letter_subword_of_ne_one R A x 1 (by omega),
      letter_subword_of_ne_one R A x 0 (by omega)]
    simp

/-- The suspended Taylor map used to extend `g : ker ε_A ⟶ ker ε_B` to `A ⟶ B`. -/
private noncomputable def liftHomTaylor (εA : AA.Augmentation) (εB : BB.Augmentation)
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    ReducedTensorWords R A →ₗ[R] B :=
  εB.unitHom ∘ₗ εA.toLinearMap ∘ₗ letter R A +
    εB.augmentationIdeal.subtype ∘ₗ g.taylor ∘ₗ
      ReducedTensorWords.map (R := R) εA.reducedPart

private theorem isHomogeneous_liftHomReducedTerm (εA : AA.Augmentation) (εB : BB.Augmentation)
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    LinearMap.IsHomogeneous
      (εB.augmentationIdeal.subtype ∘ₗ g.taylor ∘ₗ
        ReducedTensorWords.map (R := R) εA.reducedPart)
      (gradedPiece (AA.grading.shift 1)) (BB.grading.shift 1).piece 0 := by
  simpa using (εB.inclusionStrictHom.isHomogeneous_shift 1).comp
    (g.isHomogeneous_taylor.comp (isHomogeneous_map _ _ εA.isHomogeneous_reducedPart_shift_one))

private theorem isHomogeneous_liftHomTaylor (εA : AA.Augmentation) (εB : BB.Augmentation)
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    LinearMap.IsHomogeneous (εA.liftHomTaylor εB g)
      (gradedPiece (AA.grading.shift 1)) (BB.grading.shift 1).piece 0 := by
  have hscal : LinearMap.IsHomogeneous (εB.unitHom ∘ₗ εA.toLinearMap ∘ₗ letter R A)
      (gradedPiece (AA.grading.shift 1)) (BB.grading.shift 1).piece 0 := by
    refine LinearMap.isHomogeneous_def.mpr fun p z hz ↦ ?_
    rw [add_zero]
    have hl : letter R A z ∈ (AA.grading.shift 1).piece p := by
      simpa using (isHomogeneous_letter (AA.grading.shift 1)).map_mem hz
    rw [InternalGrading.shift_piece] at hl
    by_cases hp : p + 1 = 0
    · have hp' : p = -1 := by omega
      subst hp'
      simpa [unitHom_apply] using Submodule.smul_mem _ _ εB.isStrictUnit.mem_shift_one_piece
    · simp only [LinearMap.comp_apply, εA.map_of_mem_ne_zero (p + 1) _ hl hp, map_zero]
      exact zero_mem _
  exact hscal.add (εA.isHomogeneous_liftHomReducedTerm εB g)

private theorem liftHomTaylor_of_tprod_eq_zero (εA : AA.Augmentation) (εB : BB.Augmentation)
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra)
    (m : {k : ℕ // 0 < k}) (hm : m.1 ≠ 1) (y : Fin m.1 → A) (hy : ∃ i, y i = εA.unit) :
    εA.liftHomTaylor εB g (of R A m (PiTensorProduct.tprod R y)) = 0 := by
  obtain ⟨i, hi⟩ := hy
  have hne1 : m ≠ 1 := fun h ↦ hm (congrArg Subtype.val h)
  rw [liftHomTaylor, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    letter_of_of_ne_one R A hne1, map_zero, map_zero, zero_add,
    LinearMap.comp_apply, LinearMap.comp_apply, map_of_tprod,
    (PiTensorProduct.tprod R).map_coord_zero i (by rw [hi, εA.reducedPart_unit]),
    map_zero, map_zero, map_zero]

private theorem degenerateWords_le_ker_liftHomTaylor (εA : AA.Augmentation) (εB : BB.Augmentation)
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    degenerateWords R A εA.unit ≤
      LinearMap.ker
        (BB.taylor ∘ₗ coalgHom R (εA.liftHomTaylor εB g) -
          εA.liftHomTaylor εB g ∘ₗ AA.barDifferential) := by
  set F := εA.liftHomTaylor εB g
  set G := εB.augmentationIdeal.subtype ∘ₗ g.taylor ∘ₗ
    ReducedTensorWords.map (R := R) εA.reducedPart
  have hGe : degenerateWords R A εA.unit ≤ LinearMap.ker G := by
    rw [degenerateWords_le_iff]
    rintro m y ⟨i, hi⟩
    rw [LinearMap.mem_ker]
    simp only [G, LinearMap.comp_apply]
    rw [map_of_tprod,
      (PiTensorProduct.tprod R).map_coord_zero i (by rw [hi, εA.reducedPart_unit]),
      map_zero, map_zero, map_zero]
  rw [degenerateWords_le_iff_of_mem_piece _ εA.isStrictUnit.mem_shift_one_piece]
  rintro ⟨_ | n, hn⟩ x 𝒟 j hx hj _
  · omega
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.comp_apply,
    LinearMap.comp_apply]
  have he : F (ofLetter R A εA.unit) = εB.unit := by simp [F, liftHomTaylor]
  rw [taylor_coalgHom_of_tprod_eq_unit εB.isStrictUnit he
    (εA.liftHomTaylor_of_tprod_eq_zero εB g) x j hj]
  have hFG : F (AA.barDifferential (of R A ⟨n + 1, hn⟩ (PiTensorProduct.tprod R x))) =
      (εB.unitHom ∘ₗ εA.toLinearMap ∘ₗ letter R A)
        (AA.barDifferential (of R A ⟨n + 1, hn⟩ (PiTensorProduct.tprod R x))) +
      G (AA.barDifferential (of R A ⟨n + 1, hn⟩ (PiTensorProduct.tprod R x))) :=
    LinearMap.add_apply _ _ _
  rw [hFG, scalarTaylor_barDifferential_of_tprod_eq_unit εA εB x j hj,
    apply_barDifferential_of_tprod_eq_unit εA.isStrictUnit
      (εA.isHomogeneous_liftHomReducedTerm εB g) hGe x 𝒟 hx j hj,
    eq_comm, add_add_add_comm]
  congr 1 <;> split_ifs <;> simp [F, liftHomTaylor, map_add]

private theorem liftHomTaylor_comp_map_subtype (εA : AA.Augmentation) (εB : BB.Augmentation)
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    εA.liftHomTaylor εB g ∘ₗ ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype =
      εB.augmentationIdeal.subtype ∘ₗ g.taylor := by
  refine LinearMap.ext fun w ↦ ?_
  have hl := LinearMap.congr_fun (letter_comp_map (R := R) εA.augmentationIdeal.subtype) w
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hl
  have he0 : εA (letter R A (ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype w)) =
      0 := by
    rw [hl]
    exact (εA.mem_augmentationIdeal).1 (letter R εA.augmentationIdeal w).property
  have hm := LinearMap.congr_fun
    (ReducedTensorWords.map_comp (R := R) εA.reducedPart εA.augmentationIdeal.subtype) w
  simp only [LinearMap.comp_apply, εA.reducedPart_comp_subtype, ReducedTensorWords.map_id,
    LinearMap.id_apply] at hm
  simp [liftHomTaylor, he0, ← hm]

private theorem taylor_comp_coalgHom_liftHomTaylor (εA : AA.Augmentation) (εB : BB.Augmentation)
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    BB.taylor ∘ₗ coalgHom R (εA.liftHomTaylor εB g) =
      εA.liftHomTaylor εB g ∘ₗ AA.barDifferential := by
  set F := εA.liftHomTaylor εB g
  have hmap_sub := εA.liftHomTaylor_comp_map_subtype εB g
  have hred_eq : ∀ w : ReducedTensorWords R εA.augmentationIdeal,
      (BB.taylor ∘ₗ coalgHom R F)
        (ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype w) =
      (F ∘ₗ AA.barDifferential)
        (ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype w) := fun w ↦ by
    have h1 : coalgHom R F (ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype w) =
        ReducedTensorWords.map (R := R) εB.augmentationIdeal.subtype (g.barMap w) := by
      have hc := LinearMap.congr_fun
        (((isCoalgHom_coalgHom F).comp
          (isCoalgHom_map (R := R) εA.augmentationIdeal.subtype)).eq_coalgHom) w
      rw [← LinearMap.comp_assoc, letter_comp_coalgHom, hmap_sub, ← map_comp_coalgHom,
        ← g.barMap_eq_coalgHom] at hc
      exact hc
    have hB := LinearMap.congr_fun εB.inclusionStrictHom.taylor_comp_barMap (g.barMap w)
    have hg := LinearMap.congr_fun g.taylor_comp_barMap w
    have hA := LinearMap.congr_fun εA.inclusionStrictHom.barDifferential_comp_barMap w
    have hsub := LinearMap.congr_fun hmap_sub (εA.reducedAlgebra.barDifferential w)
    simp only [AInfinityStrictHom.barMap_def, inclusionStrictHom_toLinearMap,
      LinearMap.comp_apply] at hB hg hA hsub ⊢
    rw [h1, hB, hg, hA, ← hsub]
  refine LinearMap.ext fun z ↦ ?_
  have hm := LinearMap.congr_fun
    (ReducedTensorWords.map_comp (R := R) εA.augmentationIdeal.subtype εA.reducedPart) z
  simp only [LinearMap.comp_apply] at hm
  have hsplit : z = (z - ReducedTensorWords.map (R := R)
        (εA.augmentationIdeal.subtype ∘ₗ εA.reducedPart) z) +
      ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype
        (ReducedTensorWords.map (R := R) εA.reducedPart z) := by
    rw [← hm, sub_add_cancel]
  conv_lhs => rw [hsplit]
  conv_rhs => rw [hsplit]
  rw [map_add, map_add,
    sub_eq_zero.1
      (εA.degenerateWords_le_ker_liftHomTaylor εB g
        (sub_map_reducedPart_mem_degenerateWords εA z)),
    hred_eq]

/-- Extend an `A∞` morphism `g : ker ε_A ⟶ ker ε_B` between reduced augmentation ideals to a
strictly unital augmented `A∞` morphism `A ⟶ B`. -/
noncomputable def liftHom (εA : AA.Augmentation) (εB : BB.Augmentation)
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) : AInfinityHom AA BB :=
  AInfinityHom.ofTaylor (εA.liftHomTaylor εB g) (εA.isHomogeneous_liftHomTaylor εB g)
    (εA.taylor_comp_coalgHom_liftHomTaylor εB g)

/-- The suspended Taylor map of `liftHom`. -/
@[simp]
theorem taylor_liftHom (εA : AA.Augmentation) (εB : BB.Augmentation)
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    (εA.liftHom εB g).taylor =
      εB.unitHom ∘ₗ εA.toLinearMap ∘ₗ letter R A +
        εB.augmentationIdeal.subtype ∘ₗ g.taylor ∘ₗ
          ReducedTensorWords.map (R := R) εA.reducedPart :=
  AInfinityHom.taylor_ofTaylor _ _ _

/-- The linear part of `liftHom` carries the source strict unit to the target strict unit. -/
theorem linearPart_liftHom_unit (εA : AA.Augmentation) (εB : BB.Augmentation)
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    (εA.liftHom εB g).linearPart εA.unit = εB.unit := by
  simp [AInfinityHom.linearPart_apply]

/-- On an element of `ker ε_A`, the linear part of `liftHom` agrees with `g.linearPart`. -/
theorem linearPart_liftHom_coe (εA : AA.Augmentation) (εB : BB.Augmentation)
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) (x : εA.augmentationIdeal) :
    (εA.liftHom εB g).linearPart (x : A) = (g.linearPart x : B) := by
  have hx : εA (x : A) = 0 := (εA.mem_augmentationIdeal).1 x.property
  simp [AInfinityHom.linearPart_apply, hx]

/-- `liftHom` produces a strictly unital `A∞` morphism. -/
theorem isStrictlyUnital_liftHom (εA : AA.Augmentation) (εB : BB.Augmentation)
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    (εA.liftHom εB g).IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit where
  map_unit := εA.linearPart_liftHom_unit εB g
  component_eq_zero {n} hn x hx := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · obtain ⟨i, hi⟩ := hx
      rw [AInfinityHom.component_apply _ n hn0, εA.taylor_liftHom]
      exact εA.liftHomTaylor_of_tprod_eq_zero εB g ⟨n, hn0⟩ hn _
        ⟨i, by rw [hi, AA.grading.koszulTwist_apply_of_mem_zero εA.isStrictUnit.degree_zero]⟩

/-- `liftHom` produces an augmented `A∞` morphism. -/
theorem isAugmented_liftHom (εA : AA.Augmentation) (εB : BB.Augmentation)
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    (εA.liftHom εB g).IsAugmented εA εB := by
  rw [AInfinityHom.isAugmented_iff_taylor, εA.taylor_liftHom]
  refine LinearMap.ext fun z ↦ ?_
  have hg : εB (g.taylor (ReducedTensorWords.map (R := R) εA.reducedPart z) : B) = 0 :=
    (εB.mem_augmentationIdeal).1
      (g.taylor (ReducedTensorWords.map (R := R) εA.reducedPart z)).property
  simp [hg]

/-- Restricting `liftHom g` back to the reduced augmentation ideals recovers `g`. -/
@[simp]
theorem reducedHom_liftHom (εA : AA.Augmentation) (εB : BB.Augmentation)
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    (εA.isAugmented_liftHom εB g).reducedHom = g := by
  apply AInfinityHom.ext
  have ht : (εA.liftHom εB g).taylor = εA.liftHomTaylor εB g :=
    AInfinityHom.taylor_ofTaylor _ _ _
  rw [AInfinityHom.IsAugmented.taylor_reducedHom, ht, εA.liftHomTaylor_comp_map_subtype,
    ← LinearMap.comp_assoc, εB.reducedPart_comp_subtype, LinearMap.id_comp]

/-- Extending the reduced restriction of a strictly unital augmented morphism `f` recovers `f`. -/
@[simp]
theorem liftHom_reducedHom {f : AInfinityHom AA BB} (εA : AA.Augmentation) (εB : BB.Augmentation)
    (hf_unit : f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit)
    (hf_aug : f.IsAugmented εA εB) :
    εA.liftHom εB hf_aug.reducedHom = f := by
  apply AInfinityHom.ext
  refine LinearMap.ext fun z ↦ ?_
  set d := z - ReducedTensorWords.map (R := R)
    (εA.augmentationIdeal.subtype ∘ₗ εA.reducedPart) z
  set w := ReducedTensorWords.map (R := R) εA.reducedPart z
  have hm := LinearMap.congr_fun
    (ReducedTensorWords.map_comp (R := R) εA.augmentationIdeal.subtype εA.reducedPart) z
  simp only [LinearMap.comp_apply] at hm
  have hsplit : z = d + ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype w := by
    rw [← hm, sub_add_cancel]
  have hd : d ∈ degenerateWords R A εA.unit := sub_map_reducedPart_mem_degenerateWords εA z
  have hld : letter R A d = εA (letter R A z) • εA.unit := by
    have hl := LinearMap.congr_fun
      (letter_comp_map (R := R) (εA.augmentationIdeal.subtype ∘ₗ εA.reducedPart)) z
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, coe_reducedPart] at hl
    rw [LinearMap.map_sub, hl, sub_sub_cancel]
  have hdeg_eq : (εA.liftHom εB hf_aug.reducedHom).taylor d = f.taylor d := by
    rw [(εA.isStrictlyUnital_liftHom εB hf_aug.reducedHom).taylor_eq_linearPart_letter hd,
      hf_unit.taylor_eq_linearPart_letter hd, hld, map_smul, map_smul,
      εA.linearPart_liftHom_unit, hf_unit.map_unit]
  have hred_eq : (εA.liftHom εB hf_aug.reducedHom).taylor
      (ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype w) =
      f.taylor (ReducedTensorWords.map (R := R) εA.augmentationIdeal.subtype w) := by
    have ht : (εA.liftHom εB hf_aug.reducedHom).taylor =
        εA.liftHomTaylor εB hf_aug.reducedHom := AInfinityHom.taylor_ofTaylor _ _ _
    have hsub := LinearMap.congr_fun (εA.liftHomTaylor_comp_map_subtype εB hf_aug.reducedHom) w
    rw [ht]
    simp only [LinearMap.comp_apply, AInfinityHom.IsAugmented.taylor_reducedHom,
      Submodule.subtype_apply] at hsub
    exact hsub.trans
      (congrArg Subtype.val (εB.reducedPart_coe ⟨_, hf_aug.taylor_map_subtype_mem w⟩))
  rw [hsplit, map_add, map_add, hdeg_eq, hred_eq]

/-- **Splitting equivalence for strictly unital augmented `A∞` morphisms**: strictly unital
augmented `A∞` morphisms `A ⟶ B` correspond bijectively to `A∞` morphisms
`ker ε_A ⟶ ker ε_B` between the reduced augmentation ideals. -/
noncomputable def strictlyUnitalAugmentedHomEquiv (εA : AA.Augmentation) (εB : BB.Augmentation) :
    {f : AInfinityHom AA BB //
      f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit ∧ f.IsAugmented εA εB} ≃
      AInfinityHom εA.reducedAlgebra εB.reducedAlgebra where
  toFun f := f.property.2.reducedHom
  invFun g :=
    ⟨εA.liftHom εB g, εA.isStrictlyUnital_liftHom εB g, εA.isAugmented_liftHom εB g⟩
  left_inv f := Subtype.ext (εA.liftHom_reducedHom εB f.property.1 f.property.2)
  right_inv g := εA.reducedHom_liftHom εB g

/-- Forward evaluation of `strictlyUnitalAugmentedHomEquiv` restricts `f` to the reduced
augmentation ideals. -/
@[simp]
theorem strictlyUnitalAugmentedHomEquiv_apply (εA : AA.Augmentation) (εB : BB.Augmentation)
    (f : {f : AInfinityHom AA BB //
      f.IsStrictlyUnital εA.isStrictUnit εB.isStrictUnit ∧ f.IsAugmented εA εB}) :
    εA.strictlyUnitalAugmentedHomEquiv εB f = f.property.2.reducedHom := (rfl)

/-- Inverse evaluation of `strictlyUnitalAugmentedHomEquiv` extends `g` via `liftHom`. -/
@[simp]
theorem strictlyUnitalAugmentedHomEquiv_symm_apply (εA : AA.Augmentation) (εB : BB.Augmentation)
    (g : AInfinityHom εA.reducedAlgebra εB.reducedAlgebra) :
    ((εA.strictlyUnitalAugmentedHomEquiv εB).symm g).val = εA.liftHom εB g := (rfl)

end AInfinityAlgebra.Augmentation

end TauCeti
