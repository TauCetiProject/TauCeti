/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Augmentation
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Strict
public import TauCeti.LinearAlgebra.TensorCoalgebra.Degenerate
import TauCeti.LinearAlgebra.TensorCoalgebra.Coassoc
import TauCeti.LinearAlgebra.TensorCoalgebra.Grading

/-!
# Bar projection of an augmented `A∞` algebra

Let `(A, ε)` be an augmented `A∞` algebra with augmentation ideal `I = ker ε`.  The inclusion
`I ⟶ A` is a strict `A∞` morphism
(`TauCeti.AInfinityAlgebra.Augmentation.reducedAlgebraInclusion`), and the letterwise reduced-part
projection `π = ReducedTensorWords.map ε.reducedPart` retracts its bar map.

This file decomposes the bar coalgebra `Tᶜ(sA)` into reduced words in `I` and unit-containing
degenerate words (`sub_map_subtype_map_reducedPart_mem_degenerateWords`), computes `ε ∘ 𝒜.taylor`
(`comp_taylor`), and expresses `π ∘ b_A` as `b_I ∘ π` plus the two boundary unit-contraction
terms coming from the strict unit acting in arity two (`map_reducedPart_comp_barDifferential`).

## Main definitions

* `TauCeti.AInfinityAlgebra.Augmentation.reducedAlgebraInclusion`: the inclusion of the augmentation
  ideal as a strict `A∞` morphism.

## Main results

* `TauCeti.AInfinityAlgebra.Augmentation.sub_map_subtype_map_reducedPart_mem_degenerateWords`:
  every bar word differs from its reduced-part projection by a unit-containing degenerate word.
* `TauCeti.AInfinityAlgebra.Augmentation.comp_taylor`: the augmentation of the Taylor map is the
  product of the two letter augmentations on length-two words and vanishes elsewhere.
* `TauCeti.AInfinityAlgebra.Augmentation.map_reducedPart_comp_barDifferential`: the letterwise
  reduced-part projection intertwines `b_A` with `b_I` up to the two unit-contraction terms.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, Section 3.2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-! ### Auxiliary lemma for two-letter projections of deconcatenation -/

namespace ReducedTensorWords

/-- Applying `letter ⊗ letter` to the deconcatenation of a pure word of length other than two gives
zero, because every nontrivial cut leaves a factor of length at least two. -/
theorem map_letter_letter_deconcatenation_of_ne_two {M : Type*} [AddCommGroup M]
    [Module R M] (n : {n : ℕ // 0 < n}) (hn : n.1 ≠ 2) (x : Fin n.1 → M) :
    TensorProduct.map (ReducedTensorWords.letter R M) (ReducedTensorWords.letter R M)
      (ReducedTensorWords.deconcatenation R M
        (ReducedTensorWords.of R M n (PiTensorProduct.tprod R x))) = 0 := by
  have hn0 : 0 < n.1 := n.2
  rw [ReducedTensorWords.of_tprod_eq_subword R hn0, ReducedTensorWords.deconcatenation_subword,
    map_sum]
  refine Finset.sum_eq_zero fun d hd ↦ ?_
  rw [Finset.mem_Ioo] at hd
  rw [TensorProduct.map_tmul]
  by_cases hd1 : d = 1
  · rw [zero_add, ReducedTensorWords.letter_subword_of_ne_one R M x d (by omega),
      TensorProduct.tmul_zero]
  · rw [ReducedTensorWords.letter_subword_of_ne_one R M x 0 hd1, TensorProduct.zero_tmul]

end ReducedTensorWords

/-! ### Inclusion of the augmentation ideal -/

namespace AInfinityAlgebra.Augmentation

variable {𝒜 : AInfinityAlgebra R A}

/-- The inclusion of the reduced augmentation ideal into an augmented `A∞` algebra, as a strict
`A∞` morphism. -/
noncomputable def reducedAlgebraInclusion (ε : 𝒜.Augmentation) :
    AInfinityStrictHom ε.reducedAlgebra 𝒜 where
  toLinearMap := ε.augmentationIdeal.subtype
  map_mem' {p} {a} ha := by
    simpa only [reducedAlgebra_grading, reducedGrading_piece, Submodule.mem_comap] using ha
  map_m' n := MultilinearMap.ext fun x ↦ by
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      reducedAlgebra_m, Submodule.subtype_apply, coe_reducedOperation]

/-- The underlying linear map of the reduced-algebra inclusion is the submodule inclusion. -/
@[simp]
theorem toLinearMap_reducedAlgebraInclusion (ε : 𝒜.Augmentation) :
    ε.reducedAlgebraInclusion.toLinearMap = ε.augmentationIdeal.subtype := (rfl)

/-- The reduced-algebra inclusion acts as subtype coercion. -/
@[simp]
theorem coe_reducedAlgebraInclusion (ε : 𝒜.Augmentation) (x : ε.augmentationIdeal) :
    ε.reducedAlgebraInclusion x = (x : A) := (rfl)

/-- The bar map of the reduced-algebra inclusion applies the submodule inclusion letterwise. -/
@[simp]
theorem barMap_reducedAlgebraInclusion (ε : 𝒜.Augmentation) :
    ε.reducedAlgebraInclusion.barMap =
      ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype :=
  ε.reducedAlgebraInclusion.barMap_def


/-! ### Degenerate words and the bar differential of an augmented `A∞` algebra -/

/-- The reduced-part projection has degree zero for the suspended gradings. -/
theorem isHomogeneous_reducedPart_shift (ε : 𝒜.Augmentation) :
    LinearMap.IsHomogeneous ε.reducedPart (𝒜.grading.shift 1).piece
      (ε.reducedAlgebra.grading.shift 1).piece 0 := by
  rw [reducedAlgebra_grading, LinearMap.isHomogeneous_def]
  intro p a ha
  rw [InternalGrading.shift_piece] at ha
  rw [add_zero, InternalGrading.shift_piece]
  simpa only [add_zero] using ε.isHomogeneous_reducedPart.map_mem ha


/-- Splitting each letter of a pure tensor word into its reduced and scalar parts writes the
difference between the word and its reduced-part projection as a sum of pure words of the same
length, each having at least one scalar-multiple-of-unit letter. -/
private theorem of_tprod_sub_map_eq_sum_erase (ε : 𝒜.Augmentation) (n : {n : ℕ // 0 < n})
    (x : Fin n.1 → A) :
    ReducedTensorWords.of R A n (PiTensorProduct.tprod R x) -
      ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype
        (ReducedTensorWords.map (R := R) ε.reducedPart
          (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x))) =
      ∑ f ∈ (Finset.univ : Finset (Fin n.1 → Bool)).erase (fun _ ↦ false),
        ReducedTensorWords.of R A n (PiTensorProduct.tprod R fun i ↦
          if f i then ε (x i) • ε.unit else (ε.reducedPart (x i) : A)) := by
  classical
  let piece : Fin n.1 → Bool → A := fun i b ↦
    if b then ε (x i) • ε.unit else (ε.reducedPart (x i) : A)
  have hx (i : Fin n.1) : ∑ b ∈ (Finset.univ : Finset Bool), piece i b = x i := by
    simp [piece, coe_reducedPart]
  have hpi : Fintype.piFinset (fun _ : Fin n.1 ↦ (Finset.univ : Finset Bool)) = Finset.univ := by
    ext f
    simp
  have hsum : PiTensorProduct.tprod R x =
      ∑ f : Fin n.1 → Bool, PiTensorProduct.tprod R (fun i ↦ piece i (f i)) := by
    rw [← hpi, ← (PiTensorProduct.tprod R).map_sum_finset]
    exact congrArg _ (funext fun i ↦ (hx i).symm)
  conv_lhs =>
    arg 1
    rw [hsum, map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (fun _ : Fin n.1 ↦ false))]
  rw [ReducedTensorWords.map_of_tprod, ReducedTensorWords.map_of_tprod]
  have hfalse : (fun i : Fin n.1 ↦ piece i false) =
      fun i ↦ ε.augmentationIdeal.subtype (ε.reducedPart (x i)) := by
    funext i
    simp [piece]
  rw [hfalse, add_sub_cancel_left]

/-- Every reduced tensor word differs from its reduced-part projection by a unit-containing
degenerate word. -/
theorem sub_map_subtype_map_reducedPart_mem_degenerateWords (ε : 𝒜.Augmentation)
    (z : ReducedTensorWords R A) :
    z - ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype
      (ReducedTensorWords.map (R := R) ε.reducedPart z) ∈
        ReducedTensorWords.degenerateWords R A ε.unit := by
  classical
  let S : Submodule R (ReducedTensorWords R A) :=
    (ReducedTensorWords.degenerateWords R A ε.unit).comap
      (LinearMap.id - ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype ∘ₗ
        ReducedTensorWords.map (R := R) ε.reducedPart)
  suffices h : ⊤ ≤ S by
    simpa [S] using h Submodule.mem_top (x := z)
  rw [← ReducedTensorWords.iSup_range_of R A, iSup_le_iff]
  intro n
  rw [LinearMap.range_le_iff_comap]
  apply top_unique
  intro t ht
  clear ht
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [Submodule.mem_comap, map_smul]
    apply S.smul_mem c
    rw [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      of_tprod_sub_map_eq_sum_erase]
    refine Submodule.sum_mem _ fun f hf ↦ ?_
    have hne : f ≠ fun _ ↦ false := (Finset.mem_erase.1 hf).1
    have htrue : ∃ i, f i = true := by
      by_contra h
      push Not at h
      apply hne
      funext i
      cases hfi : f i
      · rfl
      · exact (h i hfi).elim
    obtain ⟨i, hi⟩ := htrue
    exact ReducedTensorWords.of_tprod_mem_degenerateWords_of_eq_smul n _ (i := i)
      (c := ε (x i)) (by simp [hi])
  | add u v hu hv =>
    rw [Submodule.mem_comap, map_add]
    exact S.add_mem hu hv


/-- For arity other than two, the Taylor map of an augmented `A∞` algebra depends only on the
reduced-part projection of a pure word. -/
private theorem taylor_of_tprod_eq_of_ne_two (ε : 𝒜.Augmentation) (n : {n : ℕ // 0 < n})
    (hn : n.1 ≠ 2) (x : Fin n.1 → A) :
    𝒜.taylor (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)) =
      𝒜.taylor (ReducedTensorWords.map (R := R) ε.augmentationIdeal.subtype
        (ReducedTensorWords.map (R := R) ε.reducedPart
          (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)))) := by
  classical
  rw [← sub_eq_zero, ← map_sub, of_tprod_sub_map_eq_sum_erase, map_sum]
  refine Finset.sum_eq_zero fun f hf ↦ ?_
  have hne : f ≠ fun _ ↦ false := (Finset.mem_erase.1 hf).1
  have htrue : ∃ i, f i = true := by
    by_contra h
    push Not at h
    apply hne
    funext i
    cases hfi : f i
    · rfl
    · exact (h i hfi).elim
  obtain ⟨i, hi⟩ := htrue
  let y : Fin n.1 → A := fun j ↦ if f j then ε (x j) • ε.unit else (ε.reducedPart (x j) : A)
  have hy : y = Function.update y i (ε (x i) • ε.unit) :=
    (Function.update_eq_self_iff.2 (by simp [y, hi])).symm
  change 𝒜.taylor (ReducedTensorWords.of R A n (PiTensorProduct.tprod R y)) = 0
  rw [hy, (PiTensorProduct.tprod R).map_update_smul, map_smul, map_smul,
    ε.isStrictUnit.taylor_of_tprod_eq_zero n hn _ ⟨i, by simp⟩, smul_zero]

/-- An augmentation is invariant under the degree-one Koszul twist, because it vanishes outside
degree zero. -/
private theorem map_koszulTwist_one (ε : 𝒜.Augmentation) (a : A) :
    ε (𝒜.grading.koszulTwist 1 a) = ε a := by
  have h : ε.toLinearMap ∘ₗ 𝒜.grading.koszulTwist 1 = ε.toLinearMap := by
    refine 𝒜.grading.linearMap_ext fun p x hx ↦ ?_
    simp only [LinearMap.comp_apply, 𝒜.grading.koszulTwist_apply_of_mem hx, map_smul]
    by_cases hp : p = 0
    · subst p
      simp
    · rw [ε.map_of_mem_ne_zero p x hx hp, smul_zero]
  exact LinearMap.congr_fun h a

/-- The augmentation of the Taylor map is the product of the augmentations of the two letters on a
two-letter word, and zero in all other arities. -/
theorem comp_taylor (ε : 𝒜.Augmentation) :
    ε.toLinearMap ∘ₗ 𝒜.taylor =
      LinearMap.mul' R R ∘ₗ
        TensorProduct.map
          (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A)
          (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A) ∘ₗ
        ReducedTensorWords.deconcatenation R A := by
  refine ReducedTensorWords.linearMap_ext R A fun n x ↦ ?_
  by_cases hn : n.1 = 2
  · obtain ⟨k, hk⟩ := n
    simp only at hn
    subst k
    have hx : x = ![x 0, x 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hx]
    change ε (𝒜.taylor (ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![x 0, x 1]))) =
      LinearMap.mul' R R (TensorProduct.map (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A)
        (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A)
        (ReducedTensorWords.deconcatenation R A
          (ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![x 0, x 1]))))
    rw [𝒜.taylor_of_two, ε.map_binary, ε.map_koszulTwist_one,
      ReducedTensorWords.deconcatenation_of_two, TensorProduct.map_tmul, LinearMap.comp_apply,
      LinearMap.comp_apply, ReducedTensorWords.letter_ofLetter, ReducedTensorWords.letter_ofLetter,
      LinearMap.mul'_apply]
  · simp only [LinearMap.comp_apply]
    rw [𝒜.taylor_of_tprod, ε.map_m_of_ne_two n.1 n.2 hn]
    have h0 := ReducedTensorWords.map_letter_letter_deconcatenation_of_ne_two (R := R) n hn x
    have hfac : TensorProduct.map (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A)
        (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A) =
        TensorProduct.map ε.toLinearMap ε.toLinearMap ∘ₗ
          TensorProduct.map (ReducedTensorWords.letter R A) (ReducedTensorWords.letter R A) := by
      rw [← TensorProduct.map_comp]
    rw [hfac, LinearMap.comp_apply, h0, map_zero, map_zero]


/-- The scalar projection `Tᶜ(sA) ⟶ R` extracting the augmentation of the single-letter
component. -/
private noncomputable def scalarPart (ε : 𝒜.Augmentation) : ReducedTensorWords R A →ₗ[R] R :=
  ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A

/-- The left unit-contraction term `z ↦ ∑ ε(letter z₁) • π(z₂)` of `π ∘ b_A`. -/
private noncomputable def leftUnitTerm (ε : 𝒜.Augmentation) :
    ReducedTensorWords R A →ₗ[R] ReducedTensorWords R ε.augmentationIdeal :=
  (TensorProduct.lid R (ReducedTensorWords R ε.augmentationIdeal)).toLinearMap ∘ₗ
    TensorProduct.map ε.scalarPart (ReducedTensorWords.map (R := R) ε.reducedPart) ∘ₗ
    ReducedTensorWords.deconcatenation R A

/-- The right unit-contraction term `z ↦ ∑ ε(letter z₂) • π(τ z₁)` of `π ∘ b_A`, where `τ` is the
degree-one letterwise Koszul twist of the suspended grading. -/
private noncomputable def rightUnitTerm (ε : 𝒜.Augmentation) :
    ReducedTensorWords R A →ₗ[R] ReducedTensorWords R ε.augmentationIdeal :=
  (TensorProduct.rid R (ReducedTensorWords R ε.augmentationIdeal)).toLinearMap ∘ₗ
    TensorProduct.map
      (ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ
        ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1))
      ε.scalarPart ∘ₗ
    ReducedTensorWords.deconcatenation R A

/-- The combination `leftUnitTerm + (-1) • rightUnitTerm` is a graded coderivation along the
letterwise reduced-part projection `π = map reducedPart`. -/
private theorem isGradedCoderivationAlong_unitTerms (ε : 𝒜.Augmentation) :
    ReducedTensorWords.IsGradedCoderivationAlong (𝒜.grading.shift 1) 1
      (ReducedTensorWords.map (R := R) ε.reducedPart)
      (ReducedTensorWords.map (R := R) ε.reducedPart)
      (ε.leftUnitTerm + (-1 : R) • ε.rightUnitTerm) := by
  set π := ReducedTensorWords.map (R := R) ε.reducedPart
  set τ := ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1)
  set ΔA := ReducedTensorWords.deconcatenation R A
  set ΔB := ReducedTensorWords.deconcatenation R ε.augmentationIdeal
  have hπ : ReducedTensorWords.IsCoalgHom R π := ReducedTensorWords.isCoalgHom_map ε.reducedPart
  have hπτ : ReducedTensorWords.IsCoalgHom R (π ∘ₗ τ) :=
    hπ.comp (ReducedTensorWords.isCoalgHom_map _)
  -- Three trilinear maps out of `T ⊗ (T ⊗ T)` compare the two sides via coassociativity.
  set M₁ : ReducedTensorWords R A ⊗[R]
      (ReducedTensorWords R A ⊗[R] ReducedTensorWords R A) →ₗ[R]
      ReducedTensorWords R ε.augmentationIdeal ⊗[R] ReducedTensorWords R ε.augmentationIdeal :=
    (TensorProduct.lid R _).toLinearMap ∘ₗ
      TensorProduct.map ε.scalarPart (TensorProduct.map π π)
  set M₂ : ReducedTensorWords R A ⊗[R]
      (ReducedTensorWords R A ⊗[R] ReducedTensorWords R A) →ₗ[R]
      ReducedTensorWords R ε.augmentationIdeal ⊗[R] ReducedTensorWords R ε.augmentationIdeal :=
    TensorProduct.map (π ∘ₗ τ)
      ((TensorProduct.lid R _).toLinearMap ∘ₗ TensorProduct.map ε.scalarPart π)
  set M₃ : ReducedTensorWords R A ⊗[R]
      (ReducedTensorWords R A ⊗[R] ReducedTensorWords R A) →ₗ[R]
      ReducedTensorWords R ε.augmentationIdeal ⊗[R] ReducedTensorWords R ε.augmentationIdeal :=
    (TensorProduct.rid R _).toLinearMap ∘ₗ
      (TensorProduct.assoc R _ _ R).symm.toLinearMap ∘ₗ
      TensorProduct.map (π ∘ₗ τ) (TensorProduct.map (π ∘ₗ τ) ε.scalarPart)
  have hL₁ : ΔB ∘ₗ ε.leftUnitTerm = TensorProduct.map ε.leftUnitTerm π ∘ₗ ΔA := by
    have hmid1 : ΔB ∘ₗ (TensorProduct.lid R _).toLinearMap ∘ₗ
        TensorProduct.map ε.scalarPart π = M₁ ∘ₗ LinearMap.lTensor _ ΔA := by
      refine TensorProduct.ext' fun x y ↦ ?_
      simp [M₁, ΔA, ΔB, hπ.deconcatenation_apply]
    have h1 : ΔB ∘ₗ ε.leftUnitTerm = M₁ ∘ₗ LinearMap.lTensor _ ΔA ∘ₗ ΔA := by
      calc
        ΔB ∘ₗ ε.leftUnitTerm =
            (ΔB ∘ₗ (TensorProduct.lid R _).toLinearMap ∘ₗ TensorProduct.map ε.scalarPart π) ∘ₗ
              ΔA := by simp only [leftUnitTerm, π, ΔA, LinearMap.comp_assoc]
        _ = (M₁ ∘ₗ LinearMap.lTensor _ ΔA) ∘ₗ ΔA := congrArg (· ∘ₗ ΔA) hmid1
        _ = M₁ ∘ₗ LinearMap.lTensor _ ΔA ∘ₗ ΔA := LinearMap.comp_assoc _ _ _
    have hmid2 : TensorProduct.map ε.leftUnitTerm π =
        M₁ ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ LinearMap.rTensor _ ΔA := by
      refine TensorProduct.ext' fun x y ↦ ?_
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
        leftUnitTerm]
      induction ΔA x using TensorProduct.inductionOn with
      | tmul u v => simp [M₁, π, TensorProduct.smul_tmul']
      | add u v hu hv => simp only [map_add, TensorProduct.add_tmul, hu, hv]
    have h2 : TensorProduct.map ε.leftUnitTerm π ∘ₗ ΔA =
        M₁ ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ LinearMap.rTensor _ ΔA ∘ₗ ΔA := by
      calc
        TensorProduct.map ε.leftUnitTerm π ∘ₗ ΔA =
            (M₁ ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ LinearMap.rTensor _ ΔA) ∘ₗ ΔA :=
          congrArg (· ∘ₗ ΔA) hmid2
        _ = M₁ ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ LinearMap.rTensor _ ΔA ∘ₗ ΔA := by
          simp only [LinearMap.comp_assoc]
    rw [h1, h2]
    exact congrArg (M₁ ∘ₗ ·) (ReducedTensorWords.deconcatenation_coassoc R A).symm
  have hR₂ : ΔB ∘ₗ ε.rightUnitTerm =
      TensorProduct.map π ε.rightUnitTerm ∘ₗ LinearMap.rTensor _ τ ∘ₗ ΔA := by
    have hmid1 : ΔB ∘ₗ (TensorProduct.rid R _).toLinearMap ∘ₗ
        TensorProduct.map (π ∘ₗ τ) ε.scalarPart =
        M₃ ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ LinearMap.rTensor _ ΔA := by
      refine TensorProduct.ext' fun x y ↦ ?_
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
        TensorProduct.rid_tmul, map_smul, LinearMap.rTensor_tmul]
      rw [show ΔB (π (τ x)) = TensorProduct.map (π ∘ₗ τ) (π ∘ₗ τ) (ΔA x) from
        hπτ.deconcatenation_apply x]
      induction ΔA x using TensorProduct.inductionOn with
      | tmul u v => simp [M₃]
      | add u v hu hv => simp only [map_add, TensorProduct.add_tmul, smul_add, hu, hv]
    have h1 : ΔB ∘ₗ ε.rightUnitTerm =
        M₃ ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ LinearMap.rTensor _ ΔA ∘ₗ ΔA := by
      calc
        ΔB ∘ₗ ε.rightUnitTerm =
            (ΔB ∘ₗ (TensorProduct.rid R _).toLinearMap ∘ₗ
              TensorProduct.map (π ∘ₗ τ) ε.scalarPart) ∘ₗ ΔA := by
          simp only [rightUnitTerm, π, τ, ΔA, LinearMap.comp_assoc]
        _ = (M₃ ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ LinearMap.rTensor _ ΔA) ∘ₗ ΔA :=
          congrArg (· ∘ₗ ΔA) hmid1
        _ = M₃ ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ LinearMap.rTensor _ ΔA ∘ₗ ΔA := by
          simp only [LinearMap.comp_assoc]
    have hmid2 : TensorProduct.map π ε.rightUnitTerm ∘ₗ LinearMap.rTensor _ τ =
        M₃ ∘ₗ LinearMap.lTensor _ ΔA := by
      refine TensorProduct.ext' fun x y ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul,
        LinearMap.lTensor_tmul, rightUnitTerm]
      induction ΔA y using TensorProduct.inductionOn with
      | tmul u v => simp [M₃, π, τ, TensorProduct.tmul_smul]
      | add u v hu hv => simp only [map_add, TensorProduct.tmul_add, hu, hv]
    have h2 : TensorProduct.map π ε.rightUnitTerm ∘ₗ LinearMap.rTensor _ τ ∘ₗ ΔA =
        M₃ ∘ₗ LinearMap.lTensor _ ΔA ∘ₗ ΔA := by
      calc
        TensorProduct.map π ε.rightUnitTerm ∘ₗ LinearMap.rTensor _ τ ∘ₗ ΔA =
            (TensorProduct.map π ε.rightUnitTerm ∘ₗ LinearMap.rTensor _ τ) ∘ₗ ΔA :=
          (LinearMap.comp_assoc _ _ _).symm
        _ = (M₃ ∘ₗ LinearMap.lTensor _ ΔA) ∘ₗ ΔA := congrArg (· ∘ₗ ΔA) hmid2
        _ = M₃ ∘ₗ LinearMap.lTensor _ ΔA ∘ₗ ΔA := LinearMap.comp_assoc _ _ _
    rw [h1, h2]
    exact congrArg (M₃ ∘ₗ ·) (ReducedTensorWords.deconcatenation_coassoc R A)
  have hCross : TensorProduct.map π ε.leftUnitTerm ∘ₗ LinearMap.rTensor _ τ ∘ₗ ΔA =
      TensorProduct.map ε.rightUnitTerm π ∘ₗ ΔA := by
    have hmid1 : TensorProduct.map π ε.leftUnitTerm ∘ₗ LinearMap.rTensor _ τ =
        M₂ ∘ₗ LinearMap.lTensor _ ΔA := by
      refine TensorProduct.ext' fun x y ↦ ?_
      simp [M₂, leftUnitTerm, π, ΔA]
    have h1 : TensorProduct.map π ε.leftUnitTerm ∘ₗ LinearMap.rTensor _ τ ∘ₗ ΔA =
        M₂ ∘ₗ LinearMap.lTensor _ ΔA ∘ₗ ΔA := by
      calc
        TensorProduct.map π ε.leftUnitTerm ∘ₗ LinearMap.rTensor _ τ ∘ₗ ΔA =
            (TensorProduct.map π ε.leftUnitTerm ∘ₗ LinearMap.rTensor _ τ) ∘ₗ ΔA :=
          (LinearMap.comp_assoc _ _ _).symm
        _ = (M₂ ∘ₗ LinearMap.lTensor _ ΔA) ∘ₗ ΔA := congrArg (· ∘ₗ ΔA) hmid1
        _ = M₂ ∘ₗ LinearMap.lTensor _ ΔA ∘ₗ ΔA := LinearMap.comp_assoc _ _ _
    have hmid2 : TensorProduct.map ε.rightUnitTerm π =
        M₂ ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ LinearMap.rTensor _ ΔA := by
      refine TensorProduct.ext' fun x y ↦ ?_
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
        rightUnitTerm]
      induction ΔA x using TensorProduct.inductionOn with
      | tmul u v => simp [M₂, π, τ, TensorProduct.smul_tmul]
      | add u v hu hv => simp only [map_add, TensorProduct.add_tmul, hu, hv]
    have h2 : TensorProduct.map ε.rightUnitTerm π ∘ₗ ΔA =
        M₂ ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ LinearMap.rTensor _ ΔA ∘ₗ ΔA := by
      calc
        TensorProduct.map ε.rightUnitTerm π ∘ₗ ΔA =
            (M₂ ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ LinearMap.rTensor _ ΔA) ∘ₗ ΔA :=
          congrArg (· ∘ₗ ΔA) hmid2
        _ = M₂ ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ LinearMap.rTensor _ ΔA ∘ₗ ΔA := by
          simp only [LinearMap.comp_assoc]
    rw [h1, h2]
    exact congrArg (M₂ ∘ₗ ·) (ReducedTensorWords.deconcatenation_coassoc R A).symm
  rw [ReducedTensorWords.isGradedCoderivationAlong_iff]
  change ΔB ∘ₗ (ε.leftUnitTerm + (-1 : R) • ε.rightUnitTerm) =
    TensorProduct.map (ε.leftUnitTerm + (-1 : R) • ε.rightUnitTerm) π ∘ₗ ΔA +
      TensorProduct.map π (ε.leftUnitTerm + (-1 : R) • ε.rightUnitTerm) ∘ₗ
        LinearMap.rTensor _ τ ∘ₗ ΔA
  simp only [LinearMap.comp_add, LinearMap.comp_smul, hL₁, hR₂, TensorProduct.map_add_left,
    TensorProduct.map_smul_left, TensorProduct.map_add_right, TensorProduct.map_smul_right,
    LinearMap.add_comp, LinearMap.smul_comp, hCross]
  set C := TensorProduct.map ε.rightUnitTerm π ∘ₗ ΔA
  rw [add_assoc, ← add_assoc ((-1 : R) • C)]
  have hzero : (-1 : R) • C + C = 0 := by
    conv_lhs => arg 2; rw [← one_smul R C]
    rw [← add_smul, neg_add_cancel, zero_smul]
  rw [hzero, zero_add]

/-- The letterwise reduced-part projection `π = map reducedPart` intertwines the bar differential
of `𝒜` with that of the reduced algebra `ε.reducedAlgebra`, up to the two unit-contraction terms
`leftUnitTerm + (-1) • rightUnitTerm`. -/
private theorem map_reducedPart_comp_barDifferential_aux (ε : 𝒜.Augmentation) :
    ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ 𝒜.barDifferential =
      ε.reducedAlgebra.barDifferential ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart +
        (ε.leftUnitTerm + (-1 : R) • ε.rightUnitTerm) := by
  set π := ReducedTensorWords.map (R := R) ε.reducedPart
  have hπ_coalg : ReducedTensorWords.IsCoalgHom R π :=
    ReducedTensorWords.isCoalgHom_map ε.reducedPart
  have hπ_hom : LinearMap.IsHomogeneous π
      (ReducedTensorWords.gradedPiece (𝒜.grading.shift 1))
      (ReducedTensorWords.gradedPiece (ε.reducedAlgebra.grading.shift 1)) 0 :=
    ReducedTensorWords.isHomogeneous_map _ _ ε.isHomogeneous_reducedPart_shift
  have hLHS : ReducedTensorWords.IsGradedCoderivationAlong (𝒜.grading.shift 1) 1 π π
      (π ∘ₗ 𝒜.barDifferential) :=
    hπ_coalg.comp_isGradedCoderivation 𝒜.isGradedCoderivation_barDifferential
  have hRHS : ReducedTensorWords.IsGradedCoderivationAlong (𝒜.grading.shift 1) 1 π π
      (ε.reducedAlgebra.barDifferential ∘ₗ π + (ε.leftUnitTerm + (-1 : R) • ε.rightUnitTerm)) :=
    (ε.reducedAlgebra.isGradedCoderivation_barDifferential.comp_isCoalgHom hπ_coalg hπ_hom).add
      ε.isGradedCoderivationAlong_unitTerms
  refine hLHS.eq_of_letter_comp_eq hRHS (ReducedTensorWords.linearMap_ext R A fun n x ↦ ?_)
  by_cases hn1 : n.1 = 1
  · obtain ⟨k, hk⟩ := n
    simp only at hn1
    subst k
    have hof : ReducedTensorWords.of R A ⟨1, hk⟩ (PiTensorProduct.tprod R x) =
        ReducedTensorWords.ofLetter R A (x 0) := by
      rw [ReducedTensorWords.of_tprod_eq_subword R hk,
        ReducedTensorWords.subword_one R A x (by omega)]
      rfl
    change ReducedTensorWords.letter R _
        (π (𝒜.barDifferential (ReducedTensorWords.of R A ⟨1, hk⟩ (PiTensorProduct.tprod R x)))) =
      ReducedTensorWords.letter R _
        ((ε.reducedAlgebra.barDifferential ∘ₗ π +
          (ε.leftUnitTerm + (-1 : R) • ε.rightUnitTerm))
          (ReducedTensorWords.of R A ⟨1, hk⟩ (PiTensorProduct.tprod R x)))
    rw [hof, ← LinearMap.comp_apply (ReducedTensorWords.letter R _),
      ReducedTensorWords.letter_comp_map, LinearMap.comp_apply,
      ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
      AInfinityAlgebra.letter_comp_barDifferential]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_add,
      map_smul]
    rw [← LinearMap.comp_apply (ReducedTensorWords.letter R _),
      AInfinityAlgebra.letter_comp_barDifferential]
    simp only [LinearMap.comp_apply, π, ReducedTensorWords.map_ofLetter,
      AInfinityAlgebra.taylor_ofLetter, leftUnitTerm, rightUnitTerm,
      ReducedTensorWords.deconcatenation_ofLetter, map_zero, smul_zero, add_zero]
    simpa only [← AInfinityAlgebra.differential_apply] using ε.reducedPart_differential (x 0)
  · by_cases hn2 : n.1 = 2
    · obtain ⟨k, hk⟩ := n
      simp only at hn2
      subst k
      have hx : x = ![x 0, x 1] := by
        funext i
        fin_cases i <;> rfl
      rw [hx]
      set a := x 0
      set b := x 1
      have htwist_a : 𝒜.grading.koszulTwist 1 a =
          (ε.reducedAlgebra.grading.koszulTwist 1 (ε.reducedPart a) : A) + ε a • ε.unit := by
        have ha : a = (ε.reducedPart a : A) + ε a • ε.unit := by
          rw [coe_reducedPart, sub_add_cancel]
        have hhom := ε.reducedAlgebraInclusion.isHomogeneous.koszulTwist_apply 1 (ε.reducedPart a)
        simp only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
          toLinearMap_reducedAlgebraInclusion, Submodule.subtype_apply] at hhom
        conv_lhs => rw [ha]
        rw [map_add, map_smul, 𝒜.grading.koszulTwist_apply_of_mem_zero ε.isStrictUnit.degree_zero,
          hhom]
      have htwist_red : ε.reducedPart ((𝒜.grading.shift 1).koszulTwist 1 a) =
          -ε.reducedAlgebra.grading.koszulTwist 1 (ε.reducedPart a) := by
        rw [InternalGrading.koszulTwist_one_shift_one, LinearMap.neg_apply, map_neg, htwist_a,
          map_add, map_smul, ε.reducedPart_coe, ε.reducedPart_unit, smul_zero, add_zero]
      have hprod : 𝒜.m 2 ![𝒜.grading.koszulTwist 1 a, b] =
          (ε.reducedAlgebra.m 2 ![ε.reducedAlgebra.grading.koszulTwist 1 (ε.reducedPart a),
            ε.reducedPart b] : A) +
          ε a • (ε.reducedPart b : A) +
          ε b • (ε.reducedAlgebra.grading.koszulTwist 1 (ε.reducedPart a) : A) +
          (ε a * ε b) • ε.unit := by
        have hb : b = (ε.reducedPart b : A) + ε b • ε.unit := by
          rw [coe_reducedPart, sub_add_cancel]
        have hm2 : (ε.reducedAlgebra.m 2
            ![ε.reducedAlgebra.grading.koszulTwist 1 (ε.reducedPart a), ε.reducedPart b] : A) =
            𝒜.m 2 ![(ε.reducedAlgebra.grading.koszulTwist 1 (ε.reducedPart a) : A),
              (ε.reducedPart b : A)] := by
          rw [reducedAlgebra_m, coe_reducedOperation]
          congr 1
          funext i
          fin_cases i <;> rfl
        rw [hm2, ← 𝒜.mul_apply, ← 𝒜.mul_apply, htwist_a]
        conv_lhs => rw [hb]
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, 𝒜.mul_apply,
          ε.isStrictUnit.binary_left, ε.isStrictUnit.binary_right, smul_add, smul_smul,
          mul_comm (ε b) (ε a)]
        abel
      have hπ_two : π (ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![a, b])) =
          ReducedTensorWords.of R ε.augmentationIdeal (2 : ℕ+)
            (PiTensorProduct.tprod R ![ε.reducedPart a, ε.reducedPart b]) := by
        refine (ReducedTensorWords.map_of_tprod (R := R) ε.reducedPart (2 : ℕ+) ![a, b]).trans ?_
        congr 2
        funext i
        fin_cases i <;> rfl
      change ReducedTensorWords.letter R _ (π (𝒜.barDifferential (ReducedTensorWords.of R A
          (2 : ℕ+) (PiTensorProduct.tprod R ![a, b])))) =
        ReducedTensorWords.letter R _
          ((ε.reducedAlgebra.barDifferential ∘ₗ π +
            (ε.leftUnitTerm + (-1 : R) • ε.rightUnitTerm))
            (ReducedTensorWords.of R A (2 : ℕ+) (PiTensorProduct.tprod R ![a, b])))
      rw [← LinearMap.comp_apply (ReducedTensorWords.letter R _),
        ReducedTensorWords.letter_comp_map, LinearMap.comp_apply,
        ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
        AInfinityAlgebra.letter_comp_barDifferential]
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_add,
        map_smul]
      rw [← LinearMap.comp_apply (ReducedTensorWords.letter R _),
        AInfinityAlgebra.letter_comp_barDifferential, hπ_two, 𝒜.taylor_of_two,
        ε.reducedAlgebra.taylor_of_two, hprod]
      simp only [map_add, map_smul, ε.reducedPart_coe, ε.reducedPart_unit, smul_zero, add_zero,
        leftUnitTerm, rightUnitTerm, LinearMap.comp_apply,
        ReducedTensorWords.deconcatenation_of_two, TensorProduct.map_tmul, scalarPart,
        ReducedTensorWords.letter_ofLetter, ReducedTensorWords.map_ofLetter, LinearEquiv.coe_coe,
        TensorProduct.lid_tmul, TensorProduct.rid_tmul, htwist_red, smul_neg, neg_one_smul,
        neg_neg]
      abel
    · have h0 := ReducedTensorWords.map_letter_letter_deconcatenation_of_ne_two (R := R) n hn2 x
      have hL0 : ReducedTensorWords.letter R _
          (ε.leftUnitTerm (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x))) = 0 := by
        have hfac : ReducedTensorWords.letter R _ ∘ₗ ε.leftUnitTerm =
            ((TensorProduct.lid R _).toLinearMap ∘ₗ
              TensorProduct.map ε.toLinearMap ε.reducedPart ∘ₗ
              TensorProduct.map (ReducedTensorWords.letter R A) (ReducedTensorWords.letter R A)) ∘ₗ
              ReducedTensorWords.deconcatenation R A := by
          rw [leftUnitTerm, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
          refine congrArg (· ∘ₗ ReducedTensorWords.deconcatenation R A)
            (TensorProduct.ext' fun u v ↦ ?_)
          simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
            TensorProduct.lid_tmul, map_smul, scalarPart]
          rw [← LinearMap.comp_apply (ReducedTensorWords.letter R _),
            ReducedTensorWords.letter_comp_map, LinearMap.comp_apply]
        rw [← LinearMap.comp_apply, hfac, LinearMap.comp_apply, LinearMap.comp_apply,
          LinearMap.comp_apply, h0, map_zero, map_zero]
      have hR0 : ReducedTensorWords.letter R _
          (ε.rightUnitTerm (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x))) = 0 := by
        have hfac : ReducedTensorWords.letter R _ ∘ₗ ε.rightUnitTerm =
            ((TensorProduct.rid R _).toLinearMap ∘ₗ
              TensorProduct.map (ε.reducedPart ∘ₗ (𝒜.grading.shift 1).koszulTwist 1)
                ε.toLinearMap ∘ₗ
              TensorProduct.map (ReducedTensorWords.letter R A) (ReducedTensorWords.letter R A)) ∘ₗ
              ReducedTensorWords.deconcatenation R A := by
          rw [rightUnitTerm, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
          refine congrArg (· ∘ₗ ReducedTensorWords.deconcatenation R A)
            (TensorProduct.ext' fun u v ↦ ?_)
          simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
            TensorProduct.rid_tmul, map_smul, scalarPart]
          rw [← LinearMap.comp_apply (ReducedTensorWords.letter R _),
            ReducedTensorWords.letter_comp_map, LinearMap.comp_apply,
            ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
            ReducedTensorWords.letter_comp_map, LinearMap.comp_apply]
        rw [← LinearMap.comp_apply, hfac, LinearMap.comp_apply, LinearMap.comp_apply,
          LinearMap.comp_apply, h0, map_zero, map_zero]
      change ReducedTensorWords.letter R _
          (π (𝒜.barDifferential (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)))) =
        ReducedTensorWords.letter R _
          ((ε.reducedAlgebra.barDifferential ∘ₗ π +
            (ε.leftUnitTerm + (-1 : R) • ε.rightUnitTerm))
            (ReducedTensorWords.of R A n (PiTensorProduct.tprod R x)))
      rw [← LinearMap.comp_apply (ReducedTensorWords.letter R _),
        ReducedTensorWords.letter_comp_map, LinearMap.comp_apply,
        ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
        AInfinityAlgebra.letter_comp_barDifferential]
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_add,
        map_smul, hL0, hR0, smul_zero, add_zero]
      rw [← LinearMap.comp_apply (ReducedTensorWords.letter R _),
        AInfinityAlgebra.letter_comp_barDifferential]
      simp only [LinearMap.comp_apply, π, reducedAlgebra_taylor]
      rw [ε.taylor_of_tprod_eq_of_ne_two n hn2 x]


/-- The letterwise reduced-part projection `π = map reducedPart` intertwines the bar differential
of `𝒜` with that of the reduced algebra `ε.reducedAlgebra`, up to the left and right
unit-contraction terms coming from the strict unit acting in arity two. -/
theorem map_reducedPart_comp_barDifferential (ε : 𝒜.Augmentation) :
    ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ 𝒜.barDifferential =
      ε.reducedAlgebra.barDifferential ∘ₗ ReducedTensorWords.map (R := R) ε.reducedPart +
        ((TensorProduct.lid R (ReducedTensorWords R ε.augmentationIdeal)).toLinearMap ∘ₗ
            TensorProduct.map (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A)
              (ReducedTensorWords.map (R := R) ε.reducedPart) ∘ₗ
            ReducedTensorWords.deconcatenation R A +
          (-1 : R) •
            ((TensorProduct.rid R (ReducedTensorWords R ε.augmentationIdeal)).toLinearMap ∘ₗ
              TensorProduct.map
                (ReducedTensorWords.map (R := R) ε.reducedPart ∘ₗ
                  ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1))
                (ε.toLinearMap ∘ₗ ReducedTensorWords.letter R A) ∘ₗ
              ReducedTensorWords.deconcatenation R A)) :=
  ε.map_reducedPart_comp_barDifferential_aux

end AInfinityAlgebra.Augmentation

end TauCeti
