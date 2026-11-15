/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Homotopy.TransformationLift
import TauCeti.Algebra.Module.GradedModule.Shift

/-!
# Right homotopy lifting of morphisms of A-infinity algebras

Let `f : A ⟶ B` be an `A∞` morphism over a commutative ring `R` whose linear part `f₁` extends to a
graded `TauCeti.LinearHomotopyEquiv` between the unary differentials of `A` and `B`.  This file
constructs, for any `A∞` morphism `u : C ⟶ B`, a homotopy lift `g : C ⟶ A`
(`TauCeti.AInfinityHom.liftRight`) together with an `A∞` homotopy `u ⇒ f ∘ g`
(`TauCeti.AInfinityHom.liftRightHomotopy`).

The Taylor maps of `g` and of the homotopy coderivation `H` are constructed simultaneously by
induction along the word-length filtration of `Tᶜ(sC)`:

* Suppose Taylor maps `g` and `h` define a coalgebra morphism `G = coalgHom R g` and a `(u, f ∘ G)`
  coderivation `H = gradedCoderivAlong _ 1 u.barMap (f.barMap ∘ G) h` such that the morphism defect
  `B₁ = b_A ∘ G - G ∘ b_C` and homotopy defect `B₂ = f.barMap ∘ G - u.barMap + b_B ∘ H + H ∘ b_C`
  vanish on `filtration R C n`.
* By the coderivation and deconcatenation identities, `B₁` and `B₂` send `filtration R C (n + 1)`
  into single letters, and `b_A² = 0`, `b_B² = 0`, `b_B ∘ f.barMap = f.barMap ∘ b_A` yield coupled
  cocycle-coboundary equations for their word-length `n + 1` components against `b_unary`.
* Subtracting `LinearHomotopyEquiv.obstructionLift` and `LinearHomotopyEquiv.obstructionHomotopy`
  modifies `g` and `h` only on words of length `n + 1` while extending both equations to
  `filtration R C (n + 1)`.  Assembling the stabilizing sequence via
  `ReducedTensorWords.assembleFiltration` produces the global lift and homotopy.

## Main definitions

* `TauCeti.AInfinityHom.liftRight`: right homotopy lift of `u : C ⟶ B` along `f : A ⟶ B`.
* `TauCeti.AInfinityHom.liftRightHomotopy`: homotopy `u ⇒ f ∘ liftRight` witnessing the lift.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.7.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Chapter 1, Théorème 1.3.3.1.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section (1f).
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

namespace AInfinityHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- Perturbing the Taylor map of `coalgHom` by a map vanishing on `filtration R C n` changes its
values on `filtration R C (n + 1)` by `-ofLetter ∘ γ`. -/
private theorem coalgHom_sub_apply_of_mem_filtration_succ (G : InternalGrading R C ℤ)
    (g : ReducedTensorWords R C →ₗ[R] A) {γ : ReducedTensorWords R C →ₗ[R] A} {n : ℕ}
    (hγ : ∀ u ∈ ReducedTensorWords.filtration R C n, γ u = 0)
    {w : ReducedTensorWords R C} (hw : w ∈ ReducedTensorWords.filtration R C (n + 1)) :
    ReducedTensorWords.coalgHom R (g - γ) w =
      ReducedTensorWords.coalgHom R g w - ReducedTensorWords.ofLetter R A (γ w) := by
  have hcod := (ReducedTensorWords.isCoalgHom_coalgHom (g - γ)).isGradedCoderivationAlong_sub
    (G := G) (ReducedTensorWords.isCoalgHom_coalgHom g)
  have h₀ : ∀ u ∈ ReducedTensorWords.filtration R C n,
      (ReducedTensorWords.coalgHom R (g - γ) - ReducedTensorWords.coalgHom R g) u = 0 :=
    fun u hu ↦ sub_eq_zero.2 <|
      (ReducedTensorWords.isCoalgHom_coalgHom (g - γ)).apply_eq_of_mem_filtration
        (ReducedTensorWords.isCoalgHom_coalgHom g)
        (fun v hv ↦ by
          rw [← LinearMap.comp_apply (ReducedTensorWords.letter R A),
            ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
            ReducedTensorWords.letter_comp_coalgHom, ReducedTensorWords.letter_comp_coalgHom,
            LinearMap.sub_apply, hγ v hv, sub_zero]) hu
  have key := hcod.apply_eq_ofLetter_of_mem_filtration_succ h₀ hw
  rw [LinearMap.sub_apply, map_sub, ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
    ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
    ReducedTensorWords.letter_comp_coalgHom, ReducedTensorWords.letter_comp_coalgHom,
    LinearMap.sub_apply] at key
  have hsub : g w - γ w - g w = -γ w := by abel
  rw [hsub, map_neg] at key
  calc
    ReducedTensorWords.coalgHom R (g - γ) w
      = (ReducedTensorWords.coalgHom R (g - γ) w - ReducedTensorWords.coalgHom R g w) +
          ReducedTensorWords.coalgHom R g w := by abel
    _ = -ReducedTensorWords.ofLetter R A (γ w) + ReducedTensorWords.coalgHom R g w := by rw [key]
    _ = ReducedTensorWords.coalgHom R g w - ReducedTensorWords.ofLetter R A (γ w) := by abel

/-- Perturbing the right coalgebra map on lengths `> n` and subtracting `η` (vanishing up to length
`n`) from the Taylor map of `gradedCoderivAlong` changes values on `filtration R C (n + 1)` by
`-ofLetter ∘ η`. -/
private theorem gradedCoderivAlong_sub_apply_of_mem_filtration_succ (G : InternalGrading R C ℤ)
    {U F' F'' : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B}
    (hU : ReducedTensorWords.IsCoalgHom R U) (hF' : ReducedTensorWords.IsCoalgHom R F')
    (hF'' : ReducedTensorWords.IsCoalgHom R F'')
    (h : ReducedTensorWords R C →ₗ[R] B) {η : ReducedTensorWords R C →ₗ[R] B} {n : ℕ}
    (hF_eq : ∀ u ∈ ReducedTensorWords.filtration R C n, F'' u = F' u)
    (hη : ∀ u ∈ ReducedTensorWords.filtration R C n, η u = 0)
    {w : ReducedTensorWords R C} (hw : w ∈ ReducedTensorWords.filtration R C (n + 1)) :
    ReducedTensorWords.gradedCoderivAlong G 1 U F'' (h - η) w =
      ReducedTensorWords.gradedCoderivAlong G 1 U F' h w -
        ReducedTensorWords.ofLetter R B (η w) := by
  set H := ReducedTensorWords.gradedCoderivAlong G 1 U F' h
  set H' := ReducedTensorWords.gradedCoderivAlong G 1 U F'' (h - η)
  have hH := ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong G 1 hU hF' h
  have hH' := ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong G 1 hU hF'' (h - η)
  have hH_eq : ∀ u ∈ ReducedTensorWords.filtration R C n, H' u = H u := fun u hu ↦
    hH'.apply_eq_of_mem_filtration_of_apply_eq hH (fun _ _ ↦ rfl)
      (fun v hv ↦ hF_eq v (ReducedTensorWords.filtration_monotone R C (Nat.sub_le n 1) hv))
      (fun v hv ↦ by
        rw [← LinearMap.comp_apply (ReducedTensorWords.letter R B),
          ← LinearMap.comp_apply (ReducedTensorWords.letter R B),
          ReducedTensorWords.letter_comp_gradedCoderivAlong,
          ReducedTensorWords.letter_comp_gradedCoderivAlong,
          LinearMap.sub_apply, hη v hv, sub_zero])
      hu
  refine ReducedTensorWords.eq_of_deconcatenation_eq_of_letter_eq R B ?_ ?_
  · obtain ⟨t, ht⟩ := ReducedTensorWords.map_deconcatenation_filtration_succ_le R C n ⟨w, hw, rfl⟩
    have hdec : ReducedTensorWords.deconcatenation R B
        (H w - ReducedTensorWords.ofLetter R B (η w)) =
        ReducedTensorWords.deconcatenation R B (H w) := by
      rw [map_sub, ReducedTensorWords.deconcatenation_ofLetter]; abel
    rw [hdec, hH'.deconcatenation_apply, hH.deconcatenation_apply, ← ht]
    clear ht
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
        simp only [TensorProduct.mapIncl, TensorProduct.map_tmul, Submodule.coe_subtype,
          LinearMap.rTensor_tmul]
        rw [hH_eq _ x.2, hH_eq _ y.2, hF_eq _ y.2]
    | add x y hx hy =>
        simp only [map_add] at hx hy ⊢
        rw [add_add_add_comm, hx, hy, add_add_add_comm]
  · rw [map_sub, ReducedTensorWords.letter_ofLetter,
      ← LinearMap.comp_apply (ReducedTensorWords.letter R B),
      ← LinearMap.comp_apply (ReducedTensorWords.letter R B),
      ReducedTensorWords.letter_comp_gradedCoderivAlong,
      ReducedTensorWords.letter_comp_gradedCoderivAlong, LinearMap.sub_apply]

/-- Koszul twist commutation identities for `U`, `H`, and `barDifferential` on suspended words. -/
private theorem koszulTwist_one_identities
    {U H : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B}
    (hU₀ : LinearMap.IsHomogeneous U (ReducedTensorWords.gradedPiece (CC.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) 0)
    (hH₁ : LinearMap.IsHomogeneous H (ReducedTensorWords.gradedPiece (CC.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (-1)) :
    (∀ z, ReducedTensorWords.map (R := R) ((BB.grading.shift 1).koszulTwist 1) (U z) =
        U (ReducedTensorWords.map (R := R) ((CC.grading.shift 1).koszulTwist 1) z)) ∧
      (∀ z, ReducedTensorWords.map (R := R) ((BB.grading.shift 1).koszulTwist 1) (H z) =
        -H (ReducedTensorWords.map (R := R) ((CC.grading.shift 1).koszulTwist 1) z)) ∧
      (∀ z, ReducedTensorWords.map (R := R) ((CC.grading.shift 1).koszulTwist 1)
          (CC.barDifferential z) =
        -CC.barDifferential
          (ReducedTensorWords.map (R := R) ((CC.grading.shift 1).koszulTwist 1) z)) ∧
      (∀ z, ReducedTensorWords.map (R := R) ((CC.grading.shift 1).koszulTwist 1)
          (ReducedTensorWords.map (R := R) ((CC.grading.shift 1).koszulTwist 1) z) = z) := by
  refine ⟨fun z ↦ ?_, fun z ↦ ?_, fun z ↦ ?_, fun z ↦ ?_⟩
  · simpa only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.comp_apply] using LinearMap.congr_fun (hU₀.map_koszulTwist_comp 1) z
  · simpa only [one_mul, Int.negOnePow_neg, Int.negOnePow_one, Units.val_neg, Units.val_one,
      Int.cast_neg, Int.cast_one, neg_one_smul, LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (hH₁.map_koszulTwist_comp 1) z
  · simpa only [one_mul, Int.negOnePow_one, Units.val_neg, Units.val_one, Int.cast_neg,
      Int.cast_one, neg_one_smul, LinearMap.comp_apply, LinearMap.smul_apply] using
      LinearMap.congr_fun (CC.isHomogeneous_barDifferential.map_koszulTwist_comp 1) z
  · rw [← LinearMap.comp_apply, ← ReducedTensorWords.map_comp,
      InternalGrading.koszulTwist_comp_self, ReducedTensorWords.map_id, LinearMap.id_apply]

/-- When `F'` intertwines the bar differentials up to length `n` and `B₂ = F' - U + b_B H + H b_C`
vanishes up to length `n`, `B₂` sends words of length at most `n + 1` into single letters. -/
private theorem homotopyDefect_eq_ofLetter_of_mem_filtration_succ
    {U F' H : ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B}
    (hU : ReducedTensorWords.IsCoalgHom R U)
    (hU₀ : LinearMap.IsHomogeneous U (ReducedTensorWords.gradedPiece (CC.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) 0)
    (hUb : BB.barDifferential ∘ₗ U = U ∘ₗ CC.barDifferential)
    (hF' : ReducedTensorWords.IsCoalgHom R F')
    (hH : ReducedTensorWords.IsGradedCoderivationAlong (CC.grading.shift 1) 1 U F' H)
    (hH₁ : LinearMap.IsHomogeneous H (ReducedTensorWords.gradedPiece (CC.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) (-1))
    {n : ℕ}
    (hF'b : ∀ y ∈ ReducedTensorWords.filtration R C n,
      BB.barDifferential (F' y) = F' (CC.barDifferential y))
    (hB₂ : ∀ z ∈ ReducedTensorWords.filtration R C n,
      (F' - U + (BB.barDifferential ∘ₗ H + H ∘ₗ CC.barDifferential)) z = 0)
    {w : ReducedTensorWords R C} (hw : w ∈ ReducedTensorWords.filtration R C (n + 1)) :
    (F' - U + (BB.barDifferential ∘ₗ H + H ∘ₗ CC.barDifferential)) w =
      ReducedTensorWords.ofLetter R B
        (ReducedTensorWords.letter R B
          ((F' - U + (BB.barDifferential ∘ₗ H + H ∘ₗ CC.barDifferential)) w)) := by
  obtain ⟨hτU, hτH, hτb, hττ⟩ := koszulTwist_one_identities hU₀ hH₁
  have hUb' : ∀ z, BB.barDifferential (U z) = U (CC.barDifferential z) := LinearMap.congr_fun hUb
  have hB₂' : ∀ z ∈ ReducedTensorWords.filtration R C n,
      BB.barDifferential (H z) = U z - F' z - H (CC.barDifferential z) := fun z hz ↦ by
    have h0 := hB₂ z hz
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply] at h0
    exact eq_sub_of_add_eq (eq_sub_of_add_eq' (sub_eq_zero.1 (by rwa [sub_add_eq_add_sub] at h0)))
  refine ReducedTensorWords.eq_of_deconcatenation_eq_of_letter_eq R B ?_
    (ReducedTensorWords.letter_ofLetter R B _).symm
  obtain ⟨t, ht⟩ := ReducedTensorWords.map_deconcatenation_filtration_succ_le R C n ⟨w, hw, rfl⟩
  rw [ReducedTensorWords.deconcatenation_ofLetter]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add, map_sub]
  rw [hF'.deconcatenation_apply, hU.deconcatenation_apply,
    BB.isGradedCoderivation_barDifferential.deconcatenation_apply, hH.deconcatenation_apply,
    hH.deconcatenation_apply, CC.isGradedCoderivation_barDifferential.deconcatenation_apply, ← ht]
  clear ht
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
      simp only [TensorProduct.mapIncl, Submodule.coe_subtype, map_add, TensorProduct.map_tmul,
        LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
      simp only [hτU, hτH, hτb, hττ, hUb', hF'b y.1 y.2, map_neg, TensorProduct.neg_tmul]
      rw [hB₂' x.1 x.2, hB₂' y.1 y.2]
      simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel
  | add x y hx hy =>
      simp only [map_add] at hx hy ⊢
      convert congrArg₂ (· + ·) hx hy using 1 <;> abel

/-- Partial solution up to word length `n` for right lifting of `u : C ⟶ B` along `f : A ⟶ B`. -/
private structure MorphismLiftStep (f : AInfinityHom AA BB) (u : AInfinityHom CC BB) (n : ℕ) where
  g : ReducedTensorWords R C →ₗ[R] A
  h : ReducedTensorWords R C →ₗ[R] B
  hg : LinearMap.IsHomogeneous g (ReducedTensorWords.gradedPiece (CC.grading.shift 1))
    (AA.grading.shift 1).piece 0
  hh : LinearMap.IsHomogeneous h (ReducedTensorWords.gradedPiece (CC.grading.shift 1))
    (BB.grading.shift 1).piece (-1)
  hg_eq : ∀ z ∈ ReducedTensorWords.filtration R C n,
    (AA.barDifferential ∘ₗ ReducedTensorWords.coalgHom R g -
      ReducedTensorWords.coalgHom R g ∘ₗ CC.barDifferential) z = 0
  hh_eq : ∀ z ∈ ReducedTensorWords.filtration R C n,
    (f.barMap ∘ₗ ReducedTensorWords.coalgHom R g - u.barMap +
      (BB.barDifferential ∘ₗ
        ReducedTensorWords.gradedCoderivAlong (CC.grading.shift 1) 1 u.barMap
          (f.barMap ∘ₗ ReducedTensorWords.coalgHom R g) h +
      ReducedTensorWords.gradedCoderivAlong (CC.grading.shift 1) 1 u.barMap
        (f.barMap ∘ₗ ReducedTensorWords.coalgHom R g) h ∘ₗ CC.barDifferential)) z = 0

private noncomputable def MorphismLiftStep.defect₁ {f : AInfinityHom AA BB}
    {u : AInfinityHom CC BB} {n : ℕ} (s : MorphismLiftStep f u n) :
    ReducedTensorWords R C →ₗ[R] ReducedTensorWords R A :=
  AA.barDifferential ∘ₗ ReducedTensorWords.coalgHom R s.g -
    ReducedTensorWords.coalgHom R s.g ∘ₗ CC.barDifferential

private noncomputable def MorphismLiftStep.defect₂ {f : AInfinityHom AA BB}
    {u : AInfinityHom CC BB} {n : ℕ} (s : MorphismLiftStep f u n) :
    ReducedTensorWords R C →ₗ[R] ReducedTensorWords R B :=
  f.barMap ∘ₗ ReducedTensorWords.coalgHom R s.g - u.barMap +
    (BB.barDifferential ∘ₗ
        ReducedTensorWords.gradedCoderivAlong (CC.grading.shift 1) 1 u.barMap
          (f.barMap ∘ₗ ReducedTensorWords.coalgHom R s.g) s.h +
      ReducedTensorWords.gradedCoderivAlong (CC.grading.shift 1) 1 u.barMap
        (f.barMap ∘ₗ ReducedTensorWords.coalgHom R s.g) s.h ∘ₗ CC.barDifferential)

/-- Global algebraic commutator identities for the morphism and homotopy defects of a
`MorphismLiftStep`. -/
private theorem morphismLiftStep_commutators {f : AInfinityHom AA BB} {u : AInfinityHom CC BB}
    {n : ℕ} (s : MorphismLiftStep f u n) :
    AA.barDifferential ∘ₗ s.defect₁ + s.defect₁ ∘ₗ CC.barDifferential = 0 ∧
      BB.barDifferential ∘ₗ s.defect₂ - s.defect₂ ∘ₗ CC.barDifferential =
        f.barMap ∘ₗ s.defect₁ := by
  let G := ReducedTensorWords.coalgHom R s.g
  let H := ReducedTensorWords.gradedCoderivAlong (CC.grading.shift 1) 1 u.barMap
    (f.barMap ∘ₗ G) s.h
  have hbA : AA.barDifferential ∘ₗ AA.barDifferential ∘ₗ G = 0 := by
    rw [← LinearMap.comp_assoc, AA.barDifferential_sq, LinearMap.zero_comp]
  have hbB : BB.barDifferential ∘ₗ BB.barDifferential ∘ₗ H = 0 := by
    rw [← LinearMap.comp_assoc, BB.barDifferential_sq, LinearMap.zero_comp]
  have hfG : BB.barDifferential ∘ₗ f.barMap ∘ₗ G = f.barMap ∘ₗ AA.barDifferential ∘ₗ G := by
    rw [← LinearMap.comp_assoc, f.barDifferential_comp_barMap, LinearMap.comp_assoc]
  refine ⟨?_, ?_⟩
  · simp only [MorphismLiftStep.defect₁, G, LinearMap.comp_sub, LinearMap.sub_comp,
      LinearMap.comp_assoc, hbA, CC.barDifferential_sq, LinearMap.comp_zero]
    abel
  · simp only [MorphismLiftStep.defect₂, MorphismLiftStep.defect₁, G, H, LinearMap.comp_add,
      LinearMap.add_comp, LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_assoc, hbB,
      CC.barDifferential_sq, LinearMap.comp_zero, hfG, u.barDifferential_comp_barMap]
    abel

/-- Single-letter values on `filtration R C (n + 1)` and homogeneity for the defects `s.defect₁`
and `s.defect₂` of a `MorphismLiftStep`. -/
private theorem morphismLiftStep_defects {f : AInfinityHom AA BB} {u : AInfinityHom CC BB}
    {n : ℕ} (s : MorphismLiftStep f u n) :
    (∀ w ∈ ReducedTensorWords.filtration R C (n + 1),
      s.defect₁ w = ReducedTensorWords.ofLetter R A (ReducedTensorWords.letter R A (s.defect₁ w))) ∧
    (∀ w ∈ ReducedTensorWords.filtration R C (n + 1),
      s.defect₂ w = ReducedTensorWords.ofLetter R B (ReducedTensorWords.letter R B (s.defect₂ w))) ∧
    LinearMap.IsHomogeneous s.defect₁ (ReducedTensorWords.gradedPiece (CC.grading.shift 1))
      (ReducedTensorWords.gradedPiece (AA.grading.shift 1)) 1 ∧
    LinearMap.IsHomogeneous s.defect₂ (ReducedTensorWords.gradedPiece (CC.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) 0 := by
  let G := ReducedTensorWords.coalgHom R s.g
  have hG_hom := ReducedTensorWords.isHomogeneous_coalgHom s.hg
  have hFG_hom : LinearMap.IsHomogeneous (f.barMap ∘ₗ G)
      (ReducedTensorWords.gradedPiece (CC.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) 0 := by
    simpa only [add_zero] using f.isHomogeneous_barMap.comp hG_hom
  have hH_hom := ReducedTensorWords.isHomogeneous_gradedCoderivAlong (q := 1) u.isHomogeneous_barMap
    hFG_hom s.hh
  have hB₁_cod : ReducedTensorWords.IsGradedCoderivationAlong (CC.grading.shift 1) 1 G G
      s.defect₁ := by
    have hEq : s.defect₁ =
        AA.barDifferential ∘ₗ G + (-1 : R) • (G ∘ₗ CC.barDifferential) :=
      LinearMap.ext fun z ↦ by
        simp only [MorphismLiftStep.defect₁, G, LinearMap.sub_apply, LinearMap.add_apply,
          LinearMap.smul_apply, neg_one_smul]
        abel
    rw [hEq]
    exact (AA.isGradedCoderivation_barDifferential.comp_isCoalgHom
      (ReducedTensorWords.isCoalgHom_coalgHom s.g) hG_hom).add
      (((ReducedTensorWords.isCoalgHom_coalgHom s.g).comp_isGradedCoderivation
        CC.isGradedCoderivation_barDifferential).smul (-1))
  have hB₁_hom : LinearMap.IsHomogeneous s.defect₁
      (ReducedTensorWords.gradedPiece (CC.grading.shift 1))
      (ReducedTensorWords.gradedPiece (AA.grading.shift 1)) 1 :=
    LinearMap.IsHomogeneous.sub
      (by simpa only [zero_add] using AA.isHomogeneous_barDifferential.comp hG_hom)
      (by simpa only [add_zero] using hG_hom.comp CC.isHomogeneous_barDifferential)
  have hB₂_hom : LinearMap.IsHomogeneous s.defect₂
      (ReducedTensorWords.gradedPiece (CC.grading.shift 1))
      (ReducedTensorWords.gradedPiece (BB.grading.shift 1)) 0 :=
    LinearMap.IsHomogeneous.add (hFG_hom.sub u.isHomogeneous_barMap)
      (LinearMap.IsHomogeneous.add
        (by simpa only [neg_add_cancel] using BB.isHomogeneous_barDifferential.comp hH_hom)
        (by simpa only [add_neg_cancel] using hH_hom.comp CC.isHomogeneous_barDifferential))
  refine ⟨fun _ hw ↦ hB₁_cod.apply_eq_ofLetter_of_mem_filtration_succ s.hg_eq hw,
    fun _ hw ↦ homotopyDefect_eq_ofLetter_of_mem_filtration_succ u.isCoalgHom_barMap
      u.isHomogeneous_barMap u.barDifferential_comp_barMap
      (f.isCoalgHom_barMap.comp (ReducedTensorWords.isCoalgHom_coalgHom s.g))
      (ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong _ 1 u.isCoalgHom_barMap
        (f.isCoalgHom_barMap.comp (ReducedTensorWords.isCoalgHom_coalgHom s.g)) s.h)
      hH_hom
      (fun y hy ↦ by
        have hy' := s.hg_eq y hy
        simp only [LinearMap.sub_apply, LinearMap.comp_apply] at hy'
        rw [LinearMap.comp_apply, LinearMap.comp_apply, f.barDifferential_barMap,
          sub_eq_zero.1 hy'])
      s.hh_eq hw,
    hB₁_hom, hB₂_hom⟩

/-- Coupled obstruction equations for the length-`n + 1` projected defects `Φ` and `Ψ` of a
`MorphismLiftStep`. -/
private theorem morphismLiftStep_obstruction_eq {f : AInfinityHom AA BB} {u : AInfinityHom CC BB}
    {n : ℕ} (s : MorphismLiftStep f u n) :
    let π := ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩
    let Φ := (ReducedTensorWords.letter R A ∘ₗ s.defect₁) ∘ₗ π
    let Ψ := (ReducedTensorWords.letter R B ∘ₗ s.defect₂) ∘ₗ π
    (AA.differential ∘ₗ Φ + (1 : R) • (Φ ∘ₗ CC.unaryBarDifferential) = 0) ∧
      (BB.differential ∘ₗ Ψ - (1 : R) • (Ψ ∘ₗ CC.unaryBarDifferential) = f.linearPart ∘ₗ Φ) := by
  intro π Φ Ψ
  obtain ⟨hcomm₁, hcomm₂⟩ := morphismLiftStep_commutators s
  obtain ⟨hB₁_let, hB₂_let, _, _⟩ := morphismLiftStep_defects s
  refine ⟨LinearMap.ext fun z ↦ ?_, LinearMap.ext fun z ↦ ?_⟩
  · have hw := ReducedTensorWords.lengthProj_mem_filtration R C ⟨n + 1, n.succ_pos⟩ z
    have hhigh : s.defect₁ (CC.higherBarDifferential (π z)) = 0 :=
      s.hg_eq _ (CC.higherBarDifferential_filtration n ⟨π z, hw, rfl⟩)
    have key := congrArg (ReducedTensorWords.letter R A) (LinearMap.congr_fun hcomm₁ (π z))
    rw [LinearMap.zero_apply, map_zero, LinearMap.add_apply, map_add, LinearMap.comp_apply,
      hB₁_let _ hw, AA.barDifferential_ofLetter, ReducedTensorWords.letter_ofLetter,
      ← AA.differential_apply, LinearMap.comp_apply, CC.barDifferential_eq_unary_add_higher,
      LinearMap.add_apply, map_add, map_add, hhigh, map_zero, add_zero] at key
    change AA.differential ((ReducedTensorWords.letter R A ∘ₗ s.defect₁) (π z)) +
        (ReducedTensorWords.letter R A ∘ₗ s.defect₁) (CC.unaryBarDifferential (π z)) = 0 at key
    rw [taylor_lengthProj_unaryBarDifferential CC
      (ReducedTensorWords.letter R A ∘ₗ s.defect₁)] at key
    simpa only [Φ, π, one_smul, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.zero_apply] using key
  · have hw := ReducedTensorWords.lengthProj_mem_filtration R C ⟨n + 1, n.succ_pos⟩ z
    have hhigh : s.defect₂ (CC.higherBarDifferential (π z)) = 0 :=
      s.hh_eq _ (CC.higherBarDifferential_filtration n ⟨π z, hw, rfl⟩)
    have key := congrArg (ReducedTensorWords.letter R B) (LinearMap.congr_fun hcomm₂ (π z))
    rw [LinearMap.sub_apply, map_sub, LinearMap.comp_apply, hB₂_let _ hw,
      BB.barDifferential_ofLetter, ReducedTensorWords.letter_ofLetter, ← BB.differential_apply,
      LinearMap.comp_apply, CC.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
      map_add, hhigh, map_zero, add_zero, LinearMap.comp_apply, hB₁_let _ hw, barMap_ofLetter,
      ReducedTensorWords.letter_ofLetter] at key
    change BB.differential ((ReducedTensorWords.letter R B ∘ₗ s.defect₂) (π z)) -
        (ReducedTensorWords.letter R B ∘ₗ s.defect₂) (CC.unaryBarDifferential (π z)) =
        f.linearPart ((ReducedTensorWords.letter R A ∘ₗ s.defect₁) (π z)) at key
    rw [taylor_lengthProj_unaryBarDifferential CC
      (ReducedTensorWords.letter R B ∘ₗ s.defect₂)] at key
    simpa only [Φ, Ψ, π, one_smul, LinearMap.sub_apply, LinearMap.comp_apply] using key

/-- Verification of `hg_eq` on `filtration R C (n + 1)` after subtracting an obstruction lift `γ`.
-/
private theorem morphismLiftStep_hg_succ {f : AInfinityHom AA BB} {u : AInfinityHom CC BB}
    {n : ℕ} (s : MorphismLiftStep f u n) {γ : ReducedTensorWords R C →ₗ[R] A}
    (hγ₀ : ∀ z ∈ ReducedTensorWords.filtration R C n, γ z = 0)
    (hγ_eq : AA.differential ∘ₗ γ - (1 : R) • (γ ∘ₗ CC.unaryBarDifferential) =
      (ReducedTensorWords.letter R A ∘ₗ s.defect₁) ∘ₗ
        ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩)
    {w : ReducedTensorWords R C} (hw : w ∈ ReducedTensorWords.filtration R C (n + 1)) :
    (AA.barDifferential ∘ₗ ReducedTensorWords.coalgHom R (s.g - γ) -
      ReducedTensorWords.coalgHom R (s.g - γ) ∘ₗ CC.barDifferential) w = 0 := by
  set G := ReducedTensorWords.coalgHom R s.g
  obtain ⟨hB₁_let, _, _, _⟩ := morphismLiftStep_defects s
  have hGw := coalgHom_sub_apply_of_mem_filtration_succ (CC.grading.shift 1) s.g hγ₀ hw
  have hGbw := coalgHom_sub_apply_of_mem_filtration_succ (CC.grading.shift 1) s.g hγ₀
    (CC.barDifferential_mem_filtration hw)
  have hγb : γ (CC.barDifferential w) = γ (CC.unaryBarDifferential w) := by
    rw [CC.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
      hγ₀ _ (CC.higherBarDifferential_filtration n ⟨w, hw, rfl⟩), add_zero]
  have h₀ : ∀ v ∈ ReducedTensorWords.filtration R C n,
      (ReducedTensorWords.letter R A ∘ₗ s.defect₁) v = 0 := fun v hv ↦ by
    rw [LinearMap.comp_apply, MorphismLiftStep.defect₁, s.hg_eq v hv, map_zero]
  have hΦw := ReducedTensorWords.apply_lengthProj_of_mem_filtration R C h₀ hw
  have hγ_w := LinearMap.congr_fun hγ_eq w
  simp only [one_smul, LinearMap.sub_apply, LinearMap.comp_apply] at hγ_w hΦw
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, hGw, hGbw, map_sub,
    AA.barDifferential_ofLetter, ← AA.differential_apply, hγb,
    show AA.barDifferential (G w) - ReducedTensorWords.ofLetter R A (AA.differential (γ w)) -
        (G (CC.barDifferential w) -
          ReducedTensorWords.ofLetter R A (γ (CC.unaryBarDifferential w))) =
      s.defect₁ w - (ReducedTensorWords.ofLetter R A (AA.differential (γ w)) -
        ReducedTensorWords.ofLetter R A (γ (CC.unaryBarDifferential w))) by
      simp only [MorphismLiftStep.defect₁, G, LinearMap.sub_apply, LinearMap.comp_apply]; abel,
    ← map_sub, hγ_w, hΦw, ← hB₁_let w hw, sub_self]

/-- Verification of `hh_eq` on `filtration R C (n + 1)` after subtracting `(γ, η)`. -/
private theorem morphismLiftStep_hh_succ {f : AInfinityHom AA BB} {u : AInfinityHom CC BB}
    {n : ℕ} (s : MorphismLiftStep f u n)
    {γ : ReducedTensorWords R C →ₗ[R] A} {η : ReducedTensorWords R C →ₗ[R] B}
    (hγ₀ : ∀ z ∈ ReducedTensorWords.filtration R C n, γ z = 0)
    (hη₀ : ∀ z ∈ ReducedTensorWords.filtration R C n, η z = 0)
    (hη_eq : f.linearPart ∘ₗ γ +
        (BB.differential ∘ₗ η + (1 : R) • (η ∘ₗ CC.unaryBarDifferential)) =
      (ReducedTensorWords.letter R B ∘ₗ s.defect₂) ∘ₗ
        ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩)
    {w : ReducedTensorWords R C} (hw : w ∈ ReducedTensorWords.filtration R C (n + 1)) :
    (f.barMap ∘ₗ ReducedTensorWords.coalgHom R (s.g - γ) - u.barMap +
      (BB.barDifferential ∘ₗ
        ReducedTensorWords.gradedCoderivAlong (CC.grading.shift 1) 1 u.barMap
          (f.barMap ∘ₗ ReducedTensorWords.coalgHom R (s.g - γ)) (s.h - η) +
      ReducedTensorWords.gradedCoderivAlong (CC.grading.shift 1) 1 u.barMap
        (f.barMap ∘ₗ ReducedTensorWords.coalgHom R (s.g - γ)) (s.h - η) ∘ₗ
        CC.barDifferential)) w = 0 := by
  set G := ReducedTensorWords.coalgHom R s.g
  set H := ReducedTensorWords.gradedCoderivAlong (CC.grading.shift 1) 1 u.barMap (f.barMap ∘ₗ G) s.h
  obtain ⟨_, hB₂_let, _, _⟩ := morphismLiftStep_defects s
  have hG_eq_n : ∀ v ∈ ReducedTensorWords.filtration R C n,
      (f.barMap ∘ₗ ReducedTensorWords.coalgHom R (s.g - γ)) v = (f.barMap ∘ₗ G) v := fun v hv ↦
    congrArg f.barMap <| (ReducedTensorWords.isCoalgHom_coalgHom _).apply_eq_of_mem_filtration
      (ReducedTensorWords.isCoalgHom_coalgHom _)
      (fun y hy ↦ by
        rw [← LinearMap.comp_apply (ReducedTensorWords.letter R A),
          ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
          ReducedTensorWords.letter_comp_coalgHom, ReducedTensorWords.letter_comp_coalgHom,
          LinearMap.sub_apply, hγ₀ y hy, sub_zero]) hv
  have hGw := coalgHom_sub_apply_of_mem_filtration_succ (CC.grading.shift 1) s.g hγ₀ hw
  have hHw := gradedCoderivAlong_sub_apply_of_mem_filtration_succ (CC.grading.shift 1)
    u.isCoalgHom_barMap
    (f.isCoalgHom_barMap.comp (ReducedTensorWords.isCoalgHom_coalgHom s.g))
    (f.isCoalgHom_barMap.comp (ReducedTensorWords.isCoalgHom_coalgHom (s.g - γ)))
    s.h hG_eq_n hη₀ hw
  have hHbw := gradedCoderivAlong_sub_apply_of_mem_filtration_succ (CC.grading.shift 1)
    u.isCoalgHom_barMap
    (f.isCoalgHom_barMap.comp (ReducedTensorWords.isCoalgHom_coalgHom s.g))
    (f.isCoalgHom_barMap.comp (ReducedTensorWords.isCoalgHom_coalgHom (s.g - γ)))
    s.h hG_eq_n hη₀ (CC.barDifferential_mem_filtration hw)
  have hηb : η (CC.barDifferential w) = η (CC.unaryBarDifferential w) := by
    rw [CC.barDifferential_eq_unary_add_higher, LinearMap.add_apply, map_add,
      hη₀ _ (CC.higherBarDifferential_filtration n ⟨w, hw, rfl⟩), add_zero]
  have h₀ : ∀ v ∈ ReducedTensorWords.filtration R C n,
      (ReducedTensorWords.letter R B ∘ₗ s.defect₂) v = 0 := fun v hv ↦ by
    rw [LinearMap.comp_apply, MorphismLiftStep.defect₂, s.hh_eq v hv, map_zero]
  have hΨw := ReducedTensorWords.apply_lengthProj_of_mem_filtration R C h₀ hw
  have hη_w := LinearMap.congr_fun hη_eq w
  simp only [one_smul, LinearMap.add_apply, LinearMap.comp_apply] at hη_w hΨw
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  rw [hGw, hHw, hHbw, map_sub, map_sub, barMap_ofLetter, BB.barDifferential_ofLetter,
    ← BB.differential_apply, hηb,
    show f.barMap (G w) - ReducedTensorWords.ofLetter R B (f.linearPart (γ w)) - u.barMap w +
        (BB.barDifferential (H w) - ReducedTensorWords.ofLetter R B (BB.differential (η w)) +
          (H (CC.barDifferential w) -
            ReducedTensorWords.ofLetter R B (η (CC.unaryBarDifferential w)))) =
      s.defect₂ w - (ReducedTensorWords.ofLetter R B (f.linearPart (γ w)) +
        (ReducedTensorWords.ofLetter R B (BB.differential (η w)) +
          ReducedTensorWords.ofLetter R B (η (CC.unaryBarDifferential w)))) by
      simp only [MorphismLiftStep.defect₂, G, H, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.comp_apply]
      abel,
    ← map_add, ← map_add, hη_w, hΨw, ← hB₂_let w hw, sub_self]

/-- Inductive step `n ↦ n + 1` for `MorphismLiftStep`, with stabilization on `filtration R C n`. -/
private noncomputable def morphismLiftStepSucc
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    (he : e.IsGraded AA.grading.piece BB.grading.piece 1)
    {f : AInfinityHom AA BB} (hf : e.hom = f.linearPart)
    (u : AInfinityHom CC BB) {n : ℕ} (s : MorphismLiftStep f u n) :
    {s' : MorphismLiftStep f u (n + 1) //
      (∀ z ∈ ReducedTensorWords.filtration R C n, s'.g z = s.g z) ∧
      (∀ z ∈ ReducedTensorWords.filtration R C n, s'.h z = s.h z)} := by
  set π := ReducedTensorWords.lengthProj R C ⟨n + 1, n.succ_pos⟩
  set Φ := (ReducedTensorWords.letter R A ∘ₗ s.defect₁) ∘ₗ π
  set Ψ := (ReducedTensorWords.letter R B ∘ₗ s.defect₂) ∘ₗ π
  obtain ⟨_, _, hB₁_hom, hB₂_hom⟩ := morphismLiftStep_defects s
  obtain ⟨hΦ_eq, hΨ_eq⟩ := morphismLiftStep_obstruction_eq s
  rw [← hf] at hΨ_eq
  have he' := isGraded_shift_one he
  have hΦ_hom : LinearMap.IsHomogeneous Φ (ReducedTensorWords.gradedPiece (CC.grading.shift 1))
      (AA.grading.shift 1).piece (0 + 1) := by
    simpa only [Φ, π, zero_add, add_zero] using
      ((ReducedTensorWords.isHomogeneous_letter (AA.grading.shift 1)).comp hB₁_hom).comp
        (ReducedTensorWords.isHomogeneous_lengthProj (CC.grading.shift 1) ⟨n + 1, n.succ_pos⟩)
  have hΨ_hom : LinearMap.IsHomogeneous Ψ (ReducedTensorWords.gradedPiece (CC.grading.shift 1))
      (BB.grading.shift 1).piece 0 := by
    simpa only [Ψ, π, zero_add] using
      ((ReducedTensorWords.isHomogeneous_letter (BB.grading.shift 1)).comp hB₂_hom).comp
        (ReducedTensorWords.isHomogeneous_lengthProj (CC.grading.shift 1) ⟨n + 1, n.succ_pos⟩)
  set γ := e.obstructionLift Φ Ψ
  set η := e.obstructionHomotopy Φ Ψ
  have hγ₀ : ∀ z ∈ ReducedTensorWords.filtration R C n, γ z = 0 := fun _ hz ↦
    ReducedTensorWords.apply_eq_zero_of_comp_lengthProj_succ_eq
      (by rw [e.obstructionLift_comp, ReducedTensorWords.comp_lengthProj_comp_lengthProj,
        ReducedTensorWords.comp_lengthProj_comp_lengthProj]) hz
  have hη₀ : ∀ z ∈ ReducedTensorWords.filtration R C n, η z = 0 := fun _ hz ↦
    ReducedTensorWords.apply_eq_zero_of_comp_lengthProj_succ_eq
      (by rw [e.obstructionHomotopy_comp, ReducedTensorWords.comp_lengthProj_comp_lengthProj,
        ReducedTensorWords.comp_lengthProj_comp_lengthProj]) hz
  have hη_eq := e.hom_comp_obstructionLift_add hΦ_eq hΨ_eq
  rw [hf] at hη_eq
  exact ⟨⟨s.g - γ, s.h - η,
      s.hg.sub (e.isHomogeneous_obstructionLift he' hΦ_hom hΨ_hom),
      s.hh.sub (by simpa only [zero_sub] using
        e.isHomogeneous_obstructionHomotopy he' hΦ_hom hΨ_hom),
      fun _ hw ↦ morphismLiftStep_hg_succ s hγ₀ (e.dM_comp_obstructionLift_sub hΦ_eq hΨ_eq) hw,
      fun _ hw ↦ morphismLiftStep_hh_succ s hγ₀ hη₀ hη_eq hw⟩,
    fun z hz ↦ by rw [LinearMap.sub_apply, hγ₀ z hz, sub_zero],
    fun z hz ↦ by rw [LinearMap.sub_apply, hη₀ z hz, sub_zero]⟩

/-- Sequence of partial lifts `MorphismLiftStep f u n` constructed by iterating
`morphismLiftStepSucc`. -/
private noncomputable def morphismLiftSeq
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    (he : e.IsGraded AA.grading.piece BB.grading.piece 1)
    {f : AInfinityHom AA BB} (hf : e.hom = f.linearPart)
    (u : AInfinityHom CC BB) : ∀ n, MorphismLiftStep f u n :=
  Nat.rec
    { g := 0
      h := 0
      hg := LinearMap.isHomogeneous_zero _ _ 0
      hh := LinearMap.isHomogeneous_zero _ _ (-1)
      hg_eq := ReducedTensorWords.apply_eq_zero_of_mem_filtration_zero R C _
      hh_eq := ReducedTensorWords.apply_eq_zero_of_mem_filtration_zero R C _ }
    fun _ s ↦ (morphismLiftStepSucc e he hf u s).1

private theorem morphismLiftSeq_g_succ
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    (he : e.IsGraded AA.grading.piece BB.grading.piece 1)
    {f : AInfinityHom AA BB} (hf : e.hom = f.linearPart)
    (u : AInfinityHom CC BB) (n : ℕ) :
    ∀ z ∈ ReducedTensorWords.filtration R C n,
      (morphismLiftSeq e he hf u (n + 1)).g z = (morphismLiftSeq e he hf u n).g z :=
  (morphismLiftStepSucc e he hf u (morphismLiftSeq e he hf u n)).2.1

private theorem morphismLiftSeq_h_succ
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    (he : e.IsGraded AA.grading.piece BB.grading.piece 1)
    {f : AInfinityHom AA BB} (hf : e.hom = f.linearPart)
    (u : AInfinityHom CC BB) (n : ℕ) :
    ∀ z ∈ ReducedTensorWords.filtration R C n,
      (morphismLiftSeq e he hf u (n + 1)).h z = (morphismLiftSeq e he hf u n).h z :=
  (morphismLiftStepSucc e he hf u (morphismLiftSeq e he hf u n)).2.2

private theorem coalgHom_assembleFiltration_apply_of_mem_filtration
    {t : ℕ → ReducedTensorWords R C →ₗ[R] A}
    (ht : ∀ n, ∀ z ∈ ReducedTensorWords.filtration R C n, t (n + 1) z = t n z)
    {n : ℕ} {z : ReducedTensorWords R C} (hz : z ∈ ReducedTensorWords.filtration R C n) :
    ReducedTensorWords.coalgHom R (ReducedTensorWords.assembleFiltration t) z =
      ReducedTensorWords.coalgHom R (t n) z :=
  (ReducedTensorWords.isCoalgHom_coalgHom _).apply_eq_of_mem_filtration
    (ReducedTensorWords.isCoalgHom_coalgHom _)
    (fun _ hw ↦ by
      rw [← LinearMap.comp_apply (ReducedTensorWords.letter R A),
        ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
        ReducedTensorWords.letter_comp_coalgHom, ReducedTensorWords.letter_comp_coalgHom,
        ReducedTensorWords.assembleFiltration_apply_of_mem_filtration ht hw]) hz

/-- **Right lifting of an `A∞` morphism** along `f : A ⟶ B` when `f₁` extends to a graded
`LinearHomotopyEquiv`: for any `u : C ⟶ B`, `liftRight` is an `A∞` morphism `C ⟶ A` such that
`f ∘ liftRight` is homotopic to `u` (`liftRightHomotopy`). -/
noncomputable def liftRight (e : LinearHomotopyEquiv AA.differential BB.differential)
    (he : e.IsGraded AA.grading.piece BB.grading.piece 1)
    {f : AInfinityHom AA BB} (hf : e.hom = f.linearPart) (u : AInfinityHom CC BB) :
    AInfinityHom CC AA := by
  let seq := morphismLiftSeq e he hf u
  let g_tay := ReducedTensorWords.assembleFiltration fun n ↦ (seq n).g
  have hstabG := morphismLiftSeq_g_succ e he hf u
  refine ofTaylor g_tay (ReducedTensorWords.isHomogeneous_assembleFiltration fun n ↦ (seq n).hg) ?_
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := ReducedTensorWords.exists_mem_filtration R C z
  have key := congrArg (ReducedTensorWords.letter R A) ((seq n).hg_eq z hn)
  rw [LinearMap.sub_apply, map_sub, map_zero, sub_eq_zero, LinearMap.comp_apply,
    ← LinearMap.comp_apply (ReducedTensorWords.letter R A), AA.letter_comp_barDifferential,
    LinearMap.comp_apply, ← LinearMap.comp_apply (ReducedTensorWords.letter R A),
    ReducedTensorWords.letter_comp_coalgHom] at key
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    coalgHom_assembleFiltration_apply_of_mem_filtration hstabG hn, key,
    ReducedTensorWords.assembleFiltration_apply_of_mem_filtration hstabG
      (CC.barDifferential_mem_filtration hn)]

private theorem barMap_liftRight_apply_of_mem_filtration
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    (he : e.IsGraded AA.grading.piece BB.grading.piece 1)
    {f : AInfinityHom AA BB} (hf : e.hom = f.linearPart) (u : AInfinityHom CC BB)
    {n : ℕ} {z : ReducedTensorWords R C} (hz : z ∈ ReducedTensorWords.filtration R C n) :
    (liftRight e he hf u).barMap z =
      ReducedTensorWords.coalgHom R (morphismLiftSeq e he hf u n).g z := by
  rw [liftRight, barMap_ofTaylor]
  exact coalgHom_assembleFiltration_apply_of_mem_filtration (morphismLiftSeq_g_succ e he hf u) hz

private theorem liftRightHomotopy_coderiv_eq
    (e : LinearHomotopyEquiv AA.differential BB.differential)
    (he : e.IsGraded AA.grading.piece BB.grading.piece 1)
    {f : AInfinityHom AA BB} (hf : e.hom = f.linearPart) (u : AInfinityHom CC BB)
    {n : ℕ} {z : ReducedTensorWords R C} (hn : z ∈ ReducedTensorWords.filtration R C n) :
    ReducedTensorWords.gradedCoderivAlong (CC.grading.shift 1) 1 u.barMap
        (f.comp (liftRight e he hf u)).barMap
        (ReducedTensorWords.assembleFiltration fun k ↦ (morphismLiftSeq e he hf u k).h) z =
      ReducedTensorWords.gradedCoderivAlong (CC.grading.shift 1) 1 u.barMap
        (f.barMap ∘ₗ ReducedTensorWords.coalgHom R (morphismLiftSeq e he hf u n).g)
        (morphismLiftSeq e he hf u n).h z :=
  (ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong _ 1 u.isCoalgHom_barMap
    (f.comp (liftRight e he hf u)).isCoalgHom_barMap _).apply_eq_of_mem_filtration_of_apply_eq
    (ReducedTensorWords.isGradedCoderivationAlong_gradedCoderivAlong _ 1 u.isCoalgHom_barMap
      (f.isCoalgHom_barMap.comp
        (ReducedTensorWords.isCoalgHom_coalgHom (morphismLiftSeq e he hf u n).g))
      (morphismLiftSeq e he hf u n).h)
    (fun _ _ ↦ rfl)
    (fun v hv ↦ by
      rw [barMap_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        barMap_liftRight_apply_of_mem_filtration e he hf u
          (ReducedTensorWords.filtration_monotone R C (Nat.sub_le n 1) hv)])
    (fun _ hw ↦ by
      rw [← LinearMap.comp_apply (ReducedTensorWords.letter R B),
        ← LinearMap.comp_apply (ReducedTensorWords.letter R B),
        ReducedTensorWords.letter_comp_gradedCoderivAlong,
        ReducedTensorWords.letter_comp_gradedCoderivAlong,
        ReducedTensorWords.assembleFiltration_apply_of_mem_filtration
          (morphismLiftSeq_h_succ e he hf u) hw]) hn

/-- The homotopy `u ⇒ f ∘ liftRight` witnessing that `liftRight` lifts `u` along `f`. -/
noncomputable def liftRightHomotopy (e : LinearHomotopyEquiv AA.differential BB.differential)
    (he : e.IsGraded AA.grading.piece BB.grading.piece 1)
    {f : AInfinityHom AA BB} (hf : e.hom = f.linearPart) (u : AInfinityHom CC BB) :
    Homotopy u (f.comp (liftRight e he hf u)) := by
  let seq := morphismLiftSeq e he hf u
  let g := liftRight e he hf u
  let h_tay := ReducedTensorWords.assembleFiltration fun n ↦ (seq n).h
  refine Homotopy.ofTaylor h_tay
    (ReducedTensorWords.isHomogeneous_assembleFiltration fun n ↦ (seq n).hh)
    (LinearMap.ext fun z ↦ ?_)
  obtain ⟨n, hn⟩ := ReducedTensorWords.exists_mem_filtration R C z
  have h1 : ReducedTensorWords.letter R B
      (f.barMap (ReducedTensorWords.coalgHom R (seq n).g z)) = (f.comp g).taylor z := by
    rw [← barMap_liftRight_apply_of_mem_filtration e he hf u hn, ← LinearMap.comp_apply f.barMap,
      ← barMap_comp f g, ← LinearMap.comp_apply (ReducedTensorWords.letter R B), ← taylor_def]
  have h2 : ReducedTensorWords.letter R B
      (BB.barDifferential (ReducedTensorWords.gradedCoderivAlong (CC.grading.shift 1) 1 u.barMap
        (f.barMap ∘ₗ ReducedTensorWords.coalgHom R (seq n).g) (seq n).h z)) =
      BB.taylor (ReducedTensorWords.gradedCoderivAlong (CC.grading.shift 1) 1 u.barMap
        (f.comp g).barMap h_tay z) := by
    rw [← liftRightHomotopy_coderiv_eq e he hf u hn,
      ← LinearMap.comp_apply (ReducedTensorWords.letter R B) BB.barDifferential,
      BB.letter_comp_barDifferential]
  have h3 : ReducedTensorWords.letter R B
      (ReducedTensorWords.gradedCoderivAlong (CC.grading.shift 1) 1 u.barMap
        (f.barMap ∘ₗ ReducedTensorWords.coalgHom R (seq n).g) (seq n).h (CC.barDifferential z)) =
      h_tay (CC.barDifferential z) := by
    rw [← LinearMap.comp_apply (ReducedTensorWords.letter R B),
      ReducedTensorWords.letter_comp_gradedCoderivAlong,
      ReducedTensorWords.assembleFiltration_apply_of_mem_filtration
        (morphismLiftSeq_h_succ e he hf u) (CC.barDifferential_mem_filtration hn)]
  have key := congrArg (ReducedTensorWords.letter R B) ((seq n).hh_eq z hn)
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add, map_sub,
    map_zero] at key
  rw [h1, h2, h3, ← LinearMap.comp_apply (ReducedTensorWords.letter R B) u.barMap,
    ← taylor_def] at key
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply]
  calc
    u.taylor z - (f.comp g).taylor z
      = (u.taylor z - (f.comp g).taylor z) +
          ((f.comp g).taylor z - u.taylor z +
            (BB.taylor (ReducedTensorWords.gradedCoderivAlong (CC.grading.shift 1) 1 u.barMap
              (f.comp g).barMap h_tay z) + h_tay (CC.barDifferential z))) := by rw [key, add_zero]
    _ = BB.taylor (ReducedTensorWords.gradedCoderivAlong (CC.grading.shift 1) 1 u.barMap
          (f.comp g).barMap h_tay z) + h_tay (CC.barDifferential z) := by abel

end AInfinityHom

end TauCeti
