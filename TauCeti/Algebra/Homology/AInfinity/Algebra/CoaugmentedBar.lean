/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra
public import TauCeti.LinearAlgebra.TensorCoalgebra.CoaugmentedGradedCoderivation

/-!
# The bar coderivation of the coaugmented tensor coalgebra

`TauCeti.AInfinityAlgebra.barDifferential` is the square-zero coderivation of the *reduced* tensor
coalgebra, and the Stasheff identities are read off from it.  The module and bimodule theories
need one step more: a right module is a coderivation over `b` on the cofree right bar comodule,
and a bimodule a bicomodule coderivation, so in both cases `b` has to be available as a coderivation
of the *coaugmented* tensor coalgebra, which also carries the empty word.

This file supplies that extension.  The empty word is annihilated, and the coproduct of a word of
positive length is its two degenerate cuts together with the reduced coproduct, so the graded
co-Leibniz identity on the coaugmented coalgebra reduces to the one already known on the reduced
coalgebra: the extended coderivation is a degree-one
`TauCeti.TensorWords.IsGradedCoderivation` of cohomological degree one, its square is zero, and it
raises the total letter degree by one.  The letterwise Koszul twist of the suspension grading fixes
the empty word, which is what makes the twisted term of the identity agree with the reduced one.

The coaugmented co-Leibniz identity itself, the letterwise maps, and the total-letter-degree pieces
are in `TauCeti.LinearAlgebra.TensorCoalgebra.CoaugmentedGradedCoderivation`.

## Main definitions

* `TauCeti.AInfinityAlgebra.coaugmentedBarDifferential`: the bar coderivation extended to all
  tensor words by zero on the empty word.

## Main results

* `TauCeti.AInfinityAlgebra.coaugmentedBarDifferential_comp_reducedInclusion` and
  `TauCeti.AInfinityAlgebra.isGradedCoderivation_coaugmentedBarDifferential`: the extension
  restricts to the bar differential on the words of positive length, where it is a degree-one
  graded coderivation of the coaugmented coalgebra.
* `TauCeti.AInfinityAlgebra.coaugmentedBarDifferential_sq`: its square is zero.
* `TauCeti.AInfinityAlgebra.isHomogeneous_coaugmentedBarDifferential`: it raises the total letter
  degree by one.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uA uM

namespace TauCeti

open TensorWords

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- The bar differential extended to the coaugmented tensor words: the square-zero coderivation
`TauCeti.AInfinityAlgebra.barDifferential` of the reduced tensor coalgebra, sent along
`TauCeti.TensorWords.reducedInclusion`, so that the empty word is annihilated. -/
noncomputable def coaugmentedBarDifferential (𝒜 : AInfinityAlgebra R A) :
    TensorWords R A →ₗ[R] TensorWords R A :=
  reducedInclusion R A ∘ₗ
    DirectSum.toModule R ℕ (ReducedTensorWords R A) fun n ↦
      if h : 0 < n then
        𝒜.barDifferential ∘ₗ
          (ReducedTensorWords.of R A ⟨n, h⟩ :
            TensorPower R n A →ₗ[R] ReducedTensorWords R A)
      else 0

/-- The extension annihilates the empty word. -/
@[simp]
theorem coaugmentedBarDifferential_one (𝒜 : AInfinityAlgebra R A) :
    𝒜.coaugmentedBarDifferential (1 : TensorWords R A) = 0 := by
  rw [TensorWords.one_eq_of_zero, coaugmentedBarDifferential, LinearMap.coe_comp,
    Function.comp_apply, TensorWords.toModule_of, dite_eq_right (by omega),
    LinearMap.zero_apply, map_zero]

/-- The extension annihilates every word of length zero. -/
@[simp]
theorem coaugmentedBarDifferential_of_zero (𝒜 : AInfinityAlgebra R A) (z : TensorPower R 0 A) :
    𝒜.coaugmentedBarDifferential (TensorWords.of R A 0 z) = 0 := by
  rw [coaugmentedBarDifferential, LinearMap.coe_comp, Function.comp_apply,
    TensorWords.toModule_of, dite_eq_right (by omega), LinearMap.zero_apply, map_zero]

/-- On a word of positive length the extension is the bar differential of that word. -/
@[simp]
theorem coaugmentedBarDifferential_of (𝒜 : AInfinityAlgebra R A) {n : ℕ} (hn : 0 < n)
    (z : TensorPower R n A) :
    𝒜.coaugmentedBarDifferential (TensorWords.of R A n z) =
      reducedInclusion R A
        (𝒜.barDifferential (ReducedTensorWords.of R A ⟨n, hn⟩ z)) := by
  rw [coaugmentedBarDifferential, LinearMap.coe_comp, Function.comp_apply,
    TensorWords.toModule_of, dite_eq_left hn, LinearMap.coe_comp, Function.comp_apply]

/-- The extension agrees with the bar differential on the words of positive length. -/
theorem coaugmentedBarDifferential_comp_reducedInclusion (𝒜 : AInfinityAlgebra R A) :
    𝒜.coaugmentedBarDifferential ∘ₗ reducedInclusion R A
      = reducedInclusion R A ∘ₗ 𝒜.barDifferential := by
  refine ReducedTensorWords.linearMap_ext R A
    (f := 𝒜.coaugmentedBarDifferential ∘ₗ reducedInclusion R A)
    (g := reducedInclusion R A ∘ₗ 𝒜.barDifferential) fun n z => ?_
  rw [LinearMap.coe_comp, Function.comp_apply, TensorWords.reducedInclusion_of,
    coaugmentedBarDifferential_of _ n.2, LinearMap.coe_comp, Function.comp_apply]

/-- The extension acts on the words of positive length as the bar differential. -/
private theorem coaugmentedBarDifferential_reducedInclusion (𝒜 : AInfinityAlgebra R A)
    (w : ReducedTensorWords R A) :
    𝒜.coaugmentedBarDifferential (reducedInclusion R A w) =
      reducedInclusion R A (𝒜.barDifferential w) := by
  have h : 𝒜.coaugmentedBarDifferential ∘ₗ reducedInclusion R A
      = reducedInclusion R A ∘ₗ 𝒜.barDifferential :=
    coaugmentedBarDifferential_comp_reducedInclusion 𝒜
  simpa only [LinearMap.coe_comp, Function.comp_apply] using LinearMap.congr_fun h w

/-- The letterwise Koszul twist of the suspension grading agrees on the words of positive length
with the reduced one, and so fixes the empty word as well. -/
private theorem map_koszulTwist_comp_reducedInclusion (𝒜 : AInfinityAlgebra R A) :
    TensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1) ∘ₗ reducedInclusion R A
      = reducedInclusion R A ∘ₗ
          ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1) := by
  refine ReducedTensorWords.linearMap_ext R A fun n z => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, TensorWords.reducedInclusion_of,
    TensorWords.map_of, ReducedTensorWords.map_of]

/-- Twisting an included word and then including it is the inclusion of the twisted word. -/
private theorem map_koszulTwist_reducedInclusion (𝒜 : AInfinityAlgebra R A)
    (w : ReducedTensorWords R A) :
    TensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1) (reducedInclusion R A w) =
      reducedInclusion R A
        (ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1) w) := by
  exact LinearMap.congr_fun (map_koszulTwist_comp_reducedInclusion 𝒜) w

/-- Differentiating the left factor of an included tensor and then including is the inclusion of
the bar differential of that factor, as a map. -/
private theorem rTensor_comp_reducedInclusion_map (𝒜 : AInfinityAlgebra R A) :
    LinearMap.rTensor (TensorWords R A) 𝒜.coaugmentedBarDifferential ∘ₗ
        TensorProduct.map (reducedInclusion R A) (reducedInclusion R A)
      = TensorProduct.map (reducedInclusion R A) (reducedInclusion R A) ∘ₗ
          LinearMap.rTensor (ReducedTensorWords R A) 𝒜.barDifferential := by
  refine TensorProduct.ext' fun x y => ?_
  rw [LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
    coaugmentedBarDifferential_reducedInclusion, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.rTensor_tmul, TensorProduct.map_tmul]

/-- Differentiating the right factor of an included tensor and then including is the inclusion of
the bar differential of that factor, as a map. -/
private theorem lTensor_comp_reducedInclusion_map (𝒜 : AInfinityAlgebra R A) :
    LinearMap.lTensor (TensorWords R A) 𝒜.coaugmentedBarDifferential ∘ₗ
        TensorProduct.map (reducedInclusion R A) (reducedInclusion R A)
      = TensorProduct.map (reducedInclusion R A) (reducedInclusion R A) ∘ₗ
          LinearMap.lTensor (ReducedTensorWords R A) 𝒜.barDifferential := by
  refine TensorProduct.ext' fun x y => ?_
  rw [LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul, LinearMap.lTensor_tmul,
    coaugmentedBarDifferential_reducedInclusion, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.lTensor_tmul, TensorProduct.map_tmul]

/-- Twisting the left factor of an included tensor and then including it is the inclusion of the
twisted tensor, as a map. -/
private theorem rTensor_map_koszulTwist_reducedInclusion_map (𝒜 : AInfinityAlgebra R A) :
    LinearMap.rTensor (TensorWords R A)
          (TensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1)) ∘ₗ
        TensorProduct.map (reducedInclusion R A) (reducedInclusion R A)
      = TensorProduct.map (reducedInclusion R A) (reducedInclusion R A) ∘ₗ
          LinearMap.rTensor (ReducedTensorWords R A)
            (ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1)) := by
  refine TensorProduct.ext' fun x y => ?_
  rw [LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
    map_koszulTwist_reducedInclusion 𝒜 x, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.rTensor_tmul, TensorProduct.map_tmul]

/-- The same statement as `rTensor_comp_reducedInclusion_map`, on one tensor. -/
private theorem rTensor_coaugmentedBarDifferential_map (𝒜 : AInfinityAlgebra R A)
    (X : ReducedTensorWords R A ⊗[R] ReducedTensorWords R A) :
    LinearMap.rTensor (TensorWords R A) 𝒜.coaugmentedBarDifferential
        (TensorProduct.map (reducedInclusion R A) (reducedInclusion R A) X)
      = TensorProduct.map (reducedInclusion R A) (reducedInclusion R A)
          (LinearMap.rTensor (ReducedTensorWords R A) 𝒜.barDifferential X) := by
  convert LinearMap.congr_fun (rTensor_comp_reducedInclusion_map 𝒜) X using 1

/-- The same statement as `lTensor_comp_reducedInclusion_map`, on one tensor. -/
private theorem lTensor_coaugmentedBarDifferential_map (𝒜 : AInfinityAlgebra R A)
    (X : ReducedTensorWords R A ⊗[R] ReducedTensorWords R A) :
    LinearMap.lTensor (TensorWords R A) 𝒜.coaugmentedBarDifferential
        (TensorProduct.map (reducedInclusion R A) (reducedInclusion R A) X)
      = TensorProduct.map (reducedInclusion R A) (reducedInclusion R A)
          (LinearMap.lTensor (ReducedTensorWords R A) 𝒜.barDifferential X) := by
  convert LinearMap.congr_fun (lTensor_comp_reducedInclusion_map 𝒜) X using 1

/-- The same statement as `rTensor_map_koszulTwist_reducedInclusion_map`, on one tensor. -/
private theorem rTensor_map_koszulTwist_map (𝒜 : AInfinityAlgebra R A)
    (X : ReducedTensorWords R A ⊗[R] ReducedTensorWords R A) :
    LinearMap.rTensor (TensorWords R A)
          (TensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1))
          (TensorProduct.map (reducedInclusion R A) (reducedInclusion R A) X)
      = TensorProduct.map (reducedInclusion R A) (reducedInclusion R A)
          (LinearMap.rTensor (ReducedTensorWords R A)
            (ReducedTensorWords.map (R := R) ((𝒜.grading.shift 1).koszulTwist 1)) X) := by
  convert LinearMap.congr_fun (rTensor_map_koszulTwist_reducedInclusion_map 𝒜) X using 1

/-- The extension squares to zero. -/
@[simp]
theorem coaugmentedBarDifferential_sq (𝒜 : AInfinityAlgebra R A) :
    𝒜.coaugmentedBarDifferential ∘ₗ 𝒜.coaugmentedBarDifferential = 0 := by
  refine TensorWords.linearMap_ext R A fun n x => ?_
  rw [LinearMap.coe_comp, Function.comp_apply]
  rcases n with _ | n
  · rw [coaugmentedBarDifferential_of_zero, map_zero, LinearMap.zero_apply]
  · rw [coaugmentedBarDifferential_of _ (Nat.succ_pos n),
      coaugmentedBarDifferential_reducedInclusion]
    set y := ReducedTensorWords.of R A ⟨n + 1, Nat.succ_pos n⟩ (PiTensorProduct.tprod R x)
    have hb : 𝒜.barDifferential (𝒜.barDifferential y) = 0 := by
      simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply] using
        LinearMap.congr_fun (barDifferential_sq 𝒜) y
    rw [hb, LinearMap.zero_apply, map_zero]

/-- The extension raises the total letter degree by one. -/
theorem isHomogeneous_coaugmentedBarDifferential (𝒜 : AInfinityAlgebra R A) :
    LinearMap.IsHomogeneous 𝒜.coaugmentedBarDifferential
      (gradedPiece (𝒜.grading.shift 1)) (gradedPiece (𝒜.grading.shift 1)) 1 := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  refine gradedPiece_induction
    (motive := fun z ↦ 𝒜.coaugmentedBarDifferential z ∈
      gradedPiece (𝒜.grading.shift 1) (D + 1)) hz ?_ ?_ ?_ ?_
  · intro n 𝒟 x hx hD
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [coaugmentedBarDifferential_of_zero]
      exact Submodule.zero_mem _
    · rw [coaugmentedBarDifferential_of _ hn]
      refine mem_gradedPiece_of_reducedInclusion ?_
      simpa only [hD] using 𝒜.isHomogeneous_barDifferential.map_mem
        (ReducedTensorWords.mem_gradedPiece_of_tprod (𝒜.grading.shift 1) hn x 𝒟 hx)
  · simp
  · intro u v _ _ hu hv
    rw [map_add]
    exact Submodule.add_mem _ hu hv
  · intro c u _ hu
    rw [map_smul]
    exact (Submodule.smul_mem (gradedPiece (𝒜.grading.shift 1) (D + 1)) c) hu

/-- The extension satisfies the graded co-Leibniz identity of the coaugmented tensor coalgebra.
On a word of positive length the two degenerate cuts of its coproduct are read off the term in
which the nonempty half is differentiated, and they vanish in the other term because the extension
annihilates the empty word; the empty word itself is annihilated on both sides, so the whole
identity reduces to the reduced one. -/
theorem isGradedCoderivation_coaugmentedBarDifferential (𝒜 : AInfinityAlgebra R A) :
    TensorWords.IsGradedCoderivation (𝒜.grading.shift 1) 1 𝒜.coaugmentedBarDifferential := by
  rw [TensorWords.isGradedCoderivation_iff]
  refine TensorWords.linearMap_ext R A fun n x => ?_
  rcases n with _ | n
  · -- the empty word
    have hone : TensorWords.of R A 0 (PiTensorProduct.tprod R x) = (1 : TensorWords R A) := by
      rw [TensorWords.one_eq_of_zero]
      exact TensorWords.of_tprod_congr R A (fun i : Fin 0 => i.elim0)
    conv_lhs =>
      simp only [hone, LinearMap.coe_comp, Function.comp_apply,
        coaugmentedBarDifferential_one, map_zero]
    conv_rhs =>
      simp only [hone, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        TensorWords.deconcatenation_one, LinearMap.rTensor_tmul, TensorWords.map_one,
        LinearMap.lTensor_tmul, coaugmentedBarDifferential_one, TensorProduct.zero_tmul,
        TensorProduct.tmul_zero, add_zero]
  · -- a word of positive length
    rw [← TensorWords.reducedInclusion_of R A ⟨n + 1, Nat.succ_pos n⟩
      (PiTensorProduct.tprod R x)]
    set u := ReducedTensorWords.of R A ⟨n + 1, Nat.succ_pos n⟩
      (PiTensorProduct.tprod R x)
    -- The coproduct of the value of the extension, read off the reduced co-Leibniz identity.
    conv_lhs =>
      simp only [LinearMap.coe_comp, Function.comp_apply,
        coaugmentedBarDifferential_reducedInclusion,
        TensorWords.deconcatenation_comp_reducedInclusion_apply,
        𝒜.isGradedCoderivation_barDifferential.deconcatenation_apply, map_add]
    -- The two terms of the co-Leibniz identity on the coaugmented coalgebra.
    conv_rhs =>
      simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        TensorWords.deconcatenation_comp_reducedInclusion_apply, map_add,
        LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorWords.map_one,
        coaugmentedBarDifferential_one, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
        coaugmentedBarDifferential_reducedInclusion, rTensor_coaugmentedBarDifferential_map,
        map_koszulTwist_reducedInclusion, rTensor_map_koszulTwist_map,
        lTensor_coaugmentedBarDifferential_map]
    abel

end AInfinityAlgebra

end TauCeti
