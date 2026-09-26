/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.GradedCoderivation

/-!
# Extending reduced endomorphisms to tensor words

`TauCeti.TensorWords = ⨆_{n ≥ 0} M^{⊗ n}` is the coaugmented tensor coalgebra and
`TauCeti.ReducedTensorWords = ⨆_{n ≥ 1} M^{⊗ n}` the reduced one, sitting in it as the summand of
the words of positive length by `TauCeti.TensorWords.reducedInclusion`, with retraction
`TauCeti.TensorWords.reducedProjection`.  Any endomorphism of the reduced words therefore has a
canonical extension to all tensor words, the one that is zero on the empty word:
`TauCeti.TensorWords.extendReduced`.

The extension is what carries the coderivation theory of the reduced coalgebra over to the
coaugmented one, whose coproduct admits the two degenerate cuts at the ends of a word.  The
extension preserves the three properties that the module and bimodule theories need from a
coderivation over `b`: the square-zero law
`TauCeti.TensorWords.extendReduced_sq`, homogeneity in the total letter degree
`TauCeti.TensorWords.isHomogeneous_extendReduced`, and the `q`-twisted co-Leibniz identity
`TauCeti.TensorWords.isGradedCoderivation_extendReduced`.

## Main definitions

* `TauCeti.TensorWords.extendReduced`: extend an endomorphism of the reduced words by zero on the
  empty word.

## Main results

* `TauCeti.TensorWords.extendReduced_comp_reducedInclusion`: the extension restricts to the
  endomorphism it extends.
* `TauCeti.TensorWords.extendReduced_sq`: the extension of a square-zero endomorphism squares to
  zero.
* `TauCeti.TensorWords.isHomogeneous_extendReduced`: the extension of a homogeneous endomorphism
  is homogeneous of the same degree in the total letter degree.
* `TauCeti.TensorWords.isGradedCoderivation_extendReduced`: the extension of a `q`-twisted graded
  coderivation of the reduced words is one of the coaugmented words.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM

namespace TauCeti

namespace TensorWords

section Extension

variable {R : Type uR} {M : Type uM} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The extension of an endomorphism of the reduced tensor words to all tensor words: it deletes
the empty word, applies the endomorphism, and includes the result, so that the empty word is
annihilated. -/
noncomputable def extendReduced (f : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) :
    TensorWords R M →ₗ[R] TensorWords R M :=
  reducedInclusion R M ∘ₗ f ∘ₗ reducedProjection R M

/-- On a word the extension is the inclusion of the value of the endomorphism on the
positive-length part of that word. -/
@[simp]
theorem extendReduced_apply (f : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (w : TensorWords R M) :
    extendReduced f w = reducedInclusion R M (f (reducedProjection R M w)) := by
  simp only [extendReduced, LinearMap.coe_comp, Function.comp_apply]

/-- The extension annihilates every word of length zero. -/
@[simp high]
theorem extendReduced_of_zero (f : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (z : TensorPower R 0 M) : extendReduced f (of R M 0 z) = 0 := by
  rw [extendReduced_apply, reducedProjection_of_zero, map_zero, map_zero]

/-- The extension annihilates the empty word. -/
@[simp high]
theorem extendReduced_one (f : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) :
    extendReduced f (1 : TensorWords R M) = 0 := by
  rw [one_eq_of_zero, extendReduced_of_zero]

/-- On a word of positive length the extension is the inclusion of the value of the endomorphism. -/
theorem extendReduced_of (f : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) {n : ℕ}
    (hn : 0 < n) (z : TensorPower R n M) :
    extendReduced f (of R M n z) =
      reducedInclusion R M (f (ReducedTensorWords.of R M ⟨n, hn⟩ z)) := by
  rw [extendReduced_apply, reducedProjection_of_of_pos]

/-- The extension agrees with the endomorphism it extends on the words of positive length. -/
theorem extendReduced_comp_reducedInclusion
    (f : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) :
    extendReduced f ∘ₗ reducedInclusion R M = reducedInclusion R M ∘ₗ f := by
  refine LinearMap.ext fun w => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, extendReduced_apply,
    reducedProjection_reducedInclusion]

/-- The extension acts on the words of positive length as the endomorphism it extends. -/
theorem extendReduced_reducedInclusion
    (f : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) (w : ReducedTensorWords R M) :
    extendReduced f (reducedInclusion R M w) = reducedInclusion R M (f w) :=
  LinearMap.congr_fun (extendReduced_comp_reducedInclusion f) w

/-- The extension of a square-zero endomorphism squares to zero. -/
@[simp]
theorem extendReduced_sq (f : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M)
    (hf : f ∘ₗ f = 0) : extendReduced f ∘ₗ extendReduced f = 0 := by
  have h : extendReduced f ∘ₗ extendReduced f
      = reducedInclusion R M ∘ₗ (f ∘ₗ f) ∘ₗ reducedProjection R M := by
    refine LinearMap.ext fun w => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, extendReduced_apply,
      reducedProjection_reducedInclusion]
  rw [h, hf, LinearMap.zero_comp, LinearMap.comp_zero]

end Extension

section GradedExtension

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]

/-- The extension of a homogeneous endomorphism of the reduced words is homogeneous of the same
degree in the total letter degree of the coaugmented words. -/
theorem isHomogeneous_extendReduced {G : InternalGrading R M} {r : ℤ}
    {f : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hf : LinearMap.IsHomogeneous f (ReducedTensorWords.gradedPiece G)
      (ReducedTensorWords.gradedPiece G) r) :
    LinearMap.IsHomogeneous (extendReduced f) (gradedPiece G) (gradedPiece G) r := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  refine gradedPiece_induction
    (motive := fun z ↦ extendReduced f z ∈ gradedPiece G (D + r)) hz ?_ ?_ ?_ ?_
  · intro n 𝒟 x hx hD
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [extendReduced_of_zero]
      exact Submodule.zero_mem _
    · rw [extendReduced_of _ hn]
      refine mem_gradedPiece_of_reducedInclusion ?_
      simpa only [hD] using hf.map_mem
        (ReducedTensorWords.mem_gradedPiece_of_tprod G hn x 𝒟 hx)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro u v _ _ hu hv
    rw [map_add]
    exact Submodule.add_mem _ hu hv
  · intro c u _ hu
    rw [map_smul]
    exact (Submodule.smul_mem (gradedPiece G (D + r)) c) hu

/-- Differentiating the left factor of an included tensor and then including is the inclusion of the
value of the endomorphism on that factor, as a map. -/
private theorem rTensor_comp_extend_map (f : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) :
    LinearMap.rTensor (TensorWords R M) (extendReduced f) ∘ₗ
        TensorProduct.map (reducedInclusion R M) (reducedInclusion R M)
      = TensorProduct.map (reducedInclusion R M) (reducedInclusion R M) ∘ₗ
          LinearMap.rTensor (ReducedTensorWords R M) f := by
  refine TensorProduct.ext' fun x y => ?_
  rw [LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
    extendReduced_reducedInclusion, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.rTensor_tmul, TensorProduct.map_tmul]

/-- Differentiating the right factor of an included tensor and then including is the inclusion
of the value of the endomorphism on that factor, as a map. -/
private theorem lTensor_comp_extend_map (f : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) :
    LinearMap.lTensor (TensorWords R M) (extendReduced f) ∘ₗ
        TensorProduct.map (reducedInclusion R M) (reducedInclusion R M)
      = TensorProduct.map (reducedInclusion R M) (reducedInclusion R M) ∘ₗ
          LinearMap.lTensor (ReducedTensorWords R M) f := by
  refine TensorProduct.ext' fun x y => ?_
  rw [LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul, LinearMap.lTensor_tmul,
    extendReduced_reducedInclusion, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.lTensor_tmul, TensorProduct.map_tmul]

/-- Twisting the left factor of an included tensor and then including it is the inclusion of the
twisted tensor, as a map. -/
private theorem rTensor_map_comp_reducedInclusion_map (G : InternalGrading R M) (q : ℤ) :
    LinearMap.rTensor (TensorWords R M) (map (InternalGrading.koszulTwist G q)) ∘ₗ
        TensorProduct.map (reducedInclusion R M) (reducedInclusion R M)
      = TensorProduct.map (reducedInclusion R M) (reducedInclusion R M) ∘ₗ
          LinearMap.rTensor (ReducedTensorWords R M)
            (ReducedTensorWords.map (R := R) (InternalGrading.koszulTwist G q)) := by
  have hmap (w : ReducedTensorWords R M) :
      map (InternalGrading.koszulTwist G q) (reducedInclusion R M w) =
        reducedInclusion R M
          (ReducedTensorWords.map (R := R) (InternalGrading.koszulTwist G q) w) :=
    LinearMap.congr_fun (map_comp_reducedInclusion (InternalGrading.koszulTwist G q)) w
  refine TensorProduct.ext' fun x y => ?_
  rw [LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
    hmap x, LinearMap.coe_comp, Function.comp_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul]

/-- The extension of a `q`-twisted graded coderivation of the reduced tensor words is a `q`-twisted
graded coderivation of the coaugmented ones. -/
theorem isGradedCoderivation_extendReduced {G : InternalGrading R M} {q : ℤ}
    {f : ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M}
    (hf : ReducedTensorWords.IsGradedCoderivation G q f) :
    IsGradedCoderivation G q (extendReduced f) := by
  rw [isGradedCoderivation_iff]
  refine linearMap_ext R M fun n x => ?_
  rcases n with _ | n
  · -- the empty word is annihilated on both sides
    have hone : of R M 0 (PiTensorProduct.tprod R x) = (1 : TensorWords R M) := by
      rw [one_eq_of_zero]
      exact of_tprod_congr R M (fun i : Fin 0 => i.elim0)
    conv_lhs =>
      simp only [hone, LinearMap.coe_comp, Function.comp_apply, extendReduced_one, map_zero]
    conv_rhs =>
      simp only [hone, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        deconcatenation_one, LinearMap.rTensor_tmul, map_one, LinearMap.lTensor_tmul,
        extendReduced_one, TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]
  · -- a word of positive length, by the reduced co-Leibniz identity and the degenerate cuts
    rw [← reducedInclusion_of R M ⟨n + 1, Nat.succ_pos n⟩ (PiTensorProduct.tprod R x)]
    -- The coproduct of the value of the extension, read off the reduced co-Leibniz identity.
    have htwist : ∀ w : ReducedTensorWords R M,
        map (InternalGrading.koszulTwist G q) (reducedInclusion R M w) =
          reducedInclusion R M
            (ReducedTensorWords.map (R := R) (InternalGrading.koszulTwist G q) w) :=
      fun w => LinearMap.congr_fun (map_comp_reducedInclusion (InternalGrading.koszulTwist G q)) w
    have hrTensor : ∀ X : ReducedTensorWords R M ⊗[R] ReducedTensorWords R M,
        LinearMap.rTensor (TensorWords R M) (extendReduced f)
            (TensorProduct.map (reducedInclusion R M) (reducedInclusion R M) X) =
          TensorProduct.map (reducedInclusion R M) (reducedInclusion R M)
            (LinearMap.rTensor (ReducedTensorWords R M) f X) :=
      fun X => LinearMap.congr_fun (rTensor_comp_extend_map f) X
    have hlTensor : ∀ X : ReducedTensorWords R M ⊗[R] ReducedTensorWords R M,
        LinearMap.lTensor (TensorWords R M) (extendReduced f)
            (TensorProduct.map (reducedInclusion R M) (reducedInclusion R M) X) =
          TensorProduct.map (reducedInclusion R M) (reducedInclusion R M)
            (LinearMap.lTensor (ReducedTensorWords R M) f X) :=
      fun X => LinearMap.congr_fun (lTensor_comp_extend_map f) X
    have htwistR : ∀ X : ReducedTensorWords R M ⊗[R] ReducedTensorWords R M,
        LinearMap.rTensor (TensorWords R M) (map (InternalGrading.koszulTwist G q))
            (TensorProduct.map (reducedInclusion R M) (reducedInclusion R M) X) =
          TensorProduct.map (reducedInclusion R M) (reducedInclusion R M)
            (LinearMap.rTensor (ReducedTensorWords R M)
              (ReducedTensorWords.map (R := R) (InternalGrading.koszulTwist G q)) X) :=
      fun X => LinearMap.congr_fun (rTensor_map_comp_reducedInclusion_map G q) X
    conv_lhs =>
      simp only [LinearMap.coe_comp, Function.comp_apply, extendReduced_reducedInclusion,
        deconcatenation_comp_reducedInclusion_apply,
        ReducedTensorWords.IsGradedCoderivation.deconcatenation_apply hf, map_add]
    -- The two terms of the co-Leibniz identity on the coaugmented coalgebra.
    conv_rhs =>
      simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        deconcatenation_comp_reducedInclusion_apply, map_add,
        LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, map_one, extendReduced_one,
        TensorProduct.zero_tmul, TensorProduct.tmul_zero,
        extendReduced_reducedInclusion, hrTensor, htwist, htwistR, hlTensor]
    abel

end GradedExtension

end TensorWords

end TauCeti
