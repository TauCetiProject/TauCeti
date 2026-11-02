/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Graded.ComposableWords
public import TauCeti.LinearAlgebra.TensorCoalgebra.Brace

/-!
# Braces on composable paths

Path-compatible Taylor maps form a submodule of the maps from reduced tensor words to the total
morphism module. The tensor-word brace restricts to these submodules: inserting an operation on
a composable block preserves the endpoints, and every insertion into a non-composable word
vanishes after the outer operation. This also makes them closed under the Gerstenhaber bracket.

`WordPathCochain.component` evaluates a cochain on a path, with output in the Hom module between
its endpoints. The homogeneous evaluation formula for a brace retains the exact Koszul prefix
sign, including a possible shift of the grading. No equality transports between Hom modules are
part of this interface. These constructions supply the pathwise operations used in Hochschild
cochains of an A-infinity category.

The brace and its signs are those of Getzler--Jones, *A-infinity algebras and the cyclic bar
complex*, Sections 1--2; the path convention follows Keller, *Introduction to A-infinity
algebras and modules*, Section 7. We restrict `ReducedTensorWords.brace`, rather than introducing
a second substitution or sign calculus.
-/

public section

noncomputable section

namespace TauCeti.GradedLinearQuiver

open ReducedTensorWords

universe u u' v v' w

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  {D : Type u'} [GradedLinearQuiver.{u', v', w} R D]

/-- Taylor maps along an object map, supported on composable paths and preserving endpoints. -/
def wordPathCochains (φ : C → D) :
    Submodule R (ReducedTensorWords R (TotalHom R C) →ₗ[R] TotalHom R D) where
  carrier := {F | IsWordPathCompatible φ F}
  zero_mem' := ⟨fun _ ↦ zero_mem _, fun _ ↦ rfl⟩
  add_mem' hF hG := ⟨fun hw ↦ add_mem (hF.mem_range_of_mem_composableWords hw)
    (hG.mem_range_of_mem_composableWords hw), fun hw ↦ by
      simp [hF.eq_zero_of_mem_nonComposableWords hw, hG.eq_zero_of_mem_nonComposableWords hw]⟩
  smul_mem' r F hF := ⟨fun hw ↦ Submodule.smul_mem _ r (hF.mem_range_of_mem_composableWords hw),
    fun hw ↦ by simp [hF.eq_zero_of_mem_nonComposableWords hw]⟩

@[simp]
theorem mem_wordPathCochains {φ : C → D}
    {F : ReducedTensorWords R (TotalHom R C) →ₗ[R] TotalHom R D} :
    F ∈ wordPathCochains φ ↔ IsWordPathCompatible φ F := Iff.rfl

/-- Path cochains are closed under the Gerstenhaber bracket. -/
theorem gerstenhaberBracket_mem_wordPathCochains
    {F G : ReducedTensorWords R (TotalHom R C) →ₗ[R] TotalHom R C}
    (hF : F ∈ wordPathCochains (id : C → C)) (hG : G ∈ wordPathCochains (id : C → C))
    (c p q : ℤ) :
    gerstenhaberBracket ((totalGrading R C).shift c) p q F G ∈ wordPathCochains (id : C → C) := by
  rw [gerstenhaberBracket_def, brace_def, brace_def]
  exact (wordPathCochains id).sub_mem (hF.comp_gradedCoderiv hG c q)
    ((wordPathCochains id).smul_mem _ (hG.comp_gradedCoderiv hF c p))

/-- A path-compatible Taylor map along `φ`, viewed as an element of its cochain module. -/
abbrev WordPathCochain (φ : C → D) : Type (max u u' v v' w) :=
  ↥(wordPathCochains (R := R) φ)

namespace WordPathCochain

variable {φ : C → D}

/-- The multilinear component of a path cochain, valued in the Hom module of its endpoints.
The positive arity excludes empty words from the reduced tensor coalgebra. -/
def component (F : WordPathCochain (R := R) φ) {n : ℕ} (hn : 0 < n) (X : Fin (n + 1) → C) :
    MultilinearMap R (fun i : Fin n ↦ homModule (R := R) (X i.rev.castSucc) (X i.rev.succ))
      (homModule (R := R) (φ (X 0)) (φ (X (Fin.last n)))) :=
  ((F.val ∘ₗ of R _ ⟨n, hn⟩).compMultilinearMap
    (PiTensorProduct.tprod R)).restrictToPath φ X

theorem component_apply (F : WordPathCochain (R := R) φ) {n : ℕ} (hn : 0 < n)
    (X : Fin (n + 1) → C)
    (x : ∀ i : Fin n, homModule (R := R) (X i.rev.castSucc) (X i.rev.succ)) :
    F.component hn X x = homProjection (φ (X 0)) (φ (X (Fin.last n)))
      (F.val (of R _ ⟨n, hn⟩ (PiTensorProduct.tprod R fun i ↦ homInclusion _ _ (x i)))) :=
  MultilinearMap.restrictToPath_apply _ φ X x

@[simp]
theorem component_zero {n : ℕ} (hn : 0 < n) (X : Fin (n + 1) → C) :
    (0 : WordPathCochain (R := R) φ).component hn X = 0 := by
  ext x
  simp [component_apply]

@[simp]
theorem component_add (F G : WordPathCochain (R := R) φ) {n : ℕ} (hn : 0 < n)
    (X : Fin (n + 1) → C) :
    (F + G).component hn X = F.component hn X + G.component hn X := by
  ext x
  simp [component_apply]

@[simp]
theorem component_smul (r : R) (F : WordPathCochain (R := R) φ) {n : ℕ} (hn : 0 < n)
    (X : Fin (n + 1) → C) :
    (r • F).component hn X = r • F.component hn X := by
  ext x
  simp [component_apply]

/-- Evaluating on a path and then including the output recovers the total-module evaluation. -/
@[simp]
theorem homInclusion_component (F : WordPathCochain (R := R) φ) {n : ℕ} (hn : 0 < n)
    (X : Fin (n + 1) → C)
    (x : ∀ i : Fin n, homModule (R := R) (X i.rev.castSucc) (X i.rev.succ)) :
    homInclusion (φ (X 0)) (φ (X (Fin.last n))) (F.component hn X x) =
      F.val (of R _ ⟨n, hn⟩ (PiTensorProduct.tprod R fun i ↦ homInclusion _ _ (x i))) := by
  exact (isWordPathCompatible_iff.mp F.property n hn).homInclusion_restrictToPath X x

/-- A path cochain is determined by its multilinear components on composable paths. -/
@[ext]
theorem ext {F G : WordPathCochain (R := R) φ}
    (h : ∀ (n : ℕ) (hn : 0 < n) (X : Fin (n + 1) → C),
      F.component hn X = G.component hn X) : F = G := by
  apply Subtype.ext
  refine ReducedTensorWords.linearMap_ext R (TotalHom R C) fun n x ↦ ?_
  rcases n with ⟨_ | n, hn⟩
  · omega
  have e := ((isWordPathCompatible_iff).mp F.property (n + 1) hn).ext
    ((isWordPathCompatible_iff).mp G.property (n + 1) hn) fun X y ↦ by
      rw [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        ← homInclusion_component F hn X y, ← homInclusion_component G hn X y, h]
  exact MultilinearMap.congr_fun e x

/-- The brace on path cochains, at a specified shift and twist parameter. -/
def brace (c q : ℤ) : WordPathCochain (R := R) (id : C → C) →ₗ[R]
    WordPathCochain (R := R) (id : C → C) →ₗ[R] WordPathCochain (R := R) (id : C → C) :=
  LinearMap.mk₂ R (fun F G ↦ ⟨ReducedTensorWords.brace ((totalGrading R C).shift c) F G q,
    by rw [ReducedTensorWords.brace_def]
       exact F.property.comp_gradedCoderiv G.property c q⟩)
    (fun _ _ _ ↦ Subtype.ext (brace_add_left ..))
    (fun _ _ _ ↦ Subtype.ext (brace_smul_left ..))
    (fun _ _ _ ↦ Subtype.ext (brace_add_right ..))
    (fun _ _ _ ↦ Subtype.ext (brace_smul_right ..))

@[simp]
theorem coe_brace (c q : ℤ) (F G : WordPathCochain (R := R) (id : C → C)) :
    (brace c q F G).val = ReducedTensorWords.brace ((totalGrading R C).shift c) F G q := by
  simp [brace]

/-- On a homogeneous path, insertion after `r` inputs has sign
`(-1)^(q * ((d₀-c) + ⋯ + (dᵣ₋₁-c)))`. Thus `c = 1` uses suspended input degrees.
All sums are finite even when the cochains have infinitely many nonzero Taylor components. -/
theorem component_brace (c q : ℤ) (F G : WordPathCochain (R := R) (id : C → C))
    {n : ℕ} (hn : 0 < n) (X : Fin (n + 1) → C) (d : Fin n → ℤ)
    (x : ∀ i : Fin n, homModule (R := R) (X i.rev.castSucc) (X i.rev.succ))
    (hx : ∀ i, x i ∈ (grading (R := R) (X i.rev.castSucc) (X i.rev.succ)).piece (d i)) :
    (brace c q F G).component hn X x =
      ∑ r ∈ Finset.range n, ∑ s ∈ Finset.range (n + 1),
        negOnePowCast R (q * ∑ j ∈ Finset.range r, if h : j < n then d ⟨j, h⟩ - c else 0) •
          homProjection (X 0) (X (Fin.last n))
            (F.val (splice R (fun i ↦ homInclusion _ _ (x i)) 0 n r s
              (G.val (subword R (fun i ↦ homInclusion _ _ (x i)) r s)))) := by
  have hx' (i : Fin n) : homInclusion _ _ (x i) ∈
      ((totalGrading R C).shift c).piece (d i - c) := by
    rw [InternalGrading.shift_piece, sub_add_cancel, homInclusion_mem_totalGrading_piece_iff]
    exact hx i
  rw [component_apply, coe_brace, ReducedTensorWords.brace_def, LinearMap.comp_apply,
    gradedCoderiv_of_tprod_of_homogeneous _ _ q hn _ (fun i ↦ d i - c) hx']
  simp only [map_sum, map_smul, negOnePowCast_eq_intCast, id_eq]

end WordPathCochain

end TauCeti.GradedLinearQuiver
