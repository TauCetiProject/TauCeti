/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Independence
public import TauCeti.Analysis.CStarAlgebra.GNS
public import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Inner products of reduced words

For a free family of star subalgebras, a reduced word is a product of centered letters whose
consecutive factor labels differ. Two reduced words with different label sequences are
orthogonal in the GNS space of a positive state. For matching label sequences their inner
product is the product of the inner products of corresponding letters. The empty word gives
the vacuum, of squared norm one.

The algebraic calculation needs only a normalized, star-preserving linear functional, and
holds over a commutative star ring. Positivity enters only when interpreting it as a GNS inner
product. No trace or faithfulness is assumed. This is the inner-product formula underlying the
Hilbert tensor decomposition of free products into reduced words.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 7.
* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, §1.5.

The Hilbert-space interpretation uses Mathlib's `PositiveLinearMap.PreGNS` and its completion.
-/

public section

open scoped ComplexOrder

namespace TauCeti

namespace IsFreelyIndependent

section Algebraic

variable {R A ι : Type*} [CommRing R] [StarRing R] [Ring A] [StarRing A]
  [Algebra R A] [StarModule R A] {φ : A →ₗ[R] R} {B : ι → StarSubalgebra R A}

private theorem apply_star_prod_mul_middle_mul_prod_eq_zero
    (h : IsFreelyIndependent φ fun i => (B i).toSubalgebra)
    (hstar : ∀ a, φ (star a) = star (φ a))
    (w v : List (ι × A)) {i : ι} {c : A}
    (hw : (i :: w.map Prod.fst).IsChain (· ≠ ·))
    (hv : (i :: v.map Prod.fst).IsChain (· ≠ ·))
    (hwB : ∀ x ∈ w, x.2 ∈ B x.1) (hvB : ∀ x ∈ v, x.2 ∈ B x.1)
    (hwφ : ∀ x ∈ w, φ x.2 = 0) (hvφ : ∀ x ∈ v, φ x.2 = 0)
    (hcB : c ∈ B i) (hcφ : φ c = 0) :
    φ (star (w.map Prod.snd).prod * c * (v.map Prod.snd).prod) = 0 := by
  have hz := (isFreelyIndependent_iff.1 h) (w.reverse.map (fun x => (x.1, star x.2)) ++ (i, c) :: v)
    (by simp) ?_ ?_ ?_
  · have hs : star (w.map Prod.snd).prod =
        (w.map (fun x => star x.2)).reverse.prod := by
      simpa [List.map_map, Function.comp_def] using
        unop_map_list_prod (starMulEquiv : A ≃* Aᵐᵒᵖ) (w.map Prod.snd)
    simpa [List.map_append, List.map_map, List.map_reverse, Function.comp_def,
      List.prod_append, hs, mul_assoc] using hz
  · simp only [List.map_append, List.map_map, List.map_cons, List.map_reverse,
      Function.comp_def]
    apply List.isChain_split.mpr
    exact ⟨by simpa [← List.reverse_cons, List.isChain_reverse, ne_comm] using hw, hv⟩
  · intro x hx
    simp only [List.mem_append, List.mem_map, List.mem_reverse, List.mem_cons] at hx
    rcases hx with ⟨y, hy, rfl⟩ | rfl | hx
    · exact (B y.1).star_mem' (hwB y hy)
    · exact hcB
    · exact hvB x hx
  · intro x hx
    simp only [List.mem_append, List.mem_map, List.mem_reverse, List.mem_cons] at hx
    rcases hx with ⟨y, hy, rfl⟩ | rfl | hx
    · simp [hstar, hwφ y hy]
    · exact hcφ
    · exact hvφ x hx

variable [DecidableEq ι]

/-- Reduced words have zero pairing unless their factor-label sequences coincide. When they
coincide, the pairing is the product of the pairings of corresponding letters. The words may
be empty; the empty-empty pairing is one. Positivity and traciality are unnecessary. -/
theorem apply_star_prod_mul_prod
    (h : IsFreelyIndependent φ fun i => (B i).toSubalgebra) (hφ : φ 1 = 1)
    (hstar : ∀ a, φ (star a) = star (φ a)) (w v : List (ι × A))
    (hw : (w.map Prod.fst).IsChain (· ≠ ·))
    (hv : (v.map Prod.fst).IsChain (· ≠ ·))
    (hwB : ∀ x ∈ w, x.2 ∈ B x.1) (hvB : ∀ x ∈ v, x.2 ∈ B x.1)
    (hwφ : ∀ x ∈ w, φ x.2 = 0) (hvφ : ∀ x ∈ v, φ x.2 = 0) :
    φ (star (w.map Prod.snd).prod * (v.map Prod.snd).prod) =
      if w.map Prod.fst = v.map Prod.fst then
        (List.zipWith (fun x y => φ (star x.2 * y.2)) w v).prod else 0 := by
  induction w generalizing v with
  | nil =>
    cases v with
    | nil => simp [hφ]
    | cons y v =>
      simpa using (isFreelyIndependent_iff.1 h) (y :: v) (by simp) hv hvB hvφ
  | cons x w ih =>
    cases v with
    | nil =>
      have hz := (isFreelyIndependent_iff.1 h) (x :: w) (by simp) hw hwB hwφ
      simp only [List.map_nil, List.prod_nil, mul_one]
      rw [hstar, hz]
      simp
    | cons y v =>
      have hwB' : ∀ z ∈ w, z.2 ∈ B z.1 := fun z hz => hwB z (by simp [hz])
      have hvB' : ∀ z ∈ v, z.2 ∈ B z.1 := fun z hz => hvB z (by simp [hz])
      have hwφ' : ∀ z ∈ w, φ z.2 = 0 := fun z hz => hwφ z (by simp [hz])
      have hvφ' : ∀ z ∈ v, φ z.2 = 0 := fun z hz => hvφ z (by simp [hz])
      by_cases hxy : x.1 = y.1
      · -- Center the product of the two leading letters. Its centered part gives a reduced
        -- word with zero expectation; its scalar part leaves the pairing of the tails.
        have hcB : star x.2 * y.2 ∈ B x.1 :=
          (B x.1).mul_mem ((B x.1).star_mem' (hwB x (by simp)))
            (hxy ▸ hvB y (by simp))
        have hz := h.apply_star_prod_mul_middle_mul_prod_eq_zero hstar w v hw
          (hxy ▸ hv) hwB' hvB' hwφ' hvφ'
          ((B x.1).sub_mem hcB ((B x.1).algebraMap_mem (φ (star x.2 * y.2))))
          (by simp [Algebra.algebraMap_eq_smul_one, hφ])
        have hrec := ih v hw.tail hv.tail hwB' hvB' hwφ' hvφ'
        simp only [mul_sub, sub_mul, map_sub, Algebra.algebraMap_eq_smul_one,
          mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul, mul_one, sub_eq_zero] at hz
        have hz' : φ (star ((x :: w).map Prod.snd).prod *
            ((y :: v).map Prod.snd).prod) =
            φ (star x.2 * y.2) * φ (star (w.map Prod.snd).prod * (v.map Prod.snd).prod) := by
          simpa only [List.map_cons, List.prod_cons, star_mul, mul_assoc] using hz
        rw [hz', hrec]
        simp [hxy]
      · -- Distinct leading labels leave the entire concatenation reduced.
        have hz := h.apply_star_prod_mul_middle_mul_prod_eq_zero hstar w (y :: v) hw
          (by simpa using And.intro hxy hv) hwB' hvB hwφ' hvφ
          ((B x.1).star_mem' (hwB x (by simp)))
          (by simp [hstar, hwφ x (by simp)])
        simpa [List.map_cons, List.prod_cons, star_mul, mul_assoc, hxy] using hz

end Algebraic

section GNS

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [DecidableEq ι] {φ : A →ₚ[ℂ] ℂ} {B : ι → StarSubalgebra ℂ A}

/-- In the GNS Hilbert space, centered alternating words are orthogonal for distinct label
sequences, and have the tensor-product inner product for equal label sequences. This includes
the vacuum and does not require the state to be faithful or tracial. -/
theorem inner_gnsStarAlgHom_prod_gnsVector
    (h : IsFreelyIndependent φ.toLinearMap fun i => (B i).toSubalgebra) (hφ : φ 1 = 1)
    (w v : List (ι × A))
    (hw : (w.map Prod.fst).IsChain (· ≠ ·))
    (hv : (v.map Prod.fst).IsChain (· ≠ ·))
    (hwB : ∀ x ∈ w, x.2 ∈ B x.1) (hvB : ∀ x ∈ v, x.2 ∈ B x.1)
    (hwφ : ∀ x ∈ w, φ x.2 = 0) (hvφ : ∀ x ∈ v, φ x.2 = 0) :
    inner ℂ (φ.gnsStarAlgHom (w.map Prod.snd).prod φ.gnsVector)
      (φ.gnsStarAlgHom (v.map Prod.snd).prod φ.gnsVector) =
      if w.map Prod.fst = v.map Prod.fst then
        (List.zipWith (fun x y => φ (star x.2 * y.2)) w v).prod else 0 := by
  rw [PositiveLinearMap.inner_gnsStarAlgHom_gnsVector]
  exact h.apply_star_prod_mul_prod hφ (fun a => map_star φ a) w v hw hv hwB hvB hwφ hvφ

end GNS

end IsFreelyIndependent

end TauCeti
