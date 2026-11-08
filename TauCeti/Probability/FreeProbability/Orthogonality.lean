/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Independence
public import TauCeti.Analysis.CStarAlgebra.GNS
public import Mathlib.Algebra.Star.Subalgebra
import TauCeti.Algebra.Star.BigOperators

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
  let u : List (ι × A) := (w.map fun x => (x.1, star x.2)).reverse
  have hs : star (w.map Prod.snd).prod = (u.map Prod.snd).prod := by
    rw [star_list_prod]
    simp [u, List.map_reverse, Function.comp_def]
  have hu : (u.map Prod.fst).IsChain (· ≠ ·) := by
    simpa [u, List.map_reverse, List.map_map, Function.comp_def, List.isChain_reverse,
      ne_comm] using hw
  have huB : ∀ x ∈ u, x.2 ∈ (B x.1).toSubalgebra := by
    intro x hx
    simp only [u, List.mem_reverse, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (B y.1).star_mem' (hwB y hy)
  have huφ : ∀ x ∈ u, φ x.2 = 0 := by
    intro x hx
    simp only [u, List.mem_reverse, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simp [hstar, hwφ y hy]
  rw [hs, h.apply_prod_mul_prod hφ u v hu hv huB hvB huφ hvφ]
  simp [u, Function.comp_def, List.zipWith_map_left]

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
