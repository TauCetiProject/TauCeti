/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Pi
public import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# Ideals in a finite product of simple Lie algebras

An ideal in a product of Lie algebras contains the entire axis of a nonabelian simple factor
as soon as some element of the ideal has nonzero projection there. For a finite family of such
factors, each ideal therefore consists of exactly the vectors vanishing outside a unique set
of coordinates.

This is the product-ideal argument in Lawrence and Venkatesh, *Diophantine problems and
p-adic period mappings*, §2.7, preceding Lemma 2.12.
-/

public section

namespace LieIdeal

variable {ι R : Type*} {L : ι → Type*} [CommRing R] [∀ i, LieRing (L i)]
  [∀ i, LieAlgebra R (L i)]

/-- An ideal with nonzero projection to a simple factor contains that whole coordinate axis.
The index set can be infinite and the other factors can be arbitrary Lie algebras. -/
theorem single_mem_of_apply_ne_zero [DecidableEq ι] (I : LieIdeal R (∀ i, L i))
    (i : ι) [LieAlgebra.IsSimple R (L i)] {x : ∀ i, L i} (hx : x ∈ I) (hxi : x i ≠ 0)
    (y : L i) : Pi.single i y ∈ I := by
  let J := I.comap (LieHom.single R L i)
  rcases LieAlgebra.IsSimple.eq_bot_or_eq_top J with hbot | htop
  · exfalso
    apply hxi
    have hcenter : x i ∈ LieAlgebra.center R (L i) := by
      apply (LieModule.mem_maxTrivSubmodule R (L i) (L i) _).2
      intro z
      have hsingle : Pi.single i ⁅z, x i⁆ = ⁅Pi.single i z, x⁆ := by
        ext j
        rw [LieAlgebra.Pi.bracket_apply]
        exact (Pi.apply_single (fun j (a : L j) => ⁅a, x j⁆) (fun j => zero_lie (x j)) i z j).symm
      have hbr : ⁅z, x i⁆ ∈ J := by
        apply LieIdeal.mem_comap.mpr
        rw [LieHom.single_apply, hsingle]
        exact I.lie_mem hx
      simpa only [hbot, LieSubmodule.mem_bot] using hbr
    simpa only [LieAlgebra.center_eq_bot, LieSubmodule.mem_bot] using hcenter
  · rw [← LieHom.single_apply (R := R)]
    have hy : y ∈ J := htop ▸ LieSubmodule.mem_top y
    exact LieIdeal.mem_comap.mp hy

/-- Every Lie ideal of a finite product of nonabelian simple Lie algebras consists of the
vectors vanishing outside a unique subset of the given coordinates. -/
theorem existsUnique_mem_iff_eq_zero_off [Finite ι] [∀ i, LieAlgebra.IsSimple R (L i)]
    (I : LieIdeal R (∀ i, L i)) :
    ∃! s : Set ι, ∀ x, x ∈ I ↔ ∀ i ∉ s, x i = 0 := by
  classical
  let := Fintype.ofFinite ι
  let s := {i : ι | ∃ x ∈ I, x i ≠ 0}
  refine ⟨s, ?_, ?_⟩
  · intro x
    constructor
    · intro hx i hi
      exact not_not.mp fun hxi => hi ⟨x, hx, hxi⟩
    · intro hx
      rw [← Finset.univ_sum_single x]
      apply I.sum_mem
      intro i _
      by_cases hi : i ∈ s
      · obtain ⟨u, hu, hui⟩ := hi
        exact I.single_mem_of_apply_ne_zero i hu hui (x i)
      · simp [hx i hi]
  · intro t ht
    ext i
    constructor
    · intro hi
      let := LieAlgebra.IsSimple.nontrivial R (L i)
      obtain ⟨y, hy⟩ := exists_ne (0 : L i)
      have hsingle : Pi.single i y ∈ I := (ht _).2 fun j hj =>
        Pi.single_eq_of_ne (ne_of_mem_of_not_mem hi hj).symm y
      exact ⟨Pi.single i y, hsingle, by simpa only [Pi.single_eq_same] using hy⟩
    · rintro ⟨x, hx, hxi⟩
      exact not_not.mp fun hi => hxi ((ht x).1 hx i hi)

end LieIdeal
