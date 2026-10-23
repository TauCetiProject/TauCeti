/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import TauCeti.Algebra.Colimit.Ring

/-!
# Henselian pairs under directed colimits

Let `(G i, I i)` be a directed system of pairs of a commutative ring and an ideal, indexed by a
nonempty directed preorder, whose transition maps `f i j` carry `I i` into `I j`. The main
result, `Ring.DirectLimit.henselianRing`, is that if every `(G i, I i)` is Henselian, then
`Ring.DirectLimit G f` is Henselian along the colimit ideal `⨆ i, (I i).map (of G f i)`.

A monic polynomial over the colimit with a simple root modulo the colimit ideal comes, together
with its approximate root and the witnesses for both conditions, from a single stage (using the
descent lemmas of `TauCeti.Algebra.Colimit.Ring`); the root found there maps to the required root
in the colimit. This is the filtered-colimit case of the permanence properties of Henselian
pairs. Directedness is essential: the coproduct of two copies of `(ℤ_[p], (p))`, which is not a
directed colimit, is not Henselian along `p`.

## Main results

* `Ring.DirectLimit.henselianRing`: a directed colimit of Henselian pairs is Henselian along the
  colimit ideal.

## References

* [Stacks Project, Lemma 15.11.13](https://stacks.math.columbia.edu/tag/0FWT).
* [Stacks Project, Example 15.11.14](https://stacks.math.columbia.edu/tag/0FWU) for the failure
  along non-filtered colimits.
-/

public section

open Polynomial

namespace Ring.DirectLimit

variable {ι : Type*} [Preorder ι] {G : ι → Type*} [∀ i, CommRing (G i)]
  {f : ∀ i j, i ≤ j → G i →+* G j} {I : ∀ i, Ideal (G i)}

/-- **Henselian pairs are stable under directed colimits.** If every `(G i, I i)` is a
Henselian pair and the transition maps carry `I i` into `I j`, then the directed colimit
`Ring.DirectLimit G f` is Henselian along the colimit ideal `⨆ i, (I i).map (of G f i)`. -/
theorem henselianRing [Nonempty ι] [IsDirectedOrder ι] [DirectedSystem G (f · · ·)]
    [∀ i, HenselianRing (G i) (I i)]
    (hI : ∀ i j (hij : i ≤ j), I i ≤ (I j).comap (f i j hij)) :
    HenselianRing (DirectLimit G (f · · ·)) (⨆ i, (I i).map (of G (f · · ·) i)) where
  jac z hz := by
    obtain ⟨i, x, hx, rfl⟩ := (mem_iSup_map_of_iff hI).1 hz
    refine Ideal.mem_jacobson_bot.2 fun c ↦ ?_
    induction c using DirectLimit.induction_on with
    | ih j y =>
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      have hu := Ideal.mem_jacobson_bot.1
        (HenselianRing.jac (I := I k) (hI i k hik hx)) (f j k hjk y)
      simpa using hu.map (of G (f · · ·) k)
  is_henselian P hP a₀ h₁ h₂ := by
    -- Lift `P` to a monic polynomial `q` and `a₀` to an element `b`, at a common stage `k`.
    obtain ⟨i, q, hqm, rfl⟩ := Polynomial.exists_monic_of hP
    obtain ⟨j, b, rfl⟩ := exists_of a₀
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    have hqm := hqm.map (f i k hik)
    rw [← of_f hjk, ← of_comp_f hik, ← Polynomial.map_map] at h₁ h₂ ⊢
    generalize q.map (f i k hik) = q at hqm h₁ h₂ ⊢
    generalize f j k hjk b = b at h₁ h₂ ⊢
    simp only [derivative_map, eval_map_apply] at h₁ h₂
    -- Both conditions descend to a common later stage `l`, where `(G l, I l)` is Henselian.
    obtain ⟨l₁, hkl₁, h₁⟩ := exists_f_mem_of_of_mem_iSup_map hI h₁
    obtain ⟨l₂, hkl₂, h₂⟩ := exists_isUnit_mk_f_of_isUnit_mk_of hI h₂
    obtain ⟨l, hl₁l, hl₂l⟩ := exists_ge_ge l₁ l₂
    have h₂ := h₂.map (Ideal.quotientMap (I l) (f l₂ l hl₂l) (hI l₂ l hl₂l))
    obtain ⟨a, ha, hab⟩ := HenselianRing.is_henselian (I := I l)
      (q.map (f k l (hkl₁.trans hl₁l))) (hqm.map _) (f k l _ b)
      (by simpa [DirectedSystem.map_map' f] using hI l₁ l hl₁l h₁)
      (by simpa [DirectedSystem.map_map' f] using h₂)
    refine ⟨of G (f · · ·) l a, by simpa [Polynomial.map_map] using ha.map (of G (f · · ·) l), ?_⟩
    simpa using (mem_iSup_map_of_iff hI).2 ⟨l, _, hab, rfl⟩

end Ring.DirectLimit
