/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Descriptive.Antichain
public import Mathlib.Topology.MetricSpace.CantorScheme

/-!
# Cantor antichains from Cantor schemes

A `Bool`-indexed Cantor scheme `A : List Bool → Set α` with vanishing diameter whose branch
intersections are all nonempty induces a continuous map of Cantor space into `α`, sending each
branch to a chosen point of its intersection; in a pseudometric space the intersection need not
be a single point. If moreover any point of `A (false :: l)` is
`E`-inequivalent to any point of `A (true :: l)`, the images of distinct branches are
`E`-inequivalent: two branches first differ at some position, and their images lie in the two
sibling pieces below their common prefix. So the scheme carries a Cantor antichain for `E` on its
root `A []`.

No closedness of the pieces, completeness of the space or disjointness of siblings is assumed;
the nonempty branch intersections are a hypothesis. Injectivity follows from the antichain
property by reflexivity of `E`. For closure-antitone schemes of nonempty sets in a complete space
the hypothesis can be discharged by Mathlib's `CantorScheme.ClosureAntitone.map_of_vanishingDiam`,
while fusion arguments can supply it for schemes of non-closed sets.

For equality, `E = ⊥`, this recovers under these extra hypotheses the injectivity given by
Mathlib's `CantorScheme.Disjoint.map_injective`, which needs neither vanishing diameter nor
nonempty branch intersections and gives injectivity on the domain of `inducedMap`.

## Main results

* `CantorScheme.VanishingDiam.exists_antichain_map`: the scheme induces a continuous injection of
  Cantor space along the scheme with pairwise `E`-inequivalent images.
* `CantorScheme.VanishingDiam.hasCantorAntichainOn`: the root of the scheme carries a Cantor
  antichain for `E`.

## References

* Ported from `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, `InfinitaryLogic/Descriptive/CantorAntichain.lean`
  (`CantorScheme.exists_antichain_map`).
* Divergences from that source: the results are stated on the vanishing-diameter hypothesis, for
  dot notation; the conclusion is also packaged as `Setoid.HasCantorAntichainOn`; the recursive
  splitting construction of the source is not included.
-/

public section

open Set

universe u

namespace CantorScheme

namespace VanishingDiam

variable {α : Type u} [PseudoMetricSpace α] {A : List Bool → Set α}

/-- **Cantor antichains from a scheme.** A `Bool`-scheme with vanishing diameter, nonempty branch
intersections and `E`-inequivalent siblings induces a continuous injection of Cantor space whose
image of each branch lies along it, and whose images of distinct branches are `E`-inequivalent. -/
theorem exists_antichain_map (hdiam : VanishingDiam A) (E : Setoid α)
    (hlim : ∀ x : ℕ → Bool, (⋂ n, A (PiNat.res x n)).Nonempty)
    (hcross : ∀ l : List Bool, ∀ x ∈ A (false :: l), ∀ y ∈ A (true :: l), ¬ E x y) :
    ∃ f : (ℕ → Bool) → α, Continuous f ∧ Function.Injective f ∧
      (∀ a n, f a ∈ A (PiNat.res a n)) ∧ ∀ a b, a ≠ b → ¬ E (f a) (f b) := by
  classical
  have hdom (x : ℕ → Bool) : x ∈ (inducedMap A).1 := hlim x
  -- siblings are inequivalent in either order
  have hcross' (l : List Bool) (a b : Bool) (hab : a ≠ b) :
      ∀ x ∈ A (a :: l), ∀ y ∈ A (b :: l), ¬ E x y := by
    cases a <;> cases b
    · exact absurd rfl hab
    · exact hcross l
    · exact fun x hx y hy hxy => hcross l y hy x hx (E.symm hxy)
    · exact absurd rfl hab
  let f : (ℕ → Bool) → α := fun x => (inducedMap A).2 ⟨x, hdom x⟩
  have hmem (a : ℕ → Bool) (n : ℕ) : f a ∈ A (PiNat.res a n) := map_mem ⟨a, hdom a⟩ n
  -- two distinct branches first differ at some position, below a common prefix
  have hanti (a b : ℕ → Bool) (hab : a ≠ b) : ¬ E (f a) (f b) := by
    have hres : PiNat.res a (PiNat.firstDiff a b) = PiNat.res b (PiNat.firstDiff a b) :=
      PiNat.res_eq_res.2 fun _ hi => PiNat.apply_eq_of_lt_firstDiff hi
    have hfa := hmem a (PiNat.firstDiff a b + 1)
    have hfb := hmem b (PiNat.firstDiff a b + 1)
    rw [PiNat.res_succ] at hfa hfb
    rw [← hres] at hfb
    exact hcross' _ _ _ (PiNat.apply_firstDiff_ne hab) (f a) hfa (f b) hfb
  refine ⟨f, hdiam.map_continuous.comp (by fun_prop), fun a b hfab => ?_, hmem, hanti⟩
  by_contra hne
  exact hanti a b hne (hfab ▸ E.refl _)

/-- **The root of the scheme carries a Cantor antichain.** A `Bool`-scheme with vanishing
diameter, nonempty branch intersections and `E`-inequivalent siblings gives a Cantor antichain for
`E` on `A []`. -/
theorem hasCantorAntichainOn (hdiam : VanishingDiam A) (E : Setoid α)
    (hlim : ∀ x : ℕ → Bool, (⋂ n, A (PiNat.res x n)).Nonempty)
    (hcross : ∀ l : List Bool, ∀ x ∈ A (false :: l), ∀ y ∈ A (true :: l), ¬ E x y) :
    E.HasCantorAntichainOn (A []) := by
  obtain ⟨f, hf, -, hmem, hE⟩ := hdiam.exists_antichain_map E hlim hcross
  exact Setoid.hasCantorAntichainOn_iff.2 ⟨f, hf, fun a => by simpa using hmem a 0, hE⟩

end VanishingDiam

end CantorScheme
