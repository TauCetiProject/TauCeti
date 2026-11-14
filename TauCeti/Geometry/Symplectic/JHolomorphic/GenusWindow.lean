/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.AreaWindow
public import TauCeti.Geometry.Symplectic.JHolomorphic.ConfigurationCount

/-!
# Finitely many component types of curves below an area bound

Let `X` be a closed symplectic four-manifold with symplectic area `ω` on `H = H₂(X; ℤ)`, canonical
class `κ` and intersection form `B`, and let `J` be a compatible almost complex structure. A simple
`J`-holomorphic curve has two discrete invariants: its class `C ∈ H` and the genus `g` of its
normalization. Gromov compactness is applied one such *type* `(C, g)` at a time, so the
bounded-window compactness of Taubes's curve count needs to know that below an area bound only
finitely many types occur.

`TauCeti.IsComassBounded` (in `TauCeti.Geometry.Symplectic.JHolomorphic.AreaWindow`) supplies the
finiteness of the classes. The genera are bounded by the adjunction formula: a simple curve `C`
with normalization of genus `g` and singularity number `δ ≥ 0` satisfies
`2 g - 2 + 2 δ = C · C + κ · C`, so

`2 g ≤ C · C + κ · C + 2`.

Since only finitely many classes have area at most `R`, this inequality bounds the genera of the
curves of area at most `R` uniformly. The statements below only use that the genus of each type is
bounded by some function `f` of its class; the adjunction inequality is the case
`f C = (C · C + κ · C + 2) / 2`. They take a set `T ⊆ H × ℕ` of types `(C, g)` whose classes lie in
a comass bounded set `S` and whose genera satisfy `g ≤ f C`, and prove:

* only finitely many types of `T` have area at most `R`
  (`TauCeti.IsComassBounded.finite_setOf_area_fst_le`);
* in particular the genera of the types of area at most `R` are bounded
  (`TauCeti.IsComassBounded.exists_forall_snd_le`);
* only finitely many multiplicity assignments `m : H × ℕ →₀ ℕ` supported in `T` represent a
  given class `A`, that is, a positive cycle `∑ m (C, g) C = A` of curves of bounded area has one
  of finitely many lists of component types and multiplicities
  (`TauCeti.IsComassBounded.finite_setOf_linearCombination_fst_eq`). With the types as
  candidates and their classes `Prod.fst`, the first statement is the finiteness hypothesis of
  `TauCeti.finite_setOf_support_subset_area_le`.

The geometric inputs, positivity of area, the comass bound and the genus bound (in practice the
adjunction inequality), are hypotheses here.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52 (2012), Section 2.6 (the adjunction inequality).
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893.
-/

public section

namespace TauCeti

namespace IsComassBounded

variable {H E : Type*} [AddCommGroup H] [NormedAddCommGroup E] [AddGroup.FG H] [NormedSpace ℝ E]
  {l : H →ₗ[ℤ] E} {ω : H →+ ℝ} {K : ℝ} {S : Set H} {f : H → ℤ}
  {T : Set (H × ℕ)}

/-- **Finitely many types below an area bound.** Let `T` be a set of types `(C, g)` whose classes
lie in a comass bounded set and whose genera are bounded by a function of the class, `g ≤ f C`
(for instance by the adjunction inequality `2 g ≤ C · C + κ · C + 2`). If the real extension of
the period map is injective, only finitely many types of `T` have area at most `R`. -/
theorem finite_setOf_area_fst_le (h : IsComassBounded l ω K S)
    (hl : Function.Injective (l.liftBaseChange ℝ)) (hTS : ∀ p ∈ T, p.1 ∈ S)
    (hT : ∀ p ∈ T, (p.2 : ℤ) ≤ f p.1) (R : ℝ) :
    {p ∈ T | ω p.1 ≤ R}.Finite := by
  -- Each of the finitely many classes of area at most `R` carries the genera at most `f C`.
  refine ((h.finite_setOf_area_le hl R).biUnion fun C _ =>
    (Set.finite_singleton C).prod (Set.finite_Iic (f C).toNat)).subset ?_
  rintro ⟨C, g⟩ ⟨hp, hpR⟩
  have hg : (g : ℤ) ≤ f C := hT _ hp
  simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Iic]
  exact ⟨C, ⟨hTS _ hp, hpR⟩, rfl, by omega⟩

/-- **Bounded genera below an area bound.** Under the hypotheses of
`TauCeti.IsComassBounded.finite_setOf_area_fst_le`, the genera of the types of `T` of area at
most `R` are bounded by a constant depending only on `R`. -/
theorem exists_forall_snd_le (h : IsComassBounded l ω K S)
    (hl : Function.Injective (l.liftBaseChange ℝ)) (hTS : ∀ p ∈ T, p.1 ∈ S)
    (hT : ∀ p ∈ T, (p.2 : ℤ) ≤ f p.1) (R : ℝ) :
    ∃ G : ℕ, ∀ p ∈ T, ω p.1 ≤ R → p.2 ≤ G := by
  obtain ⟨G, hG⟩ := ((h.finite_setOf_area_fst_le hl hTS hT R).image Prod.snd).bddAbove
  exact ⟨G, fun p hp hpR => hG ⟨p, ⟨hp, hpR⟩, rfl⟩⟩

/-- **Finitely many cycles of types in a class.** Under the hypotheses of
`TauCeti.IsComassBounded.finite_setOf_area_fst_le`, only finitely many multiplicity assignments
`m` supported in `T` represent a given class `A`, `∑ m (C, g) C = A`: the component types and
multiplicities of a positive cycle of curves in class `A` take finitely many values. -/
theorem finite_setOf_linearCombination_fst_eq (h : IsComassBounded l ω K S)
    (hl : Function.Injective (l.liftBaseChange ℝ)) (hTS : ∀ p ∈ T, p.1 ∈ S)
    (hT : ∀ p ∈ T, (p.2 : ℤ) ≤ f p.1) (A : H) :
    {m : H × ℕ →₀ ℕ | ↑m.support ⊆ T ∧ Finsupp.linearCombination ℕ Prod.fst m = A}.Finite :=
  (finite_setOf_support_subset_area_le (fun p hp => h.area_pos _ (hTS p hp))
    (h.finite_setOf_area_fst_le hl hTS hT (ω A))).subset fun _ hm => ⟨hm.1, hm.2 ▸ le_rfl⟩

end IsComassBounded

end TauCeti
