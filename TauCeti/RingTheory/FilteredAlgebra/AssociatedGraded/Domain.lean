/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Basic
public import TauCeti.RingTheory.FilteredAlgebra.AssociatedGraded.Basic

/-!
# Separated filtrations with a domain as associated graded ring

Let `F` be a decreasing ideal filtration of a ring `A` which is separated, `⋂ₙ Fⁿ = 0`. Every
nonzero `x ∈ A` then has an exact order (`TauCeti.AlgFiltration.exists_mem_notMem_succ`): there is
`n` with `x ∈ Fⁿ` and `x ∉ Fⁿ⁺¹`, so that its class in `Fⁿ / Fⁿ⁺¹`, the principal symbol of `x`,
is nonzero. The product of the principal symbols of `x` and `y` is the class of `x * y` in the
degree given by the sum of the orders. If the associated graded ring has no zero divisors, this
class is nonzero, hence so is `x * y`. Thus a separated filtered ring whose associated graded ring
is a domain is itself a domain; no completeness and no commutativity are needed.

This applies to the Iwasawa algebra of a uniform pro-`p` group and to power series rings, whose
associated graded rings for their natural filtrations are polynomial rings.

## Main results

* `TauCeti.AlgFiltration.nontrivial_of_nontrivial_associatedGraded`: a ring with a nontrivial
  associated graded ring is nontrivial.
* `TauCeti.AlgFiltration.noZeroDivisors_of_noZeroDivisors_associatedGraded` and
  `TauCeti.AlgFiltration.isDomain_of_isDomain_associatedGraded`: the domain property descends
  from the associated graded ring to a separated filtered ring.

## References

* P. Schneider and J. Teitelbaum, *Algebras of `p`-adic distributions and admissible
  representations*, Invent. Math. 153 (2003), §1.
* J.-E. Björk, *Filtered Noetherian rings*, in *Noetherian rings and their applications*, Math.
  Surveys Monogr. 24 (1987).
-/

public section

namespace TauCeti.AlgFiltration

variable {A : Type*} [Ring A] {F : AlgFiltration A}

/-- A ring whose associated graded ring is nontrivial is nontrivial. -/
theorem nontrivial_of_nontrivial_associatedGraded [Nontrivial F.AssociatedGraded] :
    Nontrivial A :=
  ⟨⟨1, 0, fun h => one_ne_zero (α := F.AssociatedGraded) <| by
    rw [one_eq_of_gradedZeroMk, h, map_zero, map_zero]⟩⟩

/-- If the associated graded ring of a separated filtration has no zero divisors, neither does
the filtered ring. -/
theorem noZeroDivisors_of_noZeroDivisors_associatedGraded
    (hF : ∀ x, (∀ n, x ∈ F.ideal n) → x = 0)
    [NoZeroDivisors F.AssociatedGraded] : NoZeroDivisors A where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} hxy := by
    by_contra! h
    obtain ⟨m, hxm, hxm'⟩ := exists_mem_notMem_succ hF h.1
    obtain ⟨n, hyn, hyn'⟩ := exists_mem_notMem_succ hF h.2
    have hx : DirectSum.of F.GradedPiece m ((⟨x, hxm⟩ : F.ideal m) : F.GradedPiece m) ≠ 0 := by
      rwa [Ne, of_mk_eq_zero_iff]
    have hy : DirectSum.of F.GradedPiece n ((⟨y, hyn⟩ : F.ideal n) : F.GradedPiece n) ≠ 0 := by
      rwa [Ne, of_mk_eq_zero_iff]
    have hxy' := mul_ne_zero hx hy
    rw [of_mk_mul_of_mk, Ne, of_mk_eq_zero_iff] at hxy'
    exact hxy' (by simp [hxy])

/-- If the associated graded ring of a separated filtration is a domain, so is the filtered
ring. -/
theorem isDomain_of_isDomain_associatedGraded (hF : ∀ x, (∀ n, x ∈ F.ideal n) → x = 0)
    [IsDomain F.AssociatedGraded] : IsDomain A :=
  have := nontrivial_of_nontrivial_associatedGraded (F := F)
  have := noZeroDivisors_of_noZeroDivisors_associatedGraded hF
  NoZeroDivisors.to_isDomain A

end TauCeti.AlgFiltration
