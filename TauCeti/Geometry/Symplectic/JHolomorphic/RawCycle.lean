/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.CanonicalCycle
public import TauCeti.Geometry.Symplectic.JHolomorphic.ConfigurationCount

/-!
# Positive cycles of simple curves in the canonical class

Let `X` be a closed symplectic four-manifold with canonical class `κ`, intersection form `B` and
a compatible almost complex structure `J` that is regular for its simple curves. Taubes proves
that a class `e` whose Seiberg–Witten point invariant is nonzero is *good*: `e · S ≥ -1` for
every `J`-holomorphic exceptional sphere `S`. The large-parameter limits of Seiberg–Witten
solutions for `e` and for the conjugate label `κ - e` are positive cycles `C_A` and `C_B` of
simple `J`-holomorphic curves, in the classes `e` and `κ - e`. Their sum `D = C_A + C_B`, with
equal images combined, is a positive cycle in the canonical class, and its intersection algebra
(`TauCeti.IsCanonicalCycle`) forces `e` to be good.

This file carries out that step for cycles of candidate curves. The candidates form a type `ι`:
a curve `c` has a class `cls c`, the genus `g c` of its normalization and a singularity number
`δ c`, and `s` is the set of simple curves of `J`. A positive cycle is a multiplicity assignment
`l : ι →₀ ℕ` supported in `s`, with class `∑ l c • cls c = Finsupp.linearCombination ℕ cls l`.
Assume that distinct curves of `s` meet nonnegatively, by positivity of intersections, and that
every curve of `s` satisfies adjunction and the index bound of a regular `J`
(`TauCeti.IsRegularSimpleCurve`). Then:

* a positive cycle in the canonical class is a canonical cycle
  (`TauCeti.isCanonicalCycle_of_linearCombination_eq`), and its curves are embedded
  (`TauCeti.singularity_eq_zero_of_linearCombination_eq`);
* every subcycle `a ≤ l` of a positive cycle `l` in the canonical class, such as `C_A ≤ C_A + C_B`,
  has virtual dimension zero (`TauCeti.apply_canonical_eq_apply_self_of_le_of_linearCombination_eq`)
  and pairs to `0` or `-1` with every curve of negative square
  (`TauCeti.apply_eq_zero_or_eq_neg_one_of_le_of_linearCombination_eq`), which is an exceptional
  sphere by adjunction;
* the class of such a subcycle is represented by a configuration of embedded curves which are
  pairwise compatible as soon as homologically disjoint curves are
  (`TauCeti.mem_compatibleConfigurations_of_le_of_linearCombination_eq`); repeated curves are tori
  (`TauCeti.genus_eq_one_of_one_lt_of_linearCombination_eq`);
* in particular, if the classes `e` and `κ - e` are represented by positive cycles of simple
  curves, then `e` is good (`TauCeti.neg_one_le_apply_of_linearCombination_add_eq`).
  Contrapositively a class that is not good, `e · S < -1` for some exceptional sphere `S`,
  admits no such pair of cycles; this is the numerical input to the vanishing of the
  Seiberg–Witten point invariant of `e`.

The candidate curves, their classes, genera and singularity numbers, positivity of intersections,
adjunction and the regularity of `J` are inputs here; the geometric theorems supplying them, and
the construction of the cycles from Seiberg–Witten solutions, are separate.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *Seiberg–Witten and Gromov invariants for symplectic 4-manifolds*,
  First International Press Lecture Series 2 (2000).
-/

public section

open LinearMap (BilinForm)

namespace TauCeti

variable {ι H : Type*} [AddCommGroup H] {B : BilinForm ℤ H} {κ : H} {cls : ι → H} {s : Set ι}
  {g δ : ι → ℕ} {l a : ι →₀ ℕ}

variable (hpos : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → 0 ≤ B (cls c) (cls d))
  (hreg : ∀ c ∈ s, IsRegularSimpleCurve B κ (cls c) (g c) (δ c))
  (hs : ↑l.support ⊆ s) (hl : Finsupp.linearCombination ℕ cls l = κ)
include hpos hreg hs hl

/-- **A positive cycle in the canonical class is a canonical cycle.** If distinct curves of `s`
meet nonnegatively and every curve of `s` is a regular simple curve, then a positive cycle `l`
supported in `s` and representing the canonical class satisfies `TauCeti.IsCanonicalCycle`,
indexed by its support. -/
theorem isCanonicalCycle_of_linearCombination_eq :
    IsCanonicalCycle B κ (fun c : l.support ↦ cls c) (fun c ↦ l c) :=
  isCanonicalCycle_of_isRegularSimpleCurve (g := fun c ↦ g c) (δ := fun c ↦ δ c)
    (fun c ↦ Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 c.property))
    (fun {c d} hcd ↦ hpos c (hs c.property) d (hs d.property) (Subtype.coe_ne_coe.2 hcd))
    (fun c ↦ hreg c (hs c.property))
    (by rw [← Finsupp.linearCombination_eq_sum_coe_of_support_subset subset_rfl, hl])

/-- The curves of a positive cycle in the canonical class are embedded. -/
theorem singularity_eq_zero_of_linearCombination_eq {c : ι} (hc : c ∈ l.support) : δ c = 0 :=
  (isCanonicalCycle_of_linearCombination_eq hpos hreg hs hl).singularity_eq_zero
    (fun c : l.support ↦ hreg c (hs c.property)) ⟨c, hc⟩

variable (hB : B.IsSymm)
include hB

/-- A curve occurring with multiplicity at least two in a positive cycle in the canonical class
is a torus. -/
theorem genus_eq_one_of_one_lt_of_linearCombination_eq {c : ι} (hc : 1 < l c) : g c = 1 :=
  (isCanonicalCycle_of_linearCombination_eq hpos hreg hs hl).genus_eq_one_of_one_lt_mult hB
    (fun c : l.support ↦ hreg c (hs c.property)) (i := ⟨c, Finsupp.mem_support_iff.2 (by omega)⟩) hc

/-- Every subcycle `a ≤ l` of a positive cycle in the canonical class has virtual dimension zero:
`κ · e = e · e` for its class `e`. -/
theorem apply_canonical_eq_apply_self_of_le_of_linearCombination_eq (ha : a ≤ l) :
    B κ (Finsupp.linearCombination ℕ cls a) =
      B (Finsupp.linearCombination ℕ cls a) (Finsupp.linearCombination ℕ cls a) := by
  rw [Finsupp.linearCombination_eq_sum_coe_of_support_subset (Finsupp.support_mono ha)]
  exact (isCanonicalCycle_of_linearCombination_eq hpos hreg hs hl).apply_canonical_sum_eq_apply_self
    hB fun c ↦ ha c

/-- Every subcycle `a ≤ l` of a positive cycle in the canonical class pairs to `0` or `-1` with
every curve `S` of `s` of negative square, which is an exceptional sphere. -/
theorem apply_eq_zero_or_eq_neg_one_of_le_of_linearCombination_eq (ha : a ≤ l) {S : ι}
    (hS : S ∈ s) (hSS : B (cls S) (cls S) < 0) :
    B (Finsupp.linearCombination ℕ cls a) (cls S) = 0 ∨
      B (Finsupp.linearCombination ℕ cls a) (cls S) = -1 := by
  rw [Finsupp.linearCombination_eq_sum_coe_of_support_subset (Finsupp.support_mono ha)]
  refine (isCanonicalCycle_of_linearCombination_eq hpos hreg hs hl).apply_sum_eq_zero_or_eq_neg_one
    hB (fun c ↦ ha c) (by rw [(hreg S hS).apply_canonical_eq_neg_one_of_apply_self_neg hSS]; simp)
    fun c ↦ ?_
  by_cases hcS : (c : ι) = S
  · exact .inl (by rw [hcS])
  · exact .inr (hpos c (hs c.property) S hS hcS)

/-- Every subcycle `a ≤ l` of a positive cycle in the canonical class pairs to at least `-1` with
every exceptional sphere of `s`: its class is good. -/
theorem neg_one_le_apply_of_le_of_linearCombination_eq (ha : a ≤ l) {S : ι} (hS : S ∈ s)
    (hSS : B (cls S) (cls S) < 0) : -1 ≤ B (Finsupp.linearCombination ℕ cls a) (cls S) := by
  rcases apply_eq_zero_or_eq_neg_one_of_le_of_linearCombination_eq hpos hreg hs hl hB ha hS hSS
    with h | h <;> omega

/-- The class of a subcycle `a ≤ l` of a positive cycle in the canonical class is represented by a
configuration of embedded curves of `s` (`TauCeti.compatibleConfigurations`), for every
compatibility relation `r` that holds between homologically disjoint curves, such as
disjointness of the images under positivity of intersections. -/
theorem mem_compatibleConfigurations_of_le_of_linearCombination_eq {r : ι → ι → Prop}
    (hr : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → B (cls c) (cls d) = 0 → r c d) (ha : a ≤ l) :
    a ∈ compatibleConfigurations r cls {c ∈ s | δ c = 0} (Finsupp.linearCombination ℕ cls a) := by
  have hcan := isCanonicalCycle_of_linearCombination_eq hpos hreg hs hl
  have hsub : (↑a.support : Set ι) ⊆ ↑l.support := Finsupp.support_mono ha
  rw [mem_compatibleConfigurations]
  refine ⟨fun c hc ↦ ⟨hs (hsub hc), singularity_eq_zero_of_linearCombination_eq hpos hreg hs hl
    (hsub hc)⟩, fun c hc d hd hcd ↦ hr c (hs (hsub hc)) d (hs (hsub hd)) hcd ?_, rfl⟩
  exact hcan.apply_eq_zero_of_ne hB (i := ⟨c, hsub hc⟩) (j := ⟨d, hsub hd⟩)
    (Subtype.coe_ne_coe.1 hcd)

omit hs hl in
/-- **A class with a conjugate pair of cycles is good.** If a positive cycle `a` of curves of
`s` represents a class `e` and a positive cycle `b` of curves of `s` represents the conjugate
class `κ - e`, then `e · S ≥ -1` for every curve `S` of `s` of negative square, which is an
exceptional sphere. -/
theorem neg_one_le_apply_of_linearCombination_add_eq {b : ι →₀ ℕ} (ha : ↑a.support ⊆ s)
    (hb : ↑b.support ⊆ s)
    (hab : Finsupp.linearCombination ℕ cls a + Finsupp.linearCombination ℕ cls b = κ) {S : ι}
    (hS : S ∈ s) (hSS : B (cls S) (cls S) < 0) :
    -1 ≤ B (Finsupp.linearCombination ℕ cls a) (cls S) := by
  classical
  refine neg_one_le_apply_of_le_of_linearCombination_eq (l := a + b) hpos hreg ?_
    (by rw [map_add, hab]) hB le_self_add hS hSS
  exact (Finset.coe_subset.2 Finsupp.support_add).trans (by simpa using ⟨ha, hb⟩)

end TauCeti
