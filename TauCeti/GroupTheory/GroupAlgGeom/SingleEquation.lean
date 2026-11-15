/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.MalcevEquation
import Mathlib.Order.CompleteLattice.Finset

/-!
# Finite systems and finite unions of algebraic sets as single equations

In a torsion-free CSA group `H` satisfying Vaught's condition (`Group.IsVaught`) and containing
two noncommuting elements `a` and `b`, the word `TauCeti.malcevWord a b x y` vanishes exactly when
both `x` and `y` do, and `TauCeti.malcevOrWord a b x y` vanishes exactly when `x` or `y` does
(see `TauCeti.GroupTheory.MalcevEquation`).

Applied to equations over a coefficient group `G`, with `a` and `b` coefficients whose images in
`H` do not commute, these words turn a conjunction or a disjunction of two equations into one
equation with the same solutions in `H`. Hence every finite system of equations over `G`, and
every finite union of algebraic sets of finite systems, is the algebraic set in `H` of a single
equation. Nonabelian free groups are torsion-free and CSA, and satisfy Vaught's condition by
Lyndon's theorem; over them this is the reduction of conjunctions and disjunctions of equations to
a single equation, on which Merzljakov's theorem on formal solutions of positive sentences is
built.

## Main results

* `TauCeti.GroupAlgGeom.V_singleton_malcevWord`,
  `TauCeti.GroupAlgGeom.V_singleton_malcevOrWord`: intersections and unions of the solution sets
  of two equations are solution sets of one equation.
* `TauCeti.GroupAlgGeom.exists_V_singleton_eq_of_finite`: a finite system has the same solutions
  as a single equation.
* `TauCeti.GroupAlgGeom.exists_V_singleton_eq_biUnion`: a finite union of algebraic sets of
  finite systems is the algebraic set of a single equation.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §3.1, Corollaries 2–5.
* G. S. Makanin, *Decidability of the universal and positive theories of a free group*,
  Math. USSR Izv. 25 (1985), §4.
* R. C. Lyndon, *The equation `a²b² = c²` in free groups*, Michigan Math. J. 6 (1959).
-/

public section

open Monoid.Coprod
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom

open Group

variable {G H : Type*} [Group G] [Group H]

/-! ### Single equations over a coefficient group -/

section Equations

variable {X : Type*} {ι : G →* H} [IsMulTorsionFree H] {a b : G}

/-- Over a torsion-free CSA group satisfying Vaught's condition, Malcev's word in two equations,
with noncommuting coefficients, has the solutions common to both equations. -/
theorem V_singleton_malcevWord (hV : IsVaught H) (hH : IsCSA H) (hab : ¬Commute (ι a) (ι b))
    (s t : GX G X) : V ι {malcevWord (inl a) (inl b) s t} = V ι {s, t} := by
  ext v
  simp [hV.malcevWord_eq_one_iff hH hab]

/-- Over a torsion-free CSA group satisfying Vaught's condition, `malcevOrWord` in two equations,
with noncommuting coefficients, has the solutions of either equation. -/
theorem V_singleton_malcevOrWord (hV : IsVaught H) (hH : IsCSA H) (hab : ¬Commute (ι a) (ι b))
    (s t : GX G X) : V ι {malcevOrWord (inl a) (inl b) s t} = V ι {s} ∪ V ι {t} := by
  ext v
  simp [hV.malcevOrWord_eq_one_iff hH hab]

/-- Over a torsion-free CSA group satisfying Vaught's condition in which two coefficients do not
commute, every finite system of equations has the same solutions as a single equation. -/
theorem exists_V_singleton_eq_of_finite (hV : IsVaught H) (hH : IsCSA H)
    (hab : ¬Commute (ι a) (ι b)) {S : Set (GX G X)} (hS : S.Finite) :
    ∃ s, V ι {s} = V ι S := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨1, by ext v; simp⟩
  | @insert u T _ _ ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨malcevWord (inl a) (inl b) u s, ?_⟩
    rw [V_singleton_malcevWord hV hH hab]
    simp only [Set.insert_eq, V_union, hs]

/-- Over a torsion-free CSA group satisfying Vaught's condition in which two coefficients do not
commute, every finite union of algebraic sets of finite systems is the algebraic set of a single
equation. The empty union is cut out by the commutator of the two coefficients. -/
theorem exists_V_singleton_eq_biUnion (hV : IsVaught H) (hH : IsCSA H)
    (hab : ¬Commute (ι a) (ι b)) {κ : Type*} (t : Finset κ) (S : κ → Set (GX G X))
    (hS : ∀ i ∈ t, (S i).Finite) : ∃ s, V ι {s} = ⋃ i ∈ t, V ι (S i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨inl ⁅a, b⁆, ?_⟩
    rw [V_singleton_inl_eq_empty (by rwa [map_commutatorElement, ne_eq,
      commutatorElement_eq_one_iff_commute])]
    simp
  | insert i t _ ih =>
    obtain ⟨s, hs⟩ := ih fun j hj => hS j (Finset.mem_insert_of_mem hj)
    obtain ⟨u, hu⟩ := exists_V_singleton_eq_of_finite hV hH hab (hS i (Finset.mem_insert_self i t))
    refine ⟨malcevOrWord (inl a) (inl b) u s, ?_⟩
    rw [V_singleton_malcevOrWord hV hH hab, hu, hs, Finset.set_biUnion_insert]

end Equations

end TauCeti.GroupAlgGeom
