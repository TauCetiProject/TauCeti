/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Point

/-!
# The Leray–Hirsch map

Let `k` be a commutative ring, `p : E ⟶ B` a continuous map, and for every degree `d` let
`e d : ι d → Hᵈ(E; k)` be a family of global classes on `E`. The **Leray–Hirsch map** in degree `n`
is

`⨁_{d + q = n} ⨁_{i : ι d} H^q(B; k) ⟶ Hⁿ(E; k)`, `(a_{d,i}) ↦ ∑ p^* a_{d,i} ⌣ e_{d,i}`.

The Leray–Hirsch theorem asserts that it is bijective for a locally trivial bundle with fibre `F`
whose classes `e d` restrict to a basis of `Hᵈ` of every fibre, under finiteness hypotheses on the
fibre.

## Main definitions and results

* `TopCat.lerayHirsch`: the Leray–Hirsch map, characterized on summands by
  `TopCat.lerayHirsch_lof`.
* `TopCat.lerayHirsch_bijective_of_isEmpty`: the Leray–Hirsch map over an empty base.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4D.1 (Leray–Hirsch).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory
open scoped DirectSum

universe w u

namespace TopCat

variable {k : Type w} [CommRing k] {E B : TopCat.{w}} (p : E ⟶ B) (n : ℕ) {ι : ℕ → Type u}
  [∀ d, DecidableEq (ι d)]
  (e : ∀ d, ι d → E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) d)

/-- **The Leray–Hirsch map** of `p : E ⟶ B` and a family of classes `e d : ι d → Hᵈ(E; k)` in degree
`n`, `⨁_{d + q = n} ⨁_{i : ι d} H^q(B; k) ⟶ Hⁿ(E; k)`, sending `a` in the summand indexed by
`d + q = n` and `i : ι d` to `p^* a ⌣ e d i`. -/
def lerayHirsch :
    (⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
        B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2) →ₗ[k]
      E.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) n :=
  DirectSum.toModule k _ _ fun j ↦
    (E.singularCup k (λ_ _).inv (λ_ _).hom j.1.1.2 j.1.1.1 n
        (by rw [add_comm]; exact j.1.2)).flip (e j.1.1.1 j.2) ∘ₗ
      (TopCat.singularCohomologyMap p j.1.1.2).hom

/-- The Leray–Hirsch map sends `a` in the summand indexed by `d + q = n` and `i : ι d` to
`p^* a ⌣ e d i`. -/
@[simp]
lemma lerayHirsch_lof (d q : ℕ) (h : d + q = n) (i : ι d)
    (a : B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    lerayHirsch p n e (DirectSum.lof k _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
        ι pq.1.1 ↦
        B.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j.1.1.2)
        ⟨⟨(d, q), h⟩, i⟩ a) =
      E.singularCup k (λ_ _).inv (λ_ _).hom q d n (by omega)
        (TopCat.singularCohomologyMap p q a) (e d i) := by
  simp [lerayHirsch]

/-- The Leray–Hirsch map over an empty base is bijective: its source and target vanish. -/
lemma lerayHirsch_bijective_of_isEmpty [IsEmpty B] : Function.Bijective (lerayHirsch p n e) := by
  have : IsEmpty E := Function.isEmpty p
  have := ModuleCat.subsingleton_of_isZero
    (TauCeti.isZero_singularCohomology_of_isEmpty (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) E n)
  have (j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1) :=
    ModuleCat.subsingleton_of_isZero
      (TauCeti.isZero_singularCohomology_of_isEmpty (𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) B j.1.1.2)
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

end TopCat
