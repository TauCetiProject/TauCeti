/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import TauCeti.CategoryTheory.GrothendieckGroup.Exact

/-!
# Finite-support Euler sums

For a family `f : ℤ → G` in an additive commutative group, its Euler sum over a finite set
`s` is

```text
∑ n ∈ s, (-1)ⁿ f(n).
```

The finite set is explicit: `TauCeti.finiteEulerSum f s` is a finite truncation, with no value
assigned to an unsupported infinite sum.  If `f` vanishes outside `s`, the result is independent
of the chosen supporting set.  Translation of the grading changes the sum by the expected sign.

For an invariant additive on the conflations of an exact category,
`TauCeti.ExactK0.AdditiveInvariant.finiteEulerSum` applies this construction to a family of
objects.  Its API records independence of an object support, invariance under pointwise
isomorphism, additivity under pointwise biproducts, and additivity along a degreewise family of
conflations.  These formulas let bounded complexes and finite Ext families share the same
finite-support calculation.

## Main definitions

* `TauCeti.finiteEulerSum`: the finite alternating sum of a `ℤ`-indexed family.
* `TauCeti.ExactK0.AdditiveInvariant.finiteEulerSum`: the corresponding sum of the values of an
  exact-additive invariant on a family of objects.

## Main results

* `TauCeti.finiteEulerSum_eq_of_eq_zero`: independence of the chosen finite support.
* `TauCeti.finiteEulerSum_reindex_add`: translation of the index contributes its parity sign.
* `TauCeti.ExactK0.AdditiveInvariant.finiteEulerSum_biprod`: additivity under pointwise
  biproducts.
* `TauCeti.ExactK0.AdditiveInvariant.finiteEulerSum_conflation`: additivity along degreewise
  conflations.
-/

public section

namespace TauCeti

universe w v u

variable {G : Type*} [AddCommGroup G]

/-- The Euler sum of a `ℤ`-indexed family over an explicit finite set of degrees. -/
def finiteEulerSum (f : ℤ → G) (s : Finset ℤ) : G :=
  ∑ n ∈ s, (n.negOnePow : ℤ) • f n

/-- A finite Euler sum is the alternating sum over its chosen finite set of degrees. -/
theorem finiteEulerSum_def (f : ℤ → G) (s : Finset ℤ) :
    finiteEulerSum f s = ∑ n ∈ s, (n.negOnePow : ℤ) • f n := by
  rw [finiteEulerSum]

@[simp]
theorem finiteEulerSum_empty (f : ℤ → G) : finiteEulerSum f ∅ = 0 := by
  simp [finiteEulerSum]

@[simp]
theorem finiteEulerSum_insert (f : ℤ → G) {s : Finset ℤ} {n : ℤ} (hn : n ∉ s) :
    finiteEulerSum f (insert n s) = (n.negOnePow : ℤ) • f n + finiteEulerSum f s := by
  simp [finiteEulerSum, hn]

/-- Pointwise equal families have equal Euler sums over the same finite set. -/
theorem finiteEulerSum_congr {f g : ℤ → G} {s : Finset ℤ} (h : ∀ n ∈ s, f n = g n) :
    finiteEulerSum f s = finiteEulerSum g s := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [h n hn]

@[simp]
theorem finiteEulerSum_zero (s : Finset ℤ) : finiteEulerSum (fun _ ↦ (0 : G)) s = 0 := by
  simp [finiteEulerSum]

/-- Euler sums distribute over pointwise addition. -/
theorem finiteEulerSum_add (f g : ℤ → G) (s : Finset ℤ) :
    finiteEulerSum (fun n ↦ f n + g n) s = finiteEulerSum f s + finiteEulerSum g s := by
  simp only [finiteEulerSum, smul_add, Finset.sum_add_distrib]

/-- Two finite sets supporting the same family compute the same Euler sum. -/
theorem finiteEulerSum_eq_of_eq_zero (f : ℤ → G) {s t : Finset ℤ}
    (hs : ∀ n, n ∉ s → f n = 0) (ht : ∀ n, n ∉ t → f n = 0) :
    finiteEulerSum f s = finiteEulerSum f t := by
  have hsu : finiteEulerSum f s = finiteEulerSum f (s ∪ t) :=
    Finset.sum_subset Finset.subset_union_left fun n _ hn ↦ by
      rw [hs n hn, smul_zero]
  have htu : finiteEulerSum f t = finiteEulerSum f (s ∪ t) :=
    Finset.sum_subset Finset.subset_union_right fun n _ hn ↦ by
      rw [ht n hn, smul_zero]
  rw [hsu, htu]

/-- Translating the grading by `m` multiplies its Euler sum by `(-1)ᵐ`.  The set on the right is
the corresponding translate of the finite summation range. -/
theorem finiteEulerSum_reindex_add (f : ℤ → G) (m : ℤ) (s : Finset ℤ) :
    finiteEulerSum (fun n ↦ f (n + m)) s =
      (m.negOnePow : ℤ) •
        finiteEulerSum f (s.map (Equiv.addRight m).toEmbedding) := by
  rw [finiteEulerSum, finiteEulerSum, Finset.sum_map, Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp only [Equiv.coe_toEmbedding, Equiv.coe_addRight, Int.negOnePow_add,
    Units.val_mul, smul_smul]
  rw [mul_left_comm, ← Units.val_mul, Int.units_mul_self]
  simp

namespace ExactK0.AdditiveInvariant

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : ExactStructure C} (a : ExactK0.AdditiveInvariant E G)

/-- The Euler sum of an exact-additive invariant on a `ℤ`-indexed family of objects, over an
explicit finite set of degrees. -/
def finiteEulerSum (X : ℤ → C) (s : Finset ℤ) : G :=
  TauCeti.finiteEulerSum (fun n ↦ a.obj (X n)) s

/-- The object-family Euler sum is its defining finite alternating sum. -/
theorem finiteEulerSum_def (X : ℤ → C) (s : Finset ℤ) :
    a.finiteEulerSum X s = ∑ n ∈ s, (n.negOnePow : ℤ) • a.obj (X n) :=
  by rw [finiteEulerSum, TauCeti.finiteEulerSum]

@[simp]
theorem finiteEulerSum_empty (X : ℤ → C) : a.finiteEulerSum X ∅ = 0 :=
  TauCeti.finiteEulerSum_empty _

/-- If the object family is zero outside each of two finite sets, both sets compute the same
Euler sum. -/
theorem finiteEulerSum_eq_of_isZero (X : ℤ → C) {s t : Finset ℤ}
    (hs : ∀ n, n ∉ s → IsZero (X n)) (ht : ∀ n, n ∉ t → IsZero (X n)) :
    a.finiteEulerSum X s = a.finiteEulerSum X t :=
  TauCeti.finiteEulerSum_eq_of_eq_zero _
    (fun n hn ↦ a.obj_eq_zero_of_isZero (hs n hn))
    (fun n hn ↦ a.obj_eq_zero_of_isZero (ht n hn))

/-- Pointwise isomorphic object families have the same Euler sum. -/
theorem finiteEulerSum_iso {X Y : ℤ → C} {s : Finset ℤ}
    (e : ∀ n ∈ s, X n ≅ Y n) : a.finiteEulerSum X s = a.finiteEulerSum Y s :=
  TauCeti.finiteEulerSum_congr fun n hn ↦ a.map_iso (e n hn)

/-- Translating the degrees of an object family changes its Euler sum by the parity sign of the
translation. -/
theorem finiteEulerSum_reindex_add (X : ℤ → C) (m : ℤ) (s : Finset ℤ) :
    a.finiteEulerSum (fun n ↦ X (n + m)) s =
      (m.negOnePow : ℤ) •
        a.finiteEulerSum X (s.map (Equiv.addRight m).toEmbedding) :=
  by
    rw [finiteEulerSum, finiteEulerSum]
    exact TauCeti.finiteEulerSum_reindex_add (G := G) (fun n ↦ a.obj (X n)) m s

/-- The Euler sum of pointwise biproducts is the sum of the two Euler sums. -/
theorem finiteEulerSum_biprod (X Y : ℤ → C) (s : Finset ℤ) :
    a.finiteEulerSum (fun n ↦ X n ⊞ Y n) s =
      a.finiteEulerSum X s + a.finiteEulerSum Y s := by
  rw [finiteEulerSum, finiteEulerSum, finiteEulerSum, ← TauCeti.finiteEulerSum_add]
  apply TauCeti.finiteEulerSum_congr
  intro n _
  exact a.map_conflation (E.conflation_biprodShortComplex (X n) (Y n))

/-- A degreewise family of conflations gives an additive identity of Euler sums.  Only the
degrees in the stated finite range need to be conflations. -/
theorem finiteEulerSum_conflation (S : ℤ → ShortComplex C) (s : Finset ℤ)
    (hS : ∀ n ∈ s, E.Conflation (S n)) :
    a.finiteEulerSum (fun n ↦ (S n).X₂) s =
      a.finiteEulerSum (fun n ↦ (S n).X₁) s +
        a.finiteEulerSum (fun n ↦ (S n).X₃) s := by
  rw [finiteEulerSum, finiteEulerSum, finiteEulerSum, ← TauCeti.finiteEulerSum_add]
  apply TauCeti.finiteEulerSum_congr
  intro n hn
  exact a.map_conflation (hS n hn)

end ExactK0.AdditiveInvariant

end TauCeti
