/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import TauCeti.CategoryTheory.GrothendieckGroup.Abelian
public import TauCeti.CategoryTheory.ObjectProperty.AdditiveFunction

import TauCeti.Algebra.Homology.ShortComplex.Abelian
import TauCeti.CategoryTheory.Abelian.Images
import TauCeti.CategoryTheory.ObjectProperty.Kernels

/-!
# Euler--Poincaré for finitely supported complexes of arbitrary shape

Let `C` be an abelian category, `c : ComplexShape ι` a complex shape equipped with alternating
signs (`ComplexShape.EulerCharSigns`), and `K : HomologicalComplex C c` a complex whose terms
vanish outside a finite set `s : Finset ι`. Suppose `P : ObjectProperty C` contains a zero object
and is closed under kernels and cokernels (for instance, a weak Serre class or a Serre class),
every term `K.X i` for `i ∈ s` lies in `P`, and `v : C → G` is a function into an abelian group
that is additive on short exact sequences whose terms lie in `P`.

This file proves the general Euler--Poincaré identity
(`HomologicalComplex.sum_χ_smul_X_eq_sum_χ_smul_homology`):

```text
∑ i ∈ s, (c.χ i : ℤ) • v (K.X i) = ∑ i ∈ s, (c.χ i : ℤ) • v (K.homology i).
```

The argument needs neither closure of `P` under extensions nor any order or direct-sum regrouping
on the index type `ι`. At each index `i`, the two canonical short exact sequences
`0 ⟶ ker g ⟶ X₂ ⟶ coim g ⟶ 0` and `0 ⟶ im f ⟶ ker g ⟶ H ⟶ 0` for `K.sc i` stay inside `P` and
yield `v (K.X i) = v (K.homology i) + v (im (K.d (c.prev i) i)) + v (im (K.d i (c.next i)))`
(`CategoryTheory.ShortComplex.map_X₂_eq_add_image`). Weighting by `c.χ i` and summing over `i ∈ s`,
each relation `c.Rel i j` appears once from `i` with sign `c.χ i` and once from `j` with sign
`c.χ j = -c.χ i`, so all boundary terms cancel pairwise.

Specializing to `P = ⊤` yields the identity for any `TauCeti.AbelianK0.AdditiveInvariant`
(`HomologicalComplex.sum_χ_smul_obj_X_eq_sum_χ_smul_obj_homology`). For the specialization to
`ModuleCat` Euler characteristics, see `TauCeti.Algebra.Homology.EulerCharacteristic.Finite`.

## References

* Stacks Project, Tag 02MO (weak Serre subcategories) and Tag 0754 (characterisation by kernels,
  cokernels and extensions).
* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 1.3 and 1.6.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace HomologicalComplex

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}

/-- **Euler--Poincaré for a finitely supported complex of arbitrary shape.** Let `c` be a complex
shape with alternating signs (`ComplexShape.EulerCharSigns`), `K : HomologicalComplex C c` a
complex vanishing outside a finite set `s`, and `P` a property containing zero and closed under
kernels and cokernels such that `K.X i` lies in `P` for every `i ∈ s`. Then for any function
`v : C → G` into an abelian group that is additive on short exact sequences in `P`,

```text
∑ i ∈ s, (c.χ i : ℤ) • v (K.X i) = ∑ i ∈ s, (c.χ i : ℤ) • v (K.homology i).
``` -/
theorem sum_χ_smul_X_eq_sum_χ_smul_homology [c.EulerCharSigns]
    (K : HomologicalComplex C c) (P : ObjectProperty C)
    [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    {G : Type*} [AddCommGroup G] (v : C → G) (hv : P.IsAdditiveOn v)
    (s : Finset ι) (hs : ∀ i : ι, i ∉ s → IsZero (K.X i)) (hsP : ∀ i ∈ s, P (K.X i)) :
    ∑ i ∈ s, (c.χ i : ℤ) • v (K.X i) =
      ∑ i ∈ s, (c.χ i : ℤ) • v (K.homology i) := by
  classical
  have hP : ∀ i : ι, P (K.X i) := fun i ↦
    if hi : i ∈ s then hsP i hi else P.prop_of_isZero (hs i hi)
  have hX : ∀ i : ι, v (K.X i) =
      v (K.homology i) + v (Abelian.image (K.d (c.prev i) i)) +
        v (Abelian.image (K.d i (c.next i))) := fun i ↦
    (K.sc i).map_X₂_eq_add_image P v hv (hP _) (hP _) (hP _)
  -- Rewrite the outgoing and incoming boundary terms as sums over `s` indexed by `c.Rel`.
  have hout : ∀ i ∈ s, v (Abelian.image (K.d i (c.next i))) =
      ∑ j ∈ s, if c.Rel i j then v (Abelian.image (K.d i j)) else 0 := by
    intro i _
    by_cases hrel : c.Rel i (c.next i)
    · by_cases hmem : c.next i ∈ s
      · rw [Finset.sum_eq_single (c.next i)]
        · simp [hrel]
        · intro j _ hne
          exact ite_eq_right (fun h ↦ hne (c.next_eq' h).symm)
        · intro h; exact absurd hmem h
      · rw [P.map_eq_zero_of_isZero hv
          (TauCeti.Abelian.isZero_abelianImage_of_isZero_tgt _ (hs _ hmem))]
        symm
        refine Finset.sum_eq_zero fun j _ ↦ ite_eq_right fun h ↦ hmem ?_
        rwa [c.next_eq' h]
    · rw [P.map_eq_zero_of_isZero hv
        (TauCeti.Abelian.isZero_abelianImage_of_eq_zero (K.shape _ _ hrel))]
      symm
      refine Finset.sum_eq_zero fun j _ ↦ ite_eq_right fun h ↦ hrel ?_
      rwa [c.next_eq' h]
  have hin : ∀ j ∈ s, v (Abelian.image (K.d (c.prev j) j)) =
      ∑ i ∈ s, if c.Rel i j then v (Abelian.image (K.d i j)) else 0 := by
    intro j _
    by_cases hrel : c.Rel (c.prev j) j
    · by_cases hmem : c.prev j ∈ s
      · rw [Finset.sum_eq_single (c.prev j)]
        · simp [hrel]
        · intro i _ hne
          exact ite_eq_right (fun h ↦ hne (c.prev_eq' h).symm)
        · intro h; exact absurd hmem h
      · rw [P.map_eq_zero_of_isZero hv
          (TauCeti.Abelian.isZero_abelianImage_of_isZero_src _ (hs _ hmem))]
        symm
        refine Finset.sum_eq_zero fun i _ ↦ ite_eq_right fun h ↦ hmem ?_
        rwa [c.prev_eq' h]
    · rw [P.map_eq_zero_of_isZero hv
        (TauCeti.Abelian.isZero_abelianImage_of_eq_zero (K.shape _ _ hrel))]
      symm
      refine Finset.sum_eq_zero fun i _ ↦ ite_eq_right fun h ↦ hrel ?_
      rwa [c.prev_eq' h]
  -- Expand `v (K.X i)` in the sum and cancel the paired boundary sums using `c.χ_next`.
  have hsum : ∑ i ∈ s, (c.χ i : ℤ) • v (K.X i) =
      ∑ i ∈ s, (c.χ i : ℤ) • v (K.homology i) +
      (∑ i ∈ s, ∑ j ∈ s,
        if c.Rel i j then (c.χ i : ℤ) • v (Abelian.image (K.d i j)) else 0) +
      (∑ j ∈ s, ∑ i ∈ s,
        if c.Rel i j then (c.χ j : ℤ) • v (Abelian.image (K.d i j)) else 0) := by
    calc ∑ i ∈ s, (c.χ i : ℤ) • v (K.X i)
        = ∑ i ∈ s, ((c.χ i : ℤ) • v (K.homology i) +
            (c.χ i : ℤ) • v (Abelian.image (K.d i (c.next i))) +
            (c.χ i : ℤ) • v (Abelian.image (K.d (c.prev i) i))) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hX i, smul_add, smul_add]
          abel
      _ = ∑ i ∈ s, (c.χ i : ℤ) • v (K.homology i) +
          ∑ i ∈ s, (c.χ i : ℤ) • v (Abelian.image (K.d i (c.next i))) +
          ∑ i ∈ s, (c.χ i : ℤ) • v (Abelian.image (K.d (c.prev i) i)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = _ := by
          congr 1
          · congr 1
            refine Finset.sum_congr rfl fun i hi ↦ ?_
            rw [hout i hi, Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            split_ifs <;> simp
          · refine Finset.sum_congr rfl fun j hj ↦ ?_
            rw [hin j hj, Finset.smul_sum]
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            split_ifs <;> simp
  have hcancel :
      (∑ i ∈ s, ∑ j ∈ s,
          if c.Rel i j then (c.χ i : ℤ) • v (Abelian.image (K.d i j)) else 0) +
      (∑ j ∈ s, ∑ i ∈ s,
          if c.Rel i j then (c.χ j : ℤ) • v (Abelian.image (K.d i j)) else 0) = 0 := by
    rw [Finset.sum_comm (s := s) (t := s) (f := fun j i ↦
      if c.Rel i j then (c.χ j : ℤ) • v (Abelian.image (K.d i j)) else 0),
      ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    by_cases hrel : c.Rel i j
    · simp only [hrel, ↓reduceIte, c.χ_next hrel, Units.val_neg, neg_smul, add_neg_cancel]
    · simp [hrel]
  rw [hsum, add_assoc, hcancel, add_zero]

/-- **Euler--Poincaré for an additive invariant on a finitely supported complex of arbitrary
shape.** This is the specialization of `HomologicalComplex.sum_χ_smul_X_eq_sum_χ_smul_homology`
to `P = ⊤`. -/
theorem sum_χ_smul_obj_X_eq_sum_χ_smul_obj_homology [c.EulerCharSigns]
    (K : HomologicalComplex C c) {G : Type*} [AddCommGroup G]
    (v : TauCeti.AbelianK0.AdditiveInvariant C G)
    (s : Finset ι) (hs : ∀ i : ι, i ∉ s → IsZero (K.X i)) :
    ∑ i ∈ s, (c.χ i : ℤ) • v.obj (K.X i) =
      ∑ i ∈ s, (c.χ i : ℤ) • v.obj (K.homology i) :=
  K.sum_χ_smul_X_eq_sum_χ_smul_homology ⊤ v.obj (v.isAdditiveOn ⊤) s hs (fun _ _ ↦ trivial)

end Abelian

end HomologicalComplex
