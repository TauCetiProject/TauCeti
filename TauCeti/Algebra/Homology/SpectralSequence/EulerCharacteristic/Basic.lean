/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.Algebra.Homology.SpectralSequence.BidegreeAssignment
public import TauCeti.Algebra.Homology.SpectralSequence.EulerCharacteristic.Signs
public import TauCeti.CategoryTheory.GrothendieckGroup.Abelian
public import TauCeti.CategoryTheory.ObjectProperty.AdditiveFunction

import TauCeti.Algebra.Homology.EulerCharacteristic.ComplexShape
import TauCeti.Algebra.Homology.EulerCharacteristic.Finite
import TauCeti.Algebra.Homology.SpectralSequence.Degeneration
import TauCeti.Algebra.Homology.SpectralSequence.ModuleCat
import TauCeti.Algebra.Homology.SpectralSequence.SerreClass
import TauCeti.CategoryTheory.ObjectProperty.Homology
import TauCeti.CategoryTheory.ObjectProperty.Kernels

/-!
# Euler characteristics of pages of a spectral sequence

Let `E : SpectralSequence C c r₀` be a spectral sequence in an abelian category with a bidegree
assignment `A : TauCeti.BidegreeAssignment c r₀`, let `P : ObjectProperty C` contain zero and be
closed under kernels and cokernels (for instance a weak Serre class or a Serre class), and let
`v : C → G` be a function into an abelian group that is additive on short exact sequences in `P`.

If page `r` vanishes outside a finite set `s : Finset κ` and every term in `s` lies in `P`, then:

* the alternating sum of `v` weighted by `(-1)^(A.deg pq)` is invariant on passing from page `r` to
  page `r + 1` (`CategoryTheory.SpectralSequence.sum_negOnePow_page_eq_sum_negOnePow_page_add_one`),
  and hence to any later page `r' ≥ r`
  (`CategoryTheory.SpectralSequence.sum_negOnePow_page_eq_sum_negOnePow_page_of_le`).

Specializing to `P = ⊤` yields the identity for any `TauCeti.AbelianK0.AdditiveInvariant`, and
specializing to `ModuleCat R` over a Noetherian ring with rank-nullity (such as a field or `ℤ`)
shows invariance of Mathlib's `HomologicalComplex.eulerChar` across pages
(`CategoryTheory.SpectralSequence.eulerChar_page_eq_eulerChar_page_add_one`,
`CategoryTheory.SpectralSequence.eulerChar_page_eq_eulerChar_page_of_le`).

## References

* Stacks Project, Tag 0BDW (the page-invariance step of Lemma 24.12).
* Stacks Project, Tag 02MO and Tag 0754 (weak Serre subcategories).
-/

public section

namespace CategoryTheory.SpectralSequence

open Limits TauCeti

universe v u

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] {κ : Type*} {c : ℤ → ComplexShape κ}
  {r₀ : ℤ}

/-- **The Euler characteristic of a page equals that of the next page** (Stacks Project, Tag 0BDW,
page step of Lemma 24.12). Let `A` be a bidegree assignment, `P` a property containing zero and
closed under kernels and cokernels (in particular, any weak Serre class), and `v : C → G` a
function into an abelian group that is additive on short exact sequences in `P`. If page `r`
vanishes outside a finite set `s` and its terms in `s` lie in `P`, then

```text
∑ pq ∈ s, (-1)^(A.deg pq) • v ((E.page r hr).X pq) =
  ∑ pq ∈ s, (-1)^(A.deg pq) • v ((E.page (r + 1)).X pq).
``` -/
theorem sum_negOnePow_page_eq_sum_negOnePow_page_add_one
    (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀)
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels]
    {G : Type*} [AddCommGroup G] (v : C → G) (hv : P.IsAdditiveOn v)
    (r : ℤ) (hr : r₀ ≤ r) (s : Finset κ)
    (hs : ∀ pq : κ, pq ∉ s → IsZero ((E.page r hr).X pq))
    (hsP : ∀ pq ∈ s, P ((E.page r hr).X pq)) :
    ∑ pq ∈ s, ((A.deg pq).negOnePow : ℤ) • v ((E.page r hr).X pq) =
      ∑ pq ∈ s, ((A.deg pq).negOnePow : ℤ) • v ((E.page (r + 1)).X pq) := by
  classical
  let _ : (c r).EulerCharSigns := A.eulerCharSigns r hr
  have hP : ∀ pq : κ, P ((E.page r hr).X pq) := fun pq ↦
    if hpq : pq ∈ s then hsP pq hpq else P.prop_of_isZero (hs pq hpq)
  have hsum := (E.page r hr).sum_χ_smul_X_eq_sum_χ_smul_homology P v hv s hs hsP
  simp only [BidegreeAssignment.eulerCharSigns_χ] at hsum
  refine hsum.trans (Finset.sum_congr rfl fun pq _ ↦ ?_)
  rw [P.map_eq_of_iso hv (E.iso r (r + 1) pq rfl hr)
    (P.prop_homology_of_isClosedUnderKernels (E.page r hr) pq (hP _) (hP _) (hP _))]

/-- **Invariance of the page Euler characteristic across later pages.** Under the hypotheses of
`sum_negOnePow_page_eq_sum_negOnePow_page_add_one`, the alternating sum over `s` is unchanged on
every later page `r' ≥ r`. -/
theorem sum_negOnePow_page_eq_sum_negOnePow_page_of_le
    (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀)
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels]
    {G : Type*} [AddCommGroup G] (v : C → G) (hv : P.IsAdditiveOn v)
    (r : ℤ) (hr : r₀ ≤ r) (s : Finset κ)
    (hs : ∀ pq : κ, pq ∉ s → IsZero ((E.page r hr).X pq))
    (hsP : ∀ pq ∈ s, P ((E.page r hr).X pq))
    (r' : ℤ) (hrr' : r ≤ r') :
    ∑ pq ∈ s, ((A.deg pq).negOnePow : ℤ) • v ((E.page r hr).X pq) =
      ∑ pq ∈ s, ((A.deg pq).negOnePow : ℤ) • v ((E.page r' (hr.trans hrr')).X pq) := by
  induction r', hrr' using Int.leInduction with
  | base => rfl
  | succ t hrt ih =>
    refine ih.trans (E.sum_negOnePow_page_eq_sum_negOnePow_page_add_one A P v hv t (hr.trans hrt) s
      (fun pq hpq ↦ E.isZero_page_X_of_le hr (hs pq hpq) t hrt)
      (fun pq _ ↦ E.prop_page_X_of_finset P hr s hs hsP t hrt pq))

/-- Specialization of `sum_negOnePow_page_eq_sum_negOnePow_page_add_one` to a
`TauCeti.AbelianK0.AdditiveInvariant`, taking `P = ⊤`. -/
theorem sum_negOnePow_obj_page_eq_sum_negOnePow_obj_page_add_one
    (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀)
    {G : Type*} [AddCommGroup G] (v : TauCeti.AbelianK0.AdditiveInvariant C G)
    (r : ℤ) (hr : r₀ ≤ r) (s : Finset κ)
    (hs : ∀ pq : κ, pq ∉ s → IsZero ((E.page r hr).X pq)) :
    ∑ pq ∈ s, ((A.deg pq).negOnePow : ℤ) • v.obj ((E.page r hr).X pq) =
      ∑ pq ∈ s, ((A.deg pq).negOnePow : ℤ) • v.obj ((E.page (r + 1)).X pq) :=
  E.sum_negOnePow_page_eq_sum_negOnePow_page_add_one A ⊤ v.obj (v.isAdditiveOn ⊤)
    r hr s hs (fun _ _ ↦ trivial)

/-- Specialization of `sum_negOnePow_page_eq_sum_negOnePow_page_of_le` to a
`TauCeti.AbelianK0.AdditiveInvariant`, taking `P = ⊤`. -/
theorem sum_negOnePow_obj_page_eq_sum_negOnePow_obj_page_of_le
    (E : SpectralSequence C c r₀) (A : BidegreeAssignment c r₀)
    {G : Type*} [AddCommGroup G] (v : TauCeti.AbelianK0.AdditiveInvariant C G)
    (r : ℤ) (hr : r₀ ≤ r) (s : Finset κ)
    (hs : ∀ pq : κ, pq ∉ s → IsZero ((E.page r hr).X pq))
    (r' : ℤ) (hrr' : r ≤ r') :
    ∑ pq ∈ s, ((A.deg pq).negOnePow : ℤ) • v.obj ((E.page r hr).X pq) =
      ∑ pq ∈ s, ((A.deg pq).negOnePow : ℤ) • v.obj ((E.page r' (hr.trans hrr')).X pq) :=
  E.sum_negOnePow_page_eq_sum_negOnePow_page_of_le A ⊤ v.obj (v.isAdditiveOn ⊤)
    r hr s hs (fun _ _ ↦ trivial) r' hrr'

end Abelian

section ModuleCat

variable {R : Type u} [Ring R] [IsNoetherianRing R] {κ : Type*} {c : ℤ → ComplexShape κ}
  {r₀ : ℤ}

/-- **Invariance of Mathlib's `HomologicalComplex.eulerChar` across one page** for a spectral
sequence of modules over a Noetherian ring with rank-nullity (such as a field or `ℤ`). When the
signs of `c r` and `c (r + 1)` agree — which holds automatically by `simp` for all standard
cohomological and homological spectral sequence shapes — the `eulerChar` of page `r` equals that
of page `r + 1`. -/
theorem eulerChar_page_eq_eulerChar_page_add_one [HasRankNullity.{v} R]
    (E : SpectralSequence (ModuleCat.{v} R) c r₀) (r : ℤ) (hr : r₀ ≤ r)
    [(c r).EulerCharSigns] [(c (r + 1)).EulerCharSigns]
    (s : Finset κ) (hs : ∀ pq : κ, pq ∉ s → IsZero ((E.page r hr).X pq))
    (hfg : ∀ pq ∈ s, Module.Finite R ((E.page r hr).X pq))
    (hχ : ∀ pq : κ, (c r).χ pq = (c (r + 1)).χ pq := by simp) :
    (E.page r hr).eulerChar = (E.page (r + 1)).eulerChar := by
  rw [(E.page r hr).eulerChar_eq_homologyEulerChar_of_finset s hs hfg]
  exact finsum_congr fun pq ↦ by
    rw [hχ pq, (E.iso r (r + 1) pq rfl hr).toLinearEquiv.finrank_eq]

/-- **Invariance of Mathlib's `HomologicalComplex.eulerChar` across later pages** for a spectral
sequence of modules over a Noetherian ring with rank-nullity, when signs agree on pages
`t ∈ [r, r')`. -/
theorem eulerChar_page_eq_eulerChar_page_of_le [HasRankNullity.{v} R]
    (E : SpectralSequence (ModuleCat.{v} R) c r₀) [∀ t, (c t).EulerCharSigns]
    (r : ℤ) (hr : r₀ ≤ r)
    (s : Finset κ) (hs : ∀ pq : κ, pq ∉ s → IsZero ((E.page r hr).X pq))
    (hfg : ∀ pq ∈ s, Module.Finite R ((E.page r hr).X pq))
    (r' : ℤ) (hrr' : r ≤ r')
    (hχ : ∀ (t : ℤ), r ≤ t → t < r' → ∀ pq : κ, (c t).χ pq = (c (t + 1)).χ pq := by simp) :
    (E.page r hr).eulerChar = (E.page r' (hr.trans hrr')).eulerChar := by
  induction r', hrr' using Int.leInduction with
  | base => rfl
  | succ t hrt ih =>
    refine (ih (fun u hu hut ↦ hχ u hu (lt_of_lt_of_le hut (Int.le_add_one le_rfl)))).trans ?_
    exact E.eulerChar_page_eq_eulerChar_page_add_one t (hr.trans hrt) s
      (fun pq hpq ↦ E.isZero_page_X_of_le hr (hs pq hpq) t hrt)
      (fun pq hpq ↦ E.finite_page_X_of_le hr (hfg pq hpq) t hrt)
      (hχ t hrt (Int.lt_add_one_iff.2 le_rfl))

end ModuleCat

end CategoryTheory.SpectralSequence
