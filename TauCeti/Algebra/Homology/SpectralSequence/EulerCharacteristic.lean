/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.Finiteness.Finsupp
public import TauCeti.Algebra.Homology.EulerCharacteristic.HomologicalComplex
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.Algebra.Homology.SpectralObject.Abutment
public import TauCeti.Algebra.Homology.SpectralSequence.Degeneration

/-!
# Euler characteristic of pages and abutments of spectral sequences

In a spectral sequence `(E_r)` of modules over a ring `R`, each page `E_r` is a homological complex
whose homology is isomorphic to `E_{r+1}`. Whenever a differential vector `u = (u₁, u₂)` has odd
total degree `u₁ + u₂`, the total-degree sign `(p, q) ↦ (-1)^(p + q)` alternates along the
differentials of `E_r` and does not depend on the page index `r`: for cohomological and homological
spectral sequences with `u = (r, 1 - r)`, one has `r + (1 - r) = 1`.

Combining this sign convention with `HomologicalComplex.eulerChar_eq_homologyEulerChar` gives
invariance of the Euler characteristic across the pages of a finitely supported spectral sequence,
and combining `TauCeti.cokernelSequence_shortExact` with rank--nullity gives additivity of `finrank`
across a bounded filtration of the abutment of a spectral object:

* `ComplexShape.eulerCharSignsUp'Sub`, `ComplexShape.eulerCharSignsDown'Sub`,
  `ComplexShape.eulerCharSignsSpectralSequenceNat`,
  `ComplexShape.eulerCharSignsSpectralSequenceFin`: total-degree alternating signs on the page
  shapes of cohomological and homological spectral sequences, built from the odd-total-degree
  constructors `ComplexShape.EulerCharSigns.ofUp'Odd` and companions.
* `CategoryTheory.SpectralSequence.finite_page_X_of_le`: over a Noetherian ring, finite generation
  at `pq` propagates from `E_r` to `E_{r'}` for `r ≤ r'`.
* `CategoryTheory.SpectralSequence.eulerChar_page_eq_of_succ` and
  `CategoryTheory.SpectralSequence.eulerChar_page_eq_of_le`: Euler characteristic invariance across
  one step (needing no Noetherian hypothesis) and across arbitrarily many pages (over a Noetherian
  ring with rank--nullity).
* `CategoryTheory.Abelian.SpectralObject.prop_abutment_of_prop_cokernel`,
  `CategoryTheory.Abelian.SpectralObject.isZero_abutment_of_isZero_cokernel`,
  `CategoryTheory.Abelian.SpectralObject.finite_abutment_of_finite_cokernel`, and
  `CategoryTheory.Abelian.SpectralObject.finrank_abutment_eq_sum_Ico`: extension-closed properties,
  vanishing, finite generation, and `finrank` of the abutment from the graded pieces
  `cokernel (X.abutmentFiltrationMap q m)` of a finite filtration.

## References

* Jean-Pierre Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54
  (1951), 425--505, Chapter II, Section 4.
* John McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 2.6 and Exercise 1.1.
-/

public section

open CategoryTheory Limits Module

universe u v

namespace ComplexShape

/-- Total-degree Euler characteristic signs `(p, q) ↦ (-1)^(p + q)` on `ComplexShape.up' u` for any
shift `u : ℤ × ℤ` of odd total degree `u.1 + u.2`. -/
@[expose, instance_reducible, simps]
def EulerCharSigns.ofUp'Odd {u : ℤ × ℤ} (hu : Odd (u.1 + u.2)) :
    (up' u).EulerCharSigns where
  χ pq := (pq.1 + pq.2).negOnePow
  χ_next {pq pq'} h := by
    have hsum : pq'.1 + pq'.2 = (pq.1 + pq.2) + (u.1 + u.2) := by
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      dsimp at h1 h2
      lia
    rw [hsum, Int.negOnePow_add, Int.negOnePow_odd _ hu, mul_neg, mul_one]

/-- Total-degree Euler characteristic signs `(p, q) ↦ (-1)^(p + q)` on `ComplexShape.down' u` for
any shift `u : ℤ × ℤ` of odd total degree `u.1 + u.2`. -/
@[expose, instance_reducible, simps]
def EulerCharSigns.ofDown'Odd {u : ℤ × ℤ} (hu : Odd (u.1 + u.2)) :
    (down' u).EulerCharSigns where
  χ pq := (pq.1 + pq.2).negOnePow
  χ_next {pq pq'} h := by
    have hsum : pq.1 + pq.2 = (pq'.1 + pq'.2) + (u.1 + u.2) := by
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      dsimp at h1 h2
      lia
    have hneg : (pq.1 + pq.2).negOnePow = -(pq'.1 + pq'.2).negOnePow := by
      rw [hsum, Int.negOnePow_add, Int.negOnePow_odd _ hu, mul_neg, mul_one]
    rw [hneg, neg_neg]

/-- Total-degree Euler characteristic signs `(p, q) ↦ (-1)^(p + q)` on
`ComplexShape.spectralSequenceNat u` for any shift `u : ℤ × ℤ` of odd total degree. -/
@[expose, instance_reducible, simps]
def EulerCharSigns.ofSpectralSequenceNatOdd {u : ℤ × ℤ} (hu : Odd (u.1 + u.2)) :
    (spectralSequenceNat u).EulerCharSigns where
  χ pq := ((pq.1 : ℤ) + pq.2).negOnePow
  χ_next {pq pq'} h := by
    have hsum : (pq'.1 : ℤ) + pq'.2 = ((pq.1 : ℤ) + pq.2) + (u.1 + u.2) := by
      rw [← h.1, ← h.2]
      ring
    rw [hsum, Int.negOnePow_add, Int.negOnePow_odd _ hu, mul_neg, mul_one]

/-- Total-degree Euler characteristic signs `(p, q) ↦ (-1)^(p + q)` on
`ComplexShape.spectralSequenceFin l u` for any shift `u : ℤ × ℤ` of odd total degree. -/
@[expose, instance_reducible, simps]
def EulerCharSigns.ofSpectralSequenceFinOdd {l : ℕ} {u : ℤ × ℤ} (hu : Odd (u.1 + u.2)) :
    (spectralSequenceFin l u).EulerCharSigns where
  χ pq := (pq.1 + pq.2).negOnePow
  χ_next {pq pq'} h := by
    have hsum : pq'.1 + pq'.2 = (pq.1 + pq.2) + (u.1 + u.2) := by
      rw [← h.1, ← h.2]
      ring
    rw [hsum, Int.negOnePow_add, Int.negOnePow_odd _ hu, mul_neg, mul_one]

/-- Alternating signs `(p, q) ↦ (-1)^(p + q)` on page `r` of a cohomological spectral sequence. -/
instance eulerCharSignsUp'Sub (r : ℤ) :
    (up' (r, 1 - r)).EulerCharSigns :=
  EulerCharSigns.ofUp'Odd ⟨0, by lia⟩

/-- The alternating sign at `pq` on `ComplexShape.up' (r, 1 - r)` is `(-1)^(pq.1 + pq.2)`. -/
@[simp]
theorem χ_up'_sub (r : ℤ) (pq : ℤ × ℤ) :
    (up' (r, 1 - r)).χ pq = (pq.1 + pq.2).negOnePow := rfl

/-- Alternating signs `(p, q) ↦ (-1)^(p + q)` on page `r` of a homological spectral sequence. -/
instance eulerCharSignsDown'Sub (r : ℤ) :
    (down' (r, 1 - r)).EulerCharSigns :=
  EulerCharSigns.ofDown'Odd ⟨0, by lia⟩

/-- The alternating sign at `pq` on `ComplexShape.down' (r, 1 - r)` is `(-1)^(pq.1 + pq.2)`. -/
@[simp]
theorem χ_down'_sub (r : ℤ) (pq : ℤ × ℤ) :
    (down' (r, 1 - r)).χ pq = (pq.1 + pq.2).negOnePow := rfl

/-- Alternating signs `(p, q) ↦ (-1)^(p + q)` on page `r` of a first-quadrant cohomological
spectral sequence indexed by `ℕ × ℕ`. -/
instance eulerCharSignsSpectralSequenceNat (r : ℤ) :
    (spectralSequenceNat (r, 1 - r)).EulerCharSigns :=
  EulerCharSigns.ofSpectralSequenceNatOdd ⟨0, by lia⟩

/-- The alternating sign at `pq` on `ComplexShape.spectralSequenceNat (r, 1 - r)` is
`(-1)^(pq.1 + pq.2)`. -/
@[simp]
theorem χ_spectralSequenceNat (r : ℤ) (pq : ℕ × ℕ) :
    (spectralSequenceNat (r, 1 - r)).χ pq = ((pq.1 : ℤ) + pq.2).negOnePow := rfl

/-- Alternating signs `(p, q) ↦ (-1)^(p + q)` on page `r` of a bounded-row cohomological spectral
sequence indexed by `ℤ × Fin l`. -/
instance eulerCharSignsSpectralSequenceFin (l : ℕ) (r : ℤ) :
    (spectralSequenceFin l (r, 1 - r)).EulerCharSigns :=
  EulerCharSigns.ofSpectralSequenceFinOdd ⟨0, by lia⟩

/-- The alternating sign at `pq` on `ComplexShape.spectralSequenceFin l (r, 1 - r)` is
`(-1)^(pq.1 + pq.2)`. -/
@[simp]
theorem χ_spectralSequenceFin (l : ℕ) (r : ℤ) (pq : ℤ × Fin l) :
    (spectralSequenceFin l (r, 1 - r)).χ pq = (pq.1 + pq.2).negOnePow := rfl

end ComplexShape

namespace CategoryTheory.SpectralSequence

section Abelian

variable {C κ : Type*} [Category* C] [Abelian C] {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (E : SpectralSequence C c r₀)

/-- If `E_r` is nonzero at only finitely many positions, then so is every later page `E_{r'}` with
`r ≤ r'`. -/
theorem finite_not_isZero_page_X_of_le {r : ℤ} (hr : r₀ ≤ r)
    (h : {pq : κ | ¬ IsZero ((E.page r).X pq)}.Finite) (r' : ℤ) (hrr' : r ≤ r') :
    {pq : κ | ¬ IsZero ((E.page r' (hr.trans hrr')).X pq)}.Finite :=
  h.subset fun _ hpq hpq₀ ↦ hpq (E.isZero_page_X_of_le hr hpq₀ r' hrr')

end Abelian

section ModuleCat

variable {R : Type u} [Ring R] {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (E : SpectralSequence (ModuleCat.{v} R) c r₀)

/-- **Finite generation propagates to later pages.** Over a Noetherian ring, if `(E.page r).X pq` is
finitely generated, then `(E.page r').X pq` is finitely generated for every `r' ≥ r`. -/
theorem finite_page_X_of_le [IsNoetherianRing R] {r : ℤ} (hr : r₀ ≤ r) {pq : κ}
    [h : Module.Finite R ((E.page r).X pq)] (r' : ℤ) (hrr' : r ≤ r') :
    Module.Finite R ((E.page r' (hr.trans hrr')).X pq) := by
  induction r', hrr' using Int.leInduction with
  | base => exact h
  | succ s hrs ih =>
    have : Module.Finite R ((E.page s (hr.trans hrs)).X pq) := ih
    exact ((E.page s (hr.trans hrs)).finite_homology pq).equiv
      (E.iso s (s + 1) pq rfl (hr.trans hrs)).toLinearEquiv

/-- **One-step Euler characteristic invariance.** Over a ring with rank--nullity, if page `s` has
finitely generated terms, finitely many nonzero objects, and the same alternating signs as page
`s + 1`, then `(E.page s).eulerChar = (E.page (s + 1)).eulerChar`. -/
theorem eulerChar_page_eq_of_succ [StrongRankCondition R] [HasRankNullity.{v} R]
    {s : ℤ} (hs : r₀ ≤ s) [(c s).EulerCharSigns] [(c (s + 1)).EulerCharSigns]
    [∀ pq, Module.Finite R ((E.page s hs).X pq)]
    (hfin : {pq : κ | ¬ IsZero ((E.page s hs).X pq)}.Finite)
    (hχ : ∀ pq, (c s).χ pq = (c (s + 1)).χ pq := by intros; rfl) :
    (E.page s hs).eulerChar = (E.page (s + 1) (Int.le_add_one hs)).eulerChar := by
  rw [(E.page s hs).eulerChar_eq_homologyEulerChar hfin]
  exact finsum_congr fun pq ↦ by
    rw [hχ pq, (E.iso s (s + 1) pq rfl hs).toLinearEquiv.finrank_eq]

/-- **Invariance of the Euler characteristic across pages of a spectral sequence.** Over a
Noetherian ring satisfying rank--nullity, if page `r` has finitely generated terms and finitely many
nonzero objects, and all pages carry the same alternating signs, then every later page `r' ≥ r` has
the same Euler characteristic as page `r`. -/
theorem eulerChar_page_eq_of_le [IsNoetherianRing R] [HasRankNullity.{v} R]
    [∀ s, (c s).EulerCharSigns] {r : ℤ} (hr : r₀ ≤ r)
    [∀ pq, Module.Finite R ((E.page r).X pq)]
    (hfin : {pq : κ | ¬ IsZero ((E.page r).X pq)}.Finite)
    (r' : ℤ) (hrr' : r ≤ r')
    (hχ : ∀ s s' pq, (c s).χ pq = (c s').χ pq := by intros; rfl) :
    (E.page r' (hr.trans hrr')).eulerChar = (E.page r).eulerChar := by
  induction r', hrr' using Int.leInduction with
  | base => rfl
  | succ s hrs ih =>
    have : ∀ pq, Module.Finite R ((E.page s (hr.trans hrs)).X pq) :=
      fun _ ↦ E.finite_page_X_of_le hr s hrs
    rw [← E.eulerChar_page_eq_of_succ (hr.trans hrs)
      (E.finite_not_isZero_page_X_of_le hr hfin s hrs) (fun pq ↦ hχ s (s + 1) pq), ih]

end ModuleCat

end CategoryTheory.SpectralSequence

namespace CategoryTheory.Abelian.SpectralObject

section Abelian

variable {C : Type*} [Category* C] [Abelian C] (X : SpectralObject C EInt)

/-- The transition morphism `F_q H^n ⟶ F_{q+1} H^n` in the abutment filtration of a spectral object
is a monomorphism. -/
instance mono_abutmentFiltrationMap (q n : ℤ) : Mono (X.abutmentFiltrationMap q n) :=
  mono_of_mono_fac (X.abutmentFiltrationMap_ι q n)

/-- The filtration step `0 ⟶ F_q H^n ⟶ F_{q+1} H^n ⟶ F_{q+1} H^n / F_q H^n ⟶ 0` of the abutment of
a spectral object is short exact. -/
lemma shortExact_cokernelSequence_abutmentFiltrationMap (q n : ℤ) :
    (ShortComplex.cokernelSequence (X.abutmentFiltrationMap q n)).ShortExact :=
  TauCeti.cokernelSequence_shortExact _

/-- If `P` contains zero and is closed under isomorphisms and extensions, `F_a H^m` vanishes, and
every graded piece `F_{q+1} H^m / F_q H^m` for `a ≤ q < b` satisfies `P`, then `F_b H^m` satisfies
`P`. -/
theorem prop_abutmentFiltration_of_prop_cokernel (P : ObjectProperty C)
    [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderExtensions]
    {a b m : ℤ} (hab : a ≤ b) (ha : IsZero (X.abutmentFiltration a m))
    (hcok : ∀ q ∈ Finset.Ico a b, P (cokernel (X.abutmentFiltrationMap q m))) :
    P (X.abutmentFiltration b m) := by
  revert hcok
  induction b, hab using Int.leInduction with
  | base => exact fun _ ↦ P.prop_of_isZero ha
  | succ s has ih =>
    intro hcok
    exact P.prop_X₂_of_shortExact (X.shortExact_cokernelSequence_abutmentFiltrationMap s m)
      (ih fun q hq ↦ hcok q (Finset.Ico_subset_Ico_right (Int.le_add_one le_rfl) hq))
      (hcok s (Finset.mem_Ico.2 ⟨has, by lia⟩))

/-- If `P` contains zero and is closed under isomorphisms and extensions, `F_a H^m = 0`,
`F_b H^m ≅ H^m`, and every graded piece `F_{q+1} H^m / F_q H^m` for `a ≤ q < b` satisfies `P`,
then the abutment `X.abutment m` satisfies `P`. -/
theorem prop_abutment_of_prop_cokernel (P : ObjectProperty C)
    [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderExtensions]
    {a b m : ℤ} (hab : a ≤ b) (ha : IsZero (X.abutmentFiltration a m))
    [IsIso (X.abutmentFiltrationι b m)]
    (hcok : ∀ q ∈ Finset.Ico a b, P (cokernel (X.abutmentFiltrationMap q m))) :
    P (X.abutment m) :=
  P.prop_of_iso (asIso (X.abutmentFiltrationι b m))
    (X.prop_abutmentFiltration_of_prop_cokernel P hab ha hcok)

/-- If the filtration of `X.abutment m` starts at `0` at `a`, reaches the whole abutment at `b`,
and has vanishing graded pieces for `a ≤ q < b`, then `X.abutment m` vanishes. -/
theorem isZero_abutment_of_isZero_cokernel {a b m : ℤ} (hab : a ≤ b)
    (ha : IsZero (X.abutmentFiltration a m)) [IsIso (X.abutmentFiltrationι b m)]
    (hcok : ∀ q ∈ Finset.Ico a b, IsZero (cokernel (X.abutmentFiltrationMap q m))) :
    IsZero (X.abutment m) :=
  X.prop_abutment_of_prop_cokernel IsZero hab ha hcok

end Abelian

section ModuleCat

variable {R : Type u} [Ring R] (X : SpectralObject (ModuleCat.{v} R) EInt)

/-- Over any ring, if `F_a H^m = 0` and every graded piece `F_{q+1} H^m / F_q H^m` for `a ≤ q < b`
is finitely generated, then `F_b H^m` is finitely generated. -/
theorem finite_abutmentFiltration_of_finite_cokernel {a b m : ℤ} (hab : a ≤ b)
    (ha : IsZero (X.abutmentFiltration a m))
    (hfin : ∀ q ∈ Finset.Ico a b, Module.Finite R ↑(cokernel (X.abutmentFiltrationMap q m))) :
    Module.Finite R (X.abutmentFiltration b m) := by
  revert hfin
  induction b, hab using Int.leInduction with
  | base =>
    intro _
    have := ModuleCat.subsingleton_of_isZero ha
    infer_instance
  | succ s has ih =>
    intro hfin
    have hS := X.shortExact_cokernelSequence_abutmentFiltrationMap s m
    have : Module.Finite R (ShortComplex.cokernelSequence (X.abutmentFiltrationMap s m)).X₁ :=
      ih fun q hq ↦ hfin q (Finset.Ico_subset_Ico_right (Int.le_add_one le_rfl) hq)
    have : Module.Finite R (ShortComplex.cokernelSequence (X.abutmentFiltrationMap s m)).X₃ :=
      hfin s (Finset.mem_Ico.2 ⟨has, by lia⟩)
    exact Module.Finite.of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS.exact)
      hS.moduleCat_surjective_g

/-- Over any ring, if the filtration of `X.abutment m` starts at `0` at `a`, reaches the whole
abutment at `b`, and has finitely generated graded pieces for `a ≤ q < b`, then `X.abutment m` is
finitely generated. -/
theorem finite_abutment_of_finite_cokernel {a b m : ℤ} (hab : a ≤ b)
    (ha : IsZero (X.abutmentFiltration a m)) [IsIso (X.abutmentFiltrationι b m)]
    (hfin : ∀ q ∈ Finset.Ico a b, Module.Finite R ↑(cokernel (X.abutmentFiltrationMap q m))) :
    Module.Finite R (X.abutment m) := by
  have := X.finite_abutmentFiltration_of_finite_cokernel hab ha hfin
  exact Module.Finite.equiv (asIso (X.abutmentFiltrationι b m)).toLinearEquiv

/-- Over a ring satisfying the strong rank condition and rank--nullity, if `F_a H^m = 0` and every
graded piece `F_{q+1} H^m / F_q H^m` for `a ≤ q < b` is finitely generated, then the rank of
`F_b H^m` is the sum of the ranks of those graded pieces. -/
theorem finrank_abutmentFiltration_eq_sum_Ico [StrongRankCondition R] [HasRankNullity.{v} R]
    {a b m : ℤ} (hab : a ≤ b) (ha : IsZero (X.abutmentFiltration a m))
    (hfin : ∀ q ∈ Finset.Ico a b, Module.Finite R ↑(cokernel (X.abutmentFiltrationMap q m))) :
    finrank R (X.abutmentFiltration b m) =
      ∑ q ∈ Finset.Ico a b, finrank R ↑(cokernel (X.abutmentFiltrationMap q m)) := by
  revert hfin
  induction b, hab using Int.leInduction with
  | base =>
    intro _
    simp [ModuleCat.finrank_eq_zero_of_isZero ha]
  | succ s has ih =>
    intro hfin
    have : Module.Finite R (ShortComplex.cokernelSequence (X.abutmentFiltrationMap s m)).X₂ :=
      X.finite_abutmentFiltration_of_finite_cokernel (Int.le_add_one has) ha hfin
    rw [show Finset.Ico a (s + 1) = insert s (Finset.Ico a s) by grind,
      Finset.sum_insert Finset.right_notMem_Ico,
      ← ih fun q hq ↦ hfin q (Finset.Ico_subset_Ico_right (Int.le_add_one le_rfl) hq)]
    exact ((X.shortExact_cokernelSequence_abutmentFiltrationMap s m).moduleCat_finrank_eq_add).trans
      (add_comm _ _)

/-- **Rank of the abutment from its graded pieces.** Over a ring satisfying the strong rank
condition and rank--nullity, if the filtration of `X.abutment m` starts at `0` at `a`, reaches the
whole abutment at `b`, and has finitely generated graded pieces for `a ≤ q < b`, then the rank of
`X.abutment m` is the sum of the ranks of those graded pieces. -/
theorem finrank_abutment_eq_sum_Ico [StrongRankCondition R] [HasRankNullity.{v} R]
    {a b m : ℤ} (hab : a ≤ b) (ha : IsZero (X.abutmentFiltration a m))
    [IsIso (X.abutmentFiltrationι b m)]
    (hfin : ∀ q ∈ Finset.Ico a b, Module.Finite R ↑(cokernel (X.abutmentFiltrationMap q m))) :
    finrank R (X.abutment m) =
      ∑ q ∈ Finset.Ico a b, finrank R ↑(cokernel (X.abutmentFiltrationMap q m)) := by
  rw [← (asIso (X.abutmentFiltrationι b m)).toLinearEquiv.finrank_eq]
  exact X.finrank_abutmentFiltration_eq_sum_Ico hab ha hfin

end ModuleCat

end CategoryTheory.Abelian.SpectralObject
