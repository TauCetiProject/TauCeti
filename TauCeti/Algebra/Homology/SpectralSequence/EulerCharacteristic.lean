/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.Algebra.Homology.EulerCharacteristic.ComplexShape
public import TauCeti.Algebra.Homology.SpectralObject.Abutment
import TauCeti.Algebra.Category.ModuleCat.Finrank
import TauCeti.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.Algebra.Homology.SpectralSequence.Degeneration

/-!
# Euler characteristic of spectral sequences and filtered abutments

Let `E` be a spectral sequence of `R`-modules over a Noetherian ring satisfying
`StrongRankCondition` and `HasRankNullity` (for instance a division ring or a Noetherian
commutative domain). Because each page `E_{r+1}` is isomorphic to the homology of `E_r`,
subquotients preserve finite generation (`CategoryTheory.SpectralSequence.finite_page_X_of_le`), and
when the alternating signs `(c s).χ` are independent of the page `s`, Euler–Poincaré for arbitrary
complex shapes (`HomologicalComplex.sum_eulerCharSigns_finrank_X_eq_sum_finrank_homology`) shows
that the Euler characteristic `(E.page r).eulerChar` is constant across all pages `r' ≥ r` once
page `r` has finite support and finitely generated terms
(`CategoryTheory.SpectralSequence.eulerChar_page_eq_of_le`, specialized to cohomological spectral
sequences in `CategoryTheory.CohomologicalSpectralSequence.eulerChar_page_eq_of_le`).

On the abutment side, for a spectral object `X` indexed by `EInt`, each filtration inclusion
`F_q H^n ⟶ F_{q+1} H^n` fits into a short exact sequence with quotient
`cokernel (X.abutmentFiltrationMap q n)`
(`CategoryTheory.Abelian.SpectralObject.shortExact_abutmentFiltrationMap`).
When the filtration vanishes at `a` and exhausts `H^n` at `b`, induction along `Ico a b` transfers
vanishing (`isZero_abutment_of_forall_isZero_cokernel`), finite generation
(`finite_abutment_of_forall_finite_cokernel`), and `finrank` (`finrank_abutment_eq_sum_Ico`) from
the graded pieces to the abutment. Combining strong convergence on a finite box of bidegrees with
total-degree alternating signs equates `(E.page r).eulerChar` with the alternating sum of the ranks
of `X.abutment` (`CategoryTheory.CohomologicalSpectralSequence.eulerChar_page_eq_sum_abutment`).

## Main results

* `CategoryTheory.ShortComplex.ShortExact.moduleCat_finite_X₂`: in `ModuleCat R`, an extension of
  finitely generated modules is finitely generated.
* `CategoryTheory.SpectralSequence.finite_page_X_of_le`: over a Noetherian ring, finitely generated
  objects on page `r` stay finitely generated on every page `r' ≥ r`.
* `CategoryTheory.SpectralSequence.eulerChar_page_eq_of_le` and
  `CategoryTheory.CohomologicalSpectralSequence.eulerChar_page_eq_of_le`: invariance of the Euler
  characteristic across pages of a spectral sequence.
* `CategoryTheory.Abelian.SpectralObject.isZero_abutment_of_forall_isZero_cokernel`,
  `CategoryTheory.Abelian.SpectralObject.finite_abutment_of_forall_finite_cokernel`, and
  `CategoryTheory.Abelian.SpectralObject.finrank_abutment_eq_sum_Ico`: vanishing, finite generation,
  and rank of a finitely filtered abutment from its graded pieces.
* `CategoryTheory.CohomologicalSpectralSequence.eulerChar_page_eq_sum_abutment`: the Euler
  characteristic of a converged page equals the alternating sum of the ranks of the abutment.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II, §3.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 1.15 and Chapter 2.
-/

public section

open CategoryTheory Limits Module

universe u v

namespace CategoryTheory.ShortComplex.ShortExact

/-- Over any ring `R`, if `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is a short exact sequence in `ModuleCat R` with
`X₁` and `X₃` finitely generated, then `X₂` is finitely generated. -/
theorem moduleCat_finite_X₂ {R : Type u} [Ring R] {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) [Module.Finite R S.X₁] [Module.Finite R S.X₃] :
    Module.Finite R S.X₂ :=
  Module.Finite.of_exact (f := S.f.hom) (g := S.g.hom)
    ((moduleCat_exact_iff_function_exact S).1 hS.exact) hS.moduleCat_surjective_g

end CategoryTheory.ShortComplex.ShortExact

namespace CategoryTheory.SpectralSequence

section Finite

variable {R : Type u} [Ring R] [IsNoetherianRing R]
  {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  (E : SpectralSequence (ModuleCat.{v} R) c r₀)

/-- Over a Noetherian ring, if the object at `pq` on page `r` of a spectral sequence of modules is
finitely generated, then the object at `pq` on every later page `r' ≥ r` is finitely generated. -/
theorem finite_page_X_of_le {r : ℤ} (hr : r₀ ≤ r) {pq : κ}
    (h : Module.Finite R ((E.page r).X pq)) (r' : ℤ) (hrr' : r ≤ r') :
    Module.Finite R ((E.page r' (hr.trans hrr')).X pq) := by
  induction r', hrr' using Int.leInduction with
  | base => exact h
  | succ s hrs ih =>
    have : Module.Finite R ((E.page s (hr.trans hrs)).sc pq).X₂ := ih
    have : Module.Finite R ((E.page s (hr.trans hrs)).homology pq) :=
      ((E.page s (hr.trans hrs)).sc pq).finite_homology
    exact .equiv (E.iso s (s + 1) pq rfl (hr.trans hrs)).toLinearEquiv

end Finite

section EulerChar

variable {R : Type u} [Ring R] [IsNoetherianRing R] [StrongRankCondition R] [HasRankNullity.{v} R]
  {κ : Type*} {c : ℤ → ComplexShape κ} [∀ r, (c r).EulerCharSigns] {r₀ : ℤ}
  (E : SpectralSequence (ModuleCat.{v} R) c r₀)

/-- Over a Noetherian ring satisfying `StrongRankCondition` and `HasRankNullity`, if page `r` of a
spectral sequence vanishes outside `s : Finset κ`, has finitely generated terms on `s`, and the
Euler characteristic signs `(c t).χ` agree on `s` for `r ≤ t ≤ r'`, then the alternating sum of
ranks over `s` on page `r'` equals that on page `r`. -/
theorem sum_eulerCharSigns_finrank_page_X_eq_of_le {r : ℤ} (hr : r₀ ≤ r) {s : Finset κ}
    (hs : ∀ pq ∉ s, IsZero ((E.page r).X pq))
    (hfin : ∀ pq ∈ s, Module.Finite R ((E.page r).X pq))
    (r' : ℤ) (hrr' : r ≤ r')
    (hχ : ∀ t, r ≤ t → t ≤ r' → ∀ pq ∈ s, (c t).χ pq = (c r).χ pq) :
    ∑ pq ∈ s, ((c r').χ pq : ℤ) * finrank R ((E.page r' (hr.trans hrr')).X pq) =
      ∑ pq ∈ s, ((c r).χ pq : ℤ) * finrank R ((E.page r).X pq) := by
  induction r', hrr' using Int.leInduction with
  | base => rfl
  | succ t hrt ih =>
    have hstep := (E.page t (hr.trans hrt)).sum_eulerCharSigns_finrank_X_eq_sum_finrank_homology
      (fun pq hpq ↦ E.isZero_page_X_of_le hr (hs pq hpq) t hrt)
      (fun pq hpq ↦ E.finite_page_X_of_le hr (hfin pq hpq) t hrt)
    rw [← ih (fun u hru hut ↦ hχ u hru (hut.trans (Int.le_add_one le_rfl))), hstep]
    refine Finset.sum_congr rfl fun pq hpq ↦ ?_
    rw [hχ (t + 1) (Int.le_add_one hrt) le_rfl pq hpq,
      hχ t hrt (Int.le_add_one le_rfl) pq hpq,
      (E.iso t (t + 1) pq rfl (hr.trans hrt)).toLinearEquiv.finrank_eq]

/-- **Page invariance of the Euler characteristic of a spectral sequence.** Under the hypotheses of
`sum_eulerCharSigns_finrank_page_X_eq_of_le`, `(E.page r').eulerChar = (E.page r).eulerChar` for
every `r' ≥ r`. -/
theorem eulerChar_page_eq_of_le {r : ℤ} (hr : r₀ ≤ r) {s : Finset κ}
    (hs : ∀ pq ∉ s, IsZero ((E.page r).X pq))
    (hfin : ∀ pq ∈ s, Module.Finite R ((E.page r).X pq))
    (r' : ℤ) (hrr' : r ≤ r')
    (hχ : ∀ t, r ≤ t → t ≤ r' → ∀ pq ∈ s, (c t).χ pq = (c r).χ pq) :
    (E.page r' (hr.trans hrr')).eulerChar = (E.page r).eulerChar := by
  nontriviality R
  rw [(E.page r' (hr.trans hrr')).eulerChar_eq_sum_finSet_of_finrankSupport_subset s
      ((GradedObject.finrankSupport_subset_iff _ _).2 fun pq hpq ↦
        ModuleCat.finrank_eq_zero_of_isZero (E.isZero_page_X_of_le hr (hs pq hpq) r' hrr')),
    (E.page r).eulerChar_eq_sum_finSet_of_finrankSupport_subset s
      ((GradedObject.finrankSupport_subset_iff _ _).2 fun pq hpq ↦
        ModuleCat.finrank_eq_zero_of_isZero (hs pq hpq))]
  exact E.sum_eulerCharSigns_finrank_page_X_eq_of_le hr hs hfin r' hrr' hχ

end EulerChar

end CategoryTheory.SpectralSequence

namespace CategoryTheory.Abelian.SpectralObject

section General

variable {C : Type*} [Category* C] [Abelian C] (X : SpectralObject C EInt)

instance (q n : ℤ) : Mono (X.abutmentFiltrationMap q n) :=
  mono_of_mono_fac (X.abutmentFiltrationMap_ι q n)

/-- Each step `F_q H^n ⟶ F_{q+1} H^n` of the filtration of the abutment fits into a short exact
sequence with its cokernel. -/
theorem shortExact_abutmentFiltrationMap (q n : ℤ) :
    (ShortComplex.mk (X.abutmentFiltrationMap q n)
      (cokernel.π (X.abutmentFiltrationMap q n)) (cokernel.condition _)).ShortExact :=
  { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }

/-- If `F_a H^n` is zero and every graded piece `F_{q+1} H^n / F_q H^n` for `a ≤ q < b` is zero,
then `F_b H^n` is zero. -/
theorem isZero_abutmentFiltration_of_forall_isZero_cokernel {a b n : ℤ} (hab : a ≤ b)
    (ha : IsZero (X.abutmentFiltration a n))
    (hcok : ∀ q ∈ Finset.Ico a b, IsZero (cokernel (X.abutmentFiltrationMap q n))) :
    IsZero (X.abutmentFiltration b n) := by
  induction b, hab using Int.leInduction with
  | base => exact ha
  | succ q haq ih =>
    exact (X.shortExact_abutmentFiltrationMap q n).exact.isZero_of_both_isZero
      (ih fun i hi ↦ hcok i (Finset.mem_Ico.2 ⟨(Finset.mem_Ico.1 hi).1,
        (Finset.mem_Ico.1 hi).2.trans_le (Int.le_add_one le_rfl)⟩))
      (hcok q (Finset.mem_Ico.2 ⟨haq, Int.lt_add_one_iff.2 le_rfl⟩))

/-- If the filtration of `X.abutment n` starts at `0` at `a`, exhausts the abutment at `b ≥ a`, and
has vanishing graded pieces on `Ico a b`, then `X.abutment n` is zero. -/
theorem isZero_abutment_of_forall_isZero_cokernel {a b n : ℤ} (hab : a ≤ b)
    (ha : IsZero (X.abutmentFiltration a n)) (hb : IsIso (X.abutmentFiltrationι b n))
    (hcok : ∀ q ∈ Finset.Ico a b, IsZero (cokernel (X.abutmentFiltrationMap q n))) :
    IsZero (X.abutment n) :=
  have := hb
  (X.isZero_abutmentFiltration_of_forall_isZero_cokernel hab ha hcok).of_iso
    (asIso (X.abutmentFiltrationι b n)).symm

end General

section ModuleCat

variable {R : Type u} [Ring R] (X : SpectralObject (ModuleCat.{v} R) EInt)

/-- Over any ring `R`, if `F_a H^n` is zero and every graded piece `F_{q+1} H^n / F_q H^n` for
`a ≤ q < b` is finitely generated, then `F_b H^n` is finitely generated. -/
theorem finite_abutmentFiltration_of_forall_finite_cokernel {a b n : ℤ} (hab : a ≤ b)
    (ha : IsZero (X.abutmentFiltration a n))
    (hcok : ∀ q ∈ Finset.Ico a b, Module.Finite R ↥(cokernel (X.abutmentFiltrationMap q n))) :
    Module.Finite R (X.abutmentFiltration b n) := by
  induction b, hab using Int.leInduction with
  | base =>
    have := ModuleCat.subsingleton_of_isZero ha
    infer_instance
  | succ q haq ih =>
    have : Module.Finite R (X.abutmentFiltration q n) :=
      ih fun i hi ↦ hcok i (Finset.mem_Ico.2 ⟨(Finset.mem_Ico.1 hi).1,
        (Finset.mem_Ico.1 hi).2.trans_le (Int.le_add_one le_rfl)⟩)
    have : Module.Finite R ↥(cokernel (X.abutmentFiltrationMap q n)) :=
      hcok q (Finset.mem_Ico.2 ⟨haq, Int.lt_add_one_iff.2 le_rfl⟩)
    exact (X.shortExact_abutmentFiltrationMap q n).moduleCat_finite_X₂

/-- Over any ring `R`, if the filtration of `X.abutment n` starts at `0` at `a`, exhausts the
abutment at `b ≥ a`, and has finitely generated graded pieces on `Ico a b`, then `X.abutment n` is
finitely generated. -/
theorem finite_abutment_of_forall_finite_cokernel {a b n : ℤ} (hab : a ≤ b)
    (ha : IsZero (X.abutmentFiltration a n)) (hb : IsIso (X.abutmentFiltrationι b n))
    (hcok : ∀ q ∈ Finset.Ico a b, Module.Finite R ↥(cokernel (X.abutmentFiltrationMap q n))) :
    Module.Finite R (X.abutment n) :=
  have := hb
  have := X.finite_abutmentFiltration_of_forall_finite_cokernel hab ha hcok
  .equiv (asIso (X.abutmentFiltrationι b n)).toLinearEquiv

/-- Over a ring satisfying `StrongRankCondition` and `HasRankNullity`, if `F_a H^n` is zero and
every graded piece `F_{q+1} H^n / F_q H^n` for `a ≤ q < b` is finitely generated, then the rank of
`F_b H^n` is the sum of the ranks of those graded pieces. -/
theorem finrank_abutmentFiltration_eq_sum_Ico [StrongRankCondition R] [HasRankNullity.{v} R]
    {a b n : ℤ} (hab : a ≤ b) (ha : IsZero (X.abutmentFiltration a n))
    (hcok : ∀ q ∈ Finset.Ico a b, Module.Finite R ↥(cokernel (X.abutmentFiltrationMap q n))) :
    finrank R (X.abutmentFiltration b n) =
      ∑ q ∈ Finset.Ico a b, finrank R ↥(cokernel (X.abutmentFiltrationMap q n)) := by
  nontriviality R
  induction b, hab using Int.leInduction with
  | base =>
    simp [ModuleCat.finrank_eq_zero_of_isZero ha]
  | succ q haq ih =>
    have hcok' : ∀ i ∈ Finset.Ico a (q + 1),
        Module.Finite R ↥(cokernel (X.abutmentFiltrationMap i n)) :=
      fun i hi ↦ hcok i (Finset.mem_Ico.2 ⟨(Finset.mem_Ico.1 hi).1, (Finset.mem_Ico.1 hi).2⟩)
    have : Module.Finite R (X.abutmentFiltration (q + 1) n) :=
      X.finite_abutmentFiltration_of_forall_finite_cokernel (Int.le_add_one haq) ha hcok'
    have hIco : Finset.Ico a (q + 1) = insert q (Finset.Ico a q) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      lia
    rw [hIco, Finset.sum_insert (by simp),
      ← ih (fun i hi ↦ hcok i (Finset.mem_Ico.2 ⟨(Finset.mem_Ico.1 hi).1,
        (Finset.mem_Ico.1 hi).2.trans_le (Int.le_add_one le_rfl)⟩)),
      (X.shortExact_abutmentFiltrationMap q n).moduleCat_finrank_eq_add, add_comm]

/-- Over a ring satisfying `StrongRankCondition` and `HasRankNullity`, if the filtration of
`X.abutment n` starts at `0` at `a`, exhausts the abutment at `b ≥ a`, and has finitely generated
graded pieces on `Ico a b`, then the rank of `X.abutment n` is the sum of the ranks of those graded
pieces. -/
theorem finrank_abutment_eq_sum_Ico [StrongRankCondition R] [HasRankNullity.{v} R]
    {a b n : ℤ} (hab : a ≤ b) (ha : IsZero (X.abutmentFiltration a n))
    (hb : IsIso (X.abutmentFiltrationι b n))
    (hcok : ∀ q ∈ Finset.Ico a b, Module.Finite R ↥(cokernel (X.abutmentFiltrationMap q n))) :
    finrank R (X.abutment n) =
      ∑ q ∈ Finset.Ico a b, finrank R ↥(cokernel (X.abutmentFiltrationMap q n)) := by
  have := hb
  rw [← (asIso (X.abutmentFiltrationι b n)).toLinearEquiv.finrank_eq]
  exact X.finrank_abutmentFiltration_eq_sum_Ico hab ha hcok

end ModuleCat

end CategoryTheory.Abelian.SpectralObject

namespace CategoryTheory.CohomologicalSpectralSequence

variable {R : Type u} [Ring R] [StrongRankCondition R] [HasRankNullity.{v} R]

/-- **Page invariance of the Euler characteristic of a cohomological spectral sequence.** Over a
Noetherian ring satisfying `StrongRankCondition` and `HasRankNullity`, if page `r` vanishes outside
a finite set `s` of bidegrees and has finitely generated terms on `s`, then
`(E.page r').eulerChar = (E.page r).eulerChar` for every `r' ≥ r`. -/
theorem eulerChar_page_eq_of_le [IsNoetherianRing R] {r₀ : ℤ}
    (E : CohomologicalSpectralSequence (ModuleCat.{v} R) r₀) {r : ℤ} (hr : r₀ ≤ r)
    {s : Finset (ℤ × ℤ)} (hs : ∀ pq ∉ s, IsZero ((E.page r).X pq))
    (hfin : ∀ pq ∈ s, Module.Finite R ((E.page r).X pq)) (r' : ℤ) (hrr' : r ≤ r') :
    (E.page r' (hr.trans hrr')).eulerChar = (E.page r).eulerChar :=
  SpectralSequence.eulerChar_page_eq_of_le E hr hs hfin r' hrr' fun _ _ _ _ _ ↦ by
    simp [ComplexShape.eulerCharSignsCohomologicalSpectralSequence_χ]

/-- **Euler characteristic of a converged page equals the alternating sum of abutment ranks.**
Suppose page `r` of a cohomological spectral sequence `E` vanishes outside the bidegrees `pq` with
`pq.1 + pq.2 ∈ I` and `pq.2 ∈ Ico a b`, and at each such bidegree `(E.page r).X pq` is finitely
generated and isomorphic to the graded piece
`cokernel (X.abutmentFiltrationMap pq.2 (pq.1 + pq.2))` of a filtration of `X.abutment` that starts
at `0` at `a` and is exhaustive at `b`. Then `(E.page r).eulerChar` equals
`∑ n ∈ I, (-1)^n * finrank R (X.abutment n)`. -/
theorem eulerChar_page_eq_sum_abutment {r₀ : ℤ}
    (E : CohomologicalSpectralSequence (ModuleCat.{v} R) r₀)
    (X : Abelian.SpectralObject (ModuleCat.{v} R) EInt)
    {r : ℤ} (hr : r₀ ≤ r) (I : Finset ℤ) {a b : ℤ} (hab : a ≤ b)
    (ha : ∀ n ∈ I, IsZero (X.abutmentFiltration a n))
    (hb : ∀ n ∈ I, IsIso (X.abutmentFiltrationι b n))
    (hzero : ∀ pq : ℤ × ℤ, ¬ (pq.1 + pq.2 ∈ I ∧ pq.2 ∈ Finset.Ico a b) →
      IsZero ((E.page r).X pq))
    (hfin : ∀ pq : ℤ × ℤ, pq.1 + pq.2 ∈ I → pq.2 ∈ Finset.Ico a b →
      Module.Finite R ((E.page r).X pq))
    (hiso : ∀ pq : ℤ × ℤ, pq.1 + pq.2 ∈ I → pq.2 ∈ Finset.Ico a b →
      Nonempty (((E.page r).X pq) ≅ cokernel (X.abutmentFiltrationMap pq.2 (pq.1 + pq.2)))) :
    (E.page r).eulerChar = ∑ n ∈ I, (n.negOnePow : ℤ) * finrank R (X.abutment n) := by
  nontriviality R
  let s : Finset (ℤ × ℤ) := (I ×ˢ Finset.Ico a b).image fun nq ↦ (nq.1 - nq.2, nq.2)
  have hmem_s (pq : ℤ × ℤ) : pq ∈ s ↔ pq.1 + pq.2 ∈ I ∧ pq.2 ∈ Finset.Ico a b := by
    constructor
    · intro hpq
      rcases Finset.mem_image.1 hpq with ⟨⟨n, q⟩, hnq, h⟩
      rcases Finset.mem_product.1 hnq with ⟨hn, hq⟩
      rcases Prod.mk.inj h with ⟨hp, rfl⟩
      exact ⟨by rwa [show pq.1 + pq.2 = n by lia], hq⟩
    · rintro ⟨hn, hq⟩
      exact Finset.mem_image.2 ⟨(pq.1 + pq.2, pq.2), Finset.mem_product.2 ⟨hn, hq⟩,
        Prod.ext (add_sub_cancel_right pq.1 pq.2) rfl⟩
  rw [(E.page r).eulerChar_eq_sum_finSet_of_finrankSupport_subset s
    ((GradedObject.finrankSupport_subset_iff _ _).2 fun pq hpq ↦
      ModuleCat.finrank_eq_zero_of_isZero (hzero pq ((hmem_s pq).not.1 hpq)))]
  rw [Finset.sum_image (by
    rintro ⟨n₁, q₁⟩ _ ⟨n₂, q₂⟩ _ h
    simp only [Prod.mk.injEq] at h ⊢
    lia)]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hcok (q : ℤ) (hq : q ∈ Finset.Ico a b) :
      Module.Finite R ↥(cokernel (X.abutmentFiltrationMap q n)) := by
    have hpq : (n - q) + q ∈ I := by simpa using hn
    have := hfin (n - q, q) hpq hq
    have e := (hiso (n - q, q) hpq hq).some
    dsimp only at e
    rw [sub_add_cancel] at e
    exact .equiv e.toLinearEquiv
  rw [X.finrank_abutment_eq_sum_Ico hab (ha n hn) (hb n hn) hcok, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  have hpq : (n - q) + q ∈ I := by simpa using hn
  simp only [ComplexShape.eulerCharSignsCohomologicalSpectralSequence_χ,
    (hiso (n - q, q) hpq hq).some.toLinearEquiv.finrank_eq, sub_add_cancel]
  rw [sub_add_cancel]

end CategoryTheory.CohomologicalSpectralSequence
