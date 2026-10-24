/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import TauCeti.RingTheory.AdjoinRoot.Minpoly

/-!
# Belyi's degree reduction

Let `F` be a perfect field, for instance `ℚ`. Every finite set `S` of elements algebraic over `F`
is carried into `F` by a polynomial `q ∈ F[X]` with nonzero derivative whose critical values,
the values of `q` at the roots of `q′` in any field extension, also lie in `F`. This is the first
half of Belyi's construction of a Belyi map on a curve over `AlgebraicClosure ℚ`. A polynomial
also fixes `∞`, so a finite subset of `ℙ¹(AlgebraicClosure ℚ)` is carried into `ℙ¹(ℚ)` together
with the critical values of `q`.

## Main results

* `TauCeti.exists_irreducible_finset_dvd_comp`: the degree-reduction step.
* `TauCeti.exists_forall_dvd_sub_C`: for a finite set `P` of irreducible polynomials, a
  polynomial `q` with `q′ ≠ 0` that is constant modulo every member of `P` and modulo every
  irreducible factor of `q′`.
* `TauCeti.exists_polynomial_aeval_mem_range`: the same statement for a finite set of algebraic
  elements of a field extension, with the critical values of `q` taken in an arbitrary field
  extension.

## Implementation notes

The set `S` is replaced by the finite set of minimal polynomials of its elements, which records
its closure under conjugation over `F`. A root of an irreducible `r ∈ F[X]` is mapped by a
polynomial `μ` into the root set of an irreducible `p'` exactly when `r ∣ p'.comp μ`, and `q`
takes a value `c ∈ F` at the roots of `r` exactly when `r ∣ q - C c`. All statements are made in
these terms over `F` and transferred to elements of field extensions at the end.

The degree-reduction step: if `μ` has the largest degree `d ≥ 2` among the polynomials in such a
set `P`, then `μ` maps the roots of `P`, together with the roots of `μ′`, into the roots of a
new finite set `P'` of irreducible polynomials of degree at most `d`, with strictly fewer of
degree exactly `d`. Indeed the roots of `μ` go to `0`, every root of any polynomial in `P` goes to
a point of no larger degree, and the roots of `μ′` have degree at most `d - 1` since `μ′ ≠ 0`
(here perfectness is used). The well-founded measure of the induction is therefore the pair
(largest degree `d`, number of members of degree `d`), ordered lexicographically. The
cardinality of the root set alone need not drop: `X ^ 2 - 2` sends `{√2, -√2}` to `{0}` and adds
its critical value `-2`.

## References

* G. V. Belyi, *On Galois extensions of a maximal cyclotomic field*, Math. USSR Izv. 14 (1980).
* B. Köck, *Belyi's theorem revisited*, Beiträge Algebra Geom. 45 (2004), Lemma 3.5.
-/

public section

open Polynomial UniqueFactorizationMonoid
open scoped Finset

namespace TauCeti

variable {F : Type*} [Field F]

/-- **The degree-reduction step.** Let `P` be a finite set of irreducible polynomials over a
perfect field, and let `μ ∈ P` have the largest degree `d ≥ 2` in `P`. Then there is a finite set
`P'` of irreducible polynomials of degree at most `d`, with fewer members of degree `d` than `P`,
such that `μ` maps the roots of every member of `P`, and the roots of `μ′`, into the roots of
members of `P'`. -/
theorem exists_irreducible_finset_dvd_comp [PerfectField F] {P : Finset F[X]}
    (hP : ∀ p ∈ P, Irreducible p) {μ : F[X]} (hμ : μ ∈ P)
    (hdeg : ∀ p ∈ P, p.natDegree ≤ μ.natDegree) (hμ2 : 2 ≤ μ.natDegree) :
    ∃ P' : Finset F[X], (∀ p ∈ P', Irreducible p) ∧ (∀ p ∈ P', p.natDegree ≤ μ.natDegree) ∧
      #{p ∈ P' | p.natDegree = μ.natDegree} < #{p ∈ P | p.natDegree = μ.natDegree} ∧
      (∀ p ∈ P, ∃ p' ∈ P', p ∣ p'.comp μ) ∧
      ∀ r, Irreducible r → r ∣ derivative μ → ∃ p' ∈ P', r ∣ p'.comp μ := by
  classical
  have hμ' : derivative μ ≠ 0 := (separable_iff_derivative_ne_zero (hP μ hμ)).1
    (PerfectField.separable_of_irreducible (hP μ hμ))
  -- The irreducible factors of `μ′` have degree less than `μ`.
  have hcrit : ∀ r ∈ normalizedFactors (derivative μ), r.natDegree < μ.natDegree := fun r hr ↦
    have := natDegree_derivative_le μ
    (natDegree_le_of_dvd (dvd_of_mem_normalizedFactors hr) hμ').trans_lt (by omega)
  set Q := P ∪ (normalizedFactors (derivative μ)).toFinset
  have hQ : ∀ r ∈ Q, Irreducible r := fun r hr ↦ (Finset.mem_union.1 hr).elim (hP r)
    fun h ↦ irreducible_of_normalized_factor r (Multiset.mem_toFinset.1 h)
  -- `P'` consists of the minimal polynomials of the images under `μ` of the roots of `Q`.
  refine ⟨Q.image fun r ↦ minpoly F (AdjoinRoot.mk r μ), ?_, ?_, ?_,
    fun p hp ↦ ⟨_, Finset.mem_image_of_mem _ (Finset.mem_union_left _ hp),
      AdjoinRoot.dvd_minpoly_mk_comp p μ⟩, fun r hr hdvd ↦ ?_⟩
  · simpa using fun r hr ↦ AdjoinRoot.irreducible_minpoly_mk μ (hQ r hr)
  · simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    refine fun r hr ↦ (AdjoinRoot.natDegree_minpoly_mk_le μ (hQ r hr).ne_zero).trans ?_
    rcases Finset.mem_union.1 hr with hr | hr
    · exact hdeg r hr
    · exact (hcrit r (Multiset.mem_toFinset.1 hr)).le
  · -- A member of `P'` of degree `d` is the image of a member of `P` of degree `d` other than
    -- `μ`, whose image is `X`.
    refine (Finset.card_le_card (t := ({p ∈ P | p.natDegree = μ.natDegree}.erase μ).image
      fun r ↦ minpoly F (AdjoinRoot.mk r μ)) ?_).trans_lt (Finset.card_image_le.trans_lt
        (Finset.card_erase_lt_of_mem (by simp [hμ])))
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_image] at hp
    obtain ⟨⟨r, hrQ, rfl⟩, hdr⟩ := hp
    have hle := AdjoinRoot.natDegree_minpoly_mk_le μ (hQ r hrQ).ne_zero
    rcases Finset.mem_union.1 hrQ with hrP | hrC
    · refine Finset.mem_image_of_mem _ (Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2
        ⟨hrP, le_antisymm (hdeg r hrP) (hdr ▸ hle)⟩⟩)
      -- The roots of `μ` are mapped to `0`, whose minimal polynomial is `X`.
      rintro rfl
      have := Fact.mk (hP _ hrP)
      rw [AdjoinRoot.mk_self, minpoly.zero, natDegree_X] at hdr
      omega
    · have := hcrit r (Multiset.mem_toFinset.1 hrC)
      omega
  · obtain ⟨r₀, hr₀, hassoc⟩ := exists_mem_normalizedFactors_of_dvd hμ' hr hdvd
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_union_right _ (Multiset.mem_toFinset.2 hr₀)),
      hassoc.dvd.trans (AdjoinRoot.dvd_minpoly_mk_comp r₀ μ)⟩

/-- If `μ` maps the roots of `p` into the roots of `p'`, and `q` takes the value `c` at the
roots of `p'`, then `q.comp μ` takes the value `c` at the roots of `p`. -/
private theorem dvd_comp_sub_C {p p' μ q : F[X]} {c : F} (hp : p ∣ p'.comp μ)
    (hp' : p' ∣ q - C c) : p ∣ q.comp μ - C c := by
  have := map_dvd (compRingHom μ) hp'
  rw [coe_compRingHom_apply, coe_compRingHom_apply, sub_comp, C_comp] at this
  exact hp.trans this

/-- If `μ` maps the roots of `P`, and the roots of `μ′`, into the roots of `P'`, and `q` is
constant modulo every member of `P'` and every irreducible factor of `q′`, then `q.comp μ` is
constant modulo every member of `P` and every irreducible factor of its derivative. -/
private theorem forall_dvd_sub_C_comp {P P' : Finset F[X]} {μ q : F[X]} (hμ' : derivative μ ≠ 0)
    (hPP' : ∀ p ∈ P, ∃ p' ∈ P', p ∣ p'.comp μ)
    (hcrit : ∀ r, Irreducible r → r ∣ derivative μ → ∃ p' ∈ P', r ∣ p'.comp μ)
    (hq' : derivative q ≠ 0) (hqP' : ∀ p ∈ P', ∃ c, p ∣ q - C c)
    (hqcrit : ∀ r, Irreducible r → r ∣ derivative q → ∃ c, r ∣ q - C c) :
    derivative (q.comp μ) ≠ 0 ∧ (∀ p ∈ P, ∃ c, p ∣ q.comp μ - C c) ∧
      ∀ r, Irreducible r → r ∣ derivative (q.comp μ) → ∃ c, r ∣ q.comp μ - C c := by
  refine ⟨?_, fun p hp ↦ ?_, fun r hr hdvd ↦ ?_⟩
  · rw [derivative_comp]
    refine mul_ne_zero hμ' fun h ↦ ?_
    rcases comp_eq_zero_iff.1 h with h | ⟨-, h⟩
    · exact hq' h
    · exact hμ' (by rw [h, derivative_C])
  · obtain ⟨p', hp', hpp'⟩ := hPP' p hp
    obtain ⟨c, hc⟩ := hqP' p' hp'
    exact ⟨c, dvd_comp_sub_C hpp' hc⟩
  rw [derivative_comp] at hdvd
  rcases hr.prime.dvd_or_dvd hdvd with h | h
  · -- A root of `μ′` is mapped into the roots of a member of `P'`.
    obtain ⟨p', hp', hrp'⟩ := hcrit r hr h
    obtain ⟨c, hc⟩ := hqP' p' hp'
    exact ⟨c, dvd_comp_sub_C hrp' hc⟩
  · -- A root of `q′ ∘ μ` is mapped by `μ` to a root of `q′`.
    obtain ⟨c, hc⟩ := hqcrit _ (AdjoinRoot.irreducible_minpoly_mk μ hr)
      (AdjoinRoot.minpoly_mk_dvd_iff.2 h)
    exact ⟨c, dvd_comp_sub_C (AdjoinRoot.dvd_minpoly_mk_comp r μ) hc⟩

/-- The polynomial `X` has nonzero derivative and is constant modulo every irreducible
polynomial of degree one. -/
private theorem forall_dvd_sub_C_X {P : Finset F[X]} (hP : ∀ p ∈ P, Irreducible p)
    (hdeg : ∀ p ∈ P, p.natDegree ≤ 1) :
    derivative (X : F[X]) ≠ 0 ∧ (∀ p ∈ P, ∃ c, p ∣ X - C c) ∧
      ∀ r, Irreducible r → r ∣ derivative (X : F[X]) → ∃ c, r ∣ X - C c := by
  refine ⟨by simp, fun p hp ↦ ?_, fun r hr hdvd ↦
    absurd (isUnit_of_dvd_one (derivative_X (R := F) ▸ hdvd)) hr.not_isUnit⟩
  have hp1 : p.degree = 1 := (degree_eq_iff_natDegree_eq (hP p hp).ne_zero).2
    (le_antisymm (hdeg p hp) (hP p hp).natDegree_pos)
  obtain ⟨c, hc⟩ := exists_root_of_degree_eq_one hp1
  exact ⟨c, ((irreducible_X_sub_C c).associated_of_dvd (hP p hp) (dvd_iff_isRoot.2 hc)).symm.dvd⟩

/-- **Belyi's degree reduction over `F`.** For a finite set `P` of irreducible polynomials over a
perfect field `F`, there is a polynomial `q ∈ F[X]` with `q′ ≠ 0` that is constant modulo every
member of `P` and modulo every irreducible factor of `q′`: at the roots of each of these, in any
field extension, `q` takes a value in `F`. -/
theorem exists_forall_dvd_sub_C [PerfectField F] (P : Finset F[X])
    (hP : ∀ p ∈ P, Irreducible p) :
    ∃ q : F[X], derivative q ≠ 0 ∧ (∀ p ∈ P, ∃ c, p ∣ q - C c) ∧
      ∀ r, Irreducible r → r ∣ derivative q → ∃ c, r ∣ q - C c := by
  classical
  -- Induction on the largest degree `d` in `P`, then on the number of members of degree `d`.
  suffices h : ∀ (d n : ℕ) (P : Finset F[X]), (∀ p ∈ P, Irreducible p) →
      (∀ p ∈ P, p.natDegree ≤ d) → #{p ∈ P | p.natDegree = d} ≤ n →
      ∃ q : F[X], derivative q ≠ 0 ∧ (∀ p ∈ P, ∃ c, p ∣ q - C c) ∧
        ∀ r, Irreducible r → r ∣ derivative q → ∃ c, r ∣ q - C c from
    h _ _ P hP (fun p hp ↦ Finset.le_sup (f := natDegree) hp) le_rfl
  intro d
  induction d with
  | zero =>
    exact fun _ P hP hd _ ↦ ⟨X, forall_dvd_sub_C_X hP fun p hp ↦ (hd p hp).trans zero_le_one⟩
  | succ d ihd =>
    intro n
    induction n with
    | zero =>
      -- No member has degree `d + 1`, so all have degree at most `d`.
      intro P hP hd hn
      refine ihd _ P hP (fun p hp ↦ Nat.le_of_lt_succ (lt_of_le_of_ne (hd p hp) fun h ↦ ?_))
        le_rfl
      rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hn
      exact hn hp h
    | succ n ihn =>
      intro P hP hd hn
      by_cases hd1 : d + 1 ≤ 1
      · exact ⟨X, forall_dvd_sub_C_X hP fun p hp ↦ (hd p hp).trans hd1⟩
      by_cases hex : ∃ μ ∈ P, μ.natDegree = d + 1
      · -- Apply the degree-reduction step to a member `μ` of degree `d + 1`, and compose.
        obtain ⟨μ, hμ, hμd⟩ := hex
        obtain ⟨P', hP', hd', hlt, hPP', hcrit⟩ :=
          exists_irreducible_finset_dvd_comp hP hμ (hμd ▸ hd) (by omega)
        rw [hμd] at hd' hlt
        obtain ⟨q, hq', hqP', hqcrit⟩ := ihn P' hP' hd' (by omega)
        exact ⟨q.comp μ, forall_dvd_sub_C_comp ((separable_iff_derivative_ne_zero (hP μ hμ)).1
          (PerfectField.separable_of_irreducible (hP μ hμ))) hPP' hcrit hq' hqP' hqcrit⟩
      · push Not at hex
        exact ihd _ P hP (fun p hp ↦ Nat.le_of_lt_succ (lt_of_le_of_ne (hd p hp) (hex p hp)))
          le_rfl

/-- If the minimal polynomial of `x` divides `q - C c`, then `q` takes the value `c` at `x`. -/
private theorem aeval_mem_range_of_minpoly_dvd {L : Type*} [Field L] [Algebra F L] {x : L}
    {q : F[X]} {c : F} (h : minpoly F x ∣ q - C c) :
    aeval x q ∈ Set.range (algebraMap F L) :=
  ⟨c, by
    have := aeval_eq_zero_of_dvd_aeval_eq_zero h (minpoly.aeval F x)
    rwa [map_sub, aeval_C, sub_eq_zero, eq_comm] at this⟩

universe w

/-- **Belyi's degree reduction.** Every finite set `S` of elements algebraic over a perfect field
`F`, such as a finite subset of `AlgebraicClosure ℚ`, is carried into `F` by a polynomial
`q ∈ F[X]` with `q′ ≠ 0`, in particular nonconstant, whose critical values in every field
extension of `F` also lie in `F`. -/
theorem exists_polynomial_aeval_mem_range [PerfectField F] {K : Type*} [Field K] [Algebra F K]
    (S : Finset K) (hS : ∀ s ∈ S, IsIntegral F s) :
    ∃ q : F[X], derivative q ≠ 0 ∧ (∀ s ∈ S, aeval s q ∈ Set.range (algebraMap F K)) ∧
      ∀ (L : Type w) [Field L] [Algebra F L] (x : L), aeval x (derivative q) = 0 →
        aeval x q ∈ Set.range (algebraMap F L) := by
  classical
  obtain ⟨q, hq', hqS, hqcrit⟩ := exists_forall_dvd_sub_C (S.image (minpoly F))
    (by simpa using fun s hs ↦ minpoly.irreducible (hS s hs))
  refine ⟨q, hq', fun s hs ↦ ?_, fun L _ _ x hx ↦ ?_⟩
  · obtain ⟨c, hc⟩ := hqS _ (Finset.mem_image_of_mem _ hs)
    exact aeval_mem_range_of_minpoly_dvd hc
  · have hint : IsIntegral F x := (IsAlgebraic.isIntegral ⟨_, hq', hx⟩)
    obtain ⟨c, hc⟩ := hqcrit _ (minpoly.irreducible hint) (minpoly.dvd F x hx)
    exact aeval_mem_range_of_minpoly_dvd hc

end TauCeti
