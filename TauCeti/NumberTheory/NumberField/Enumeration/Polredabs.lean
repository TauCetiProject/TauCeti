/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Data.List.Lex
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import TauCeti.Algebra.Polynomial.Coeff.List
public import TauCeti.NumberTheory.NumberField.Enumeration.DefiningPolys
public import TauCeti.NumberTheory.NumberField.Enumeration.T2

/-!
# The canonical defining polynomial of a number field

A number field `K` has infinitely many defining polynomials (`TauCeti.NumberField.definingPolys`).
Tables of number fields, such as the LMFDB, name `K` by a canonical one: the polynomial returned
by PARI's `polredabs`. This file defines that choice and proves that it is well defined and
classifies number fields up to isomorphism.

For a monic integer polynomial `P = Xⁿ + a₁ Xⁿ⁻¹ + ⋯ + aₙ`, the **polredabs key** compares, in
this order,

1. the `T₂` norm `Polynomial.t2 P`, the sum of the squared absolute values of the complex roots;
2. the absolute value `|disc P|` of the polynomial discriminant;
3. the **sign vector** `[|a₁|, a₁, |a₂|, a₂, …, |aₙ|, aₙ]`, lexicographically.

It is `Polynomial.polredabsKey P`, an element of `Lex (ℝ × Lex (ℕ × List ℤ))`. The canonical
polynomial of `K` is the defining polynomial of least key. Ties in the first two components are
genuine (`X ^ 2 - X - 1` and `X ^ 2 + X - 1` both define `ℚ(√5)`, with `T₂ = 3` and
`|disc| = 5`), and the sign vector breaks them: the key is injective on monic polynomials
(`Polynomial.polredabsKey_inj`), since the sign vector records every coefficient below the leading
one and its length records the degree.

A canonical datum `p : TauCeti.NumberField.CanonicalPolynomial K` is a defining polynomial of `K`
together with its key-minimality, and `TauCeti.NumberField.polredabs K p` is its polynomial. Such
a datum exists, because the defining polynomials of `T₂` at most a given bound form a finite set;
it is unique, by injectivity of the key; and since isomorphic fields have the same defining
polynomials, the canonical polynomial is a complete isomorphism invariant.

## Main definitions

* `Polynomial.signVector P`: the list `[|a₁|, a₁, …, |aₙ|, aₙ]` of the coefficients of `P` below
  the leading one, each preceded by its absolute value.
* `Polynomial.polredabsKey P`: the key `(T₂ P, |disc P|, signVector P)`, ordered
  lexicographically.
* `TauCeti.NumberField.CanonicalPolynomial K`: the defining polynomials of `K` of least key,
  with constructor `TauCeti.NumberField.CanonicalPolynomial.mk`.
* `TauCeti.NumberField.polredabs K p`: the polynomial of a canonical datum `p`.

## Main results

* `Polynomial.signVector_inj`, `Polynomial.polredabsKey_inj`: on monic integer polynomials the
  sign vector, and hence the key, is injective.
* `TauCeti.NumberField.exists_polredabs`: every number field has a key-minimal defining
  polynomial, so `CanonicalPolynomial K` is nonempty.
* `TauCeti.NumberField.polredabs_unique`: the canonical polynomial does not depend on the datum.
* `TauCeti.NumberField.polredabs_eq_iff`: `polredabs K p = P` exactly when `P` is a key-minimal
  defining polynomial of `K`.
* `TauCeti.NumberField.polredabs_eq_of_algEquiv`,
  `TauCeti.NumberField.nonempty_algEquiv_of_polredabs_eq`: two number fields have the same
  canonical polynomial if and only if they are isomorphic.
* `TauCeti.NumberField.polredabs_rat`: the canonical polynomial of `ℚ` is `X`.

## References

* The LMFDB Collaboration, knowl `nf.polredabs` (the three successive minimizations).
* The PARI Group, *PARI/GP User's Guide*, `polredabs`.
* H. Cohen, *A Course in Computational Algebraic Number Theory*, GTM 138, Springer 1993, §4.4.12.
-/

public section

open Polynomial Module
open scoped NumberField

namespace Polynomial

variable {P Q : ℤ[X]}

/-! ### The sign vector -/

/-- Interleaving each entry of a list of integers with its absolute value, `[|a|, a, |b|, b, …]`,
loses nothing: the entry at position `2 k + 1` is the `k`-th entry of the list. -/
private theorem getElem?_flatMap_abs_two_mul_add_one (l : List ℤ) (k : ℕ) :
    (l.flatMap fun a ↦ [|a|, a])[2 * k + 1]? = l[k]? := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [List.flatMap_cons, show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring,
        List.getElem?_append_right (by simp)]
      simpa using ih k

/-- The entry at position `2 k` of `[|a|, a, |b|, b, …]` is the absolute value of the `k`-th
entry of the list. -/
private theorem getElem?_flatMap_abs_two_mul (l : List ℤ) (k : ℕ) :
    (l.flatMap fun a ↦ [|a|, a])[2 * k]? = l[k]?.map abs := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [List.flatMap_cons, show 2 * (k + 1) = 2 * k + 2 by ring,
        List.getElem?_append_right (by simp)]
      simpa using ih k

/-- The **sign vector** of an integer polynomial `P = Xⁿ + a₁ Xⁿ⁻¹ + ⋯ + aₙ` of degree `n`:
the list `[|a₁|, a₁, |a₂|, a₂, …, |aₙ|, aₙ]` of length `2 n`, built from the coefficients
`coeffList P = [1, a₁, …, aₙ]` below the leading one. Its lexicographic order is the last
tie-break of the polredabs key: it prefers small absolute values, and then a negative sign. -/
noncomputable def signVector (P : ℤ[X]) : List ℤ :=
  P.coeffList.tail.flatMap fun a ↦ [|a|, a]

theorem signVector_def (P : ℤ[X]) : P.signVector = P.coeffList.tail.flatMap fun a ↦ [|a|, a] :=
  (rfl)

@[simp]
theorem length_signVector (P : ℤ[X]) : P.signVector.length = 2 * P.natDegree := by
  have h (l : List ℤ) : (l.flatMap fun a ↦ [|a|, a]).length = 2 * l.length := by
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons,
        List.length_nil, ih]; ring
  classical
  rw [signVector_def, h, List.length_tail, length_coeffList_eq_ite]
  split_ifs with hP <;> simp [hP]

/-- The entry of the sign vector at position `2 k + 1` is `a_{k+1} = P.coeff (n - (k + 1))`. -/
theorem getElem?_signVector_two_mul_add_one {k : ℕ} (hk : k < P.natDegree) :
    P.signVector[2 * k + 1]? = some (P.coeff (P.natDegree - (k + 1))) := by
  have hlen : k + 1 < P.coeffList.length := by
    simp [ne_zero_of_natDegree_gt hk, hk]
  simp [signVector_def, getElem?_flatMap_abs_two_mul_add_one, List.getElem?_eq_getElem hlen]

/-- The entry of the sign vector at position `2 k` is `|a_{k+1}|`. -/
theorem getElem?_signVector_two_mul {k : ℕ} (hk : k < P.natDegree) :
    P.signVector[2 * k]? = some |P.coeff (P.natDegree - (k + 1))| := by
  have hlen : k + 1 < P.coeffList.length := by
    simp [ne_zero_of_natDegree_gt hk, hk]
  simp [signVector_def, getElem?_flatMap_abs_two_mul, List.getElem?_eq_getElem hlen]

@[simp]
theorem signVector_intCast (a : ℤ) : (a : ℤ[X]).signVector = [] := by
  rw [← List.length_eq_zero_iff, length_signVector, natDegree_intCast, mul_zero]

@[simp]
theorem signVector_X : (X : ℤ[X]).signVector = [0, 0] := by
  rw [signVector_def, coeffList_of_ne_zero X_ne_zero]
  simp [List.range_succ]

/-- **The sign vector determines a monic polynomial.** Its odd entries give the coefficients
below the leading one. Monicity is needed: the constants `1` and `2` both have empty sign
vector. -/
theorem signVector_inj (hP : P.Monic) (hQ : Q.Monic) : P.signVector = Q.signVector ↔ P = Q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have htail : P.coeffList.tail = Q.coeffList.tail := List.ext_getElem? fun k ↦ by
    rw [← getElem?_flatMap_abs_two_mul_add_one, ← signVector_def, h, signVector_def,
      getElem?_flatMap_abs_two_mul_add_one]
  -- the leading coefficient of both is `1`
  have hcons {R : ℤ[X]} (hR : R.Monic) : R.coeffList = 1 :: R.coeffList.tail := by
    obtain ⟨l, hl⟩ := coeffList_eq_cons_leadingCoeff hR.ne_zero
    rw [hl, hR.leadingCoeff, List.tail_cons]
  rw [← ofCoeffList_reverse_coeffList P, ← ofCoeffList_reverse_coeffList Q, hcons hP, hcons hQ,
    htail]

/-! ### The polredabs key -/

/-- The **polredabs key** of an integer polynomial: `T₂ P`, then `|disc P|`, then the sign vector
of `P`, compared lexicographically. Among the defining polynomials of a number field, the one of
least key is the canonical polynomial returned by PARI's `polredabs`. -/
noncomputable def polredabsKey (P : ℤ[X]) : Lex (ℝ × Lex (ℕ × List ℤ)) :=
  toLex (t2 P, toLex (P.discr.natAbs, P.signVector))

theorem polredabsKey_def (P : ℤ[X]) :
    polredabsKey P = toLex (t2 P, toLex (P.discr.natAbs, P.signVector)) :=
  (rfl)

/-- The key compares the `T₂` norms first. -/
theorem t2_le_t2_of_polredabsKey_le (h : polredabsKey P ≤ polredabsKey Q) : t2 P ≤ t2 Q :=
  Prod.Lex.monotone_fst _ _ h

/-- A polynomial of strictly smaller `T₂` norm has strictly smaller key. -/
theorem polredabsKey_lt_of_t2_lt (h : t2 P < t2 Q) : polredabsKey P < polredabsKey Q :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- **The key determines a monic polynomial**, through its sign vector. -/
theorem polredabsKey_inj (hP : P.Monic) (hQ : Q.Monic) :
    polredabsKey P = polredabsKey Q ↔ P = Q := by
  refine ⟨fun h ↦ (signVector_inj hP hQ).mp ?_, fun h ↦ h ▸ rfl⟩
  simp only [polredabsKey_def, toLex_inj, Prod.mk.injEq] at h
  exact h.2.2

end Polynomial

namespace TauCeti.NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] {P : ℤ[X]}

/-! ### Existence and uniqueness of the canonical polynomial -/

/-- Two key-minimal defining polynomials of `K` are equal, by injectivity of the key on monic
polynomials. -/
private theorem eq_of_forall_polredabsKey_le {Q : ℤ[X]} (hP : P ∈ definingPolys K)
    (hPmin : ∀ R ∈ definingPolys K, polredabsKey P ≤ polredabsKey R) (hQ : Q ∈ definingPolys K)
    (hQmin : ∀ R ∈ definingPolys K, polredabsKey Q ≤ polredabsKey R) : P = Q :=
  (polredabsKey_inj (monic_of_mem_definingPolys hP) (monic_of_mem_definingPolys hQ)).mp
    ((hPmin Q hQ).antisymm (hQmin P hP))

variable (K) in
/-- **Existence of the canonical polynomial.** Every number field has a defining polynomial of
least polredabs key. The defining polynomials of `T₂` at most that of a fixed one form a finite
set, on which the key attains its minimum; every other defining polynomial has larger `T₂`. -/
theorem exists_polredabs :
    ∃ P ∈ definingPolys K, ∀ Q ∈ definingPolys K, polredabsKey P ≤ polredabsKey Q := by
  obtain ⟨P₀, hP₀⟩ := definingPolys_nonempty (K := K)
  have hcand {Q : ℤ[X]} (hQ : Q ∈ definingPolys K) (hQB : t2 Q ≤ t2 P₀) :
      Q ∈ candidates (finrank ℚ K) (t2 P₀) :=
    mem_candidates.mpr ⟨monic_of_mem_definingPolys hQ, natDegree_of_mem_definingPolys hQ, hQB⟩
  obtain ⟨P, ⟨hP, hPB⟩, hmin⟩ := Set.exists_min_image (definingPolys K ∩ _) polredabsKey
    ((candidates_finite (finrank ℚ K) (t2 P₀)).subset Set.inter_subset_right)
    ⟨P₀, hP₀, hcand hP₀ le_rfl⟩
  refine ⟨P, hP, fun Q hQ ↦ ?_⟩
  by_cases hQB : t2 Q ≤ t2 P₀
  · exact hmin Q ⟨hQ, hcand hQ hQB⟩
  · exact (polredabsKey_lt_of_t2_lt ((mem_candidates.mp hPB).2.2.trans_lt (not_le.mp hQB))).le

variable (K) in
/-- The **canonical polynomials** of a number field `K`: its defining polynomials of least
polredabs key, that is, of least `T₂`, then least `|disc|`, then least sign vector. There is
exactly one (`exists_polredabs`, `polredabs_unique`); a term of this type is a datum certifying
it, built by `CanonicalPolynomial.mk`, and `polredabs K p` is the polynomial. The body is exposed
because the module system requires it for the computable `CanonicalPolynomial.mk` and `polredabs`.
-/
@[expose] def CanonicalPolynomial : Type :=
  {P : ℤ[X] // P ∈ definingPolys K ∧ ∀ Q ∈ definingPolys K, polredabsKey P ≤ polredabsKey Q}

/-- The canonical datum of a defining polynomial `P` of `K` of least key. -/
def CanonicalPolynomial.mk (hP : P ∈ definingPolys K)
    (hmin : ∀ Q ∈ definingPolys K, polredabsKey P ≤ polredabsKey Q) : CanonicalPolynomial K :=
  ⟨P, hP, hmin⟩

variable (K) in
/-- The **canonical polynomial** `polredabs K p` of a number field `K`: the polynomial of the
canonical datum `p`. It does not depend on `p` (`polredabs_unique`). -/
def polredabs (p : CanonicalPolynomial K) : ℤ[X] :=
  Subtype.val p

/-- The canonical polynomial of the datum `CanonicalPolynomial.mk hP hmin` is `P`. -/
@[simp]
theorem polredabs_mk (hP : P ∈ definingPolys K)
    (hmin : ∀ Q ∈ definingPolys K, polredabsKey P ≤ polredabsKey Q) :
    polredabs K (.mk hP hmin) = P :=
  (rfl)

/-- The canonical polynomial is a defining polynomial. -/
theorem polredabs_mem_definingPolys (p : CanonicalPolynomial K) :
    polredabs K p ∈ definingPolys K :=
  p.property.1

/-- The canonical polynomial has the least key among the defining polynomials. -/
theorem polredabsKey_polredabs_le (p : CanonicalPolynomial K) {Q : ℤ[X]}
    (hQ : Q ∈ definingPolys K) : polredabsKey (polredabs K p) ≤ polredabsKey Q :=
  p.property.2 Q hQ

/-- The canonical polynomial has the least `T₂` norm among the defining polynomials. -/
theorem t2_polredabs_le (p : CanonicalPolynomial K) {Q : ℤ[X]} (hQ : Q ∈ definingPolys K) :
    t2 (polredabs K p) ≤ t2 Q :=
  t2_le_t2_of_polredabsKey_le (polredabsKey_polredabs_le p hQ)

/-- **Characterization of the canonical polynomial.** `polredabs K p = P` exactly when `P` is a
defining polynomial of `K` of least key. -/
theorem polredabs_eq_iff (p : CanonicalPolynomial K) :
    polredabs K p = P ↔
      P ∈ definingPolys K ∧ ∀ Q ∈ definingPolys K, polredabsKey P ≤ polredabsKey Q := by
  refine ⟨fun h ↦ h ▸ ⟨polredabs_mem_definingPolys p, fun _ ↦ polredabsKey_polredabs_le p⟩,
    fun ⟨hP, hmin⟩ ↦ ?_⟩
  exact eq_of_forall_polredabsKey_le (polredabs_mem_definingPolys p)
    (fun _ ↦ polredabsKey_polredabs_le p) hP hmin

/-- **Uniqueness of the canonical polynomial**: it does not depend on the canonical datum. -/
theorem polredabs_unique (p q : CanonicalPolynomial K) : polredabs K p = polredabs K q :=
  (polredabs_eq_iff p).mpr ⟨polredabs_mem_definingPolys q, fun _ ↦ polredabsKey_polredabs_le q⟩

instance : Nonempty (CanonicalPolynomial K) :=
  let ⟨_, hP, hmin⟩ := exists_polredabs K
  ⟨.mk hP hmin⟩

instance : Subsingleton (CanonicalPolynomial K) :=
  ⟨fun p q ↦ Subtype.ext (polredabs_unique p q)⟩

/-- The canonical polynomial is monic. -/
theorem monic_polredabs (p : CanonicalPolynomial K) : (polredabs K p).Monic :=
  monic_of_mem_definingPolys (polredabs_mem_definingPolys p)

/-- The canonical polynomial of `K` has degree `[K : ℚ]`. -/
theorem natDegree_polredabs (p : CanonicalPolynomial K) :
    (polredabs K p).natDegree = finrank ℚ K :=
  natDegree_of_mem_definingPolys (polredabs_mem_definingPolys p)

/-- The canonical polynomial is irreducible over `ℤ`. -/
theorem irreducible_polredabs (p : CanonicalPolynomial K) : Irreducible (polredabs K p) :=
  irreducible_of_mem_definingPolys (polredabs_mem_definingPolys p)

/-- The canonical polynomial stays irreducible over `ℚ`. -/
theorem irreducible_map_polredabs (p : CanonicalPolynomial K) :
    Irreducible ((polredabs K p).map (Int.castRingHom ℚ)) :=
  irreducible_map_of_mem_definingPolys (polredabs_mem_definingPolys p)

/-! ### Isomorphism invariance -/

/-- **Isomorphic number fields have the same canonical polynomial**, since they have the same
defining polynomials. -/
theorem polredabs_eq_of_algEquiv (e : K ≃ₐ[ℚ] L) (p : CanonicalPolynomial K)
    (q : CanonicalPolynomial L) : polredabs K p = polredabs L q := by
  rw [polredabs_eq_iff, definingPolys_eq_of_algEquiv e]
  exact ⟨polredabs_mem_definingPolys q, fun _ ↦ polredabsKey_polredabs_le q⟩

/-- **Number fields with the same canonical polynomial are isomorphic**: both are the stem field
of that polynomial. -/
theorem nonempty_algEquiv_of_polredabs_eq {p : CanonicalPolynomial K} {q : CanonicalPolynomial L}
    (h : polredabs K p = polredabs L q) : Nonempty (K ≃ₐ[ℚ] L) :=
  nonempty_algEquiv_of_mem_definingPolys (polredabs_mem_definingPolys p)
    (h ▸ polredabs_mem_definingPolys q)

/-- **The canonical polynomial classifies number fields**: two number fields have the same
canonical polynomial if and only if they are isomorphic over `ℚ`. -/
theorem polredabs_eq_polredabs_iff (p : CanonicalPolynomial K) (q : CanonicalPolynomial L) :
    polredabs K p = polredabs L q ↔ Nonempty (K ≃ₐ[ℚ] L) :=
  ⟨nonempty_algEquiv_of_polredabs_eq, fun ⟨e⟩ ↦ polredabs_eq_of_algEquiv e p q⟩

/-! ### The rational field -/

/-- The canonical polynomial of `ℚ` is `X`: the defining polynomials of `ℚ` are the `X - n`, and
`X` is the only one of `T₂` norm `0`. -/
@[simp]
theorem polredabs_rat (p : CanonicalPolynomial ℚ) : polredabs ℚ p = X := by
  rw [polredabs_eq_iff, definingPolys_rat]
  refine ⟨⟨0, by simp⟩, ?_⟩
  rintro _ ⟨n, rfl⟩
  dsimp only
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  refine (polredabsKey_lt_of_t2_lt ?_).le
  rw [t2_X, eq_intCast C, t2_X_sub_intCast]
  positivity

end TauCeti.NumberField
