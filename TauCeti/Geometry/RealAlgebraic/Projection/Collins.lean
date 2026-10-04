/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.MvPolynomial.Equiv
public import TauCeti.RingTheory.Polynomial.Reductum
public import TauCeti.RingTheory.Polynomial.Subresultant.GCD
import TauCeti.Algebra.Polynomial.Derivative
import TauCeti.RingTheory.Polynomial.Roots

/-!
# The Collins projection set

For a finite family `F` of univariate polynomials over a commutative ring `R`, the Collins
projection `F.collinsProjection` is a finite subset of `R`. Write `T` for the set of all reducta
of all members of `F`. The projection contains

* every coefficient `r.coeff i`, `i ≤ r.natDegree`, of every `r ∈ T`;
* every principal subresultant coefficient of `r` and `r.derivative` for `r ∈ T`;
* every principal subresultant coefficient of `r` and `s` for `r, s ∈ T`,

where the principal subresultant coefficients are taken at the actual degrees of the reducta,
at every index from zero through the smaller of the two degrees. Zero and constant entries, and
pairs coming from the same member of `F`, are retained: this gives a simple finite superset of
Collins' projection which needs no preprocessing of the family.

The intended coefficient ring is `R = MvPolynomial (Fin n) A`, so that `F` is a family of
polynomials in one distinguished variable over the base coordinates. Specializing the base
coordinates is a ring homomorphism `φ : R →+* S`, and it can lower degrees. Truncation and
principal coefficients are taken *before* specialization, and the reducta account for every
possible drop in degree. The coefficients of `p.map φ` are the images of the coefficients of
`p`, which lie in the projection, and the specialization lemmas below show that the principal
subresultant coefficients of the specialized polynomials, at their actual specialized degrees,
are also images under `φ` of elements of the projection. Thus the signs of the projection at a
base point determine the degrees of the specialized polynomials and, through the subresultant
gcd criterion, the degrees of their pairwise gcds and of their gcds with their derivatives; this
is how the projection enters Collins' delineability theorem. The last section of this file
proves this: whenever the same elements of the projection vanish under two specializations
`φ : R →+* K` and `ψ : R →+* L` into fields (for instance evaluation at two points of a base set
on which the projection is sign-invariant), the specialized family has the same degrees, the same
nullified members, the same pairwise gcd degrees and the same gcd degrees with derivatives.

## Main definitions and results

* `Finset.collinsProjection`: the Collins projection set of a finite family.
* `Finset.mem_collinsProjection`: the explicit description of its elements.
* `Finset.collinsProjection_mono`: the projection is monotone in the family.
* `Finset.collinsProjection_image_map`: an injective coefficient map commutes with projection.
* `Finset.collinsProjection_image_finSuccEquiv'_map`,
  `Finset.collinsProjection_image_finSuccEquiv_map`: for a family of polynomials in `n + 1`
  variables, singling out a variable and projecting commutes with an injective coefficient map.
  In particular the projection of a family with integer coefficients, viewed over `ℝ`, is the
  image of the projection computed entirely over `ℤ`.
* `Finset.psc_map_mem_image_collinsProjection`,
  `Finset.psc_map_derivative_mem_image_collinsProjection`: principal subresultant coefficients
  of specialized polynomials, at the specialized degrees, come from the projection.
* `Finset.natDegree_map_eq_of_collinsProjection`, `Finset.map_eq_zero_iff_of_collinsProjection`:
  two specializations under which the same elements of the projection vanish give every member
  of the family the same degree, and nullify the same members.
* `Finset.natDegree_gcd_map_eq_of_collinsProjection`,
  `Finset.natDegree_gcd_map_derivative_eq_of_collinsProjection`: under the same hypothesis, the
  specialized pairwise gcds, and the specialized gcds of each member with its derivative, have
  the same degrees.
* `Finset.card_roots_toFinset_map_eq_of_collinsProjection`: over algebraically closed fields of
  characteristic zero, each specialized member then has the same number of distinct roots.

## References

* G. E. Collins, *Quantifier elimination for real closed fields by cylindrical algebraic
  decomposition*, Lecture Notes in Computer Science 33 (1975), 134–183.
* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapters 5 and 11.
* D. Jovanović, *Solving Non-Linear Arithmetic*, dissertation, New York University, 2012,
  Definition 2.5 and Theorem 2.6.
-/

public section

open Polynomial

namespace Finset

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The Collins projection of a finite family of polynomials. With `T` the set of all reducta of
members of `F`, it consists of all coefficients of members of `T`, and the principal
subresultant coefficients of `(r, r.derivative)` and of `(r, s)` for `r, s ∈ T`, at the actual
degrees of these polynomials and at every index through the smaller degree. -/
noncomputable def collinsProjection (F : Finset R[X]) : Finset R := by
  classical
  let T := F.biUnion reducta
  exact (T.biUnion fun r ↦ (range (r.natDegree + 1)).image r.coeff) ∪
    (T.biUnion fun r ↦ (range (min r.natDegree r.derivative.natDegree + 1)).image
      (psc r r.derivative r.natDegree r.derivative.natDegree)) ∪
    T.biUnion fun r ↦ T.biUnion fun s ↦ (range (min r.natDegree s.natDegree + 1)).image
      (psc r s r.natDegree s.natDegree)

/-- The elements of the Collins projection: coefficients of reducta, principal subresultant
coefficients of a reductum and its derivative, and principal subresultant coefficients of two
reducta, all at actual degrees. -/
theorem mem_collinsProjection {F : Finset R[X]} {a : R} :
    a ∈ F.collinsProjection ↔
      (∃ p ∈ F, ∃ r ∈ p.reducta, ∃ i ≤ r.natDegree, r.coeff i = a) ∨
      (∃ p ∈ F, ∃ r ∈ p.reducta, ∃ j ≤ min r.natDegree r.derivative.natDegree,
        psc r r.derivative r.natDegree r.derivative.natDegree j = a) ∨
      ∃ p ∈ F, ∃ r ∈ p.reducta, ∃ q ∈ F, ∃ s ∈ q.reducta, ∃ j ≤ min r.natDegree s.natDegree,
        psc r s r.natDegree s.natDegree j = a := by
  classical
  simp only [collinsProjection, mem_union, mem_biUnion, mem_image, mem_range, Nat.lt_succ_iff,
    or_assoc]
  grind

/-- Every coefficient of a reductum of a member of the family, up to its degree, lies in the
Collins projection. -/
theorem coeff_mem_collinsProjection {F : Finset R[X]} {p r : R[X]} (hp : p ∈ F)
    (hr : r ∈ p.reducta) {i : ℕ} (hi : i ≤ r.natDegree) : r.coeff i ∈ F.collinsProjection :=
  mem_collinsProjection.2 <| Or.inl ⟨p, hp, r, hr, i, hi, rfl⟩

/-- The principal subresultant coefficients of a reductum of a member of the family and its
derivative, at their actual degrees, lie in the Collins projection. -/
theorem psc_derivative_mem_collinsProjection {F : Finset R[X]} {p r : R[X]} (hp : p ∈ F)
    (hr : r ∈ p.reducta) {j : ℕ} (hj : j ≤ min r.natDegree r.derivative.natDegree) :
    psc r r.derivative r.natDegree r.derivative.natDegree j ∈ F.collinsProjection :=
  mem_collinsProjection.2 <| Or.inr <| Or.inl ⟨p, hp, r, hr, j, hj, rfl⟩

/-- The principal subresultant coefficients of two reducta of members of the family, at their
actual degrees, lie in the Collins projection. -/
theorem psc_mem_collinsProjection {F : Finset R[X]} {p q r s : R[X]} (hp : p ∈ F)
    (hr : r ∈ p.reducta) (hq : q ∈ F) (hs : s ∈ q.reducta) {j : ℕ}
    (hj : j ≤ min r.natDegree s.natDegree) :
    psc r s r.natDegree s.natDegree j ∈ F.collinsProjection :=
  mem_collinsProjection.2 <| Or.inr <| Or.inr ⟨p, hp, r, hr, q, hq, s, hs, j, hj, rfl⟩

/-- The Collins projection of the empty family is empty. -/
@[simp]
theorem collinsProjection_empty : (∅ : Finset R[X]).collinsProjection = ∅ := by
  ext a
  simp [mem_collinsProjection]

/-- Enlarging the family enlarges its Collins projection. -/
@[gcongr]
theorem collinsProjection_mono {F G : Finset R[X]} (h : F ⊆ G) :
    F.collinsProjection ⊆ G.collinsProjection := by
  intro a ha
  rw [mem_collinsProjection] at ha ⊢
  rcases ha with ⟨p, hp, r, hr, i, hi, rfl⟩ | ⟨p, hp, r, hr, j, hj, rfl⟩ |
    ⟨p, hp, r, hr, q, hq, s, hs, j, hj, rfl⟩
  · exact Or.inl ⟨p, h hp, r, hr, i, hi, rfl⟩
  · exact Or.inr <| Or.inl ⟨p, h hp, r, hr, j, hj, rfl⟩
  · exact Or.inr <| Or.inr ⟨p, h hp, r, hr, q, h hq, s, hs, j, hj, rfl⟩

open scoped Classical in
/-- An injective coefficient map commutes with the Collins projection. Injectivity preserves the
degrees of all reducta and of their derivatives, so the principal subresultant coefficients are
taken at the same formal bounds before and after the map. Without injectivity degrees can drop,
and the two sides use different bounds. -/
theorem collinsProjection_image_map {φ : R →+* S} (hφ : Function.Injective φ)
    (F : Finset R[X]) :
    (F.image (Polynomial.map φ)).collinsProjection = F.collinsProjection.image φ := by
  have hdeg (r : R[X]) : (r.map φ).natDegree = r.natDegree := natDegree_map_eq_of_injective hφ r
  have hcoeff (r : R[X]) : (r.map φ).coeff = φ ∘ r.coeff := funext (coeff_map φ)
  have hpsc (r s : R[X]) (m n : ℕ) : psc (r.map φ) (s.map φ) m n = φ ∘ psc r s m n :=
    funext (psc_map_map φ r s m n)
  simp only [collinsProjection, image_union, image_biUnion, biUnion_image, biUnion_biUnion,
    reducta_map, image_image, hdeg, derivative_map, hpsc, hcoeff]

section MvPolynomial

variable {n : ℕ} [DecidableEq (MvPolynomial (Fin n) S)] [DecidableEq (MvPolynomial (Fin n) R)[X]]
  [DecidableEq (MvPolynomial (Fin n) S)[X]]

/-- **Projection of multivariate families along an injective coefficient map.** Let `P` be a
finite family of polynomials in the variables `X 0, …, X n` over `R`, viewed as polynomials in
the distinguished variable `X i` over the polynomials in the other variables. Mapping the
coefficients along an injective `φ : R →+* S` before singling out `X i` gives a family whose
Collins projection is the image of the Collins projection computed over `R`. -/
theorem collinsProjection_image_finSuccEquiv'_map {φ : R →+* S} (hφ : Function.Injective φ)
    (P : Finset (MvPolynomial (Fin (n + 1)) R)) (i : Fin (n + 1)) :
    (P.image fun f ↦ MvPolynomial.finSuccEquiv' S i (f.map φ)).collinsProjection =
      (P.image (MvPolynomial.finSuccEquiv' R i)).collinsProjection.image (MvPolynomial.map φ) := by
  -- `collinsProjection_image_map` is stated with classical `DecidableEq` instances; `convert`
  -- identifies them with the ones here, leaving the two descriptions of the mapped family.
  convert collinsProjection_image_map (MvPolynomial.map_injective φ hφ) _ using 2
  ext
  simp [MvPolynomial.finSuccEquiv'_map]

/-- **Projection of multivariate families along an injective coefficient map**, for the
distinguished variable `X 0` singled out by `MvPolynomial.finSuccEquiv`. For
`φ = Int.castRingHom ℝ`, this says that the Collins projection of a family of polynomials with
integer coefficients, read over `ℝ`, is the image of the Collins projection computed entirely
over `ℤ`. -/
theorem collinsProjection_image_finSuccEquiv_map {φ : R →+* S} (hφ : Function.Injective φ)
    (P : Finset (MvPolynomial (Fin (n + 1)) R)) :
    (P.image fun f ↦ MvPolynomial.finSuccEquiv S n (f.map φ)).collinsProjection =
      (P.image (MvPolynomial.finSuccEquiv R n)).collinsProjection.image (MvPolynomial.map φ) := by
  simpa only [MvPolynomial.finSuccEquiv'_zero] using
    collinsProjection_image_finSuccEquiv'_map hφ P 0

end MvPolynomial

/-- **Specialization of principal subresultant coefficients.** For members `p, q` of the family
and any coefficient map `φ`, the principal subresultant coefficients of `p.map φ` and `q.map φ`
at their actual degrees are images of elements of the Collins projection. The witnesses are the
corresponding coefficients of the reducta cut off just above the specialized degrees. -/
theorem psc_map_mem_image_collinsProjection [DecidableEq S] (φ : R →+* S) {F : Finset R[X]}
    {p q : R[X]} (hp : p ∈ F) (hq : q ∈ F) {j : ℕ}
    (hj : j ≤ min (p.map φ).natDegree (q.map φ).natDegree) :
    psc (p.map φ) (q.map φ) (p.map φ).natDegree (q.map φ).natDegree j ∈
      F.collinsProjection.image φ := by
  have hr := natDegree_reductum_natDegree_map_add_one φ p
  have hs := natDegree_reductum_natDegree_map_add_one φ q
  refine mem_image.2 ⟨_, psc_mem_collinsProjection hp (p.reductum_mem_reducta _) hq
    (q.reductum_mem_reducta _) (j := j) (by rwa [hr, hs]), ?_⟩
  rw [← psc_map_map, map_reductum_natDegree_map_add_one, map_reductum_natDegree_map_add_one,
    hr, hs]

/-- **Specialization of derivative principal subresultant coefficients.** For a member `p` of the
family and a coefficient map `φ` into an additively torsion-free ring, the principal subresultant
coefficients of `p.map φ` and its derivative at their actual degrees are images of elements of the
Collins projection. Torsion-freeness ensures that the specialized derivative has the expected
degree; in positive characteristic the derivative of a reductum can drop further in degree under
specialization. -/
theorem psc_map_derivative_mem_image_collinsProjection [IsAddTorsionFree S] [DecidableEq S]
    (φ : R →+* S) {F : Finset R[X]} {p : R[X]} (hp : p ∈ F) {j : ℕ}
    (hj : j ≤ min (p.map φ).natDegree (p.map φ).derivative.natDegree) :
    psc (p.map φ) (p.map φ).derivative (p.map φ).natDegree (p.map φ).derivative.natDegree j ∈
      F.collinsProjection.image φ := by
  set r := p.reductum ((p.map φ).natDegree + 1)
  have hmap : r.map φ = p.map φ := map_reductum_natDegree_map_add_one φ p
  have hr : r.natDegree = (p.map φ).natDegree := natDegree_reductum_natDegree_map_add_one φ p
  have hr' : r.derivative.natDegree = (p.map φ).derivative.natDegree := by
    rw [← hmap, derivative_map,
      natDegree_map_derivative_eq_of_natDegree_map_eq (by rw [hmap, hr])]
  refine mem_image.2 ⟨_, psc_derivative_mem_collinsProjection hp (p.reductum_mem_reducta _)
    (j := j) (by rwa [hr, hr']), ?_⟩
  rw [← psc_map_map, ← derivative_map, hmap, hr, hr']

/-! ### Invariance of the specialized family

Throughout, `φ` and `ψ` are two specializations under which the same elements of the Collins
projection vanish. The degrees and the zero patterns of principal subresultant coefficients agree
for specializations into arbitrary commutative rings; the gcd and root-count statements are over
fields. -/

section Invariance

variable {A B : Type*} [CommRing A] [CommRing B] {φ : R →+* A} {ψ : R →+* B} {F : Finset R[X]}
  {p q : R[X]}

/-- If the same elements of the Collins projection vanish under `φ` and `ψ`, then the same
coefficients of each member of the family vanish under `φ` and `ψ`. -/
theorem map_coeff_eq_zero_iff_of_collinsProjection
    (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F) (i : ℕ) :
    φ (p.coeff i) = 0 ↔ ψ (p.coeff i) = 0 := by
  rcases le_or_gt i p.natDegree with hi | hi
  · exact h _ (coeff_mem_collinsProjection hp p.self_mem_reducta hi)
  · simp [coeff_eq_zero_of_natDegree_lt hi]

/-- If the same elements of the Collins projection vanish under `φ` and `ψ`, then a member of the
family is nullified by `φ` exactly when it is nullified by `ψ`. -/
theorem map_eq_zero_iff_of_collinsProjection
    (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F) :
    p.map φ = 0 ↔ p.map ψ = 0 := by
  simp only [Polynomial.ext_iff, coeff_map, coeff_zero,
    map_coeff_eq_zero_iff_of_collinsProjection h hp]

/-- If the same elements of the Collins projection vanish under `φ` and `ψ`, then every member of
the family has the same degree after either specialization. -/
theorem natDegree_map_eq_of_collinsProjection
    (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F) :
    (p.map φ).natDegree = (p.map ψ).natDegree := by
  have key (n : ℕ) : (p.map φ).natDegree ≤ n ↔ (p.map ψ).natDegree ≤ n := by
    simp only [natDegree_le_iff_coeff_eq_zero, coeff_map,
      map_coeff_eq_zero_iff_of_collinsProjection h hp]
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

/-- A single reductum of a member of the family specializes to the member under both `φ` and `ψ`,
and its own degree is the specialized degree under each of them. -/
private theorem exists_mem_reducta_map_eq_and_map_eq
    (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F) :
    ∃ r ∈ p.reducta, r.natDegree = (p.map φ).natDegree ∧ r.natDegree = (p.map ψ).natDegree ∧
      r.map φ = p.map φ ∧ r.map ψ = p.map ψ := by
  have hdeg := natDegree_map_eq_of_collinsProjection h hp
  refine ⟨_, p.reductum_mem_reducta _, natDegree_reductum_natDegree_map_add_one φ p, ?_,
    map_reductum_natDegree_map_add_one φ p, ?_⟩ <;> rw [hdeg]
  exacts [natDegree_reductum_natDegree_map_add_one ψ p, map_reductum_natDegree_map_add_one ψ p]

/-- If the same elements of the Collins projection vanish under `φ` and `ψ`, then for two members
of the family the principal subresultant coefficients of their specializations, at the
specialized degrees, vanish at the same indices. -/
theorem psc_map_eq_zero_iff_of_collinsProjection
    (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F) (hq : q ∈ F) {j : ℕ}
    (hj : j ≤ min (p.map φ).natDegree (q.map φ).natDegree) :
    psc (p.map φ) (q.map φ) (p.map φ).natDegree (q.map φ).natDegree j = 0 ↔
      psc (p.map ψ) (q.map ψ) (p.map ψ).natDegree (q.map ψ).natDegree j = 0 := by
  obtain ⟨r, hrT, hrφd, hrψd, hrφ, hrψ⟩ := exists_mem_reducta_map_eq_and_map_eq h hp
  obtain ⟨s, hsT, hsφd, hsψd, hsφ, hsψ⟩ := exists_mem_reducta_map_eq_and_map_eq h hq
  have hc := psc_mem_collinsProjection hp hrT hq hsT (j := j) (by rwa [hrφd, hsφd])
  -- Both sides are the images under `φ` and `ψ` of the projection element `hc`, since `r` and
  -- `s` specialize to `p` and `q` with the same degrees.
  have eφ : φ (psc r s r.natDegree s.natDegree j) =
      psc (p.map φ) (q.map φ) (p.map φ).natDegree (q.map φ).natDegree j := by
    simp only [← psc_map_map, hrφ, hsφ, hrφd, hsφd]
  have eψ : ψ (psc r s r.natDegree s.natDegree j) =
      psc (p.map ψ) (q.map ψ) (p.map ψ).natDegree (q.map ψ).natDegree j := by
    simp only [← psc_map_map, hrψ, hsψ, hrψd, hsψd]
  rw [← eφ, ← eψ]
  exact h _ hc

/-- If the same elements of the Collins projection vanish under `φ` and `ψ`, then for a member of
the family the principal subresultant coefficients of its specialization and their derivative,
at the specialized degrees, vanish at the same indices. The targets are additively torsion-free,
so that the derivative of a specialization has the expected degree. -/
theorem psc_map_derivative_eq_zero_iff_of_collinsProjection [IsAddTorsionFree A]
    [IsAddTorsionFree B] (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F)
    {j : ℕ} (hj : j ≤ min (p.map φ).natDegree (p.map φ).derivative.natDegree) :
    psc (p.map φ) (p.map φ).derivative (p.map φ).natDegree (p.map φ).derivative.natDegree j = 0 ↔
      psc (p.map ψ) (p.map ψ).derivative (p.map ψ).natDegree
        (p.map ψ).derivative.natDegree j = 0 := by
  obtain ⟨r, hrT, hrφd, hrψd, hrφ, hrψ⟩ := exists_mem_reducta_map_eq_and_map_eq h hp
  -- Over torsion-free targets, `r` keeps its derivative degree under both specializations.
  have hrφd' : r.derivative.natDegree = (p.map φ).derivative.natDegree := by
    rw [← hrφ, derivative_map, natDegree_map_derivative_eq_of_natDegree_map_eq (hrφ ▸ hrφd.symm)]
  have hrψd' : r.derivative.natDegree = (p.map ψ).derivative.natDegree := by
    rw [← hrψ, derivative_map, natDegree_map_derivative_eq_of_natDegree_map_eq (hrψ ▸ hrψd.symm)]
  have hc := psc_derivative_mem_collinsProjection hp hrT (j := j) (by rwa [hrφd, hrφd'])
  -- Both sides are the images under `φ` and `ψ` of the projection element `hc`.
  have eφ : φ (psc r r.derivative r.natDegree r.derivative.natDegree j) =
      psc (p.map φ) (p.map φ).derivative (p.map φ).natDegree
        (p.map φ).derivative.natDegree j := by
    simp only [← psc_map_map, ← derivative_map, hrφ, hrφd, hrφd']
  have eψ : ψ (psc r r.derivative r.natDegree r.derivative.natDegree j) =
      psc (p.map ψ) (p.map ψ).derivative (p.map ψ).natDegree
        (p.map ψ).derivative.natDegree j := by
    simp only [← psc_map_map, ← derivative_map, hrψ, hrψd, hrψd']
  rw [← eφ, ← eψ]
  exact h _ hc

end Invariance

section Field

variable {K L : Type*} [Field K] [Field L] [DecidableEq K] [DecidableEq L] {φ : R →+* K}
  {ψ : R →+* L} {F : Finset R[X]} {p q : R[X]}

/-- If the same elements of the Collins projection vanish under `φ` and `ψ`, then for any two
members of the family the gcds of their specializations have the same degree. -/
theorem natDegree_gcd_map_eq_of_collinsProjection
    (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F) (hq : q ∈ F) :
    (EuclideanDomain.gcd (p.map φ) (q.map φ)).natDegree =
      (EuclideanDomain.gcd (p.map ψ) (q.map ψ)).natDegree := by
  rcases eq_or_ne (p.map ψ) 0 with hp0 | hp0
  · rw [hp0, (map_eq_zero_iff_of_collinsProjection h hp).2 hp0, EuclideanDomain.gcd_zero_left,
      EuclideanDomain.gcd_zero_left, natDegree_map_eq_of_collinsProjection h hq]
  rcases eq_or_ne (q.map ψ) 0 with hq0 | hq0
  · rw [hq0, (map_eq_zero_iff_of_collinsProjection h hq).2 hq0, EuclideanDomain.gcd_zero_right,
      EuclideanDomain.gcd_zero_right, natDegree_map_eq_of_collinsProjection h hp]
  refine natDegree_gcd_eq_of_psc_eq_zero_iff hp0 hq0 fun j hj => ?_
  refine psc_map_eq_zero_iff_of_collinsProjection h hp hq ?_
  rwa [natDegree_map_eq_of_collinsProjection h hp, natDegree_map_eq_of_collinsProjection h hq]

/-- If the same elements of the Collins projection vanish under `φ` and `ψ`, then for every member
of the family the gcd of its specialization with its derivative has the same degree under both
specializations. The targets are additively torsion-free. -/
theorem natDegree_gcd_map_derivative_eq_of_collinsProjection [IsAddTorsionFree K]
    [IsAddTorsionFree L]
    (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F) :
    (EuclideanDomain.gcd (p.map φ) (p.map φ).derivative).natDegree =
      (EuclideanDomain.gcd (p.map ψ) (p.map ψ).derivative).natDegree := by
  have hdeg := natDegree_map_eq_of_collinsProjection h hp
  rcases eq_or_ne (p.map ψ).derivative 0 with h0 | h0
  · have h0' : (p.map φ).derivative = 0 := by
      rw [derivative_eq_zero, hdeg, ← derivative_eq_zero, h0]
    rw [h0, h0', EuclideanDomain.gcd_zero_right, EuclideanDomain.gcd_zero_right, hdeg]
  have hp0 : p.map ψ ≠ 0 := fun hp0 => h0 (by rw [hp0, derivative_zero])
  refine natDegree_gcd_eq_of_psc_eq_zero_iff hp0 h0 fun j hj => ?_
  refine psc_map_derivative_eq_zero_iff_of_collinsProjection h hp ?_
  rwa [natDegree_derivative, hdeg, ← natDegree_derivative]

/-- If the same elements of the Collins projection vanish under specializations `φ` and `ψ` into
algebraically closed fields of characteristic zero, then every member of the family has the same
number of distinct roots after either specialization. A member nullified by one is nullified by
both, and `Polynomial.roots` of the zero polynomial is empty by convention, so both counts are
then zero. -/
theorem card_roots_toFinset_map_eq_of_collinsProjection [CharZero K] [CharZero L]
    [IsAlgClosed K] [IsAlgClosed L]
    (h : ∀ a ∈ F.collinsProjection, φ a = 0 ↔ ψ a = 0) (hp : p ∈ F) :
    (p.map φ).roots.toFinset.card = (p.map ψ).roots.toFinset.card := by
  rcases eq_or_ne (p.map ψ) 0 with h0 | h0
  · simp [h0, (map_eq_zero_iff_of_collinsProjection h hp).2 h0]
  rw [← natDegree_sub_natDegree_gcd_derivative_eq_card_roots_toFinset h0,
    ← natDegree_sub_natDegree_gcd_derivative_eq_card_roots_toFinset
      ((map_eq_zero_iff_of_collinsProjection h hp).not.2 h0),
    natDegree_map_eq_of_collinsProjection h hp,
    natDegree_gcd_map_derivative_eq_of_collinsProjection h hp]

end Field

end Finset
