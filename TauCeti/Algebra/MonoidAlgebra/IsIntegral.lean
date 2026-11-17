/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Laurent.Polynomial
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Integral elements of group algebras of free abelian groups

Let `G` be a free abelian group and `φ : A →+* B` a ring homomorphism. An element of `B[G]` that is
integral over `A[G]` has all its coefficients integral over `A`. For the polynomial ring this is
`MvPolynomial.isIntegral_iff_isIntegral_coeff`; the Laurent ring `B[ℤ^K]` reduces to it, since
after multiplication by a monomial the element and the equation it satisfies become polynomial.

Applied to the diagonal map `R[G] → (R[G])[G]`, `single g c ↦ single g (single g c)`, this shows
that the integral closure of a monoid algebra in `R[G]` is graded: if `x ∈ R[G]` is integral over
`R[M]` along `f : M →+ G`, then so is every term `single g (x.coeff g)` of `x`. This is the input
to the computation of the integral closure of a semigroup algebra by the saturation of the
semigroup.

Some torsion-freeness of `G` is needed: in `ℚ[ℤ/2]` the idempotent
`(1 + single 1 1) / 2` is integral over `ℤ[ℤ/2]`, but its coefficients are not integral over `ℤ`.

## Main results

* `AddMonoidAlgebra.isIntegralElem_coeff`: the coefficients of an element of `B[G]` integral over
  `A[G]` are integral over `A`.
* `AddMonoidAlgebra.isIntegralElem_single_coeff`: the terms of an element of `R[G]` integral over
  `R[M]` are integral over `R[M]`.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter V, §1, no. 8, integral closures of graded rings.
* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Chapter 4, normality of affine
  monoid algebras.
-/

public section

open Polynomial

namespace AddMonoidAlgebra

variable {A B : Type*} [CommRing A] [CommRing B]

section Laurent

open TauCeti MvPolynomial

variable {K : Type*}

/-- The case of Laurent rings `B[ℤ^K]` of `AddMonoidAlgebra.isIntegralElem_coeff`. -/
private theorem isIntegralElem_coeff_laurentRing (φ : A →+* B) {y : LaurentRing B K}
    (hy : (mapRingHom (K →₀ ℤ) φ).IsIntegralElem y) (m : K →₀ ℤ) :
    φ.IsIntegralElem (y.coeff m) := by
  classical
  obtain ⟨p, hp, hpy⟩ := hy
  -- A common monomial denominator `u = X^n` for `y` and for the coefficients of `p`.
  obtain ⟨n₁, hn₁⟩ := LaurentRing.exists_forall_mul_toLaurent_monomial (p.support.image p.coeff)
  obtain ⟨n₂, z, hz, -⟩ := LaurentRing.exists_mul_toLaurent_monomial y
  obtain ⟨z, hz⟩ := LaurentRing.exists_mul_toLaurent_monomial_add ⟨z, hz⟩ n₁
  rw [add_comm n₂] at hz
  set u : LaurentRing A K := toLaurent (monomial (n₁ + n₂) 1)
  have hcoeff (i : ℕ) : ∃ q : MvPolynomial K A, p.coeff i * u = toLaurent q := by
    by_cases hi : i ∈ p.support
    · exact LaurentRing.exists_mul_toLaurent_monomial_add
        (hn₁ _ (Finset.mem_image_of_mem _ hi)) n₂
    · exact ⟨0, by simp [Polynomial.notMem_support_iff.mp hi]⟩
  -- The rescaled equation `scaleRoots p u`, satisfied by `u * y`, has polynomial coefficients.
  have hlifts :
      p.scaleRoots u ∈ Polynomial.lifts (toLaurent : MvPolynomial K A →ₐ[A] _).toRingHom := by
    refine (lifts_iff_coeff_lifts _).mpr fun i ↦ ?_
    rw [coeff_scaleRoots]
    rcases lt_trichotomy i p.natDegree with hi | rfl | hi
    · obtain ⟨q, hq⟩ := hcoeff i
      refine ⟨q * monomial (n₁ + n₂) 1 ^ (p.natDegree - i - 1), ?_⟩
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow]
      rw [← hq, mul_assoc, ← pow_succ',
        Nat.sub_add_cancel (Nat.sub_pos_of_lt hi)]
    · exact ⟨1, by simp [hp.leadingCoeff]⟩
    · exact ⟨0, by simp [coeff_eq_zero_of_natDegree_lt hi]⟩
  obtain ⟨q, hq, -, hqm⟩ :=
    lifts_and_natDegree_eq_and_monic hlifts ((monic_scaleRoots_iff u).mpr hp)
  have hcomm : (mapRingHom (K →₀ ℤ) φ).comp (toLaurent : MvPolynomial K A →ₐ[A] _).toRingHom =
      (toLaurent : MvPolynomial K B →ₐ[B] _).toRingHom.comp (MvPolynomial.map φ) :=
    RingHom.ext fun p ↦ (toLaurent_map φ p).symm
  have huy : mapRingHom (K →₀ ℤ) φ u * y = toLaurent z := by
    rw [← hz, mul_comm]
    simp [u]
  -- So `z` is integral over `MvPolynomial K A`, and its coefficients are integral over `A`.
  have hz_int : (MvPolynomial.map φ).IsIntegralElem z := by
    refine RingHom.IsIntegralElem.of_map (g := (toLaurent : MvPolynomial K B →ₐ[B] _).toRingHom)
      toLaurent_injective ⟨q, hqm, ?_⟩
    rw [← hcomm, ← Polynomial.eval₂_map, hq, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← huy]
    exact scaleRoots_eval₂_eq_zero _ hpy
  let := φ.toAlgebra
  have hz_coeff := MvPolynomial.isIntegral_iff_isIntegral_coeff.mp hz_int
  -- The coefficient of `y` at `m` is that of `X^(n₁ + n₂) * y` at `m + (n₁ + n₂)`.
  set n : K →₀ ℤ := (n₁ + n₂).mapRange Nat.cast Nat.cast_zero
  have hym : y.coeff m = (toLaurent z).coeff (m + n) := by
    rw [← hz, toLaurent_monomial, coeff_mul_single_add, mul_one]
  by_cases hm : ∃ s : K →₀ ℕ, s.mapRange Nat.cast Nat.cast_zero = m + n
  · obtain ⟨s, hs⟩ := hm
    rw [hym, ← hs, coeff_toLaurent]
    exact hz_coeff s
  · rw [hym, MvPolynomial.toLaurent_apply, coeff_mapDomain, Finsupp.mapDomain_of_notMem_range]
    · exact φ.isIntegralElem_zero
    · rintro ⟨s, hs⟩
      exact hm ⟨s, hs⟩

end Laurent

variable {G : Type*} [AddCommGroup G]

/-- **Coefficients of integral elements of group algebras.** For a free abelian group `G` and a
ring homomorphism `φ : A →+* B`, the coefficients of an element of `B[G]` that is integral over
`A[G]` are integral over `A`. -/
theorem isIntegralElem_coeff [Module.Free ℤ G] (φ : A →+* B) {y : AddMonoidAlgebra B G}
    (hy : (mapRingHom G φ).IsIntegralElem y) (g : G) : φ.IsIntegralElem (y.coeff g) := by
  -- Transport along a basis `G ≃ (ι →₀ ℤ)` to a Laurent ring.
  let e : G ≃+ (Module.Free.ChooseBasisIndex ℤ G →₀ ℤ) :=
    (Module.Free.chooseBasis ℤ G).repr.toAddEquiv
  have hcomm : (mapDomainRingHom B e.toAddMonoidHom).comp (mapRingHom G φ) =
      (mapRingHom _ φ).comp (mapDomainRingHom A e.toAddMonoidHom) :=
    (mapRingHom_comp_mapDomainRingHom φ e.toAddMonoidHom).symm
  have hy' := hy.map (mapDomainRingHom B e.toAddMonoidHom)
  rw [hcomm] at hy'
  simpa [Finsupp.mapDomain_apply_of_injective e.injective] using
    isIntegralElem_coeff_laurentRing φ hy'.of_comp (e g)

section Diagonal

variable {R M : Type*} [CommRing R] [AddCommMonoid M]

/-- The diagonal map `R[M] → (R[M])[G]` along `f : M →+ G`, sending `single m c` to
`single (f m) (single m c)`: it records the degree `f m` of each term a second time. -/
private noncomputable def diagonal (f : M →+ G) :
    AddMonoidAlgebra R M →+* AddMonoidAlgebra (AddMonoidAlgebra R M) G :=
  (lift R (AddMonoidAlgebra (AddMonoidAlgebra R M) G) M
    ((of (AddMonoidAlgebra R M) G).comp (AddMonoidHom.toMultiplicative f) *
      MonoidHom.comp
        (algebraMap (AddMonoidAlgebra R M) (AddMonoidAlgebra (AddMonoidAlgebra R M) G)).toMonoidHom
        (of R M))).toRingHom

private theorem diagonal_single (f : M →+ G) (m : M) (c : R) :
    diagonal f (single m c) = single (f m) (single m c) := by
  simp [diagonal, single_mul_single, smul_single]

private theorem coeff_diagonal_id (x : AddMonoidAlgebra R G) (g : G) :
    (diagonal (.id G) x).coeff g = single g (x.coeff g) := by
  classical
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single h c =>
    rw [diagonal_single, AddMonoidHom.id_apply]
    by_cases hg : h = g
    · subst hg
      simp
    · simp [coeff_single, hg]

/-- **The integral closure of a monoid algebra in the algebra of a free abelian group is
graded.** If `x ∈ R[G]` is integral over `R[M]` along `f : M →+ G`, then so is each of its terms
`single g (x.coeff g)`. -/
theorem isIntegralElem_single_coeff [Module.Free ℤ G] (f : M →+ G) {x : AddMonoidAlgebra R G}
    (hx : (mapDomainRingHom R f).IsIntegralElem x) (g : G) :
    (mapDomainRingHom R f).IsIntegralElem (single g (x.coeff g)) := by
  -- The diagonal map turns the grading of `R[G]` into the coefficients of `(R[G])[G]`.
  have hcomm : (diagonal (.id G)).comp (mapDomainRingHom R f) =
      (mapRingHom G (mapDomainRingHom R f)).comp (diagonal f) :=
    ringHom_ext (by simp [diagonal_single]) (by simp [diagonal_single])
  have hx' := hx.map (diagonal (.id G))
  rw [hcomm] at hx'
  simpa [coeff_diagonal_id] using isIntegralElem_coeff _ hx'.of_comp g

end Diagonal

end AddMonoidAlgebra
