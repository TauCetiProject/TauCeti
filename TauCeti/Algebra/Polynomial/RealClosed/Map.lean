/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.CauchyIndex.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import TauCeti.FieldTheory.RealClosure.AlgebraicClosed
import TauCeti.FieldTheory.RealClosure.Hom

/-! # Roots over a real closed field under embeddings into formally real domains

A ring homomorphism `f : R →+* S` from a real closed field into a formally real domain
creates no new roots: the roots of `p.map f` in `S` are exactly the images of the roots of `p`
in `R`, with the same multiplicities. Indeed, every irreducible factor of `p` over `R` is
linear or a quadratic whose discriminant is minus a nonzero square, and such a quadratic stays
root-free in `S`. The formal reality of `S` is needed: `X ^ 2 + 1` over `ℝ` acquires roots in `ℂ`.

When `R` and `S` are ordered, `f` is automatically strictly monotone
(`RingHom.strictMono_of_isRealClosed`). Consequently the root-based invariants of univariate
real algebra are independent of the ambient ring: Tarski queries, sign counts at the roots, and
Cauchy indices on any subset of `S` are computed in `R`.

## Main results

* `Polynomial.roots_map_of_isRealClosed`: the roots of `p.map f` are the images of those of `p`.
* `Polynomial.tarskiQuery_map_of_isRealClosed` and
  `Polynomial.signCount_roots_map_of_isRealClosed`: transport of Tarski queries and of sign
  counts at roots.
* `Polynomial.cauchyIndex_map_of_isRealClosed`: the Cauchy index of the mapped quotient on a set
  is the Cauchy index of the original quotient on its preimage.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapter 2, for real closed fields and their ordered extensions.
-/

public section

namespace Polynomial

section Roots

variable {R S : Type*} [Field R] [IsRealClosed R] [CommRing S] [IsFormallyReal S]

/-- An irreducible polynomial over a real closed field that is not linear has no root in any
nontrivial formally real ring containing it. -/
theorem _root_.Irreducible.not_isRoot_map_of_natDegree_ne_one [Nontrivial S] {q : R[X]}
    (hq : Irreducible q) (h1 : q.natDegree ≠ 1) (f : R →+* S) (s : S) :
    ¬ (q.map f).IsRoot s := by
  have h2 : q.natDegree = 2 := by
    have := natDegree_le_two_of_irreducible q hq
    have := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hq)
    omega
  have hq₂ := eq_quadratic_of_degree_le_two (degree_le_of_natDegree_le h2.le)
  have ha : q.coeff 2 ≠ 0 := by
    simpa only [leadingCoeff, h2] using leadingCoeff_ne_zero.mpr hq.ne_zero
  -- The discriminant is not a square in `R`, as otherwise `q` would have a root there.
  have hdisc : ¬ IsSquare (discrim (q.coeff 2) (q.coeff 1) (q.coeff 0)) := by
    rintro ⟨d, hd⟩
    obtain ⟨x, hx⟩ := exists_quadratic_eq_zero ha ⟨d, hd⟩
    refine hq.not_isRoot_of_natDegree_ne_one h1 (x := x) ?_
    rw [hq₂]
    simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination hx
  -- So its negative is a nonzero square, which stays a nonzero square in `S`.
  obtain ⟨e, he⟩ := IsRealClosed.isSquare_neg_of_not_isSquare hdisc
  have he₀ : f e ≠ 0 := by
    rw [_root_.map_ne_zero]
    rintro rfl
    exact hdisc ⟨0, by simpa using he⟩
  intro hs
  rw [hq₂] at hs
  simp only [IsRoot, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X,
    eval_add, eval_mul, eval_pow, eval_C, eval_X] at hs
  have hsq : discrim (f (q.coeff 2)) (f (q.coeff 1)) (f (q.coeff 0)) =
      (2 * f (q.coeff 2) * s + f (q.coeff 1)) ^ 2 :=
    discrim_eq_sq_of_quadratic_eq_zero (by linear_combination hs)
  have hdisc_map : discrim (f (q.coeff 2)) (f (q.coeff 1)) (f (q.coeff 0)) = -(f e * f e) := by
    rw [← map_mul, ← he, map_neg, neg_neg]
    simp only [discrim, map_sub, map_mul, map_pow, map_ofNat]
  -- In `S`, a square plus a nonzero square would vanish.
  have hzero : (2 * f (q.coeff 2) * s + f (q.coeff 1)) * (2 * f (q.coeff 2) * s + f (q.coeff 1)) +
      f e * f e = 0 := by
    linear_combination hdisc_map - hsq
  exact he₀ (IsReduced.eq_zero _ ⟨2, (sq _).trans
    (IsFormallyReal.eq_zero_of_add_left (.mul_self _) (.mul_self _) hzero)⟩)

variable [IsDomain S]

/-- **Roots over a real closed field.** A homomorphism from a real closed field into a formally
real domain creates no new roots: the roots of `p.map f`, with multiplicity, are the images of the
roots of `p`. -/
@[simp]
theorem roots_map_of_isRealClosed (f : R →+* S) (p : R[X]) : (p.map f).roots = p.roots.map f := by
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => simp
  | unit u hu =>
    obtain ⟨c, -, rfl⟩ := Polynomial.isUnit_iff.mp hu
    simp
  | mul p q hp hq ih =>
    rw [Polynomial.map_mul, roots_mul (mul_ne_zero (map_ne_zero hq.ne_zero) (map_ne_zero hp)),
      roots_mul (mul_ne_zero hq.ne_zero hp), Multiset.map_add, ih]
    congr 1
    by_cases h1 : q.natDegree = 1
    · refine (roots_map_of_injective_of_card_eq_natDegree f.injective ?_).symm
      rw [roots_degree_eq_one (degree_eq_iff_natDegree_eq_of_pos one_pos |>.mpr h1),
        Multiset.card_singleton, h1]
    · rw [Multiset.eq_zero_of_forall_notMem fun s hs ↦
          hq.not_isRoot_map_of_natDegree_ne_one h1 f s (isRoot_of_mem_roots hs),
        Multiset.eq_zero_of_forall_notMem fun x hx ↦
          hq.not_isRoot_of_natDegree_ne_one h1 (isRoot_of_mem_roots hx),
        Multiset.map_zero]

/-- The distinct roots of `p.map f` are the images of the distinct roots of `p`. -/
theorem roots_toFinset_map_of_isRealClosed [DecidableEq R] [DecidableEq S] (f : R →+* S)
    (p : R[X]) :
    (p.map f).roots.toFinset = p.roots.toFinset.image f := by
  rw [roots_map_of_isRealClosed, Multiset.toFinset_map]

/-- Every root of `p.map f` lies in the range of `f`. -/
theorem mem_range_of_isRoot_map_of_isRealClosed {f : R →+* S} {p : R[X]} (hp : p ≠ 0) {s : S}
    (hs : (p.map f).IsRoot s) : s ∈ Set.range f := by
  have hs' : s ∈ (p.map f).roots := (mem_roots (map_ne_zero hp)).mpr hs
  rw [roots_map_of_isRealClosed, Multiset.mem_map] at hs'
  obtain ⟨x, -, rfl⟩ := hs'
  exact Set.mem_range_self x

end Roots

section Ordered

variable {R S : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
  [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

/-- **Transport of Tarski queries.** Tarski queries over a real closed field are unchanged by
passing to any ordered ring containing it. -/
@[simp]
theorem tarskiQuery_map_of_isRealClosed (f : R →+* S) (p q : R[X]) :
    tarskiQuery (p.map f) (q.map f) = tarskiQuery p q := by
  classical
  rw [tarskiQuery_eq_signSum, tarskiQuery_eq_signSum, roots_toFinset_map_of_isRealClosed,
    Finset.signSum_map_image f.strictMono_of_isRealClosed]

/-- **Transport of sign counts at roots.** The number of roots of `p` realizing a sign condition
on a family `Q` is unchanged by passing to any ordered ring containing the real closed field. -/
theorem signCount_roots_map_of_isRealClosed {J : Type*} (f : R →+* S) (p : R[X])
    (Q : J → R[X]) (σ : J → SignType) :
    Finset.signCount (p.map f).roots.toFinset (fun j => (Q j).map f) σ =
      Finset.signCount p.roots.toFinset Q σ := by
  classical
  rw [roots_toFinset_map_of_isRealClosed, Finset.signCount_map_image f.strictMono_of_isRealClosed]

/-- **Transport of Cauchy indices.** The Cauchy index of the mapped quotient on a set `s` in an
ordered ring containing a real closed field is the Cauchy index of the original quotient on
the preimage of `s`. -/
@[simp]
theorem cauchyIndex_map_of_isRealClosed (f : R →+* S) (p q : R[X]) (s : Set S) :
    cauchyIndex (p.map f) (q.map f) s = cauchyIndex p q (f ⁻¹' s) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rw [← cauchyIndex_map_image f.strictMono_of_isRealClosed, Set.image_preimage_eq_inter_range,
    cauchyIndex_def, cauchyIndex_def]
  -- Every jump of the mapped quotient sits at a root of `p.map f`, hence in the range of `f`.
  refine finsum_mem_inter_support_eq _ _ _ ?_
  refine Set.ext fun x ↦ ⟨fun hx ↦ ⟨⟨hx.1, ?_⟩, hx.2⟩, fun hx ↦ ⟨hx.1.1, hx.2⟩⟩
  have hroot := support_cauchyJump_subset _ _ hx.2
  rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots (map_ne_zero hp)] at hroot
  exact mem_range_of_isRoot_map_of_isRealClosed hp hroot

end Ordered

end Polynomial
