/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Bigraded Poincaré series

This file defines the Poincaré series of a finite-dimensional bigraded vector space, together
with its total dimension and Alexander-graded Euler characteristic.

## Main definitions

* `TauCeti.Bigraded.Series`: the Poincaré series of a finite-dimensional bigraded vector space.
* `TauCeti.Bigraded.IsDiagonal`: a series whose nonzero coefficients lie in bidegrees `(d, d)`.
* `TauCeti.Bigraded.totalDim`: the total dimension, as a ring homomorphism.
* `TauCeti.Bigraded.euler`: the Alexander-graded Euler characteristic.
* `TauCeti.Bigraded.maslovEuler`: the Maslov-graded Euler characteristic, which agrees with
  `TauCeti.Bigraded.euler` on a series without coefficients below the diagonal exactly when the
  series is diagonal (`TauCeti.Bigraded.euler_eq_maslovEuler_iff_isDiagonal`).
-/

public section

namespace TauCeti

namespace Bigraded

open AddMonoidAlgebra

/-- The Poincaré series of a finite-dimensional bigraded vector space: the dimension of the
summand in each bidegree `(Maslov, Alexander)`, all but finitely many of them zero.

Over a field, a bigraded vector space with only finitely many nonzero finite-dimensional summands
is determined up to bigraded isomorphism by this function, and the product is the Poincaré series
of the tensor product. -/
abbrev Series : Type := AddMonoidAlgebra ℕ (ℤ × ℤ)

/-- A bigraded Poincaré series is **diagonal** when every coefficient outside a bidegree
`(d, d)` vanishes. -/
def IsDiagonal (P : Series) : Prop :=
  ∀ m a : ℤ, m ≠ a → P.coeff (m, a) = 0

/-- A bigraded Poincaré series is diagonal exactly when all its off-diagonal coefficients
vanish. -/
theorem isDiagonal_iff (P : Series) :
    IsDiagonal P ↔ ∀ m a : ℤ, m ≠ a → P.coeff (m, a) = 0 :=
  Iff.rfl

/-- The zero bigraded Poincaré series is diagonal. -/
@[simp]
theorem isDiagonal_zero : IsDiagonal 0 := by
  intro m a _
  simp

section TotalDim

/-- The total dimension of a finite-dimensional bigraded vector space, as a ring homomorphism:
the tensor product multiplies total dimensions. -/
noncomputable def totalDim : Series →+* ℕ :=
  liftNCRingHom (RingHom.id ℕ) (1 : Multiplicative (ℤ × ℤ) →* ℕ) fun _ _ => Commute.all _ _

/-- The total dimension is the sum of the dimensions of all the bigraded summands. -/
theorem totalDim_apply (P : Series) : totalDim P = P.coeff.sum fun _ c => c := by
  simp [totalDim, liftNCRingHom, AddMonoidAlgebra.liftNC]

/-- The total dimension of a series concentrated in one bidegree. -/
@[simp]
theorem totalDim_single (g : ℤ × ℤ) (r : ℕ) : totalDim (single g r) = r := by
  simp [totalDim]

/-- Only the zero series has total dimension zero. -/
@[simp]
theorem totalDim_eq_zero_iff (P : Series) : totalDim P = 0 ↔ P = 0 := by
  rw [totalDim_apply, Finsupp.sum, Finset.sum_eq_zero_iff]
  constructor
  · intro h
    ext g
    by_cases hg : g ∈ P.coeff.support
    · simpa using h g hg
    · simpa using Finsupp.notMem_support_iff.mp hg
  · rintro rfl
    simp

end TotalDim

section Euler

open LaurentPolynomial

/-- The Alexander-graded Euler characteristic of a bigraded vector space, as a monoid
homomorphism on bidegrees: bidegree `(m, a)` contributes `(-1)^m T^a`. -/
noncomputable def eulerMonoidHom : Multiplicative (ℤ × ℤ) →* ℤ[T;T⁻¹] where
  toFun g := single g.toAdd.2 (g.toAdd.1.negOnePow : ℤ)
  map_one' := rfl
  map_mul' g h := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, Int.negOnePow_add, Units.val_mul,
      single_mul_single]

/-- The Alexander-graded Euler characteristic of a finite-dimensional bigraded vector space: the
Laurent polynomial whose `T^a` coefficient is the alternating sum, over the Maslov grading, of
the dimensions in Alexander grading `a`.

This is a ring homomorphism, so it turns the tensor product into a product of Laurent
polynomials. -/
noncomputable def euler : Series →+* ℤ[T;T⁻¹] :=
  liftNCRingHom (Nat.castRingHom _) eulerMonoidHom fun _ _ => Commute.all _ _

/-- The Euler characteristic of a series concentrated in one bidegree. -/
@[simp]
theorem euler_single (m a : ℤ) (r : ℕ) :
    euler (single (m, a) r) = (r : ℤ[T;T⁻¹]) * single a (m.negOnePow : ℤ) :=
  liftNCRingHom_single _ _ _ _ _

/-- The coefficient of `T^a` in the Alexander-graded Euler characteristic is the alternating sum
of the dimensions in Alexander grading `a`. -/
theorem coeff_euler (P : Series) (a : ℤ) :
    (euler P).coeff a =
      P.coeff.sum fun g c ↦ if g.2 = a then (g.1.negOnePow : ℤ) * c else 0 := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ =>
    rw [map_add, coeff_add, Finsupp.add_apply, hP, hQ, coeff_add,
      Finsupp.sum_add_index' (by simp) (fun _ _ _ ↦ by split_ifs <;> simp [mul_add])]
  | single g r =>
    obtain ⟨m, a'⟩ := g
    rw [euler_single, coeff_single, Finsupp.sum_single_index (by simp),
      AddMonoidAlgebra.natCast_def, single_mul_single, zero_add, coeff_single, Finsupp.single_apply]
    split_ifs <;> simp_all [mul_comm]

/-- The Maslov-graded Euler characteristic, as a monoid homomorphism on bidegrees: bidegree
`(m, a)` contributes `(-1)^m T^m`. -/
noncomputable def maslovEulerMonoidHom : Multiplicative (ℤ × ℤ) →* ℤ[T;T⁻¹] where
  toFun g := single g.toAdd.1 (g.toAdd.1.negOnePow : ℤ)
  map_one' := rfl
  map_mul' g h := by
    simp only [toAdd_mul, Prod.fst_add, Int.negOnePow_add, Units.val_mul, single_mul_single]

/-- The Maslov-graded Euler characteristic of a finite-dimensional bigraded vector space: the
Laurent polynomial whose `T^m` coefficient is `(-1)^m` times the total dimension in Maslov
grading `m`. Equivalently, it is the Poincaré polynomial of the Maslov grading alone, evaluated at
`-T`.

It agrees with the Alexander-graded `TauCeti.Bigraded.euler` on diagonal series. -/
noncomputable def maslovEuler : Series →+* ℤ[T;T⁻¹] :=
  liftNCRingHom (Nat.castRingHom _) maslovEulerMonoidHom fun _ _ => Commute.all _ _

/-- The Maslov-graded Euler characteristic of a series concentrated in one bidegree. -/
@[simp]
theorem maslovEuler_single (m a : ℤ) (r : ℕ) :
    maslovEuler (single (m, a) r) = (r : ℤ[T;T⁻¹]) * single m (m.negOnePow : ℤ) :=
  liftNCRingHom_single _ _ _ _ _

/-- The coefficient of `T^m` in the Maslov-graded Euler characteristic is `(-1)^m` times the
total dimension in Maslov grading `m`. -/
theorem coeff_maslovEuler (P : Series) (m : ℤ) :
    (maslovEuler P).coeff m =
      P.coeff.sum fun g c ↦ if g.1 = m then (g.1.negOnePow : ℤ) * c else 0 := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ =>
    rw [map_add, coeff_add, Finsupp.add_apply, hP, hQ, coeff_add,
      Finsupp.sum_add_index' (by simp) (fun _ _ _ ↦ by split_ifs <;> simp [mul_add])]
  | single g r =>
    obtain ⟨m', a⟩ := g
    rw [maslovEuler_single, coeff_single, Finsupp.sum_single_index (by simp),
      AddMonoidAlgebra.natCast_def, single_mul_single, zero_add, coeff_single,
      Finsupp.single_apply]
    split_ifs <;> simp_all [mul_comm]

/-- **The two Euler characteristics agree exactly on diagonal series**, for a series with no
coefficients strictly below the diagonal. The lower-triangularity hypothesis is needed: the
series with coefficient one in bidegrees `(0, 2)` and `(2, 0)` has equal Euler characteristics
`1 + T^2` but is not diagonal. -/
theorem euler_eq_maslovEuler_iff_isDiagonal (P : Series)
    (hP : ∀ m a : ℤ, a < m → P.coeff (m, a) = 0) :
    euler P = maslovEuler P ↔ IsDiagonal P := by
  classical
  constructor
  · intro h
    by_contra hdiag
    obtain ⟨m, a, hma, hc⟩ : ∃ m a : ℤ, m ≠ a ∧ P.coeff (m, a) ≠ 0 := by
      simpa [IsDiagonal] using hdiag
    -- Let `m₀` be the least Maslov degree of an off-diagonal summand, all of which lie strictly
    -- above the diagonal. The coefficient of `T^m₀` in the Maslov-graded Euler characteristic
    -- counts every summand of Maslov degree `m₀` with the same sign, while in the
    -- Alexander-graded one only the summand in bidegree `(m₀, m₀)` survives.
    set S := P.coeff.support.filter fun g ↦ g.1 < g.2
    have hle : ∀ g ∈ P.coeff.support, g.1 ≤ g.2 := fun g hg ↦
      not_lt.mp fun hlt ↦ Finsupp.mem_support_iff.mp hg (hP g.1 g.2 hlt)
    have hS : (S.image Prod.fst).Nonempty :=
      ⟨m, Finset.mem_image.mpr ⟨(m, a), Finset.mem_filter.mpr
        ⟨Finsupp.mem_support_iff.mpr hc,
          lt_of_le_of_ne (hle _ (Finsupp.mem_support_iff.mpr hc)) hma⟩, rfl⟩⟩
    set m₀ := (S.image Prod.fst).min' hS
    obtain ⟨g₀, hg₀S, hg₀⟩ := Finset.mem_image.mp ((S.image Prod.fst).min'_mem hS)
    have hmin : ∀ g ∈ S, m₀ ≤ g.1 := fun g hg ↦
      (S.image Prod.fst).min'_le _ (Finset.mem_image_of_mem _ hg)
    -- In degree `m₀`, the two coefficients differ by the off-diagonal Maslov-degree-`m₀` part.
    have hterm : ∀ g ∈ P.coeff.support,
        (if g.2 = m₀ then (g.1.negOnePow : ℤ) * P.coeff g else 0) =
          (if g.1 = m₀ then (g.1.negOnePow : ℤ) * P.coeff g else 0) -
            (m₀.negOnePow : ℤ) * (if g.1 = m₀ ∧ g.2 ≠ m₀ then (P.coeff g : ℤ) else 0) := by
      intro g hg
      by_cases h1 : g.1 = m₀
      · by_cases h2 : g.2 = m₀ <;> simp [h1, h2]
      · have h2 : g.2 ≠ m₀ := fun h2 ↦ h1 (le_antisymm (h2 ▸ hle g hg)
          (hmin g (Finset.mem_filter.mpr ⟨hg, lt_of_le_of_ne (hle g hg) (h2 ▸ h1)⟩)))
        simp [h1, h2]
    have hcoeff := congrArg (fun f : ℤ[T;T⁻¹] ↦ f.coeff m₀) h
    simp only [coeff_euler, coeff_maslovEuler, Finsupp.sum] at hcoeff
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, sub_eq_self, ← Finset.mul_sum,
      mul_eq_zero, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ by positivity)] at hcoeff
    rcases hcoeff with hunit | hzero
    · exact Units.ne_zero _ hunit
    · have hg₀ne : g₀.2 ≠ m₀ := fun h2 ↦
        (Finset.mem_filter.mp hg₀S).2.ne (hg₀.trans h2.symm)
      have := hzero g₀ (Finset.mem_filter.mp hg₀S).1
      have hg₀' : g₀.1 = m₀ := hg₀
      simp only [hg₀', hg₀ne, ne_eq, not_false_eq_true, and_self, ite_true] at this
      exact Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hg₀S).1 (by exact_mod_cast this)
  · intro hdiag
    ext a
    rw [coeff_euler, coeff_maslovEuler]
    refine Finsupp.sum_congr fun g hg ↦ ?_
    have : g.1 = g.2 := by
      by_contra hne
      exact Finsupp.mem_support_iff.mp hg (hdiag g.1 g.2 hne)
    simp [this]

end Euler

end Bigraded

end TauCeti
