/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.PowerSeries.Trunc
public import TauCeti.RingTheory.AdjoinRoot.Basic

/-!
# Finite jets of power series

For a commutative ring `R` and `N : ℕ`, the truncated polynomial algebra
`R[X]/(X ^ N) = AdjoinRoot (X ^ N)` is the ring of `N`-jets: the quotient of `R⟦X⟧` by `(X ^ N)`.
This file constructs the jet map `PowerSeries.jet N : R⟦X⟧ →ₐ[R] R[X]/(X ^ N)`, sending a power
series to the class of its truncation below degree `N`, and proves that `R⟦X⟧` is the inverse
limit of its jets: the jet maps are compatible with the truncations
`R[X]/(X ^ M) → R[X]/(X ^ N)` for `N ≤ M`, a power series is determined by its jets, and every
compatible sequence of jets comes from a power series. These are the coordinate-ring facts behind
the presentation of the positive loop group `G(R⟦X⟧)` as the limit of the jet groups
`G(R[X]/(X ^ N))`.

## Main definitions

* `PowerSeries.jet N`: the `R`-algebra map `R⟦X⟧ → R[X]/(X ^ N)`, `f ↦ trunc N f`.

## Main results

* `PowerSeries.jet_eq_mk_iff` and `PowerSeries.jet_eq_jet_iff`: jets are determined by the
  coefficients below `N`.
* `PowerSeries.ker_jet`: the kernel of `jet N` is `(X ^ N)`.
* `PowerSeries.algHomOfDvd_jet`: jets are compatible with truncation.
* `PowerSeries.eq_of_forall_jet_eq` and `PowerSeries.exists_forall_jet_eq`: `R⟦X⟧` is the inverse
  limit of the rings `R[X]/(X ^ N)`.
* `PowerSeries.map_jet`: jets are natural in the coefficient ring.

## References

* E. Frenkel, *Langlands correspondence for loop groups*, Cambridge Studies in Advanced
  Mathematics 103 (2007), §1.3.1.
-/

public section

open scoped Polynomial PowerSeries

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The class of the truncation `trunc N f` in `R[X]/(X ^ N)` is the class of a polynomial `p`
exactly when `f` and `p` have the same coefficients below `N`. -/
private theorem mk_trunc_eq_mk_iff {N : ℕ} {f : R⟦X⟧} {p : R[X]} :
    AdjoinRoot.mk (Polynomial.X ^ N : R[X]) (trunc N f) = AdjoinRoot.mk _ p ↔
      ∀ d < N, coeff d f = p.coeff d := by
  rw [AdjoinRoot.mk_eq_mk, Polynomial.X_pow_dvd_iff]
  refine forall₂_congr fun d hd ↦ ?_
  rw [Polynomial.coeff_sub, coeff_trunc, ite_eq_left hd, sub_eq_zero]

variable (R) in
/-- **The `N`-jet of a power series.** The `R`-algebra map `R⟦X⟧ → R[X]/(X ^ N)` sending `f` to
the class of its truncation `trunc N f` below degree `N`. Its kernel is `(X ^ N)` (`ker_jet`). -/
noncomputable def jet (N : ℕ) : R⟦X⟧ →ₐ[R] AdjoinRoot (Polynomial.X ^ N : R[X]) where
  toFun f := AdjoinRoot.mk _ (trunc N f)
  map_one' := by
    rw [← map_one (AdjoinRoot.mk (Polynomial.X ^ N : R[X])), mk_trunc_eq_mk_iff]
    intro d _
    rw [← Polynomial.coeff_coe, Polynomial.coe_one]
  map_mul' f g := by
    rw [← map_mul, mk_trunc_eq_mk_iff]
    intro d hd
    rw [coeff_mul_eq_coeff_trunc_mul_trunc f g hd, ← Polynomial.coe_mul, Polynomial.coeff_coe]
  map_zero' := by simp
  map_add' f g := by simp
  commutes' r := by
    rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.of, RingHom.comp_apply, algebraMap_eq,
      ← Polynomial.coe_C, mk_trunc_eq_mk_iff]
    intro d _
    rw [Polynomial.coeff_coe]

variable {N : ℕ}

/-- The `N`-jet of `f` is the class of its truncation below degree `N`. -/
theorem jet_apply (f : R⟦X⟧) : jet R N f = AdjoinRoot.mk _ (trunc N f) := (rfl)

/-- The jet of `f` is the class of a polynomial `p` exactly when `f` and `p` have the same
coefficients below `N`. -/
theorem jet_eq_mk_iff {f : R⟦X⟧} {p : R[X]} :
    jet R N f = AdjoinRoot.mk _ p ↔ ∀ d < N, coeff d f = p.coeff d :=
  mk_trunc_eq_mk_iff

/-- Two power series have the same `N`-jet exactly when their coefficients agree below `N`. -/
theorem jet_eq_jet_iff {f g : R⟦X⟧} :
    jet R N f = jet R N g ↔ ∀ d < N, coeff d f = coeff d g := by
  rw [jet_apply g, jet_eq_mk_iff]
  refine forall₂_congr fun d hd ↦ ?_
  rw [coeff_trunc, ite_eq_left hd]

/-- The jet of a polynomial is its class. -/
@[simp]
theorem jet_coe (p : R[X]) : jet R N (p : R⟦X⟧) = AdjoinRoot.mk _ p :=
  jet_eq_mk_iff.2 fun d _ ↦ Polynomial.coeff_coe p d

/-- The jet of `X` is the root of `X ^ N`. -/
@[simp]
theorem jet_X : jet R N X = AdjoinRoot.root (Polynomial.X ^ N : R[X]) := by
  rw [← Polynomial.coe_X, jet_coe, AdjoinRoot.mk_X]

/-- Every element of `R[X]/(X ^ N)` is the jet of a power series, for instance of a polynomial. -/
theorem jet_surjective : Function.Surjective (jet R N) := fun y ↦ by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
  exact ⟨p, jet_coe p⟩

/-- The `N`-jet of `f` vanishes exactly when `X ^ N` divides `f`. -/
theorem jet_eq_zero_iff {f : R⟦X⟧} : jet R N f = 0 ↔ X ^ N ∣ f := by
  rw [← map_zero (jet R N), jet_eq_jet_iff, PowerSeries.X_pow_dvd_iff]
  simp

/-- The kernel of the jet map `R⟦X⟧ → R[X]/(X ^ N)` is the ideal `(X ^ N)`. -/
theorem ker_jet : RingHom.ker (jet R N) = Ideal.span {X ^ N} := by
  ext f
  rw [RingHom.mem_ker, jet_eq_zero_iff, Ideal.mem_span_singleton]

/-- Jets are compatible with truncation: the image of the `M`-jet of `f` in `R[X]/(X ^ N)`, for
`N ≤ M`, is the `N`-jet of `f`. -/
@[simp]
theorem algHomOfDvd_jet {M : ℕ} (h : N ≤ M) (f : R⟦X⟧) :
    AdjoinRoot.algHomOfDvd R (Polynomial.X ^ M : R[X]) (Polynomial.X ^ N)
      (pow_dvd_pow Polynomial.X h) (jet R M f) = jet R N f := by
  rw [jet_apply f, AdjoinRoot.algHomOfDvd, AdjoinRoot.coe_mapAlgHom, AdjoinRoot.map_mk, eq_comm,
    jet_eq_mk_iff]
  intro d hd
  simp [coeff_trunc, hd.trans_le h]

/-- **A power series is determined by its jets.** -/
theorem eq_of_forall_jet_eq {f g : R⟦X⟧} (h : ∀ N, jet R N f = jet R N g) : f = g := by
  ext d
  exact jet_eq_jet_iff.1 (h (d + 1)) d d.lt_succ_self

/-- **Every compatible sequence of jets comes from a power series.** If `y N ∈ R[X]/(X ^ N)` is
the image of `y (N + 1)` for every `N`, then there is a power series whose `N`-jet is `y N` for
every `N`. Together with `eq_of_forall_jet_eq`, `R⟦X⟧` is the inverse limit of the
`R[X]/(X ^ N)`. -/
theorem exists_forall_jet_eq (y : ∀ N, AdjoinRoot (Polynomial.X ^ N : R[X]))
    (hy : ∀ N, AdjoinRoot.algHomOfDvd R (Polynomial.X ^ (N + 1) : R[X]) (Polynomial.X ^ N)
      (pow_dvd_pow Polynomial.X N.le_succ) (y (N + 1)) = y N) :
    ∃ f : R⟦X⟧, ∀ N, jet R N f = y N := by
  choose g hg using fun N ↦ jet_surjective (y N)
  -- consecutive lifts agree below the smaller level
  have hstep (N : ℕ) : ∀ d < N, coeff d (g (N + 1)) = coeff d (g N) := by
    rw [← jet_eq_jet_iff, ← algHomOfDvd_jet N.le_succ, hg, hg, hy]
  -- so the coefficient of degree `d` is the same in every lift of level above `d`
  have hcoeff (N : ℕ) : ∀ d < N, coeff d (g N) = coeff d (g (d + 1)) := by
    induction N with
    | zero => exact fun d hd ↦ absurd hd d.not_lt_zero
    | succ N ih =>
      intro d hd
      rcases (Nat.lt_succ_iff.1 hd).lt_or_eq with hd | rfl
      · rw [hstep N d hd, ih d hd]
      · rfl
  refine ⟨mk fun d ↦ coeff d (g (d + 1)), fun N ↦ ?_⟩
  rw [← hg N, jet_eq_jet_iff]
  intro d hd
  rw [coeff_mk, hcoeff N d hd]

/-- **The universal property of `R⟦X⟧` as the inverse limit of its jets.** A sequence of
`k`-algebra maps `φ N : A → R[X]/(X ^ N)`, compatible with the truncations, is the sequence of jets
of a single `k`-algebra map `A → R⟦X⟧`; this map is unique by `eq_of_forall_jet_eq`. -/
theorem exists_algHom_forall_jet_comp_eq {k A : Type*} [CommSemiring k] [Semiring A]
    [Algebra k A] [Algebra k R] (φ : ∀ N, A →ₐ[k] AdjoinRoot (Polynomial.X ^ N : R[X]))
    (hφ : ∀ N, ((AdjoinRoot.algHomOfDvd R (Polynomial.X ^ (N + 1) : R[X]) (Polynomial.X ^ N)
      (pow_dvd_pow Polynomial.X N.le_succ)).restrictScalars k).comp (φ (N + 1)) = φ N) :
    ∃ ψ : A →ₐ[k] R⟦X⟧, ∀ N, ((jet R N).restrictScalars k).comp ψ = φ N := by
  choose f hf using fun a ↦ exists_forall_jet_eq (fun N ↦ φ N a) fun N ↦ congr($(hφ N) a)
  refine ⟨{ toFun := f
            map_one' := eq_of_forall_jet_eq fun N ↦ by rw [hf, map_one, map_one]
            map_mul' := fun a b ↦ eq_of_forall_jet_eq fun N ↦ by rw [hf, map_mul, map_mul, hf, hf]
            map_zero' := eq_of_forall_jet_eq fun N ↦ by rw [hf, map_zero, map_zero]
            map_add' := fun a b ↦ eq_of_forall_jet_eq fun N ↦ by rw [hf, map_add, map_add, hf, hf]
            commutes' := fun c ↦ eq_of_forall_jet_eq fun N ↦ by
              rw [hf, AlgHom.commutes]
              exact (((jet R N).restrictScalars k).commutes c).symm },
    fun N ↦ AlgHom.ext fun a ↦ hf a N⟩

/-- **Jets are natural in the coefficient ring.** For a ring homomorphism `φ : R →+* S`, the image
in `S[X]/(X ^ N)` of the `N`-jet of `f` is the `N`-jet of the image of `f`. -/
theorem map_jet {S : Type*} [CommRing S] (φ : R →+* S) (f : R⟦X⟧) :
    AdjoinRoot.map φ (Polynomial.X ^ N : R[X]) (Polynomial.X ^ N : S[X]) (by simp) (jet R N f) =
      jet S N (map φ f) := by
  rw [jet_apply, AdjoinRoot.map_mk, jet_apply, trunc_map]

end PowerSeries
