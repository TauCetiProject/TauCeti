/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Bilinear
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.MvPolynomial.Basic
import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# The submodules of polynomials of bounded total degree

Mathlib's `MvPolynomial.restrictTotalDegree σ R m` is the submodule of polynomials of total degree
at most `m`. This file records that these submodules increase with `m`, that a monomial of degree
at most `m` lies in the `m`-th one, and that the `m`-th one is spanned by those monomials, so that
a linear statement about polynomials of bounded degree reduces to monomials.

## Main results

* `MvPolynomial.restrictTotalDegree_mono`: the submodules increase with the degree bound.
* `MvPolynomial.monomial_mem_restrictTotalDegree`: a monomial of degree at most `m` has total
  degree at most `m`.
* `MvPolynomial.restrictTotalDegree_eq_span`: the monomials of degree at most `m` span the
  polynomials of total degree at most `m`.
* `MvPolynomial.basisRestrictTotalDegree`: the monomial basis, indexed by exponent vectors of
  degree at most `m`; `MvPolynomial.basisRestrictTotalDegree_repr_apply` identifies its
  coordinates with coefficients.
* `Module.Basis.apply_mem_of_monomial_degree_le`: a bilinear map takes values in a submodule on
  bounded-degree polynomials if it does so on basis vectors and bounded-degree monomials.
* `Module.Basis.constr_X_mul_mem_restrictTotalDegree`: multiplication by a linear form raises
  total degree by at most one.
-/

public section

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

variable (σ R) in
/-- The polynomials of total degree at most `m` increase with `m`. -/
theorem restrictTotalDegree_mono : Monotone (restrictTotalDegree σ R) :=
  fun _ _ h p hp ↦
    (mem_restrictTotalDegree σ _ p).2 (((mem_restrictTotalDegree σ _ p).1 hp).trans h)

/-- A monomial whose exponent has degree at most `m` has total degree at most `m`. -/
theorem monomial_mem_restrictTotalDegree {s : σ →₀ ℕ} {m : ℕ} (h : s.degree ≤ m) (r : R) :
    monomial s r ∈ restrictTotalDegree σ R m :=
  (mem_restrictTotalDegree σ m _).2 <| (totalDegree_monomial_le s r).trans <| by
    simpa [Finsupp.sum, Finsupp.degree_apply] using h

variable (σ R) in
/-- The polynomials of total degree at most `m` are those supported on exponent vectors of degree
at most `m`. -/
theorem restrictTotalDegree_eq_restrictSupport (m : ℕ) :
    restrictTotalDegree σ R m = restrictSupport R {s : σ →₀ ℕ | s.degree ≤ m} := by
  have hs : {s : σ →₀ ℕ | (s.sum fun _ e ↦ e) ≤ m} = {s | s.degree ≤ m} := by
    ext s
    simp [Finsupp.sum, Finsupp.degree_apply]
  rw [restrictTotalDegree, hs]

variable (σ R) in
/-- The polynomials of total degree at most `m` are spanned by the monomials of degree at most
`m`. -/
theorem restrictTotalDegree_eq_span (m : ℕ) :
    restrictTotalDegree σ R m =
      Submodule.span R ((monomial · 1) '' {s : σ →₀ ℕ | s.degree ≤ m}) := by
  rw [restrictTotalDegree_eq_restrictSupport, restrictSupport_eq_span]

/-- In finitely many variables there are finitely many exponent vectors of degree at most `m`. -/
instance _root_.Finsupp.finite_subtype_degree_le [Finite σ] (m : ℕ) :
    Finite {s : σ →₀ ℕ // s.degree ≤ m} :=
  (Finsupp.finite_of_degree_le m).to_subtype

variable (σ R) in
/-- The monomial basis of the polynomials of total degree at most `m`, indexed by the exponent
vectors of degree at most `m`. It is Mathlib's `MvPolynomial.basisRestrictSupport`, with the
support condition written using `Finsupp.degree`. -/
noncomputable def basisRestrictTotalDegree (m : ℕ) :
    Module.Basis {s : σ →₀ ℕ // s.degree ≤ m} R (restrictTotalDegree σ R m) :=
  (basisRestrictSupport R {s : σ →₀ ℕ | s.degree ≤ m}).map
    (LinearEquiv.ofEq _ _ (restrictTotalDegree_eq_restrictSupport σ R m).symm)

/-- The basis vector indexed by `s` is the monomial `X ^ s`. -/
@[simp]
theorem coe_basisRestrictTotalDegree_apply (m : ℕ) (s : {s : σ →₀ ℕ // s.degree ≤ m}) :
    (basisRestrictTotalDegree σ R m s : MvPolynomial σ R) = monomial s.1 1 := by
  rw [basisRestrictTotalDegree, Module.Basis.map_apply]
  exact TauCeti.coe_basisRestrictSupport_apply {s : σ →₀ ℕ | s.degree ≤ m} s

/-- The coordinate of a polynomial of total degree at most `m` in the monomial basis is its
coefficient. -/
@[simp]
theorem basisRestrictTotalDegree_repr_apply (m : ℕ) (p : restrictTotalDegree σ R m)
    (s : {s : σ →₀ ℕ // s.degree ≤ m}) :
    (basisRestrictTotalDegree σ R m).repr p s = (p : MvPolynomial σ R).coeff s.1 := by
  rfl

end MvPolynomial

namespace Module.Basis

open MvPolynomial

section Bilinear

variable {σ κ R L M : Type*} [CommSemiring R] [AddCommMonoid L] [Module R L]
  [AddCommMonoid M] [Module R M]

/-- A bilinear map out of a module and a polynomial algebra takes values in a submodule on
polynomials of total degree at most `d` if it does so on basis vectors and monomials of degree at
most `d`. -/
theorem apply_mem_of_monomial_degree_le (b : Basis κ R L)
    (Φ : L →ₗ[R] MvPolynomial σ R →ₗ[R] M) (N : Submodule R M) (d : ℕ)
    (h : ∀ (l : κ) (s : σ →₀ ℕ), s.degree ≤ d → Φ (b l) (monomial s 1) ∈ N)
    (x : L) {p : MvPolynomial σ R} (hp : p ∈ restrictTotalDegree σ R d) : Φ x p ∈ N := by
  have hle : Submodule.map₂ Φ (Submodule.span R (Set.range b))
      (Submodule.span R ((monomial · 1) '' {s : σ →₀ ℕ | s.degree ≤ d})) ≤ N := by
    rw [Submodule.map₂_span_span, Submodule.span_le]
    rintro _ ⟨_, ⟨l, rfl⟩, _, ⟨s, hs, rfl⟩, rfl⟩
    exact h l s hs
  rw [b.span_eq, ← restrictTotalDegree_eq_span] at hle
  exact Submodule.map₂_le.1 hle x Submodule.mem_top p hp

end Bilinear

variable {ι R L : Type*} [CommSemiring R] [AddCommMonoid L] [Module R L]

/-- Multiplying by the linear form attached to `x` in the basis `b` raises total degree by at
most one. -/
theorem constr_X_mul_mem_restrictTotalDegree (b : Basis ι R L) {d : ℕ} (x : L)
    {p : MvPolynomial ι R} (hp : p ∈ restrictTotalDegree ι R d) :
    b.constr R X x * p ∈ restrictTotalDegree ι R (d + 1) := by
  refine b.apply_mem_of_monomial_degree_le
    ((LinearMap.mul R _).comp (b.constr R X)) _ d (fun l σ hσ ↦ ?_) x hp
  have hm : (monomial (Finsupp.single l 1 + σ) 1 : MvPolynomial ι R) ∈
      restrictTotalDegree ι R (d + 1) :=
    monomial_mem_restrictTotalDegree (by simpa [Nat.one_add] using hσ) 1
  simpa [monomial_single_add] using hm

end Module.Basis
