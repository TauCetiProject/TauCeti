/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.HeckePolynomial.Determinant
public import TauCeti.NumberTheory.ModularForms.Newforms.Satake

/-!
# The `GL₂` Hecke polynomial of a newform

Let `f` be a newform of level `N`, weight `k` and nebentypus `χ`, extended by zero to the integers
not coprime to `N`. At a prime `p ∤ N`, the arithmetic Frobenius polynomial of the Galois
representation of `f` is `X² - a_p X + χ(p) p^{k-1}`, whose roots are the Satake parameters of `f`
at `p`. The integral `GL₂` Hecke polynomial `X² - T₁ X + p T₂` (`TauCeti.glnHeckePolynomial`)
is the cohomological form of the same polynomial: it agrees with it for the Hecke eigenvalues
`T₁ = a_p` and `T₂ = χ(p) p^{k-2}` (`HeckeRing.GL2.Newform.glnHeckeEigenvalues`). Passing to
geometric Frobenius takes the normalized reciprocal: a two-dimensional determinant with this
characteristic polynomial at a unit `u` has characteristic polynomial `(X - α⁻¹)(X - β⁻¹)` at
`u⁻¹`, where `{α, β}` are the Satake parameters.

The comparison concerns the coefficient conventions only. The Galois representation of `f`
and the identification of its Frobenius polynomials are not constructed here.

## Main definitions

* `HeckeRing.GL2.Newform.glnHeckeEigenvalues`: the coefficients `(1, a_p, χ(p) p^{k-2})` of the
  `GL₂` Hecke polynomial of `f` at `p`.

## Main results

* `HeckeRing.GL2.Newform.glnHeckePolynomial_glnHeckeEigenvalues`: the Hecke polynomial is
  `X² - a_p X + χ(p) p^{k-1}`.
* `HeckeRing.GL2.Newform.roots_glnHeckePolynomial_glnHeckeEigenvalues`: its roots are the Satake
  parameters.
* `HeckeRing.GL2.Newform.charpoly_inv_eq_prod_satakeParameters`: at geometric Frobenius the
  characteristic polynomial is `(X - α⁻¹)(X - β⁻¹)`.

## References

* P. Allen, F. Calegari, A. Caraiani, T. Gee, D. Helm, B. Le Hung, J. Newton, P. Scholze,
  R. Taylor and J. Thorne, *Potential automorphy over CM fields*, Ann. of Math. 197 (2023),
  §2.2.5, equation (2.2.6), and §2.2.20.
-/

public section

noncomputable section

open Polynomial TauCeti UpperHalfPlane

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The coefficients `(T₀, T₁, T₂) = (1, a_p, χ(p) p^{k-2})` of the `GL₂` Hecke polynomial of a
newform `f` at `p`, where `a_p` is the `p`-th Fourier coefficient of `f` and `χ` its nebentypus
extended by zero. -/
def glnHeckeEigenvalues (f : Newform N k) (p : ℕ) : Fin 3 → ℂ :=
  ![1, (qExpansion 1 f.toCuspForm).coeff p, f.dirichletLift p * (p : ℂ) ^ (k - 2)]

@[simp] lemma glnHeckeEigenvalues_zero (f : Newform N k) (p : ℕ) :
    f.glnHeckeEigenvalues p 0 = 1 :=
  (rfl)

@[simp] lemma glnHeckeEigenvalues_one (f : Newform N k) (p : ℕ) :
    f.glnHeckeEigenvalues p 1 = (qExpansion 1 f.toCuspForm).coeff p :=
  (rfl)

@[simp] lemma glnHeckeEigenvalues_two (f : Newform N k) (p : ℕ) :
    f.glnHeckeEigenvalues p 2 = f.dirichletLift p * (p : ℂ) ^ (k - 2) :=
  (rfl)

/-- `p T₂ = χ(p) p^{k-1}` for `p ≠ 0`. -/
lemma mul_glnHeckeEigenvalues_two (f : Newform N k) {p : ℕ} (hp : p ≠ 0) :
    (p : ℂ) * f.glnHeckeEigenvalues p 2 = f.dirichletLift p * (p : ℂ) ^ (k - 1) := by
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  rw [glnHeckeEigenvalues_two, mul_left_comm, show k - 1 = k - 2 + 1 by ring,
    zpow_add_one₀ hp', mul_comm ((p : ℂ) ^ (k - 2))]

/-- **The classical and cohomological `GL₂` Hecke polynomials agree**: for `p ≠ 0`,
`X² - T₁ X + p T₂` with `T₁ = a_p` and `T₂ = χ(p) p^{k-2}` is `X² - a_p X + χ(p) p^{k-1}`. -/
theorem glnHeckePolynomial_glnHeckeEigenvalues (f : Newform N k) {p : ℕ} (hp : p ≠ 0) :
    glnHeckePolynomial 2 (p : ℂ) (f.glnHeckeEigenvalues p) =
      X ^ 2 - C ((qExpansion 1 f.toCuspForm).coeff p) * X +
        C (f.dirichletLift p * (p : ℂ) ^ (k - 1)) := by
  rw [glnHeckePolynomial_two, mul_glnHeckeEigenvalues_two f hp, glnHeckeEigenvalues_zero,
    glnHeckeEigenvalues_one, C_1, one_mul]

/-- The roots of the `GL₂` Hecke polynomial of `f` at `p ≠ 0` are the Satake parameters. -/
theorem roots_glnHeckePolynomial_glnHeckeEigenvalues (f : Newform N k) {p : ℕ} (hp : p ≠ 0) :
    (glnHeckePolynomial 2 (p : ℂ) (f.glnHeckeEigenvalues p)).roots = f.satakeParameters p := by
  rw [glnHeckePolynomial_glnHeckeEigenvalues f hp, satakeParameters_def]

/-- **Geometric Frobenius for a newform.** Let `D` be a two-dimensional determinant whose
characteristic polynomial at a unit `u`, read as arithmetic Frobenius, is the `GL₂` Hecke
polynomial of `f` at `p`. Then its characteristic polynomial at the geometric Frobenius `u⁻¹` is
`(X - α⁻¹)(X - β⁻¹)`, where `{α, β}` are the Satake parameters of `f` at `p`. The hypothesis
forces `p ≠ 0` and `p` coprime to the level, since `D u = p T₂` is a unit. -/
theorem charpoly_inv_eq_prod_satakeParameters (f : Newform N k) {p : ℕ} {R : Type*} [Semiring R]
    [Algebra ℂ R] (D : Determinant ℂ R 2) {u : Rˣ}
    (h : D.charpoly u = glnHeckePolynomial 2 (p : ℂ) (f.glnHeckeEigenvalues p)) :
    D.charpoly ↑u⁻¹ = ((f.satakeParameters p).map fun α ↦ X - C α⁻¹).prod := by
  have hunit : (p : ℂ) * f.glnHeckeEigenvalues p 2 ≠ 0 := by
    have := (D.isUnit_apply u.isUnit).ne_zero
    rwa [D.apply_eq_of_charpoly_eq_glnHeckePolynomial h, Nat.choose_self, pow_one] at this
  have hp : p ≠ 0 := by
    rintro rfl
    simp at hunit
  have hpN : p.Coprime N := by
    by_contra hpN
    simp [f.dirichletLift_apply_eq_zero p hpN] at hunit
  obtain ⟨α, β, hαβ⟩ := f.exists_satakeParameters_eq_pair p
  obtain ⟨hsum, hprod⟩ := (f.satakeParameters_eq_pair_iff p).mp hαβ
  have h0 := f.zero_notMem_satakeParameters hp hpN
  have hα : α ≠ 0 := fun h ↦ h0 (by simp [hαβ, h])
  have hβ : β ≠ 0 := fun h ↦ h0 (by simp [hαβ, h])
  have hc : (p : ℂ) * f.glnHeckeEigenvalues p 2 * (α⁻¹ * β⁻¹) = 1 := by
    rw [mul_glnHeckeEigenvalues_two f hp, ← hprod]
    field_simp
  rw [Determinant.charpoly_inv_eq_of_charpoly_eq_glnHeckePolynomial_two D h hc,
    glnHeckeEigenvalues_one, ← hsum]
  simp only [hαβ, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton]
  have hC : C (α⁻¹ * β⁻¹) = C α⁻¹ * C β⁻¹ := C_mul
  have hC' : C ((α + β) * (α⁻¹ * β⁻¹)) = C α⁻¹ + C β⁻¹ := by
    rw [← C_add]
    congr 1
    field_simp
    ring
  rw [hC, hC']
  ring

end HeckeRing.GL2.Newform
