/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.Algebra.SkewPolynomial.Operator

/-!
# Algebraic semilinear operators

An operator is algebraic if each vector has its own monic skew-polynomial annihilator. This
is not a global polynomial identity and imposes no finiteness condition on the module.
Algebraicity passes to invariant submodules and quotients, and is preserved by extensions.
These are the algebraicity conditions used for Frobenius modules in Bhatt–Lurie,
*A Riemann–Hilbert correspondence in positive characteristic*, Definition 2.4.1 and §9.5.
-/

public section

open SkewPolynomial

namespace LinearMap

variable {R M N : Type*} [Semiring R] [MulSemiringAction (Multiplicative ℕ) R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  {F : M →ₛₗ[(φ : R →+* R)] M} {G : N →ₛₗ[(φ : R →+* R)] N}

/-- Each vector is annihilated by some monic skew polynomial in the operator `F`. -/
def IsOrbitAlgebraic (F : M →ₛₗ[(φ : R →+* R)] M) : Prop :=
  ∀ x : M, ∃ (n : ℕ) (q : SkewPolynomial R), q.IsMonicOfDegree n ∧ evalSemilinear F q x = 0

/-- The pointwise annihilator criterion for algebraicity. -/
theorem isOrbitAlgebraic_iff : F.IsOrbitAlgebraic ↔
    ∀ x : M, ∃ (n : ℕ) (q : SkewPolynomial R), q.IsMonicOfDegree n ∧
      evalSemilinear F q x = 0 := Iff.rfl

/-- Algebraicity passes to a target via a surjective linear intertwiner. -/
theorem IsOrbitAlgebraic.of_surjective (h : F.IsOrbitAlgebraic) {g : M →ₗ[R] N}
    (hg : Function.Semiconj g F G) (hs : Function.Surjective g) : G.IsOrbitAlgebraic := by
  apply isOrbitAlgebraic_iff.mpr
  intro y
  obtain ⟨x, rfl⟩ := hs y
  obtain ⟨n, q, hq, hx⟩ := isOrbitAlgebraic_iff.mp h x
  exact ⟨n, q, hq, by rw [← evalSemilinear_apply_map hg, hx, map_zero]⟩

/-- Algebraicity passes to a source via an injective linear intertwiner. -/
theorem IsOrbitAlgebraic.of_injective (h : G.IsOrbitAlgebraic) {f : M →ₗ[R] N}
    (hf : Function.Semiconj f F G) (hi : Function.Injective f) : F.IsOrbitAlgebraic := by
  apply isOrbitAlgebraic_iff.mpr
  intro x
  obtain ⟨n, q, hq, hx⟩ := isOrbitAlgebraic_iff.mp h (f x)
  exact ⟨n, q, hq, hi (by rw [evalSemilinear_apply_map hf, hx, map_zero])⟩

variable {L : Type*} [AddCommMonoid L] [Module R L]
  {E : L →ₛₗ[(φ : R →+* R)] L}

/-- Algebraicity of the two outer operators in an exact sequence implies algebraicity in the
middle. The maps need not be injective or surjective for this implication. -/
theorem isOrbitAlgebraic_of_exact {f : L →ₗ[R] M} {g : M →ₗ[R] N}
    (hf : Function.Semiconj f E F) (hg : Function.Semiconj g F G) (hex : Function.Exact f g)
    (hE : E.IsOrbitAlgebraic) (hG : G.IsOrbitAlgebraic) : F.IsOrbitAlgebraic := by
  apply isOrbitAlgebraic_iff.mpr
  intro x
  obtain ⟨n, q, hq, hx⟩ := isOrbitAlgebraic_iff.mp hG (g x)
  have hy : g (evalSemilinear F q x) = 0 := (evalSemilinear_apply_map hg q x).trans hx
  obtain ⟨y, hy⟩ := (hex _).mp hy
  obtain ⟨m, r, hr, hy'⟩ := isOrbitAlgebraic_iff.mp hE y
  refine ⟨m + n, r * q, hr.mul hq, ?_⟩
  rw [map_mul]
  -- Ring multiplication of additive endomorphisms acts by composition.
  change evalSemilinear F r (evalSemilinear F q x) = 0
  rw [← hy, ← evalSemilinear_apply_map hf, hy', map_zero]

section Quotient

variable {A V : Type*} [Ring A] [MulSemiringAction (Multiplicative ℕ) A]
  [AddCommGroup V] [Module A V] {T : V →ₛₗ[(φ : A →+* A)] V}

/-- Pointwise periodicity implies algebraicity: an element of period `d` is killed by `X^d - 1`. -/
theorem isOrbitAlgebraic_of_periodic
    (h : ∀ x, ∃ d : ℕ, 0 < d ∧ T^[d] x = x) : T.IsOrbitAlgebraic := by
  apply isOrbitAlgebraic_iff.mpr
  intro x
  obtain ⟨d, hd, hx⟩ := h x
  refine ⟨d, monomial d 1 - 1, isMonicOfDegree_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · simp [coeff_sub, coeff_monomial, coeff_one, hd.ne]
  · intro k hk
    by_contra! hkd
    exact mem_support_iff.mp hk (by simp [coeff_sub, coeff_monomial, coeff_one, hkd.ne,
      (hd.trans hkd).ne])
  · rw [map_sub]
    -- Evaluate the difference of the two additive endomorphisms pointwise.
    change evalSemilinear T (monomial d 1) x - evalSemilinear T 1 x = 0
    simp [hx]

/-- An operator is algebraic exactly when its restriction to an invariant submodule and its
induced operator on the ordinary quotient are both algebraic. -/
theorem isOrbitAlgebraic_iff_restrict_and_mapQ (S : Submodule A V)
    (hS : S ≤ S.comap T) :
    T.IsOrbitAlgebraic ↔ (T.restrict (p := S) (q := S) hS).IsOrbitAlgebraic ∧
      (S.mapQ S T hS).IsOrbitAlgebraic := by
  have hi : Function.Semiconj S.subtype (T.restrict hS) T :=
    fun x ↦ coe_restrict_apply (q := S) (fun _ hx ↦ hS hx) x
  have hq : Function.Semiconj S.mkQ T (S.mapQ S T hS) :=
    fun x ↦ (LinearMap.congr_fun (S.mapQ_mkQ S T (h := hS)) x).symm
  exact ⟨fun h ↦ ⟨h.of_injective hi S.injective_subtype, h.of_surjective hq S.mkQ_surjective⟩,
    fun ⟨h₁, h₂⟩ ↦ isOrbitAlgebraic_of_exact hi hq (exact_subtype_mkQ S) h₁ h₂⟩

end Quotient

end LinearMap
