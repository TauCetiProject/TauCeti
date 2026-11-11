/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint
public import TauCeti.Geometry.Symplectic.SymplecticTransport
import TauCeti.Analysis.Real.Sqrt
import TauCeti.Geometry.Symplectic.Plane
import TauCeti.LinearAlgebra.End.Basic

/-!
# Williamson normal forms on a symplectic plane

Let `(V, ω)` be a real symplectic vector space and `A` an endomorphism of `V`. A *normal pair*
for `A` is a pair `(q, p)` with `ω(q, p) = 1` on which `A` takes one of the three standard forms
of the elements of `sp(2, ℝ)`:

* **elliptic**, `A q = -c p` and `A p = c q` with `c ≠ 0`, so `A² = -c²`;
* **hyperbolic**, `A q = a q` and `A p = -a p` with `a ≠ 0`, so `A² = a²`;
* **parabolic**, `A q = 0` and `A p = ε q` with `ε ≠ 0`, so `A² = 0`.

In the coordinates `v = x q + y p`, the quadratic Hamiltonian `v ↦ ω(A v, v) / 2` of `A` (see
`TauCeti.SymplecticForm.hamiltonianEnd`) is `c (x² + y²) / 2`, `a x y` and `ε y² / 2`
respectively. These are the elliptic and hyperbolic blocks of Williamson's normal forms of
quadratic Hamiltonians, and the nilpotent block of a degenerate one. Williamson's classification
of the Cartan subalgebras of `sp(V, ω)`, which describes the nondegenerate rank-zero points of
integrable systems (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily`), assembles such
blocks, together with four-dimensional focus-focus blocks, into a Darboux basis.

This file constructs normal pairs.

* An elliptic pair through a vector `v` exists as soon as `A² v = -c² v` and `c ω(A v, v) > 0`
  (`TauCeti.SymplecticForm.exists_apply_eq_one_apply_eq_neg_smul_apply_eq_smul`); the vector `q`
  is a positive multiple of `v`. The sign of `c` is the sign of the Hamiltonian, which is definite
  on the plane spanned by the pair.
* A parabolic pair through `v` exists as soon as `A² v = 0` and `ε ω(A v, v) > 0`
  (`TauCeti.SymplecticForm.exists_apply_eq_one_apply_eq_zero_apply_eq_smul`); the vector `p` is a
  positive multiple of `v`. Any `ε` of the right sign occurs, since rescaling `(q, p)` to
  `(t q, t⁻¹ p)` changes `ε` to `t⁻² ε`.
* For `A` in the symplectic Lie algebra `sp(V, ω)` with `A² = a²`, `a ≠ 0`, every eigenvector `q`
  for `a` has a partner `p` in the eigenspace for `-a` with `ω(q, p) = 1`
  (`TauCeti.SymplecticForm.exists_apply_eq_one_apply_eq_neg_smul`), and on a nonzero space such an
  eigenvector exists, giving a hyperbolic pair
  (`TauCeti.SymplecticForm.exists_apply_eq_one_apply_eq_smul_apply_eq_neg_smul`).

None of these needs `V` to be two-dimensional. On a plane, where a pair with `ω(q, p) = 1` is a
basis, every element of `sp(V, ω)` has a normal pair or vanishes, and normal pairs classify
`sp(V, ω)` up to linear symplectomorphism. The square of `A ∈ sp(V, ω)` is a homothety `κ`
(`TauCeti.SymplecticForm.exists_mul_self_eq_smul_one`), and two elements `A`, `B` of the
symplectic Lie algebras of two symplectic planes are conjugate by a linear symplectomorphism
exactly when they have the same `κ` and their Hamiltonians `v ↦ ω(A v, v)` take positive values
together and negative values together
(`TauCeti.SymplecticForm.exists_isSymplectomorphism_forall_apply_eq_iff`). Thus the nonzero orbits
are the hyperbolic ones (`κ > 0`, one for each `κ`), the elliptic ones (`κ < 0`, two for each
`κ`, told apart by the sign of the Hamiltonian) and the two parabolic ones (`κ = 0`).

## Main results

* `TauCeti.SymplecticForm.exists_apply_eq_one_apply_eq_neg_smul_apply_eq_smul`: elliptic pairs.
* `TauCeti.SymplecticForm.exists_apply_eq_one_apply_eq_zero_apply_eq_smul`: parabolic pairs.
* `TauCeti.SymplecticForm.exists_apply_eq_one_apply_eq_smul_apply_eq_neg_smul`: hyperbolic pairs.
* `TauCeti.SymplecticForm.exists_isSymplectomorphism_forall_apply_eq_iff`: the classification of
  the symplectic Lie algebra of a plane up to linear symplectomorphism.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Appendix 6.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Section 1.8.
-/

public section

noncomputable section

open Module

namespace TauCeti.SymplecticForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {ω : SymplecticForm V} {ω' : SymplecticForm W}

/-! ### Normal pairs -/

/-- **Elliptic normal pairs.** If `A² v = -c² v` and `c ω(A v, v) > 0`, then a positive multiple
`q` of `v` and the vector `p = -c⁻¹ A q` satisfy `ω(q, p) = 1`, `A q = -c p` and `A p = c q`. On
the plane they span, the Hamiltonian `ω(A ·, ·) / 2` of `A` is `c (x² + y²) / 2`. -/
theorem exists_apply_eq_one_apply_eq_neg_smul_apply_eq_smul {A : Module.End ℝ V} {v : V} {c : ℝ}
    (hAv : A (A v) = -(c ^ 2) • v) (hv : 0 < c * ω (A v) v) :
    ∃ q p : V, ω q p = 1 ∧ A q = -c • p ∧ A p = c • q ∧ ∃ μ : ℝ, 0 < μ ∧ q = μ • v := by
  set x := ω (A v) v
  have hc : c ≠ 0 := by rintro rfl; simp at hv
  obtain ⟨μ, hμ0, hμ⟩ := Real.exists_pos_sq_mul_eq_of_mul_pos hv
  refine ⟨μ • v, -(c⁻¹ * μ) • A v, ?_, ?_, ?_, μ, hμ0, rfl⟩
  · have hvAv : ω v (A v) = -x := by rw [← ω.neg_eq]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hvAv]
    field_simp
    linear_combination hμ
  · rw [map_smul, smul_smul]
    congr 1
    field_simp
  · rw [map_smul, hAv, smul_smul, smul_smul]
    congr 1
    field_simp

/-- **Parabolic normal pairs.** If `A² v = 0` and `ε ω(A v, v) > 0`, then a positive multiple `p`
of `v` and the vector `q = ε⁻¹ A p` satisfy `ω(q, p) = 1`, `A q = 0` and `A p = ε q`. On the
plane they span, the Hamiltonian `ω(A ·, ·) / 2` of `A` is `ε y² / 2`. -/
theorem exists_apply_eq_one_apply_eq_zero_apply_eq_smul {A : Module.End ℝ V} {v : V} {ε : ℝ}
    (hAv : A (A v) = 0) (hv : 0 < ε * ω (A v) v) :
    ∃ q p : V, ω q p = 1 ∧ A q = 0 ∧ A p = ε • q ∧ ∃ μ : ℝ, 0 < μ ∧ p = μ • v := by
  have hε : ε ≠ 0 := by rintro rfl; simp at hv
  obtain ⟨μ, hμ0, hμ⟩ := Real.exists_pos_sq_mul_eq_of_mul_pos hv
  refine ⟨(ε⁻¹ * μ) • A v, μ • v, ?_, ?_, ?_, μ, hμ0, rfl⟩
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    field_simp
    linear_combination hμ
  · rw [map_smul, hAv, smul_zero]
  · rw [map_smul, smul_smul]
    congr 1
    field_simp

/-- **Hyperbolic partners.** Let `A ∈ sp(V, ω)` satisfy `A² = a²` with `a ≠ 0`. Every nonzero
eigenvector `q` of `A` for `a` has a partner `p`, an eigenvector for `-a`, with `ω(q, p) = 1`. -/
theorem exists_apply_eq_one_apply_eq_neg_smul {A : Module.End ℝ V}
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) {a : ℝ} (ha : a ≠ 0)
    (hAA : A * A = a ^ 2 • 1) {q : V} (hq : q ≠ 0) (hAq : A q = a • q) :
    ∃ p : V, ω q p = 1 ∧ A p = -a • p := by
  obtain ⟨y, hy⟩ := ω.exists_apply_eq_one hq
  have hAy : ω.toBilinForm q (A y) = -a := by
    have h := (LinearMap.mem_skewAdjointSubmodule A).1 hA q y
    simp only [hAq, map_smul, LinearMap.smul_apply, hy, smul_eq_mul, mul_one, Pi.neg_apply,
      map_neg] at h
    linarith
  have hAAy : A (A y) = a ^ 2 • y := by
    simpa using LinearMap.congr_fun hAA y
  refine ⟨(2 * a)⁻¹ • (a • y - A y), ?_, ?_⟩
  · simp only [map_smul, map_sub, smul_eq_mul, hy, hAy]
    field_simp
    ring
  · rw [map_smul, map_sub, map_smul, hAAy]
    module

/-- **Hyperbolic normal pairs.** On a nonzero space, an element `A ∈ sp(V, ω)` with `A² = a²`,
`a ≠ 0`, has a pair `(q, p)` with `ω(q, p) = 1`, `A q = a q` and `A p = -a p`. On the plane they
span, the Hamiltonian `ω(A ·, ·) / 2` of `A` is `a x y`. -/
theorem exists_apply_eq_one_apply_eq_smul_apply_eq_neg_smul [Nontrivial V] {A : Module.End ℝ V}
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) {a : ℝ} (ha : a ≠ 0)
    (hAA : A * A = a ^ 2 • 1) :
    ∃ q p : V, ω q p = 1 ∧ A q = a • q ∧ A p = -a • p := by
  -- The homothety `-a` is not in `sp(V, ω)`, so `A + a` is nonzero, and its image consists of
  -- eigenvectors for `a`.
  have hne : A + a • 1 ≠ 0 := by
    intro h
    have hA' : (-a) • (1 : Module.End ℝ V) = A := by
      rw [neg_smul, eq_neg_of_add_eq_zero_left h]
    exact ha (neg_eq_zero.1 (eq_zero_of_smul_one_mem (ω := ω) (hA' ▸ hA)))
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 hne
  set q := A v + a • v
  have hq : q ≠ 0 := by simpa [q] using hv
  have hAq : A q = a • q := by
    have hAAv : A (A v) = a ^ 2 • v := by simpa using LinearMap.congr_fun hAA v
    rw [map_add, map_smul, hAAv, smul_add, smul_smul, sq, add_comm]
  obtain ⟨p, hqp, hAp⟩ := exists_apply_eq_one_apply_eq_neg_smul hA ha hAA hq hAq
  exact ⟨q, p, hqp, hAq, hAp⟩

/-! ### Symplectic planes -/

section Plane

/-- **Williamson's classification on a symplectic plane.** Two elements `A` and `B` of the
symplectic Lie algebras of symplectic planes `(V, ω)` and `(W, ω')` are conjugate by a linear
symplectomorphism exactly when their squares are the same homothety and their Hamiltonians
`v ↦ ω(A v, v)` and `w ↦ ω'(B w, w)` take positive values together and negative values
together. -/
theorem exists_isSymplectomorphism_forall_apply_eq_iff (hV : finrank ℝ V = 2)
    (hW : finrank ℝ W = 2) {A : Module.End ℝ V} {B : Module.End ℝ W}
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm)
    (hB : B ∈ skewAdjointLieSubalgebra ω'.toBilinForm) :
    (∃ e : V ≃ₗ[ℝ] W, IsSymplectomorphism ω ω' e ∧ ∀ v, e (A v) = B (e v)) ↔
      (∀ κ : ℝ, A * A = κ • 1 ↔ B * B = κ • 1) ∧
      ((∃ v, 0 < ω (A v) v) ↔ ∃ w, 0 < ω' (B w) w) ∧
      ((∃ v, ω (A v) v < 0) ↔ ∃ w, ω' (B w) w < 0) := by
  refine ⟨fun ⟨e, he, hAB⟩ ↦ ⟨Module.End.mul_self_eq_smul_one_iff_of_forall_apply_eq hAB,
    he.exists_iff_of_forall_apply_eq hAB (0 < ·), he.exists_iff_of_forall_apply_eq hAB (· < 0)⟩,
    ?_⟩
  -- Conversely, `A² = κ` for some `κ`, and according to the sign of `κ` both `A` and `B` have
  -- normal pairs of the same elliptic, parabolic or hyperbolic type with the same parameter, or
  -- both vanish. The linear symplectomorphism matching the two pairs conjugates `A` to `B`.
  rintro ⟨hκ, hpos, hneg⟩
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨κ, hAA⟩ : ∃ κ : ℝ, A * A = κ • 1 := exists_mul_self_eq_smul_one hV ⟨A, hA⟩
  have hBB := (hκ κ).1 hAA
  have hAAv : ∀ v, A (A v) = κ • v := fun v ↦ by simpa using LinearMap.congr_fun hAA v
  have hBBw : ∀ w, B (B w) = κ • w := fun w ↦ by simpa using LinearMap.congr_fun hBB w
  -- A sign `s` taken by the Hamiltonian of `A` is taken by the Hamiltonian of `B`.
  have hsign : ∀ s : ℝ, s ≠ 0 → (∃ v, 0 < s * ω (A v) v) → ∃ w, 0 < s * ω' (B w) w := by
    rintro s hs ⟨v, hv⟩
    rcases hs.lt_or_gt with hs | hs
    · obtain ⟨w, hw⟩ := hneg.1 ⟨v, neg_of_mul_pos_right hv hs.le⟩
      exact ⟨w, mul_pos_of_neg_of_neg hs hw⟩
    · obtain ⟨w, hw⟩ := hpos.1 ⟨v, pos_of_mul_pos_right hv hs.le⟩
      exact ⟨w, mul_pos hs hw⟩
  -- A nonzero value `x` of the Hamiltonian of `A` gives a value of sign `s` with `s ^ 2 = b ^ 2`.
  have hchoose : ∀ (b : ℝ), 0 < b → ∀ x : ℝ, x ≠ 0 → ∃ s : ℝ, s ^ 2 = b ^ 2 ∧ 0 < s * x := by
    intro b hb x hx
    rcases hx.lt_or_gt with hx | hx
    · exact ⟨-b, by ring, by nlinarith⟩
    · exact ⟨b, rfl, mul_pos hb hx⟩
  rcases lt_trichotomy κ 0 with hκ0 | rfl | hκ0
  · -- Elliptic: `κ = -c²`.
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hb : 0 < √(-κ) := Real.sqrt_pos.2 (by linarith)
    have hb2 : √(-κ) ^ 2 = -κ := Real.sq_sqrt (by linarith)
    obtain ⟨c, hc2, hcv⟩ :=
      hchoose _ hb _ (apply_ne_zero_of_neg_of_mul_self_eq_smul_one hV hκ0 hAA hv)
    have hc0 : c ≠ 0 := by rintro rfl; simp at hcv
    obtain ⟨w, hcw⟩ := hsign c hc0 ⟨v, hcv⟩
    have hκc : κ = -(c ^ 2) := by linarith
    obtain ⟨q, p, hqp, hAq, hAp, -⟩ :=
      exists_apply_eq_one_apply_eq_neg_smul_apply_eq_smul (by rw [hAAv, hκc]) hcv
    obtain ⟨q', p', hqp', hBq, hBp, -⟩ :=
      exists_apply_eq_one_apply_eq_neg_smul_apply_eq_smul (by rw [hBBw, hκc]) hcw
    exact exists_isSymplectomorphism_forall_apply_eq_of_pair hV hW hqp hqp'
      (x₁ := 0) (y₁ := -c) (x₂ := c) (y₂ := 0) (by simp [hAq]) (by simp [hAp]) (by simp [hBq])
      (by simp [hBp])
  · rw [zero_smul] at hAA hBB
    by_cases hA0 : A = 0
    · -- Zero: then `B = 0` too, and any symplectomorphism conjugates them.
      have hB0 : B = 0 := by
        by_contra hB0
        obtain ⟨w, hw⟩ := DFunLike.ne_iff.1 hB0
        rw [LinearMap.zero_apply] at hw
        rcases (apply_ne_zero_of_mul_self_eq_zero hW hBB hw).lt_or_gt with h | h
        · obtain ⟨v, hv⟩ := hneg.2 ⟨w, h⟩
          simp [hA0] at hv
        · obtain ⟨v, hv⟩ := hpos.2 ⟨w, h⟩
          simp [hA0] at hv
      obtain ⟨q, hq⟩ := exists_ne (0 : V)
      obtain ⟨p, hqp⟩ := ω.exists_apply_eq_one hq
      obtain ⟨q', hq'⟩ := exists_ne (0 : W)
      obtain ⟨p', hqp'⟩ := ω'.exists_apply_eq_one hq'
      exact exists_isSymplectomorphism_forall_apply_eq_of_pair hV hW hqp hqp'
        (x₁ := 0) (y₁ := 0) (x₂ := 0) (y₂ := 0) (by simp [hA0]) (by simp [hA0])
        (by simp [hB0]) (by simp [hB0])
    · -- Parabolic: `A² = 0` and `A ≠ 0`.
      obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 hA0
      rw [LinearMap.zero_apply] at hv
      obtain ⟨ε, -, hεv⟩ := hchoose 1 one_pos _ (apply_ne_zero_of_mul_self_eq_zero hV hAA hv)
      have hε0 : ε ≠ 0 := by rintro rfl; simp at hεv
      obtain ⟨w, hεw⟩ := hsign ε hε0 ⟨v, hεv⟩
      obtain ⟨q, p, hqp, hAq, hAp, -⟩ :=
        exists_apply_eq_one_apply_eq_zero_apply_eq_smul (by simpa using hAAv v) hεv
      obtain ⟨q', p', hqp', hBq, hBp, -⟩ :=
        exists_apply_eq_one_apply_eq_zero_apply_eq_smul (by simpa using hBBw w) hεw
      exact exists_isSymplectomorphism_forall_apply_eq_of_pair hV hW hqp hqp'
        (x₁ := 0) (y₁ := 0) (x₂ := ε) (y₂ := 0) (by simp [hAq]) (by simp [hAp])
        (by simp [hBq]) (by simp [hBp])
  · -- Hyperbolic: `κ = a²`.
    have ha : √κ ≠ 0 := (Real.sqrt_pos.2 hκ0).ne'
    have ha2 : √κ ^ 2 = κ := Real.sq_sqrt hκ0.le
    obtain ⟨q, p, hqp, hAq, hAp⟩ :=
      exists_apply_eq_one_apply_eq_smul_apply_eq_neg_smul hA ha (by rw [ha2, hAA])
    obtain ⟨q', p', hqp', hBq, hBp⟩ :=
      exists_apply_eq_one_apply_eq_smul_apply_eq_neg_smul hB ha (by rw [ha2, hBB])
    exact exists_isSymplectomorphism_forall_apply_eq_of_pair hV hW hqp hqp'
      (x₁ := √κ) (y₁ := 0) (x₂ := 0) (y₂ := -√κ) (by simp [hAq]) (by simp [hAp])
      (by simp [hBq]) (by simp [hBp])

end Plane

end TauCeti.SymplecticForm
