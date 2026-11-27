/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Mixed
import TauCeti.LinearAlgebra.Eigenspace.CovectorPair

/-!
# The type of a Williamson normal form is an invariant

Let `(V, ω)` be a finite-dimensional real symplectic vector space and `b` a Darboux basis of `V`
with `m + 2f` planes. For a set `u` of planes among the first `m`, the Williamson blocks
`williamsonBlocks b u` are `k_e = |u|` elliptic blocks, `k_h = m - |u|` hyperbolic blocks and
`k_f = f` focus-focus pairs. Williamson's classification of mixed type puts the span of a
nondegenerate family of quadratic forms into the span of such blocks when that span contains a
regular element
(`IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_williamsonBlocks_of_mem_span`).
This file proves that the **type** `(k_e, k_h, k_f)` is determined by the span alone: two normal
forms with the same span have the same numbers of elliptic, hyperbolic and focus-focus blocks
(`IsDarbouxBasis.eq_and_eq_and_card_eq_of_span_williamsonBlocks_eq`). All declarations are in the
namespace `TauCeti.SymplecticForm`.

The type is read off from any *regular* element of the span. Let `P` be a form in the span of the
Williamson blocks such that the square of its Hamiltonian endomorphism `A_P` has distinct nonzero
real eigenvalues `μ ∈ s`, and `A_P` itself has distinct eigenvalues `z = a + bi ∈ t` with
`a, b > 0`, where `2 |s| + 4 |t| = dim V`. Then `|s| = m`, `|t| = f`, and exactly `|u|` of the
`μ ∈ s` are negative
(`IsDarbouxBasis.card_eq_and_card_eq_and_card_filter_eq_of_mem_span_williamsonBlocks`). The span
contains such a form
(`IsDarbouxBasis.exists_mem_span_williamsonBlocks_card_mul_two_add_card_mul_four_eq_finrank`), and
these conditions on `P` do not mention the basis, which gives the invariance.

To count, write `P = ∑ cᵢ Bᵢ` in the blocks. In the coordinates of `b`, the endomorphism `A_P` acts
on the coordinate plane of an elliptic block `Bₖ` as multiplication by the complex number `-i cₖ`,
on the two coordinate lines of a hyperbolic block by `±cₖ`, and on the `q`- and `p`-coordinates of
the `j`-th focus-focus pair, with coefficients `d` and `e`, by `d + ie` and `-d + ie`. So every
eigenvalue `μ` of `A_P²` is `-cₖ²`, `cₖ²` or, for a pair with `de = 0`, `d² - e²`, and every
eigenvalue `a + bi` of `A_P` with `a, b > 0` is `|d| + |e| i` for a pair with `de ≠ 0`. Comparing
the numbers of these values with `|s| + 2 |t| = m + 2f` forces the counts.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* E. Miranda and N. T. Zung, *Equivariant normal form for nondegenerate singular orbits of
  integrable Hamiltonian systems*, Annales scientifiques de l'École Normale Supérieure 37 (2004),
  819–839, Section 2.
-/

public section

noncomputable section

open Module

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ### The Hamiltonian endomorphism of a form in the span of the Williamson blocks -/

section Darboux

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V} {m f : ℕ}
  {b : Basis (Fin (m + f * 2) × Fin 2) ℝ V} {u : Finset (Fin m)}
  (c : Fin m ⊕ Fin f × Fin 2 → ℝ)

/-- In a Darboux basis, a form `∑ cᵢ Bᵢ` in the span of the Williamson blocks acts on the
coordinates `(x, y)` of the plane `k < m` by `(x, y) ↦ (c y, -c x)` if the block is elliptic and by
`(x, y) ↦ (c x, -c y)` if it is hyperbolic, `c = c (inl k)`. -/
private theorem IsDarbouxBasis.repr_hamiltonianEnd_sum_castAdd (hb : ω.IsDarbouxBasis b)
    (k : Fin m) (w : V) :
    b.repr (ω.hamiltonianEnd (∑ i, c i • williamsonBlocks b u i) w) (Fin.castAdd _ k, 0) =
        c (.inl k) * (if k ∈ u then b.repr w (Fin.castAdd _ k, 1)
          else b.repr w (Fin.castAdd _ k, 0)) ∧
      b.repr (ω.hamiltonianEnd (∑ i, c i • williamsonBlocks b u i) w) (Fin.castAdd _ k, 1) =
        -(c (.inl k) * (if k ∈ u then b.repr w (Fin.castAdd _ k, 0)
          else b.repr w (Fin.castAdd _ k, 1))) := by
  rw [hb.repr_hamiltonianEnd_apply_fst, hb.repr_hamiltonianEnd_apply_snd,
    hb.hamiltonianEnd_sum_smul_williamsonBlocks_apply_castAdd_snd,
    hb.hamiltonianEnd_sum_smul_williamsonBlocks_apply_castAdd_fst]
  by_cases hk : k ∈ u <;> simp [hk, hb.apply_fst, hb.apply_snd]

/-- In a Darboux basis, a form `∑ cᵢ Bᵢ` in the span of the Williamson blocks acts on the
`q`-coordinates `(x₀, x₁)` of the `j`-th focus-focus pair by multiplication by `d + ei`, and on its
`p`-coordinates `(y₀, y₁)` by multiplication by `-d + ei`, where `d = c (inr (j, 0))` and
`e = c (inr (j, 1))`. -/
private theorem IsDarbouxBasis.repr_hamiltonianEnd_sum_natAdd (hb : ω.IsDarbouxBasis b)
    (j : Fin f) (i : Fin 2) (w : V) :
    b.repr (ω.hamiltonianEnd (∑ i, c i • williamsonBlocks b u i) w)
        (Fin.natAdd m (finProdFinEquiv (j, i)), 0) =
        c (.inr (j, 0)) * b.repr w (Fin.natAdd m (finProdFinEquiv (j, i)), 0) +
          c (.inr (j, 1)) * (if i = 0 then -b.repr w (Fin.natAdd m (finProdFinEquiv (j, 1)), 0)
            else b.repr w (Fin.natAdd m (finProdFinEquiv (j, 0)), 0)) ∧
      b.repr (ω.hamiltonianEnd (∑ i, c i • williamsonBlocks b u i) w)
          (Fin.natAdd m (finProdFinEquiv (j, i)), 1) =
        -(c (.inr (j, 0)) * b.repr w (Fin.natAdd m (finProdFinEquiv (j, i)), 1)) -
          c (.inr (j, 1)) * (if i = 0 then b.repr w (Fin.natAdd m (finProdFinEquiv (j, 1)), 1)
            else -b.repr w (Fin.natAdd m (finProdFinEquiv (j, 0)), 1)) := by
  rw [hb.repr_hamiltonianEnd_apply_fst, hb.repr_hamiltonianEnd_apply_snd,
    hb.hamiltonianEnd_sum_smul_williamsonBlocks_apply_natAdd,
    hb.hamiltonianEnd_sum_smul_williamsonBlocks_apply_natAdd]
  constructor <;> fin_cases i <;> simp [hb.apply_fst, hb.apply_snd] <;> ring

/-- The coordinates of the plane `k < m` on which a form `∑ cᵢ Bᵢ` in the span of the Williamson
blocks acts as multiplication by a complex number `p + qi`: `-i cₖ` on an elliptic plane, and `±cₖ`
on the two coordinate lines of a hyperbolic plane. -/
private theorem IsDarbouxBasis.exists_covector_castAdd (hb : ω.IsDarbouxBasis b) {v : V} {k : Fin m}
    {c' : Fin 2} (hn : b.repr v (Fin.castAdd _ k, c') ≠ 0) :
    ∃ (φ ψ : V →ₗ[ℝ] ℝ) (p q : ℝ),
      (∀ w, φ (ω.hamiltonianEnd (∑ i, c i • williamsonBlocks b u i) w) = p * φ w - q * ψ w) ∧
      (∀ w, ψ (ω.hamiltonianEnd (∑ i, c i • williamsonBlocks b u i) w) = q * φ w + p * ψ w) ∧
      (φ v ≠ 0 ∨ ψ v ≠ 0) ∧
      ((k ∈ u ∧ p = 0 ∧ q = -c (.inl k)) ∨
        (k ∉ u ∧ (p = c (.inl k) ∨ p = -c (.inl k)) ∧ q = 0)) := by
  have hk := hb.repr_hamiltonianEnd_sum_castAdd c (u := u) k
  by_cases hku : k ∈ u
  · refine ⟨b.coord (Fin.castAdd _ k, 0), b.coord (Fin.castAdd _ k, 1), 0, -c (.inl k),
      fun w ↦ ?_, fun w ↦ ?_, ?_, .inl ⟨hku, rfl, rfl⟩⟩
    · simp only [Basis.coord_apply, (hk w).1]
      simp [hku]
    · simp only [Basis.coord_apply, (hk w).2]
      simp [hku]
    · fin_cases c'
      · exact .inl (by simpa using hn)
      · exact .inr (by simpa using hn)
  · fin_cases c'
    · refine ⟨b.coord (Fin.castAdd _ k, 0), 0, c (.inl k), 0, fun w ↦ ?_, fun w ↦ by simp,
        .inl (by simpa using hn), .inr ⟨hku, .inl rfl, rfl⟩⟩
      simp only [Basis.coord_apply, (hk w).1]
      simp [hku]
    · refine ⟨b.coord (Fin.castAdd _ k, 1), 0, -c (.inl k), 0, fun w ↦ ?_, fun w ↦ by simp,
        .inl (by simpa using hn), .inr ⟨hku, .inr rfl, rfl⟩⟩
      simp only [Basis.coord_apply, (hk w).2]
      simp [hku]

/-- The coordinates of the `j`-th focus-focus pair on which a form `∑ cᵢ Bᵢ` in the span of the
Williamson blocks acts as multiplication by a complex number `p + qi`: `d + ei` on the
`q`-coordinates and `-d + ei` on the `p`-coordinates, for the coefficients `d` and `e` of the
pair. -/
private theorem IsDarbouxBasis.exists_covector_natAdd (hb : ω.IsDarbouxBasis b) {v : V} {j : Fin f}
    {i c' : Fin 2} (hn : b.repr v (Fin.natAdd m (finProdFinEquiv (j, i)), c') ≠ 0) :
    ∃ (φ ψ : V →ₗ[ℝ] ℝ) (p q : ℝ),
      (∀ w, φ (ω.hamiltonianEnd (∑ i, c i • williamsonBlocks b u i) w) = p * φ w - q * ψ w) ∧
      (∀ w, ψ (ω.hamiltonianEnd (∑ i, c i • williamsonBlocks b u i) w) = q * φ w + p * ψ w) ∧
      (φ v ≠ 0 ∨ ψ v ≠ 0) ∧ (p = c (.inr (j, 0)) ∨ p = -c (.inr (j, 0))) ∧
        q = c (.inr (j, 1)) := by
  have hj (i : Fin 2) := hb.repr_hamiltonianEnd_sum_natAdd c (u := u) j i
  have hv : b.repr v (Fin.natAdd m (finProdFinEquiv (j, 0)), c') ≠ 0 ∨
      b.repr v (Fin.natAdd m (finProdFinEquiv (j, 1)), c') ≠ 0 := by
    fin_cases i
    · exact .inl hn
    · exact .inr hn
  fin_cases c'
  · refine ⟨b.coord (Fin.natAdd m (finProdFinEquiv (j, 0)), 0),
      b.coord (Fin.natAdd m (finProdFinEquiv (j, 1)), 0), c (.inr (j, 0)), c (.inr (j, 1)),
      fun w ↦ ?_, fun w ↦ ?_, by simpa using hv, .inl rfl, rfl⟩
    · simp only [Basis.coord_apply, (hj 0 w).1]
      simp
      ring
    · simp only [Basis.coord_apply, (hj 1 w).1]
      simp
      ring
  · refine ⟨b.coord (Fin.natAdd m (finProdFinEquiv (j, 0)), 1),
      b.coord (Fin.natAdd m (finProdFinEquiv (j, 1)), 1), -c (.inr (j, 0)), c (.inr (j, 1)),
      fun w ↦ ?_, fun w ↦ ?_, by simpa using hv, .inr rfl, rfl⟩
    · simp only [Basis.coord_apply, (hj 0 w).2]
      simp
    · simp only [Basis.coord_apply, (hj 1 w).2]
      simp
      ring

/-- Every nonzero vector `v` has a nonzero coordinate on a coordinate line or plane on which a form
`∑ cᵢ Bᵢ` in the span of the Williamson blocks acts as multiplication by a complex number `p + qi`:
`-i cₖ` on an elliptic plane, `±cₖ` on the coordinate lines of a hyperbolic plane, and `±d + ei` on
the coordinates of a focus-focus pair with coefficients `d` and `e`. -/
private theorem IsDarbouxBasis.exists_covector (hb : ω.IsDarbouxBasis b) {v : V} (hv : v ≠ 0) :
    ∃ (φ ψ : V →ₗ[ℝ] ℝ) (p q : ℝ),
      (∀ w, φ (ω.hamiltonianEnd (∑ i, c i • williamsonBlocks b u i) w) = p * φ w - q * ψ w) ∧
      (∀ w, ψ (ω.hamiltonianEnd (∑ i, c i • williamsonBlocks b u i) w) = q * φ w + p * ψ w) ∧
      (φ v ≠ 0 ∨ ψ v ≠ 0) ∧
      ((∃ k ∈ u, p = 0 ∧ q = -c (.inl k)) ∨ (∃ k ∉ u, (p = c (.inl k) ∨ p = -c (.inl k)) ∧ q = 0) ∨
        ∃ j, (p = c (.inr (j, 0)) ∨ p = -c (.inr (j, 0))) ∧ q = c (.inr (j, 1))) := by
  obtain ⟨⟨n, c'⟩, hn⟩ : ∃ i, b.repr v i ≠ 0 := by
    by_contra! h
    exact hv (b.ext_elem fun i ↦ by simp [h])
  induction n using Fin.addCases with
  | left k =>
    obtain ⟨φ, ψ, p, q, hφ, hψ, hφψ, ⟨hku, hp, hq⟩ | ⟨hku, hp, hq⟩⟩ :=
      hb.exists_covector_castAdd c (u := u) hn
    · exact ⟨φ, ψ, p, q, hφ, hψ, hφψ, .inl ⟨k, hku, hp, hq⟩⟩
    · exact ⟨φ, ψ, p, q, hφ, hψ, hφψ, .inr (.inl ⟨k, hku, hp, hq⟩)⟩
  | right p =>
    obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨φ, ψ, p, q, hφ, hψ, hφψ, hp, hq⟩ := hb.exists_covector_natAdd c (u := u) hn
    exact ⟨φ, ψ, p, q, hφ, hψ, hφψ, .inr (.inr ⟨j, hp, hq⟩)⟩

/-- Every eigenvalue `μ` of the square of the Hamiltonian endomorphism of `∑ cᵢ Bᵢ` is attached to a
block: it is `-cₖ²` for an elliptic plane `k`, `cₖ²` for a hyperbolic plane `k`, or `d² - e²` for a
focus-focus pair with coefficients `d`, `e` such that `de = 0`. -/
private theorem IsDarbouxBasis.exists_eq_of_hasEigenvalue_sq (hb : ω.IsDarbouxBasis b) {μ : ℝ}
    (hμ : (ω.hamiltonianEnd (∑ i, c i • williamsonBlocks b u i) ^ 2).HasEigenvalue μ) :
    (∃ k, μ = if k ∈ u then -c (.inl k) ^ 2 else c (.inl k) ^ 2) ∨
      ∃ j, c (.inr (j, 0)) * c (.inr (j, 1)) = 0 ∧
        μ = c (.inr (j, 0)) ^ 2 - c (.inr (j, 1)) ^ 2 := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hAv := hv.apply_eq_smul
  rw [sq, mul_apply_eq_comp] at hAv
  obtain ⟨φ, ψ, p, q, hφ, hψ, hφψ, hblock⟩ := hb.exists_covector c hv.2
  obtain ⟨hpq, hμ⟩ := End.mul_eq_zero_and_sq_sub_sq_eq_of_apply_apply_eq_smul hφ hψ hAv hφψ
  rcases hblock with ⟨k, hku, rfl, rfl⟩ | ⟨k, hku, hp, rfl⟩ | ⟨j, hp, rfl⟩
  · exact .inl ⟨k, by simp [hku, ← hμ]⟩
  · refine .inl ⟨k, ?_⟩
    rcases hp with rfl | rfl <;> simp [hku, ← hμ]
  · refine .inr ⟨j, ?_, ?_⟩
    · rcases hp with rfl | rfl
      · linear_combination hpq
      · linear_combination -hpq
    · rcases hp with rfl | rfl <;> simp [← hμ]

/-- Every eigenvalue `a + bi`, `a, b > 0`, of the Hamiltonian endomorphism of `∑ cᵢ Bᵢ` is
`|d| + |e| i` for a focus-focus pair with coefficients `d` and `e`. -/
private theorem IsDarbouxBasis.exists_abs_eq (hb : ω.IsDarbouxBasis b) {z : ℂ}
    (hz : 0 < z.re ∧ 0 < z.im) {v w : V} (hv : v ≠ 0)
    (hAv : ω.hamiltonianEnd (∑ i, c i • williamsonBlocks b u i) v = z.re • v - z.im • w)
    (hAw : ω.hamiltonianEnd (∑ i, c i • williamsonBlocks b u i) w = z.im • v + z.re • w) :
    ∃ j, |c (.inr (j, 0))| = z.re ∧ |c (.inr (j, 1))| = z.im := by
  obtain ⟨φ, ψ, p, q, hφ, hψ, hφψ, hblock⟩ := hb.exists_covector c hv
  obtain ⟨rfl, hq⟩ := End.eq_and_sq_eq_of_apply_eq_smul_sub_smul hφ hψ hz.2.ne' hAv hAw hφψ
  rcases hblock with ⟨k, -, hp, -⟩ | ⟨k, -, -, rfl⟩ | ⟨j, hp, rfl⟩
  · exact absurd hp hz.1.ne'
  · nlinarith [hz.2]
  · refine ⟨j, ?_, by rw [← abs_of_pos hz.2]; exact (sq_eq_sq_iff_abs_eq_abs _ _).1 hq⟩
    rcases hp with hp | hp
    · rw [← hp, abs_of_pos hz.1]
    · rw [← neg_eq_iff_eq_neg.2 hp, abs_neg, abs_of_pos hz.1]

/-! ### The type of a Williamson normal form -/

omit [FiniteDimensional ℝ V] in
/-- If a finite set `s` of nonzero reals with `m` elements consists of values `-xₖ²` for `k ∈ u` and
`xₖ²` for `k ∉ u`, then exactly `|u|` of its elements are negative. -/
private theorem card_filter_lt_zero_eq {s : Finset ℝ} (hs0 : (0 : ℝ) ∉ s) (x : Fin m → ℝ)
    (hs : s ⊆ Finset.univ.image fun k ↦ if k ∈ u then -x k ^ 2 else x k ^ 2)
    (hcard : s.card = m) : (s.filter (· < 0)).card = u.card := by
  -- Negative elements are values `-xₖ²` with `k ∈ u`, positive ones values `xₖ²` with `k ∉ u`.
  have hneg : (s.filter (· < 0)).card ≤ u.card := by
    refine (Finset.card_le_card fun μ hμ ↦ ?_).trans
      (Finset.card_image_le (s := u) (f := fun k ↦ -x k ^ 2))
    obtain ⟨hμ, hμ0⟩ := Finset.mem_filter.1 hμ
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 (hs hμ)
    by_cases hku : k ∈ u
    · exact Finset.mem_image.2 ⟨k, hku, by simp [hku]⟩
    · simp only [hku, ↓reduceIte] at hμ0
      nlinarith [sq_nonneg (x k)]
  have hpos : (s.filter fun μ ↦ ¬μ < 0).card ≤ m - u.card := by
    refine (Finset.card_le_card fun μ hμ ↦ ?_).trans
      ((Finset.card_image_le (s := uᶜ) (f := fun k ↦ x k ^ 2)).trans_eq
        (by simp [Finset.card_compl]))
    obtain ⟨hμ, hμ0⟩ := Finset.mem_filter.1 hμ
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 (hs hμ)
    by_cases hku : k ∈ u
    · have hne : -x k ^ 2 ≠ 0 := fun h ↦ hs0 (by simpa [hku, h] using hμ)
      simp only [hku, ↓reduceIte] at hμ0
      exact absurd (lt_of_le_of_ne (by nlinarith [sq_nonneg (x k)]) hne) hμ0
    · exact Finset.mem_image.2 ⟨k, Finset.mem_compl.2 hku, by simp [hku]⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := s) (· < 0)
  have hum : u.card ≤ m := by simpa using u.card_le_univ
  omega

/-- **A regular element determines the type of a Williamson normal form.** Let `b` be a Darboux
basis with `m + 2f` planes and `u` a set of planes among the first `m`, so that the Williamson
blocks of `b` are `|u|` elliptic, `m - |u|` hyperbolic and `f` focus-focus blocks. Let `P` be a form
in their span such that the square of its Hamiltonian endomorphism has distinct nonzero real
eigenvalues `μ ∈ s`, and the Hamiltonian endomorphism itself has distinct eigenvalues
`z = a + bi ∈ t` with `a, b > 0`, each with an eigenvector `v + iw`, `v ≠ 0`, where
`2 |s| + 4 |t| = dim V`. Then `|s| = m`, `|t| = f`, and exactly `|u|` of the `μ ∈ s` are
negative. -/
theorem IsDarbouxBasis.card_eq_and_card_eq_and_card_filter_eq_of_mem_span_williamsonBlocks
    (hb : ω.IsDarbouxBasis b) {P : QuadraticForm ℝ V}
    (hP : P ∈ Submodule.span ℝ (Set.range (williamsonBlocks b u))) {s : Finset ℝ} {t : Finset ℂ}
    (hst : s.card * 2 + t.card * 4 = finrank ℝ V) (hs0 : (0 : ℝ) ∉ s)
    (hPs : ∀ μ ∈ s, (ω.hamiltonianEnd P ^ 2).HasEigenvalue μ)
    (ht0 : ∀ z ∈ t, 0 < z.re ∧ 0 < z.im)
    (hPt : ∀ z ∈ t, ∃ v w : V, v ≠ 0 ∧ ω.hamiltonianEnd P v = z.re • v - z.im • w ∧
      ω.hamiltonianEnd P w = z.im • v + z.re • w) :
    s.card = m ∧ t.card = f ∧ (s.filter (· < 0)).card = u.card := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hP
  -- The focus-focus pairs whose coefficients `d = c (inr (j, 0))` and `e = c (inr (j, 1))` are
  -- both nonzero.
  set B := Finset.univ.filter fun j : Fin f ↦ c (.inr (j, 0)) * c (.inr (j, 1)) ≠ 0
  -- Each `z ∈ t` is `|d| + |e| i` for a pair in `B`; each `μ ∈ s` is `-cₖ²` for an elliptic plane
  -- `k`, `cₖ²` for a hyperbolic plane `k`, or `d² - e²` for a pair outside `B`.
  have ht_sub : t ⊆ B.image fun j ↦ (⟨|c (.inr (j, 0))|, |c (.inr (j, 1))|⟩ : ℂ) := fun z hz ↦ by
    obtain ⟨v, w, hv, hAv, hAw⟩ := hPt z hz
    obtain ⟨j, h₁, h₂⟩ := hb.exists_abs_eq c (ht0 z hz) hv hAv hAw
    refine Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, Complex.ext h₁ h₂⟩
    exact mul_ne_zero (abs_pos.1 (h₁ ▸ (ht0 z hz).1)) (abs_pos.1 (h₂ ▸ (ht0 z hz).2))
  have hs_sub : s ⊆ (Finset.univ.image fun k ↦ if k ∈ u then -c (.inl k) ^ 2 else c (.inl k) ^ 2) ∪
      Bᶜ.image fun j ↦ c (.inr (j, 0)) ^ 2 - c (.inr (j, 1)) ^ 2 := fun μ hμ ↦ by
    rcases hb.exists_eq_of_hasEigenvalue_sq c (hPs μ hμ) with ⟨k, hk⟩ | ⟨j, hj, hμj⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk.symm⟩)
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨j, ?_, hμj.symm⟩)
      simpa [B, or_iff_not_imp_left] using hj
  -- Counting: `|s| ≤ m + (f - |B|)` and `|t| ≤ |B| ≤ f`, while `|s| + 2 |t| = m + 2f`. So every
  -- pair lies in `B`, `|t| = f` and `|s| = m`.
  have hfin : finrank ℝ V = (m + f * 2) * 2 := by simp [finrank_eq_card_basis b]
  have hs_le : s.card ≤ m + (f - B.card) := by
    refine (Finset.card_le_card hs_sub).trans ((Finset.card_union_le _ _).trans ?_)
    have h₁ := Finset.card_image_le (s := Finset.univ)
      (f := fun k : Fin m ↦ if k ∈ u then -c (.inl k) ^ 2 else c (.inl k) ^ 2)
    have h₂ := Finset.card_image_le (s := Bᶜ)
      (f := fun j ↦ c (.inr (j, 0)) ^ 2 - c (.inr (j, 1)) ^ 2)
    rw [Finset.card_univ, Fintype.card_fin] at h₁
    rw [Finset.card_compl, Fintype.card_fin] at h₂
    omega
  have ht_le : t.card ≤ B.card := (Finset.card_le_card ht_sub).trans Finset.card_image_le
  have hB : B.card ≤ f := (Finset.card_le_univ B).trans_eq (Fintype.card_fin f)
  have hs : s.card = m := by omega
  have hBc : Bᶜ = ∅ := Finset.card_eq_zero.1 (by rw [Finset.card_compl, Fintype.card_fin]; omega)
  exact ⟨hs, by omega, card_filter_lt_zero_eq hs0 _ (by simpa [hBc] using hs_sub) hs⟩

/-- **The type of a Williamson normal form is an invariant.** If the Williamson blocks of two
Darboux bases, the first with `m + 2f` planes and elliptic planes `u`, the second with `m' + 2f'`
planes and elliptic planes `u'`, span the same space of quadratic forms, then they have the same
numbers of elliptic, hyperbolic and focus-focus blocks: `m = m'`, `f = f'` and `|u| = |u'|`. -/
theorem IsDarbouxBasis.eq_and_eq_and_card_eq_of_span_williamsonBlocks_eq
    (hb : ω.IsDarbouxBasis b) {m' f' : ℕ} {b' : Basis (Fin (m' + f' * 2) × Fin 2) ℝ V}
    {u' : Finset (Fin m')} (hb' : ω.IsDarbouxBasis b')
    (h : Submodule.span ℝ (Set.range (williamsonBlocks b u)) =
      Submodule.span ℝ (Set.range (williamsonBlocks b' u'))) :
    m = m' ∧ f = f' ∧ u.card = u'.card := by
  obtain ⟨P, hP, s, t, hst, hs0, hPs, ht0, hPt⟩ :=
    hb.exists_mem_span_williamsonBlocks_card_mul_two_add_card_mul_four_eq_finrank u
  obtain ⟨hs, ht, hu⟩ :=
    hb.card_eq_and_card_eq_and_card_filter_eq_of_mem_span_williamsonBlocks hP hst hs0 hPs ht0 hPt
  obtain ⟨hs', ht', hu'⟩ := hb'.card_eq_and_card_eq_and_card_filter_eq_of_mem_span_williamsonBlocks
    (h ▸ hP) hst hs0 hPs ht0 hPt
  exact ⟨hs.symm.trans hs', ht.symm.trans ht', hu.symm.trans hu'⟩

end Darboux

end TauCeti.SymplecticForm
