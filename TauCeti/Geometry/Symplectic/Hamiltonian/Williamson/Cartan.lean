/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Regular
public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Toral
import TauCeti.Data.Fin.Basic
import TauCeti.LinearAlgebra.Eigenspace.Semisimple

/-!
# Williamson normal forms span Cartan subalgebras

Let `(V, ω)` be a finite-dimensional real symplectic vector space and `b` a Darboux basis with
`m + 2f` planes. For a set `t` of planes among the first `m`, the Williamson blocks
`TauCeti.SymplecticForm.williamsonBlocks b t` are the elliptic blocks `(xₖ² + yₖ²) / 2` (`k ∈ t`)
and hyperbolic blocks `xₖ yₖ` (`k ∉ t`) on the first `m` planes, and the focus-focus pairs
`x y + x' y'`, `x y' - x' y` on the last `2f` planes. Williamson's classification
(`IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_williamsonBlocks`) says that
every nondegenerate family of quadratic forms, one whose Hamiltonian endomorphisms generate a
Cartan subalgebra of `sp(V, ω)`, spans the same space as such blocks. This file proves the
converse, so that the Williamson normal forms are exactly the Cartan subalgebras of `sp(V, ω)`.

* **The blocks are semisimple.** The Hamiltonian endomorphism `A` of each block satisfies
  `A³ = ± A`: on its own plane, or pair of planes, `A²` is `-1` for an elliptic block and for the
  second focus-focus form, and `1` for a hyperbolic block and for the first focus-focus form, and
  `A` kills the other planes. So `A` is semisimple (`TauCeti.isSemisimple_of_pow_three_eq_smul`).
* **The blocks span their centralizer.** A quadratic form `R` Poisson-commuting with every block
  is a linear combination of the blocks. Its polar form `B_R` makes each `A` skew. Since `A` kills
  the planes outside its own and is invertible on them, `B_R` pairs distinct planes of the
  elliptic and hyperbolic blocks, and distinct focus-focus pairs, trivially. On an elliptic plane
  `B_R` is a multiple of `x² + y²`, on a hyperbolic one of `x y`; on the planes `(q, p)`,
  `(q', p')` of a focus-focus pair the first form forces `B_R(q, q') = B_R(p, p') = 0`, and the
  second form `B_R(q', p') = B_R(q, p)` and `B_R(q', p) = -B_R(q, p')`.
* **Nondegeneracy.** Hence the Williamson blocks of a Darboux basis form a nondegenerate family
  (`IsDarbouxBasis.isNondegenerateQuadraticFamily_williamsonBlocks`), by the criterion
  `isNondegenerateQuadraticFamily_of_forall_quadraticPoissonBracket_eq_zero` for toral families.
  With Williamson's theorem, a family is nondegenerate exactly when it spans the Williamson blocks
  of some Darboux basis
  (`isNondegenerateQuadraticFamily_iff_exists_isDarbouxBasis_span_eq_span_williamsonBlocks`), and a
  Lie subalgebra of `sp(V, ω)` is a Cartan subalgebra exactly when it is the image of the span of
  the Williamson blocks of some Darboux basis
  (`isCartanSubalgebra_iff_exists_isDarbouxBasis_eq_map_span_williamsonBlocks`).

## Main results

All declarations are in the namespace `TauCeti.SymplecticForm`.

* `IsDarbouxBasis.isNondegenerateQuadraticFamily_williamsonBlocks`: the Williamson blocks of a
  Darboux basis form a nondegenerate family.
* `isNondegenerateQuadraticFamily_iff_exists_isDarbouxBasis_span_eq_span_williamsonBlocks`: a
  family is nondegenerate exactly when it spans the Williamson blocks of some Darboux basis.
* `isCartanSubalgebra_iff_exists_isDarbouxBasis_eq_map_span_williamsonBlocks`: the Cartan
  subalgebras of `sp(V, ω)` are exactly the images of the spans of Williamson blocks.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Section 1.8.
-/

public section

noncomputable section

open Module

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {ω : SymplecticForm V}
  {m f : ℕ} {b : Basis (Fin (m + f * 2) × Fin 2) ℝ V} {t : Finset (Fin m)}

/-! ### The Hamiltonian endomorphisms of single blocks -/

/-- In a Darboux basis, the Hamiltonian endomorphism of the focus-focus Williamson block
`inr (j, i)` kills every plane outside the `j`-th focus-focus pair. -/
private theorem IsDarbouxBasis.hamiltonianEnd_williamsonBlocks_inr_apply_of_ne
    (hb : ω.IsDarbouxBasis b) (j : Fin f) (i : Fin 2) {P : Fin (m + f * 2)}
    (hP : ∀ i', P ≠ Fin.natAdd m (finProdFinEquiv (j, i'))) (a : Fin 2) :
    ω.hamiltonianEnd (williamsonBlocks b t (.inr (j, i))) (b (P, a)) = 0 := by
  rw [williamsonBlocks_inr]
  induction P using Fin.addCases with
  | left k =>
    exact hb.hamiltonianEnd_focusFocusBlocksAt_apply_of_forall_ne _
      (fun _ ↦ Fin.natAdd_ne_castAdd _ _) a
  | right p =>
    obtain ⟨⟨j', i'⟩, rfl⟩ := finProdFinEquiv.surjective p
    have hj : j' ≠ j := fun h ↦ hP i' (by rw [h])
    have he := Fin.natAdd_comp_finProdFinEquiv_injective (m := m) (n := f) (k := 2)
    fin_cases i <;>
      simp [hb.hamiltonianEnd_focusFocusBlocksAt_zero_apply he,
        hb.hamiltonianEnd_focusFocusBlocksAt_one_apply he, hj]

/-- In a Darboux basis, the Hamiltonian endomorphism `A` of each Williamson block satisfies
`A³ = c A` for some `c ≠ 0`: `c = -1` for an elliptic block and for the second form of a
focus-focus pair, and `c = 1` for a hyperbolic block and for the first form of a focus-focus
pair. -/
private theorem IsDarbouxBasis.exists_hamiltonianEnd_williamsonBlocks_pow_three
    (hb : ω.IsDarbouxBasis b) (l : Fin m ⊕ Fin f × Fin 2) :
    ∃ c : ℝ, c ≠ 0 ∧ ω.hamiltonianEnd (williamsonBlocks b t l) ^ 3 =
      c • ω.hamiltonianEnd (williamsonBlocks b t l) := by
  rcases l with k | ⟨j, i⟩
  · refine ⟨if k ∈ t then -1 else 1, by split_ifs <;> norm_num, b.ext fun ⟨P, a⟩ ↦ ?_⟩
    by_cases hP : P = Fin.castAdd _ k
    · subst hP
      fin_cases a <;> by_cases hk : k ∈ t <;>
        simp [pow_succ, mul_apply_eq_comp, hk, hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
          hb.hamiltonianEnd_williamsonBlocks_inl_apply_snd]
    · fin_cases a <;> split_ifs <;>
        simp [pow_succ, mul_apply_eq_comp, hP, hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
          hb.hamiltonianEnd_williamsonBlocks_inl_apply_snd]
  · refine ⟨if i = 0 then 1 else -1, by split_ifs <;> norm_num, b.ext fun ⟨P, a⟩ ↦ ?_⟩
    by_cases hP : ∃ i', P = Fin.natAdd m (finProdFinEquiv (j, i'))
    · obtain ⟨i', rfl⟩ := hP
      have he := Fin.natAdd_comp_finProdFinEquiv_injective (m := m) (n := f) (k := 2)
      fin_cases i <;> fin_cases i' <;> fin_cases a <;>
        simp [pow_succ, mul_apply_eq_comp, williamsonBlocks_inr,
          hb.hamiltonianEnd_focusFocusBlocksAt_zero_apply he,
          hb.hamiltonianEnd_focusFocusBlocksAt_one_apply he]
    · push Not at hP
      have h0 := hb.hamiltonianEnd_williamsonBlocks_inr_apply_of_ne (t := t) j i hP
      split_ifs <;> simp [pow_succ, mul_apply_eq_comp, h0]

/-- In a Darboux basis, the Hamiltonian endomorphism of each Williamson block is semisimple. Once
the blocks are known to be nondegenerate this is a case of
`IsNondegenerateQuadraticFamily.isSemisimple_hamiltonianEnd`; here it is a step towards that. -/
private theorem IsDarbouxBasis.isSemisimple_hamiltonianEnd_williamsonBlocks
    (hb : ω.IsDarbouxBasis b) (l : Fin m ⊕ Fin f × Fin 2) :
    (ω.hamiltonianEnd (williamsonBlocks b t l)).IsSemisimple := by
  obtain ⟨c, hc, h⟩ := hb.exists_hamiltonianEnd_williamsonBlocks_pow_three (t := t) l
  exact isSemisimple_of_pow_three_eq_smul hc h

/-! ### The centralizer of the Williamson blocks -/

section Centralizer

variable {R : QuadraticForm ℝ V}

/-- A form Poisson-commuting with the block on the plane `k < m` pairs that plane trivially with
every other plane: the block's Hamiltonian endomorphism kills the other planes and is invertible on
its own. -/
private theorem IsDarbouxBasis.polar_castAdd_of_ne (hb : ω.IsDarbouxBasis b)
    (hR : ω.quadraticPoissonBracket R (williamsonBlocks b t (.inl k)) = 0) {P : Fin (m + f * 2)}
    (hP : P ≠ Fin.castAdd _ k) (a a' : Fin 2) :
    QuadraticMap.polar R (b (Fin.castAdd _ k, a)) (b (P, a')) = 0 := by
  have h₀ := ω.polar_hamiltonianEnd_apply_of_quadraticPoissonBracket_eq_zero hR
    (b (Fin.castAdd _ k, 0)) (b (P, a'))
  have h₁ := ω.polar_hamiltonianEnd_apply_of_quadraticPoissonBracket_eq_zero hR
    (b (Fin.castAdd _ k, 1)) (b (P, a'))
  have hA (c : Fin 2) : ω.hamiltonianEnd (williamsonBlocks b t (.inl k)) (b (P, c)) = 0 := by
    fin_cases c <;> simp [hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
      hb.hamiltonianEnd_williamsonBlocks_inl_apply_snd, hP]
  by_cases hk : k ∈ t <;> fin_cases a <;>
    simp_all [hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
      hb.hamiltonianEnd_williamsonBlocks_inl_apply_snd]

/-- A form Poisson-commuting with the first form of the `j`-th focus-focus pair pairs the two
planes of that pair trivially with every other plane. -/
private theorem IsDarbouxBasis.polar_natAdd_of_ne (hb : ω.IsDarbouxBasis b) {j : Fin f}
    (hR : ω.quadraticPoissonBracket R (williamsonBlocks b t (.inr (j, 0))) = 0)
    {P : Fin (m + f * 2)} (hP : ∀ i', P ≠ Fin.natAdd m (finProdFinEquiv (j, i'))) (i a a' : Fin 2) :
    QuadraticMap.polar R (b (Fin.natAdd m (finProdFinEquiv (j, i)), a)) (b (P, a')) = 0 := by
  have h := ω.polar_hamiltonianEnd_apply_of_quadraticPoissonBracket_eq_zero hR
    (b (Fin.natAdd m (finProdFinEquiv (j, i)), a)) (b (P, a'))
  have he := Fin.natAdd_comp_finProdFinEquiv_injective (m := m) (n := f) (k := 2)
  rw [hb.hamiltonianEnd_williamsonBlocks_inr_apply_of_ne j 0 hP, williamsonBlocks_inr,
    hb.hamiltonianEnd_focusFocusBlocksAt_zero_apply he] at h
  fin_cases a <;> simpa using h

/-- On the plane `k < m`, a form Poisson-commuting with the block of that plane has polar form a
multiple of `x² + y²` if the block is elliptic, and of `x y` if it is hyperbolic. -/
private theorem IsDarbouxBasis.polar_castAdd (hb : ω.IsDarbouxBasis b)
    (hR : ω.quadraticPoissonBracket R (williamsonBlocks b t (.inl k)) = 0) :
    (k ∈ t → QuadraticMap.polar R (b (Fin.castAdd _ k, 0)) (b (Fin.castAdd _ k, 1)) = 0 ∧
      QuadraticMap.polar R (b (Fin.castAdd _ k, 1)) (b (Fin.castAdd _ k, 1)) =
        QuadraticMap.polar R (b (Fin.castAdd _ k, 0)) (b (Fin.castAdd _ k, 0))) ∧
    (k ∉ t → QuadraticMap.polar R (b (Fin.castAdd _ k, 0)) (b (Fin.castAdd _ k, 0)) = 0 ∧
      QuadraticMap.polar R (b (Fin.castAdd _ k, 1)) (b (Fin.castAdd _ k, 1)) = 0) := by
  have h (c c' : Fin 2) := ω.polar_hamiltonianEnd_apply_of_quadraticPoissonBracket_eq_zero hR
    (b (Fin.castAdd _ k, c)) (b (Fin.castAdd _ k, c'))
  have h₀₀ := h 0 0
  have h₀₁ := h 0 1
  have h₁₁ := h 1 1
  have hpq := QuadraticMap.polar_comm R (b (Fin.castAdd _ k, 1)) (b (Fin.castAdd _ k, 0))
  refine ⟨fun hk ↦ ?_, fun hk ↦ ?_⟩ <;>
    simp only [hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
      hb.hamiltonianEnd_williamsonBlocks_inl_apply_snd, hk, ↓reduceIte,
      QuadraticMap.polar_neg_left, QuadraticMap.polar_neg_right, neg_neg] at h₀₀ h₀₁ h₁₁ <;>
    constructor <;> linarith

/-- On the planes `(q, p)` and `(q', p')` of the `j`-th focus-focus pair, the polar form of a form
Poisson-commuting with that pair vanishes on two `q`'s and on two `p`'s, and satisfies
`B(q', p) = -B(q, p')` and `B(q', p') = B(q, p)`. -/
private theorem IsDarbouxBasis.polar_natAdd (hb : ω.IsDarbouxBasis b) {j : Fin f}
    (hR₀ : ω.quadraticPoissonBracket R (williamsonBlocks b t (.inr (j, 0))) = 0)
    (hR₁ : ω.quadraticPoissonBracket R (williamsonBlocks b t (.inr (j, 1))) = 0) :
    (∀ i i' c, QuadraticMap.polar R (b (Fin.natAdd m (finProdFinEquiv (j, i)), c))
      (b (Fin.natAdd m (finProdFinEquiv (j, i')), c)) = 0) ∧
    QuadraticMap.polar R (b (Fin.natAdd m (finProdFinEquiv (j, 1)), 0))
        (b (Fin.natAdd m (finProdFinEquiv (j, 0)), 1)) =
      -QuadraticMap.polar R (b (Fin.natAdd m (finProdFinEquiv (j, 0)), 0))
        (b (Fin.natAdd m (finProdFinEquiv (j, 1)), 1)) ∧
    QuadraticMap.polar R (b (Fin.natAdd m (finProdFinEquiv (j, 1)), 0))
        (b (Fin.natAdd m (finProdFinEquiv (j, 1)), 1)) =
      QuadraticMap.polar R (b (Fin.natAdd m (finProdFinEquiv (j, 0)), 0))
        (b (Fin.natAdd m (finProdFinEquiv (j, 0)), 1)) := by
  have he := Fin.natAdd_comp_finProdFinEquiv_injective (m := m) (n := f) (k := 2)
  refine ⟨fun i i' c ↦ ?_, ?_, ?_⟩
  · -- The first form fixes the `q`'s and negates the `p`'s of the pair.
    have h := ω.polar_hamiltonianEnd_apply_of_quadraticPoissonBracket_eq_zero hR₀
      (b (Fin.natAdd m (finProdFinEquiv (j, i)), c))
      (b (Fin.natAdd m (finProdFinEquiv (j, i')), c))
    obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
    all_goals
      simp only [williamsonBlocks_inr, hb.hamiltonianEnd_focusFocusBlocksAt_zero_apply he,
        one_ne_zero, ↓reduceIte,
        QuadraticMap.polar_neg_left, QuadraticMap.polar_neg_right, neg_neg] at h
      linarith
  · -- The second form sends `q ↦ q' ↦ -q` and `p ↦ p' ↦ -p`.
    have h := ω.polar_hamiltonianEnd_apply_of_quadraticPoissonBracket_eq_zero hR₁
      (b (Fin.natAdd m (finProdFinEquiv (j, 0)), 0))
      (b (Fin.natAdd m (finProdFinEquiv (j, 0)), 1))
    simpa [williamsonBlocks_inr, hb.hamiltonianEnd_focusFocusBlocksAt_one_apply he] using h
  · have h := ω.polar_hamiltonianEnd_apply_of_quadraticPoissonBracket_eq_zero hR₁
      (b (Fin.natAdd m (finProdFinEquiv (j, 0)), 0))
      (b (Fin.natAdd m (finProdFinEquiv (j, 1)), 1))
    simpa [williamsonBlocks_inr, hb.hamiltonianEnd_focusFocusBlocksAt_one_apply he] using h

variable (b t R) in
/-- The coefficients of a form `R` Poisson-commuting with the Williamson blocks: `B_R(q, q)` on an
elliptic plane, `B_R(q, p)` on a hyperbolic one, and `B_R(q, p)`, `B_R(q, p')` for the two forms of
the focus-focus pair on the planes `(q, p)`, `(q', p')`. -/
private def williamsonCoeff : Fin m ⊕ Fin f × Fin 2 → ℝ :=
  Sum.elim
    (fun k ↦ if k ∈ t then QuadraticMap.polar R (b (Fin.castAdd _ k, 0)) (b (Fin.castAdd _ k, 0))
      else QuadraticMap.polar R (b (Fin.castAdd _ k, 0)) (b (Fin.castAdd _ k, 1)))
    (fun l ↦ QuadraticMap.polar R (b (Fin.natAdd m (finProdFinEquiv (l.1, 0)), 0))
      (b (Fin.natAdd m (finProdFinEquiv (l.1, l.2)), 1)))

/-- On the plane `k < m`, the Hamiltonian endomorphism of a form Poisson-commuting with the block
of that plane agrees with that of `∑ₗ dₗ Bₗ`, `d` the coefficients `williamsonCoeff`. -/
private theorem IsDarbouxBasis.hamiltonianEnd_apply_castAdd (hb : ω.IsDarbouxBasis b)
    (hR : ω.quadraticPoissonBracket R (williamsonBlocks b t (.inl k)) = 0) (a : Fin 2) :
    ω.hamiltonianEnd R (b (Fin.castAdd _ k, a)) =
      ω.hamiltonianEnd (∑ l, williamsonCoeff b t R l • williamsonBlocks b t l)
        (b (Fin.castAdd _ k, a)) := by
  obtain ⟨hell, hhyp⟩ := hb.polar_castAdd hR
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  all_goals
    simp only [hb.hamiltonianEnd_sum_smul_williamsonBlocks_apply_castAdd_fst,
      hb.hamiltonianEnd_sum_smul_williamsonBlocks_apply_castAdd_snd]
    refine ω.hamiltonianEnd_apply_eq_of_basis b fun ⟨P', a'⟩ ↦ ?_
    by_cases hP : P' = Fin.castAdd _ k
    · subst hP
      obtain rfl | rfl : a' = 0 ∨ a' = 1 := by omega
      all_goals by_cases hk : k ∈ t <;>
        simp [williamsonCoeff, hk, hb.apply_fst, hb.apply_snd, hell, hhyp,
          QuadraticMap.polar_comm R (b (Fin.castAdd _ k, 1)) (b (Fin.castAdd _ k, 0))]
    · rw [hb.polar_castAdd_of_ne hR hP]
      split_ifs <;> simp [hb.apply_fst, hb.apply_snd, hP]

/-- On the planes of the `j`-th focus-focus pair, the Hamiltonian endomorphism of a form
Poisson-commuting with that pair agrees with that of `∑ₗ dₗ Bₗ`, `d` the coefficients
`williamsonCoeff`. -/
private theorem IsDarbouxBasis.hamiltonianEnd_apply_natAdd (hb : ω.IsDarbouxBasis b) {j : Fin f}
    (hR₀ : ω.quadraticPoissonBracket R (williamsonBlocks b t (.inr (j, 0))) = 0)
    (hR₁ : ω.quadraticPoissonBracket R (williamsonBlocks b t (.inr (j, 1))) = 0) (i a : Fin 2) :
    ω.hamiltonianEnd R (b (Fin.natAdd m (finProdFinEquiv (j, i)), a)) =
      ω.hamiltonianEnd (∑ l, williamsonCoeff b t R l • williamsonBlocks b t l)
        (b (Fin.natAdd m (finProdFinEquiv (j, i)), a)) := by
  obtain ⟨hsame, h10, h11⟩ := hb.polar_natAdd hR₀ hR₁
  rw [hb.hamiltonianEnd_sum_smul_williamsonBlocks_apply_natAdd]
  refine ω.hamiltonianEnd_apply_eq_of_basis b fun ⟨P', a'⟩ ↦ ?_
  by_cases hP : ∃ i', P' = Fin.natAdd m (finProdFinEquiv (j, i'))
  · obtain ⟨i', rfl⟩ := hP
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    all_goals obtain rfl | rfl : i' = 0 ∨ i' = 1 := by omega
    all_goals obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
    all_goals obtain rfl | rfl : a' = 0 ∨ a' = 1 := by omega
    all_goals
      simp [williamsonCoeff, hb.apply_fst, hb.apply_snd, hsame, h10, h11,
        QuadraticMap.polar_comm R (b (_, 1)) (b (_, 0))]
  · push Not at hP
    rw [hb.polar_natAdd_of_ne hR₀ hP]
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    all_goals obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
    all_goals simp [hb.apply_fst, hb.apply_snd, hP]

/-- In a Darboux basis, a quadratic form Poisson-commuting with every Williamson block is a linear
combination of the blocks. Once the blocks are known to be nondegenerate this is a case of
`IsNondegenerateQuadraticFamily.mem_span_of_forall_quadraticPoissonBracket_eq_zero`; here it is a
step towards that. -/
private theorem IsDarbouxBasis.mem_span_williamsonBlocks_of_forall_quadraticPoissonBracket_eq_zero
    (hb : ω.IsDarbouxBasis b) (hR : ∀ l, ω.quadraticPoissonBracket R (williamsonBlocks b t l) = 0) :
    R ∈ Submodule.span ℝ (Set.range (williamsonBlocks b t)) := by
  -- `A_R` agrees on the basis with the Hamiltonian endomorphism of `∑ₗ dₗ Bₗ`.
  have hB : ω.hamiltonianEnd R =
      ω.hamiltonianEnd (∑ l, williamsonCoeff b t R l • williamsonBlocks b t l) := by
    refine b.ext fun ⟨P, a⟩ ↦ ?_
    induction P using Fin.addCases with
    | left k => exact hb.hamiltonianEnd_apply_castAdd (hR (.inl k)) a
    | right p =>
      obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective p
      exact hb.hamiltonianEnd_apply_natAdd (hR (.inr (j, 0))) (hR (.inr (j, 1))) i a
  rw [ω.hamiltonianEnd_injective hB]
  exact Submodule.sum_mem _ fun l _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

end Centralizer

/-! ### Williamson normal forms are nondegenerate -/

/-- **Williamson normal forms are nondegenerate.** In a Darboux basis with `m + 2f` planes, for any
set `t` of elliptic planes among the first `m`, the Williamson blocks form a nondegenerate family:
their Hamiltonian endomorphisms span a Cartan subalgebra of `sp(V, ω)`. -/
theorem IsDarbouxBasis.isNondegenerateQuadraticFamily_williamsonBlocks (hb : ω.IsDarbouxBasis b)
    (t : Finset (Fin m)) : ω.IsNondegenerateQuadraticFamily (williamsonBlocks b t) :=
  isNondegenerateQuadraticFamily_of_forall_quadraticPoissonBracket_eq_zero
    hb.quadraticPoissonBracket_williamsonBlocks hb.isSemisimple_hamiltonianEnd_williamsonBlocks
    fun _ hR ↦ hb.mem_span_williamsonBlocks_of_forall_quadraticPoissonBracket_eq_zero hR

/-- **Williamson's classification of nondegenerate families.** A family of quadratic forms on a
finite-dimensional real symplectic vector space is nondegenerate, that is, its Hamiltonian
endomorphisms generate a Cartan subalgebra of `sp(V, ω)`, exactly when it spans the same space as
the Williamson blocks of some Darboux basis: elliptic blocks `(xₖ² + yₖ²) / 2`, hyperbolic blocks
`xₖ yₖ` and focus-focus pairs `x y + x' y'`, `x y' - x' y` on disjoint symplectic coordinate
planes. -/
theorem isNondegenerateQuadraticFamily_iff_exists_isDarbouxBasis_span_eq_span_williamsonBlocks
    {ι : Type*} {Q : ι → QuadraticForm ℝ V} :
    ω.IsNondegenerateQuadraticFamily Q ↔
      ∃ (m f : ℕ) (b : Basis (Fin (m + f * 2) × Fin 2) ℝ V) (u : Finset (Fin m)),
        ω.IsDarbouxBasis b ∧
          Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (williamsonBlocks b u)) :=
  ⟨IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_williamsonBlocks,
    fun ⟨_, _, _, u, hb, hspan⟩ ↦ (isNondegenerateQuadraticFamily_iff_of_span_eq hspan).2
      (hb.isNondegenerateQuadraticFamily_williamsonBlocks u)⟩

/-- **Williamson's classification of the Cartan subalgebras of `sp(V, ω)`.** A Lie subalgebra `H`
of the symplectic Lie algebra of a finite-dimensional real symplectic vector space is a Cartan
subalgebra exactly when, for some Darboux basis, it consists of the Hamiltonian endomorphisms of
the linear combinations of the Williamson blocks: after a linear symplectic change of coordinates,
`H` is spanned by elliptic generators `(xₖ² + yₖ²) / 2`, hyperbolic generators `xₖ yₖ` and
focus-focus pairs `x y + x' y'`, `x y' - x' y` on disjoint symplectic coordinate planes. -/
theorem isCartanSubalgebra_iff_exists_isDarbouxBasis_eq_map_span_williamsonBlocks
    {H : LieSubalgebra ℝ (skewAdjointLieSubalgebra ω.toBilinForm)} :
    H.IsCartanSubalgebra ↔
      ∃ (m f : ℕ) (b : Basis (Fin (m + f * 2) × Fin 2) ℝ V) (u : Finset (Fin m)),
        ω.IsDarbouxBasis b ∧ H.toSubmodule =
          (Submodule.span ℝ (Set.range (williamsonBlocks b u))).map
            ω.hamiltonianEndEquiv.toLinearMap := by
  -- `H` is generated by the Hamiltonian endomorphisms of the family of forms indexed by `H`.
  set Q : H → QuadraticForm ℝ V := fun X ↦ ω.hamiltonianEndEquiv.symm X
  have hH : H.IsCartanSubalgebra ↔ ω.IsNondegenerateQuadraticFamily Q := by
    have hr : (Set.range fun X : H ↦ ω.hamiltonianEndEquiv (Q X)) = (H : Set _) := by
      ext X
      simp [Q]
    rw [isNondegenerateQuadraticFamily_iff, hr, H.lieSpan_eq]
  have hspan : Submodule.span ℝ (Set.range Q) =
      H.toSubmodule.map ω.hamiltonianEndEquiv.symm.toLinearMap := by
    rw [← Submodule.span_eq H.toSubmodule, Submodule.map_span]
    congr 1
    ext R
    simp [Q]
  rw [hH, isNondegenerateQuadraticFamily_iff_exists_isDarbouxBasis_span_eq_span_williamsonBlocks,
    hspan]
  refine exists_congr fun _ ↦ exists_congr fun _ ↦ exists_congr fun _ ↦ exists_congr fun _ ↦
    and_congr_right' ?_
  rw [Submodule.map_symm_eq_iff]
  exact eq_comm

end TauCeti.SymplecticForm
