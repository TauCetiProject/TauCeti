/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Mixed

/-!
# The Williamson type is an invariant

Let `V` be a real vector space with a basis `b` indexed as a Darboux basis with `m + 2f` planes and
let `t` be a set of planes among the first `m`. The Williamson blocks
`TauCeti.SymplecticForm.williamsonBlocks b t` are `|t|` elliptic blocks `(xₖ² + yₖ²) / 2`,
`m - |t|` hyperbolic blocks `xₖ yₖ` and `f` focus-focus pairs `x y + x' y'`, `x y' - x' y`.
Williamson's classification puts every nondegenerate family of quadratic forms on a symplectic
vector space, up to its span, into this normal form, under the hypothesis that the span contains a
regular element
(`IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_williamsonBlocks_of_mem_span`,
in the namespace `TauCeti.SymplecticForm`). This file proves that the **Williamson type**
`(k_e, k_h, k_f) = (|t|, m - |t|, f)` of a normal form is determined by its span alone
(`TauCeti.SymplecticForm.eq_and_eq_and_card_eq_of_span_range_williamsonBlocks_eq`): two normal
forms with the same span have the same numbers of elliptic, hyperbolic and focus-focus blocks. So
the type is an invariant of the span of a nondegenerate family.

The Williamson blocks are linearly independent
(`TauCeti.SymplecticForm.linearIndependent_williamsonBlocks`), and two subspaces of their span `S`
are described without reference to the basis:

* the forms in `S` whose polar bilinear form has rank at most two span the subspace of the
  elliptic and hyperbolic blocks
  (`span_setOf_mem_span_range_williamsonBlocks_and_finrank_range_polarBilin_le_two`), of
  dimension `m`. Each elliptic or hyperbolic block has rank two, while the polar form of a form
  with a nonzero focus-focus component `a (x y + x' y') + c (x y' - x' y)` is injective on the
  four coordinates of that pair;
* the positive semidefinite forms in `S` span the subspace of the elliptic blocks
  (`span_setOf_mem_span_range_williamsonBlocks_and_nonneg`), of dimension `|t|`: a hyperbolic
  block or a focus-focus component takes negative values on its own coordinates.

Both are in the namespace `TauCeti.SymplecticForm`.

The dimension of `S` alone only gives `k_e + k_h + 2 k_f`. Neither description uses the symplectic
form, so the bases need not be Darboux bases.

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

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {m f : ℕ}
  {b : Basis (Fin (m + f * 2) × Fin 2) ℝ V} {t : Finset (Fin m)}

/-! ### Values of combinations of Williamson blocks -/

variable (b) in
/-- The vectors of the coordinate block of the `j`-th focus-focus pair: the linear map sending
`y` to `∑_{i, c} y (i, c) b (m + 2j + i, c)`. -/
private def focusFocusInclusion (j : Fin f) : (Fin 2 × Fin 2 → ℝ) →ₗ[ℝ] V :=
  Fintype.linearCombination ℝ fun ic : Fin 2 × Fin 2 ↦
    b (Fin.natAdd m (finProdFinEquiv (j, ic.1)), ic.2)

/-- The vectors of the coordinate block of a focus-focus pair have no coordinates on the planes of
the elliptic and hyperbolic blocks. -/
@[simp]
private theorem repr_focusFocusInclusion_castAdd (j : Fin f) (y : Fin 2 × Fin 2 → ℝ) (k : Fin m)
    (c : Fin 2) : b.repr (focusFocusInclusion b j y) (Fin.castAdd _ k, c) = 0 := by
  simp [focusFocusInclusion, Fintype.linearCombination_apply]

/-- The coordinates of the vectors of the coordinate block of the focus-focus pair `j`. -/
@[simp]
private theorem repr_focusFocusInclusion_natAdd (j j' : Fin f) (y : Fin 2 × Fin 2 → ℝ)
    (i c : Fin 2) :
    b.repr (focusFocusInclusion b j y) (Fin.natAdd m (finProdFinEquiv (j', i)), c) =
      if j = j' then y (i, c) else 0 := by
  simp only [focusFocusInclusion, Fintype.linearCombination_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  by_cases h : j = j' <;> fin_cases i <;> fin_cases c <;> simp [h]

/-- A combination of Williamson blocks on the plane of an elliptic or hyperbolic block `k` is the
multiple of that block. -/
private theorem sum_smul_williamsonBlocks_apply_castAdd (c : Fin m ⊕ Fin f × Fin 2 → ℝ)
    (k : Fin m) (x y : ℝ) :
    (∑ i, c i • williamsonBlocks b t i)
        (x • b (Fin.castAdd _ k, 0) + y • b (Fin.castAdd _ k, 1)) =
      c (.inl k) * (if k ∈ t then (x ^ 2 + y ^ 2) / 2 else x * y) := by
  simp only [_root_.sum_apply]
  rw [Fintype.sum_sum_type,
    Finset.sum_eq_single k (fun j _ hj ↦ by simp [Ne.symm hj]) (by simp)]
  simp [Fintype.sum_prod_type, Fin.natAdd_ne_castAdd]

/-- A combination of Williamson blocks on the coordinate block of the focus-focus pair `j` is the
corresponding combination of that pair. -/
private theorem sum_smul_williamsonBlocks_apply_focusFocusInclusion
    (c : Fin m ⊕ Fin f × Fin 2 → ℝ) (j : Fin f) (y : Fin 2 × Fin 2 → ℝ) :
    (∑ i, c i • williamsonBlocks b t i) (focusFocusInclusion b j y) =
      c (.inr (j, 0)) * (y (0, 0) * y (0, 1) + y (1, 0) * y (1, 1)) +
        c (.inr (j, 1)) * (y (0, 0) * y (1, 1) - y (1, 0) * y (0, 1)) := by
  simp only [_root_.sum_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type,
    Finset.sum_eq_single j (fun j' _ hj' ↦ by simp [Ne.symm hj']) (by simp)]
  simp

/-- The polar form of a combination of Williamson blocks on the coordinate block of the
focus-focus pair `j`. -/
private theorem polarBilin_sum_smul_williamsonBlocks_focusFocusInclusion
    (c : Fin m ⊕ Fin f × Fin 2 → ℝ) (j : Fin f) (y y' : Fin 2 × Fin 2 → ℝ) :
    (∑ i, c i • williamsonBlocks b t i).polarBilin (focusFocusInclusion b j y)
        (focusFocusInclusion b j y') =
      c (.inr (j, 0)) * (y (0, 0) * y' (0, 1) + y' (0, 0) * y (0, 1) +
          y (1, 0) * y' (1, 1) + y' (1, 0) * y (1, 1)) +
        c (.inr (j, 1)) * (y (0, 0) * y' (1, 1) + y' (0, 0) * y (1, 1) -
          y (1, 0) * y' (0, 1) - y' (1, 0) * y (0, 1)) := by
  have h := sum_smul_williamsonBlocks_apply_focusFocusInclusion (b := b) (t := t) c j
  -- Name the form, so that `polar` sees its coercion rather than a sum of functions.
  generalize ∑ i, c i • williamsonBlocks b t i = P at h ⊢
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, h, h, h]
  simp only [Pi.add_apply]
  ring

/-- **The Williamson blocks are linearly independent.** -/
theorem linearIndependent_williamsonBlocks : LinearIndependent ℝ (williamsonBlocks b t) := by
  refine Fintype.linearIndependent_iff.2 fun c hc ↦ ?_
  have hc' (x : V) : (∑ i, c i • williamsonBlocks b t i) x = 0 := by
    rw [hc, _root_.zero_apply]
  rintro (k | ⟨j, i⟩)
  · have := hc' ((1 : ℝ) • b (Fin.castAdd _ k, 0) + (1 : ℝ) • b (Fin.castAdd _ k, 1))
    rw [sum_smul_williamsonBlocks_apply_castAdd] at this
    split_ifs at this <;> linarith
  · fin_cases i
    · have := hc' (focusFocusInclusion b j (Pi.single (0, 0) 1 + Pi.single (0, 1) 1))
      rw [sum_smul_williamsonBlocks_apply_focusFocusInclusion] at this
      simpa [Pi.single_apply] using this
    · have := hc' (focusFocusInclusion b j (Pi.single (0, 0) 1 + Pi.single (1, 1) 1))
      rw [sum_smul_williamsonBlocks_apply_focusFocusInclusion] at this
      simpa [Pi.single_apply] using this

/-! ### The elliptic and hyperbolic blocks: forms of rank at most two -/

/-- The polar form of an elliptic or hyperbolic Williamson block has rank at most two: its values
are combinations of the two coordinate functions of the block's plane. -/
private theorem finrank_range_polarBilin_williamsonBlocks_inl_le_two (k : Fin m) :
    finrank ℝ (LinearMap.range (williamsonBlocks b t (.inl k)).polarBilin) ≤ 2 := by
  have : FiniteDimensional ℝ V := Module.Finite.of_basis b
  have hle : LinearMap.range (williamsonBlocks b t (.inl k)).polarBilin ≤
      Submodule.span ℝ
        (Set.range ![b.coord (Fin.castAdd _ k, 0), b.coord (Fin.castAdd _ k, 1)]) := by
    rintro _ ⟨u, rfl⟩
    obtain ⟨a₀, a₁, h⟩ : ∃ a₀ a₁ : ℝ, (williamsonBlocks b t (.inl k)).polarBilin u =
        a₀ • b.coord (Fin.castAdd _ k, 0) + a₁ • b.coord (Fin.castAdd _ k, 1) := by
      by_cases hk : k ∈ t
      · exact ⟨b.repr u (Fin.castAdd _ k, 0), b.repr u (Fin.castAdd _ k, 1), by
          ext v; simp [williamsonBlocks_inl, hk, polar_elliptic]⟩
      · exact ⟨b.repr u (Fin.castAdd _ k, 1), b.repr u (Fin.castAdd _ k, 0), by
          ext v; simp [williamsonBlocks_inl, hk, polar_hyperbolic]; ring⟩
    rw [h]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  exact (Submodule.finrank_mono hle).trans ((finrank_range_le_card _).trans (by simp))

/-- A form in the span of the Williamson blocks with a nonzero focus-focus component has a polar
form of rank at least four: the polar form is injective on the coordinate block of that pair. -/
private theorem four_le_finrank_range_polarBilin_sum_smul_williamsonBlocks
    (c : Fin m ⊕ Fin f × Fin 2 → ℝ) (j : Fin f)
    (hj : c (.inr (j, 0)) ≠ 0 ∨ c (.inr (j, 1)) ≠ 0) :
    4 ≤ finrank ℝ (LinearMap.range (∑ i, c i • williamsonBlocks b t i).polarBilin) := by
  have : FiniteDimensional ℝ V := Module.Finite.of_basis b
  set L := (∑ i, c i • williamsonBlocks b t i).polarBilin
  have hinj : Function.Injective (L ∘ₗ focusFocusInclusion b j) := by
    refine (injective_iff_map_eq_zero _).2 fun y hy ↦ ?_
    have hy' (y' : Fin 2 × Fin 2 → ℝ) := congr($hy (focusFocusInclusion b j y'))
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, L,
      polarBilin_sum_smul_williamsonBlocks_focusFocusInclusion] at hy'
    have e₀₀ : c (.inr (j, 0)) * y (0, 1) + c (.inr (j, 1)) * y (1, 1) = 0 := by
      simpa using hy' (Pi.single (0, 0) 1)
    have e₀₁ : c (.inr (j, 0)) * y (0, 0) - c (.inr (j, 1)) * y (1, 0) = 0 := by
      simpa [sub_eq_add_neg] using hy' (Pi.single (0, 1) 1)
    have e₁₀ : c (.inr (j, 0)) * y (1, 1) - c (.inr (j, 1)) * y (0, 1) = 0 := by
      simpa [sub_eq_add_neg] using hy' (Pi.single (1, 0) 1)
    have e₁₁ : c (.inr (j, 0)) * y (1, 0) + c (.inr (j, 1)) * y (0, 0) = 0 := by
      simpa using hy' (Pi.single (1, 1) 1)
    -- Each coordinate of `y`, multiplied by `a² + c² ≠ 0`, is a combination of these equations.
    have hpos : c (.inr (j, 0)) ^ 2 + c (.inr (j, 1)) ^ 2 ≠ 0 := by
      rcases hj with h | h <;> positivity
    have h₀₀ : (c (.inr (j, 0)) ^ 2 + c (.inr (j, 1)) ^ 2) * y (0, 0) = 0 := by
      linear_combination c (.inr (j, 0)) * e₀₁ + c (.inr (j, 1)) * e₁₁
    have h₀₁ : (c (.inr (j, 0)) ^ 2 + c (.inr (j, 1)) ^ 2) * y (0, 1) = 0 := by
      linear_combination c (.inr (j, 0)) * e₀₀ - c (.inr (j, 1)) * e₁₀
    have h₁₀ : (c (.inr (j, 0)) ^ 2 + c (.inr (j, 1)) ^ 2) * y (1, 0) = 0 := by
      linear_combination c (.inr (j, 0)) * e₁₁ - c (.inr (j, 1)) * e₀₁
    have h₁₁ : (c (.inr (j, 0)) ^ 2 + c (.inr (j, 1)) ^ 2) * y (1, 1) = 0 := by
      linear_combination c (.inr (j, 0)) * e₁₀ + c (.inr (j, 1)) * e₀₀
    ext ⟨i, k⟩
    fin_cases i <;> fin_cases k
    · simpa using (mul_eq_zero.1 h₀₀).resolve_left hpos
    · simpa using (mul_eq_zero.1 h₀₁).resolve_left hpos
    · simpa using (mul_eq_zero.1 h₁₀).resolve_left hpos
    · simpa using (mul_eq_zero.1 h₁₁).resolve_left hpos
  calc 4 = finrank ℝ (LinearMap.range (L ∘ₗ focusFocusInclusion b j)) := by
        rw [LinearMap.finrank_range_of_inj hinj]; simp
    _ ≤ finrank ℝ (LinearMap.range L) :=
        Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

/-- **Forms of rank at most two span the elliptic and hyperbolic blocks.** In the span of the
Williamson blocks, the forms whose polar form has rank at most two span the subspace of the
elliptic and hyperbolic blocks. -/
theorem span_setOf_mem_span_range_williamsonBlocks_and_finrank_range_polarBilin_le_two :
    Submodule.span ℝ {P | P ∈ Submodule.span ℝ (Set.range (williamsonBlocks b t)) ∧
        finrank ℝ (LinearMap.range P.polarBilin) ≤ 2} =
      Submodule.span ℝ (Set.range fun k ↦ williamsonBlocks b t (.inl k)) := by
  refine le_antisymm (Submodule.span_le.2 fun P ⟨hP, hrank⟩ ↦ ?_)
    (Submodule.span_le.2 <| Set.range_subset_iff.2 fun k ↦ Submodule.subset_span
      ⟨Submodule.subset_span ⟨_, rfl⟩, finrank_range_polarBilin_williamsonBlocks_inl_le_two k⟩)
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hP
  -- A nonzero focus-focus component would give rank at least four.
  have hc (j : Fin f) : c (.inr (j, 0)) = 0 ∧ c (.inr (j, 1)) = 0 := by
    by_contra hj
    have := four_le_finrank_range_polarBilin_sum_smul_williamsonBlocks (b := b) (t := t) c j
      (not_and_or.1 hj)
    omega
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, hc, zero_smul, add_zero, Finset.sum_const_zero]
  exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- In the span of the Williamson blocks, the forms whose polar form has rank at most two span a
subspace of dimension `m`, that of the elliptic and hyperbolic blocks. -/
theorem finrank_span_setOf_mem_span_range_williamsonBlocks_and_finrank_range_polarBilin_le_two :
    finrank ℝ (Submodule.span ℝ {P | P ∈ Submodule.span ℝ (Set.range (williamsonBlocks b t)) ∧
        finrank ℝ (LinearMap.range P.polarBilin) ≤ 2}) = m := by
  rw [span_setOf_mem_span_range_williamsonBlocks_and_finrank_range_polarBilin_le_two]
  exact (finrank_span_eq_card (linearIndependent_williamsonBlocks.comp _ Sum.inl_injective)).trans
    (Fintype.card_fin m)

/-! ### The elliptic blocks: positive semidefinite forms -/

/-- **Positive semidefinite forms span the elliptic blocks.** In the span of the Williamson
blocks, the positive semidefinite forms span the subspace of the elliptic blocks. -/
theorem span_setOf_mem_span_range_williamsonBlocks_and_nonneg :
    Submodule.span ℝ {P | P ∈ Submodule.span ℝ (Set.range (williamsonBlocks b t)) ∧
        ∀ x, 0 ≤ P x} =
      Submodule.span ℝ (Set.range fun k : t ↦ williamsonBlocks b t (.inl k)) := by
  refine le_antisymm (Submodule.span_le.2 fun P ⟨hP, hnonneg⟩ ↦ ?_)
    (Submodule.span_le.2 <| Set.range_subset_iff.2 fun k ↦ Submodule.subset_span
      ⟨Submodule.subset_span ⟨_, rfl⟩, fun x ↦ by
        simp only [williamsonBlocks_inl_apply, SetLike.coe_mem, ↓reduceIte]; positivity⟩)
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hP
  -- A hyperbolic block takes the value `-c²` at `q - c p`.
  have hh (k : Fin m) (hk : k ∉ t) : c (.inl k) = 0 := by
    have := hnonneg ((1 : ℝ) • b (Fin.castAdd _ k, 0) + (-c (.inl k)) • b (Fin.castAdd _ k, 1))
    rw [sum_smul_williamsonBlocks_apply_castAdd] at this
    simp only [hk, ↓reduceIte] at this
    nlinarith
  -- A focus-focus pair takes the values `-a²` and `-c²` at suitable vectors of its block.
  have hf (j : Fin f) : c (.inr (j, 0)) = 0 ∧ c (.inr (j, 1)) = 0 := by
    have h₀ := hnonneg (focusFocusInclusion b j
      (Pi.single (0, 0) 1 + Pi.single (0, 1) (-c (.inr (j, 0)))))
    have h₁ := hnonneg (focusFocusInclusion b j
      (Pi.single (0, 0) 1 + Pi.single (1, 1) (-c (.inr (j, 1)))))
    rw [sum_smul_williamsonBlocks_apply_focusFocusInclusion] at h₀ h₁
    simp at h₀ h₁
    constructor <;> nlinarith
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, hf, zero_smul, add_zero, Finset.sum_const_zero]
  refine Submodule.sum_mem _ fun k _ ↦ ?_
  by_cases hk : k ∈ t
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩)
  · simp [hh k hk]

/-- In the span of the Williamson blocks, the positive semidefinite forms span a subspace of
dimension `|t|`, that of the elliptic blocks. -/
theorem finrank_span_setOf_mem_span_range_williamsonBlocks_and_nonneg :
    finrank ℝ (Submodule.span ℝ {P | P ∈ Submodule.span ℝ (Set.range (williamsonBlocks b t)) ∧
        ∀ x, 0 ≤ P x}) = t.card := by
  rw [span_setOf_mem_span_range_williamsonBlocks_and_nonneg]
  exact (finrank_span_eq_card ((linearIndependent_williamsonBlocks.comp _ Sum.inl_injective).comp _
    Subtype.val_injective)).trans (Fintype.card_coe t)

/-! ### Invariance of the Williamson type -/

/-- **The Williamson type is an invariant.** If the Williamson blocks of two bases `b` and `b'`,
with `m + 2f` and `m' + 2f'` planes and elliptic planes `t` and `t'`, span the same space of
quadratic forms, then the two normal forms have the same numbers of elliptic, hyperbolic and
focus-focus blocks: `m = m'`, `f = f'` and `|t| = |t'|`. -/
theorem eq_and_eq_and_card_eq_of_span_range_williamsonBlocks_eq {m' f' : ℕ}
    {b' : Basis (Fin (m' + f' * 2) × Fin 2) ℝ V} {t' : Finset (Fin m')}
    (h : Submodule.span ℝ (Set.range (williamsonBlocks b t)) =
      Submodule.span ℝ (Set.range (williamsonBlocks b' t'))) :
    m = m' ∧ f = f' ∧ t.card = t'.card := by
  have hm : m = m' := by
    rw [← finrank_span_setOf_mem_span_range_williamsonBlocks_and_finrank_range_polarBilin_le_two
        (b := b) (t := t),
      ← finrank_span_setOf_mem_span_range_williamsonBlocks_and_finrank_range_polarBilin_le_two
        (b := b') (t := t'), h]
  have hdim := (finrank_eq_card_basis b).symm.trans (finrank_eq_card_basis b')
  simp only [Fintype.card_prod, Fintype.card_fin] at hdim
  refine ⟨hm, by omega, ?_⟩
  rw [← finrank_span_setOf_mem_span_range_williamsonBlocks_and_nonneg (b := b) (t := t),
    ← finrank_span_setOf_mem_span_range_williamsonBlocks_and_nonneg (b := b') (t := t'), h]

end TauCeti.SymplecticForm
