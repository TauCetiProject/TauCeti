/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic
import TauCeti.LinearAlgebra.BilinearForm.LocalRing
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Matrix.BilinearForm

/-!
# Replacing blocks of two Jordan constituents

Let `N` be a Jordan splitting of a symmetric form `B` with respect to `π`. Its constituents are not
determined by `B`: two of them, `N k` and `N l`, can often be replaced by other submodules with the
same sum, giving a new Jordan splitting with the same constituents at every other index
(`LinearMap.BilinForm.IsJordanSplitting.update_update`). This is how a dyadic Jordan splitting is
changed by sign walking and oddity fusion, the moves of the Conway–Sloane calculus of `2`-adic
symbols.

In practice the change is local. A family `v` of `N k` whose Gram matrix is `π ^ k` times a matrix
of unit determinant splits off the constituent: `N k` is spanned by `v` and a family `t`
orthogonal to it (`LinearMap.BilinForm.IsJordanSplitting.exists_span_range_sup_span_range_eq`).
If `v` and a similar family `w` of `N l` together span the same submodule as two mutually orthogonal
families `v'` and `w'` with Gram matrices of the same kind, then replacing `v` by `v'` in `N k` and
`w` by `w'` in `N l`, keeping the complements, gives a new Jordan splitting
(`LinearMap.BilinForm.IsJordanSplitting.exists_isJordanSplitting_of_span_eq`).

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.update_update`: two constituents can be replaced by
  orthogonal modular submodules with the same sum.
* `LinearMap.BilinForm.IsJordanSplitting.exists_span_range_sup_span_range_eq`: a block of unit
  determinant splits off a constituent.
* `LinearMap.BilinForm.IsJordanSplitting.exists_isJordanSplitting_of_span_eq`: blocks of two
  constituents with the same span can be exchanged.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §91C.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M} {π : R}
  {N : ℕ → Submodule R M}

/-- **Replacing two constituents of a Jordan splitting.** If `P` and `Q` are orthogonal submodules
with `P ⊔ Q = N k ⊔ N l`, on which `B` is `π ^ k`-modular and `π ^ l`-modular, then replacing
`N k` by `P` and `N l` by `Q` gives a Jordan splitting of `B`. -/
theorem IsJordanSplitting.update_update (h : B.IsJordanSplitting π N) (hB : B.IsRefl)
    (hπ : π ∈ nonZeroDivisors R) {k l : ℕ} (hkl : k ≠ l) {P Q : Submodule R M}
    (hPQ : P ⊔ Q = N k ⊔ N l) (horth : ∀ x ∈ P, ∀ y ∈ Q, B x y = 0)
    (hP : (B.restrict P).IsModular (π ^ k)) (hQ : (B.restrict Q).IsModular (π ^ l)) :
    B.IsJordanSplitting π (Function.update (Function.update N k P) l Q) := by
  set N' := Function.update (Function.update N k P) l Q
  have hN'k : N' k = P := by simp [N', Function.update_of_ne hkl]
  have hN'l : N' l = Q := by simp [N']
  have hN'i {i : ℕ} (hk : i ≠ k) (hl : i ≠ l) : N' i = N i := by
    simp [N', Function.update_of_ne hk, Function.update_of_ne hl]
  have hsymm {x y : M} (hxy : B x y = 0) : B y x = 0 := hB x y hxy
  -- The vectors of `P ⊔ Q = N k ⊔ N l` are orthogonal to the other constituents.
  have hPQ_orth {i : ℕ} (hk : i ≠ k) (hl : i ≠ l) {x y : M} (hx : x ∈ P ⊔ Q) (hy : y ∈ N i) :
      B x y = 0 := by
    have hkl' : N k ⊔ N l = ⨆ j ∈ ({k, l} : Set ℕ), N j := by
      rw [iSup_insert, iSup_singleton]
    rw [hPQ, hkl'] at hx
    exact apply_eq_zero_of_mem_biSup B h.apply_eq_zero (t := {i}) (by simp [hk, hl])
      hx (by rwa [iSup_singleton])
  have hO : ∀ i j, i ≠ j → ∀ x ∈ N' i, ∀ y ∈ N' j, B x y = 0 := by
    intro i j hij x hx y hy
    by_cases hik : i = k <;> by_cases hil : i = l <;> by_cases hjk : j = k <;>
      by_cases hjl : j = l <;> subst_vars <;>
      simp only [hN'k, hN'l, ne_eq, not_true_eq_false] at * <;>
      first
      | exact horth x hx y hy
      | exact hsymm (horth y hy x hx)
      | exact hPQ_orth hjk hjl (Submodule.mem_sup_left hx) (hN'i hjk hjl ▸ hy)
      | exact hPQ_orth hjk hjl (Submodule.mem_sup_right hx) (hN'i hjk hjl ▸ hy)
      | exact hsymm (hPQ_orth hik hil (Submodule.mem_sup_left hy) (hN'i hik hil ▸ hx))
      | exact hsymm (hPQ_orth hik hil (Submodule.mem_sup_right hy) (hN'i hik hil ▸ hx))
      | exact h.apply_eq_zero i j hij x (hN'i hik hil ▸ hx) y (hN'i hjk hjl ▸ hy)
  have hmod (i : ℕ) : (B.restrict (N' i)).IsModular (π ^ i) := by
    by_cases hil : i = l
    · subst hil
      rwa [hN'l]
    by_cases hik : i = k
    · subst hik
      rwa [hN'k]
    rw [hN'i hik hil]
    exact h.isModular i
  -- Orthogonal nondegenerate constituents are independent, and they still span `M`.
  refine ⟨(DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨B.iSupIndep_of_restrict_separatingRight hO fun i ↦ ((hmod i).nondegenerate
      (pow_mem hπ i)).2, ?_⟩, hO, hmod⟩
  refine eq_top_iff.mpr (h.isInternal.submodule_iSup_eq_top.symm.le.trans (iSup_le fun i ↦ ?_))
  have hkl' : N k ⊔ N l ≤ ⨆ i, N' i :=
    hPQ ▸ sup_le (hN'k ▸ le_iSup N' k) (hN'l ▸ le_iSup N' l)
  by_cases hik : i = k
  · exact hik ▸ le_sup_left.trans hkl'
  by_cases hil : i = l
  · exact hil ▸ le_sup_right.trans hkl'
  exact hN'i hik hil ▸ le_iSup N' i

variable [IsLocalRing R]

/-- **Splitting a block off a Jordan constituent.** Over a local ring, let `v` be a family of the
constituent `N k` whose Gram matrix is `π ^ k * A`, with `A` of unit determinant. Then `N k` is
spanned by `v` together with a family `t` of `N k` orthogonal to `v`, whose Gram matrix is
`π ^ k * G` with `G` of unit determinant. -/
theorem IsJordanSplitting.exists_span_range_sup_span_range_eq [Module.Free R M]
    [Module.Finite R M] (h : B.IsJordanSplitting π N) (hB : B.IsSymm) (hπ : π ∈ nonZeroDivisors R)
    {k p : ℕ} {v : Fin p → M} (hv : ∀ i, v i ∈ N k) {A : Matrix (Fin p) (Fin p) R}
    (hA : ∀ i j, B (v i) (v j) = π ^ k * A i j) (hAu : IsUnit A.det) :
    ∃ (m : ℕ) (t : Fin m → M) (G : Matrix (Fin m) (Fin m) R), (∀ j, t j ∈ N k) ∧
      (∀ i j, B (t i) (t j) = π ^ k * G i j) ∧ IsUnit G.det ∧ (∀ i j, B (v i) (t j) = 0) ∧
      Submodule.span R (Set.range v) ⊔ Submodule.span R (Set.range t) = N k := by
  have := h.free k
  have := h.finite k
  let v₀ : Fin p → N k := fun i ↦ ⟨v i, hv i⟩
  obtain ⟨m, t₀, G, hG, hGu, hvt, hsup⟩ :=
    (hB.restrict (N k)).exists_orthogonal_isUnit_det_of_isModular (pow_mem hπ k) (h.isModular k)
      (v := v₀) (A := A) (fun i j ↦ by simpa [v₀] using hA i j) hAu
  refine ⟨m, (N k).subtype ∘ t₀, G, fun j ↦ (t₀ j).2, fun i j ↦ by simpa using hG i j, hGu,
    fun i j ↦ by simpa [v₀] using hvt i j, ?_⟩
  have hv₀ : (N k).subtype ∘ v₀ = v := rfl
  have := congrArg (Submodule.map (N k).subtype) hsup
  rwa [Submodule.map_sup, Submodule.map_span, Submodule.map_span, ← Set.range_comp,
    ← Set.range_comp, hv₀, Submodule.map_top, Submodule.range_subtype] at this

/-- **Exchanging blocks of two Jordan constituents.** Over a local ring, let `v` be a family of
`N k` and `w` a family of `N l`, for `k ≠ l`, with Gram matrices `π ^ k * A` and `π ^ l * D`. Let
`v'` and `w'` be mutually orthogonal families with Gram matrices `π ^ k * A'` and `π ^ l * D'`,
spanning together the same submodule as `v` and `w`; the four matrices have unit determinants.
Then there is a Jordan splitting `N'` of `B` agreeing with `N` away from `k` and `l`, in which
`N' k` is obtained from `N k` by replacing `v` by `v'`: for a family `t` orthogonal to `v` and to
`v'`, with Gram matrix `π ^ k * G` for some `G` of unit determinant, `N k` is spanned by `v` and
`t`, and `N' k` by `v'` and `t`. Likewise `N' l` is obtained from `N l` by replacing `w` by `w'`. -/
theorem IsJordanSplitting.exists_isJordanSplitting_of_span_eq [Module.Free R M]
    [Module.Finite R M] (h : B.IsJordanSplitting π N) (hB : B.IsSymm)
    (hπ : π ∈ nonZeroDivisors R) {k l : ℕ} (hkl : k ≠ l) {p q : ℕ} {v v' : Fin p → M}
    {w w' : Fin q → M} {A A' : Matrix (Fin p) (Fin p) R} {D D' : Matrix (Fin q) (Fin q) R}
    (hv : ∀ i, v i ∈ N k) (hw : ∀ i, w i ∈ N l)
    (hA : ∀ i j, B (v i) (v j) = π ^ k * A i j) (hA' : ∀ i j, B (v' i) (v' j) = π ^ k * A' i j)
    (hD : ∀ i j, B (w i) (w j) = π ^ l * D i j) (hD' : ∀ i j, B (w' i) (w' j) = π ^ l * D' i j)
    (hAu : IsUnit A.det) (hA'u : IsUnit A'.det) (hDu : IsUnit D.det) (hD'u : IsUnit D'.det)
    (hvw' : ∀ i j, B (v' i) (w' j) = 0)
    (hspan : Submodule.span R (Set.range v' ∪ Set.range w') =
      Submodule.span R (Set.range v ∪ Set.range w)) :
    ∃ N' : ℕ → Submodule R M, B.IsJordanSplitting π N' ∧ (∀ i, i ≠ k → i ≠ l → N' i = N i) ∧
      (∃ (m : ℕ) (t : Fin m → M) (G : Matrix (Fin m) (Fin m) R),
        (∀ i j, B (t i) (t j) = π ^ k * G i j) ∧ IsUnit G.det ∧ (∀ i j, B (v i) (t j) = 0) ∧
        (∀ i j, B (v' i) (t j) = 0) ∧ N k = Submodule.span R (Set.range (Sum.elim v t)) ∧
        N' k = Submodule.span R (Set.range (Sum.elim v' t))) ∧
      (∃ (m : ℕ) (s : Fin m → M) (H : Matrix (Fin m) (Fin m) R),
        (∀ i j, B (s i) (s j) = π ^ l * H i j) ∧ IsUnit H.det ∧ (∀ i j, B (w i) (s j) = 0) ∧
        (∀ i j, B (w' i) (s j) = 0) ∧ N l = Submodule.span R (Set.range (Sum.elim w s)) ∧
        N' l = Submodule.span R (Set.range (Sum.elim w' s))) := by
  have hsymm {x y : M} (hxy : B x y = 0) : B y x = 0 := by rw [hB.eq, hxy]
  obtain ⟨m, t, G, ht, hG, hGu, hvt, hNk⟩ := h.exists_span_range_sup_span_range_eq hB hπ hv hA hAu
  obtain ⟨m', s, H, hs, hH, hHu, hws, hNl⟩ := h.exists_span_range_sup_span_range_eq hB hπ hw hD hDu
  have hkl' := h.apply_eq_zero k l hkl
  have hlk := h.apply_eq_zero l k hkl.symm
  -- The new families lie in the span of the old ones, which is orthogonal to `t` and to `s`.
  have hmem {x : M} (hx : x ∈ Set.range v' ∪ Set.range w') :
      x ∈ Submodule.span R (Set.range v ∪ Set.range w) :=
    hspan ▸ Submodule.subset_span hx
  have ht' {x : M} (hx : x ∈ Set.range v' ∪ Set.range w') (j : Fin m) : B x (t j) = 0 := by
    refine apply_eq_zero_of_mem_span (t := {t j}) ?_ (hmem hx) (Submodule.subset_span rfl)
    rintro y (⟨i, rfl⟩ | ⟨i, rfl⟩) z rfl
    exacts [hvt i j, hlk _ (hw i) _ (ht j)]
  have hs' {x : M} (hx : x ∈ Set.range v' ∪ Set.range w') (j : Fin m') : B x (s j) = 0 := by
    refine apply_eq_zero_of_mem_span (t := {s j}) ?_ (hmem hx) (Submodule.subset_span rfl)
    rintro y (⟨i, rfl⟩ | ⟨i, rfl⟩) z rfl
    exacts [hkl' _ (hv i) _ (hs j), hws i j]
  have hv't (i : Fin p) (j : Fin m) : B (v' i) (t j) = 0 := ht' (.inl ⟨i, rfl⟩) j
  have hw's (i : Fin q) (j : Fin m') : B (w' i) (s j) = 0 := hs' (.inr ⟨i, rfl⟩) j
  -- The new constituents: `v'` with `t`, and `w'` with `s`.
  set P := Submodule.span R (Set.range (Sum.elim v' t))
  set Q := Submodule.span R (Set.range (Sum.elim w' s))
  have hP : (B.restrict P).IsModular (π ^ k) :=
    isModular_restrict_span_range (pow_mem hπ k)
      (hB.isRefl.apply_sum_elim_eq_mul_fromBlocks hA' hG hv't)
      (by rw [Matrix.det_fromBlocks_zero₂₁]; exact hA'u.mul hGu)
  have hQ : (B.restrict Q).IsModular (π ^ l) :=
    isModular_restrict_span_range (pow_mem hπ l)
      (hB.isRefl.apply_sum_elim_eq_mul_fromBlocks hD' hH hw's)
      (by rw [Matrix.det_fromBlocks_zero₂₁]; exact hD'u.mul hHu)
  have horth : ∀ x ∈ P, ∀ y ∈ Q, B x y = 0 := by
    refine fun x hx y hy ↦ apply_eq_zero_of_mem_span ?_ hx hy
    rintro _ ⟨i | i, rfl⟩ _ ⟨j | j, rfl⟩
    · exact hvw' i j
    · exact hs' (.inl ⟨i, rfl⟩) j
    · exact hsymm (ht' (.inr ⟨j, rfl⟩) i)
    · exact hkl' _ (ht i) _ (hs j)
  have hsup : P ⊔ Q = N k ⊔ N l := by
    simp only [P, Q, Set.Sum.elim_range, Submodule.span_union]
    rw [sup_sup_sup_comm, ← Submodule.span_union, hspan, Submodule.span_union, sup_sup_sup_comm,
      hNk, hNl]
  refine ⟨_, h.update_update hB.isRefl hπ hkl hsup horth hP hQ, fun i hik hil ↦ ?_,
    ⟨m, t, G, hG, hGu, hvt, hv't, ?_, ?_⟩, ⟨m', s, H, hH, hHu, hws, hw's, ?_, ?_⟩⟩
  · simp [Function.update_of_ne hik, Function.update_of_ne hil]
  · rw [Set.Sum.elim_range, Submodule.span_union, hNk]
  · simp [Function.update_of_ne hkl, P]
  · rw [Set.Sum.elim_range, Submodule.span_union, hNl]
  · simp [Q]

end LinearMap.BilinForm
