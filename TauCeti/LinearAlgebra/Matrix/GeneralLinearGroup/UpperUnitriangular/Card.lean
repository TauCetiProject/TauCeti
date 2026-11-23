/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Data.Finset.Prod

/-!
# The order of the upper-unitriangular group

An upper-unitriangular matrix is determined by its entries strictly above the diagonal: over a
ring `R`, `TauCeti.upperUnitriangularGroupEquiv` identifies the upper-unitriangular group
`Uₙ₊₁(R)` with the functions on the pairs `i < j` of `Fin (n + 1)`. Hence
`|Uₙ₊₁(R)| = |R| ^ (n (n + 1) / 2)` for every ring `R`
(`TauCeti.natCard_upperUnitriangularGroup`) and, over a finite field `𝔽` with `q` elements, the
index of `Uₙ₊₁(𝔽)` in `GLₙ₊₁(𝔽)` is `∏_{i = 1}^{n + 1} (q ^ i - 1)`
(`TauCeti.index_upperUnitriangularGroup`). The latter is the order of the group of `p'`-elements
of `GLₙ₊₁(𝔽)` for `p` the characteristic, and the degree of the Gelfand–Graev representations
of `GLₙ₊₁(𝔽)`.

## Main declarations

* `TauCeti.upperUnitriangularEntries`: the entries strictly above the diagonal.
* `TauCeti.upperUnitriangularOfEntries`: the upper-unitriangular matrix with given entries above
  the diagonal.
* `TauCeti.upperUnitriangularGroupEquiv`: `Uₙ₊₁(R)` is in bijection with the functions on the
  pairs `i < j`.
* `TauCeti.natCard_upperUnitriangularGroup`: `|Uₙ₊₁(R)| = |R| ^ (n (n + 1) / 2)`.
* `TauCeti.index_upperUnitriangularGroup`: `[GLₙ₊₁(𝔽) : Uₙ₊₁(𝔽)] = ∏_{i = 1}^{n + 1} (q ^ i - 1)`.
* `TauCeti.natCard_GL_fin_succ`: the order of `GLₙ₊₁(𝔽)`.

## References

* F. Digne, J. Michel, *Representations of Finite Groups of Lie Type*, Cambridge University Press,
  1991.
-/

public section

namespace TauCeti

open Matrix

variable {m : ℕ} {R : Type*} [Ring R]

/-- The entries strictly above the diagonal of an upper-unitriangular matrix of size `m + 1`. -/
public noncomputable def upperUnitriangularEntries (g : upperUnitriangularGroup (Fin (m + 1)) R) :
    {p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2} → R :=
  fun p => ((g : GL (Fin (m + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R) p.val.fst p.val.snd

@[simp]
theorem upperUnitriangularEntries_apply (g : upperUnitriangularGroup (Fin (m + 1)) R)
    (p : {p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2}) :
    upperUnitriangularEntries g p =
      ((g : GL (Fin (m + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R) p.val.fst p.val.snd := by
  simp only [upperUnitriangularEntries]

/-- The upper-unitriangular matrix of size `m + 1` with prescribed entries strictly above the
diagonal. -/
public noncomputable def upperUnitriangularMatrixOfEntries
    (f : {p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2} → R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun i j => if h : i < j then f ⟨(i, j), h⟩ else if i = j then 1 else 0

@[simp]
theorem upperUnitriangularMatrixOfEntries_apply_of_lt
    (f : {p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2} → R) {i j : Fin (m + 1)} (h : i < j) :
    upperUnitriangularMatrixOfEntries f i j = f ⟨(i, j), h⟩ :=
  dite_eq_left h

@[simp]
theorem upperUnitriangularMatrixOfEntries_apply_self
    (f : {p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2} → R) (i : Fin (m + 1)) :
    upperUnitriangularMatrixOfEntries f i i = 1 := by
  simp [upperUnitriangularMatrixOfEntries]

@[simp]
theorem upperUnitriangularMatrixOfEntries_apply_of_gt
    (f : {p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2} → R) {i j : Fin (m + 1)} (h : j < i) :
    upperUnitriangularMatrixOfEntries f i j = 0 := by
  have h' : ¬ i < j := fun h' => lt_irrefl i (h'.trans h)
  simp [upperUnitriangularMatrixOfEntries, h', (ne_of_lt h).symm]

theorem isUpperUnitriangular_upperUnitriangularMatrixOfEntries
    (f : {p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2} → R) :
    (upperUnitriangularMatrixOfEntries f).IsUpperUnitriangular := by
  rw [Matrix.isUpperUnitriangular_def]
  exact ⟨fun a b hab => upperUnitriangularMatrixOfEntries_apply_of_gt f hab,
    upperUnitriangularMatrixOfEntries_apply_self f⟩

/-- The element of `Uₙ₊₁(R)` with prescribed entries strictly above the diagonal. -/
public noncomputable def upperUnitriangularOfEntries
    (f : {p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2} → R) :
    upperUnitriangularGroup (Fin (m + 1)) R :=
  ⟨(isUpperUnitriangular_upperUnitriangularMatrixOfEntries f).toGL,
    UpperUnitriangularGroup.toGL_mem_upperUnitriangularGroup _⟩

@[simp]
theorem coe_upperUnitriangularOfEntries_apply
    (f : {p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2} → R) (i j : Fin (m + 1)) :
    ((upperUnitriangularOfEntries f : GL (Fin (m + 1)) R) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) R) i j = upperUnitriangularMatrixOfEntries f i j := by
  rw [upperUnitriangularOfEntries, Subgroup.coe_mk,
    (isUpperUnitriangular_upperUnitriangularMatrixOfEntries f).coe_toGL]

/-- The entries above the diagonal of `upperUnitriangularOfEntries f` are `f`. -/
theorem upperUnitriangularEntries_upperUnitriangularOfEntries
    (f : {p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2} → R)
    (p : {p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2}) :
    upperUnitriangularEntries (upperUnitriangularOfEntries f) p = f p := by
  rw [upperUnitriangularEntries_apply, coe_upperUnitriangularOfEntries_apply,
    upperUnitriangularMatrixOfEntries_apply_of_lt f p.property]

/-- An upper-unitriangular matrix is recovered from its entries above the diagonal. -/
theorem upperUnitriangularOfEntries_upperUnitriangularEntries
    (g : upperUnitriangularGroup (Fin (m + 1)) R) :
    upperUnitriangularOfEntries (upperUnitriangularEntries g) = g := by
  apply UpperUnitriangularGroup.ext
  intro i j hij
  rw [coe_upperUnitriangularOfEntries_apply, upperUnitriangularMatrixOfEntries_apply_of_lt _ hij,
    upperUnitriangularEntries_apply]

/-- Upper-unitriangular matrices of size `m + 1` are in bijection with their entries strictly
above the diagonal. -/
public noncomputable def upperUnitriangularGroupEquiv (m : ℕ) (R : Type*) [Ring R] :
    upperUnitriangularGroup (Fin (m + 1)) R ≃ ({p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2} → R)
    where
  toFun := upperUnitriangularEntries
  invFun := upperUnitriangularOfEntries
  left_inv := upperUnitriangularOfEntries_upperUnitriangularEntries
  right_inv := fun f => funext (upperUnitriangularEntries_upperUnitriangularOfEntries f)

/-- The number of pairs `i < j` of `Fin (m + 1)`. -/
theorem natCard_pairs_lt_fin (m : ℕ) :
    Nat.card {p : Fin (m + 1) × Fin (m + 1) // p.1 < p.2} = m * (m + 1) / 2 := by
  classical
  have h : (Finset.univ : Finset (Fin (m + 1) × Fin (m + 1))) = Finset.univ ×ˢ Finset.univ :=
    Finset.univ_product_univ.symm
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, h, Finset.card_product_filter_lt,
    Finset.card_univ, Fintype.card_fin, Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm]

/-- The order of the upper-unitriangular group over a ring `R`: an upper-unitriangular matrix of
size `m + 1` is determined by its `m (m + 1) / 2` entries strictly above the diagonal. Over an
infinite ring `R` both sides are `0`. -/
theorem natCard_upperUnitriangularGroup :
    Nat.card (upperUnitriangularGroup (Fin (m + 1)) R) = Nat.card R ^ (m * (m + 1) / 2) := by
  rw [Nat.card_congr (upperUnitriangularGroupEquiv m R)]
  rcases finite_or_infinite R with h | h
  · have : Fintype R := Fintype.ofFinite R
    rw [Nat.card_fun, natCard_pairs_lt_fin]
  · have : Infinite R := h
    rw [Nat.card_eq_zero_of_infinite (α := R)]
    rcases m with _ | m
    · rw [Nat.card_eq_one_iff_unique.mpr
        ⟨⟨fun f g => funext fun p => by
          have := p.val.fst.isLt
          have := p.val.snd.isLt
          omega⟩, ⟨fun p => by
          have := p.val.fst.isLt
          have := p.val.snd.isLt
          exact absurd p.property (by omega)⟩⟩, pow_zero]
    · have : Infinite ({p : Fin (m + 1 + 1) × Fin (m + 1 + 1) // p.1 < p.2} → R) :=
        Infinite.of_injective (f := fun c : R => fun _ => c)
          (fun a b hab => congrFun hab ⟨(⟨0, Nat.succ_pos _⟩, ⟨1, by omega⟩), by simp⟩)
      have h1 : (1 : ℕ) ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
      have hk : (m + 1) * (m + 1 + 1) / 2 ≠ 0 :=
        Nat.ne_of_gt (Nat.div_pos (Nat.mul_le_mul h1 (Nat.succ_le_succ h1)) Nat.zero_lt_two)
      rw [Nat.card_eq_zero_of_infinite
          (α := {p : Fin (m + 1 + 1) × Fin (m + 1 + 1) // p.1 < p.2} → R), zero_pow hk]

section Field

variable {m : ℕ} {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]

/-- The index of the upper-unitriangular group in `GLₙ₊₁(𝔽)` over a finite field `𝔽` with `q`
elements is `∏_{i = 1}^{n + 1} (q ^ i - 1)`. -/
theorem index_upperUnitriangularGroup :
    (upperUnitriangularGroup (Fin (m + 1)) 𝔽).index =
      ∏ i ∈ Finset.range (m + 1), (Fintype.card 𝔽 ^ (i + 1) - 1) := by
  have h := Subgroup.card_mul_index (upperUnitriangularGroup (Fin (m + 1)) 𝔽)
  rw [natCard_upperUnitriangularGroup, Matrix.card_GL_field,
    Fin.prod_univ_eq_prod_range
      (fun i => (Fintype.card 𝔽 ^ (m + 1) - Fintype.card 𝔽 ^ (i : ℕ) : ℕ)) (m + 1),
    Nat.card_eq_fintype_card] at h
  have hq : 0 < Fintype.card 𝔽 := Fintype.card_pos_iff.mpr ⟨0⟩
  refine mul_left_cancel₀ (a := Fintype.card 𝔽 ^ (m * (m + 1) / 2)) (pow_ne_zero _ hq.ne') ?_
  rw [h]
  have hfactor : ∀ i ∈ Finset.range (m + 1),
      (Fintype.card 𝔽 ^ (m + 1) - Fintype.card 𝔽 ^ i : ℕ) =
        Fintype.card 𝔽 ^ i * (Fintype.card 𝔽 ^ (m + 1 - i) - 1) := by
    intro i hi
    have hi' : i ≤ m := by simpa using hi
    have hpow : Fintype.card 𝔽 ^ (m + 1) = Fintype.card 𝔽 ^ i * Fintype.card 𝔽 ^ (m + 1 - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow, Nat.mul_sub, Nat.mul_one]
  rw [Finset.prod_congr rfl hfactor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_range_id (m + 1), Nat.add_sub_cancel]
  congr 1
  · rw [Nat.mul_comm (m + 1) m]
  · refine Finset.prod_bij (fun a _ => m - a) ?_ ?_ ?_ ?_
    · intro a ha
      have := Finset.mem_range.mp ha
      exact Finset.mem_range.mpr (by omega)
    · intro a₁ ha₁ a₂ ha₂ h
      have h1 := Finset.mem_range.mp ha₁
      have h2 := Finset.mem_range.mp ha₂
      omega
    · intro b hb
      have := Finset.mem_range.mp hb
      exact ⟨m - b, Finset.mem_range.mpr (by omega), by omega⟩
    · intro a ha
      have := Finset.mem_range.mp ha
      congr 2
      omega

/-- The order of `GLₙ₊₁(𝔽)` over a finite field `𝔽` with `q` elements:
`|GLₙ₊₁(𝔽)| = q ^ (n (n + 1) / 2) ∏_{i = 1}^{n + 1} (q ^ i - 1)`. -/
theorem natCard_GL_fin_succ :
    Nat.card (GL (Fin (m + 1)) 𝔽) = Fintype.card 𝔽 ^ (m * (m + 1) / 2) *
      ∏ i ∈ Finset.range (m + 1), (Fintype.card 𝔽 ^ (i + 1) - 1) := by
  rw [← Subgroup.card_mul_index (upperUnitriangularGroup (Fin (m + 1)) 𝔽),
    index_upperUnitriangularGroup, natCard_upperUnitriangularGroup, Nat.card_eq_fintype_card]

end Field

end TauCeti

end
