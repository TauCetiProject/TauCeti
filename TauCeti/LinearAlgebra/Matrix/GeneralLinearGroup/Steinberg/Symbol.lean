/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.K2
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.Weyl
import TauCeti.GroupTheory.Commutator

/-!
# Steinberg symbols in algebraic `K₂`

For commuting units `u` and `v` of an associative unital ring `R`, the diagonal matrices
`diag(u, u⁻¹, 1)` and `diag(v, 1, v⁻¹)` are stably elementary (by Whitehead's lemma), so they lift
to the Steinberg group `St(R)`, explicitly by the diagonal lift words `h₀₁(u)` and `h₀₂(v)`.
The **Steinberg symbol** `{u, v}` is the commutator of any two such lifts: it does not depend on
the choice of lifts because two lifts of the same matrix differ by an element of the central
subgroup `K₂(R) = ker (St(R) →* GL_∞(R))`, and it lies in `K₂(R)` because the two diagonal
matrices commute. For a field, Matsumoto's theorem presents `K₂` by these symbols.

## Main definitions

* `TauCeti.steinbergSymbol`: the Steinberg symbol `{u, v} ∈ K₂(R)` of commuting units.

## Main results

* `TauCeti.diagGL_inv_one_mem_elementarySubgroup`,
  `TauCeti.diagGL_one_inv_mem_elementarySubgroup`: `diag(u, u⁻¹, 1)` and `diag(u, 1, u⁻¹)` are
  elementary.
* `TauCeti.coe_steinbergSymbol_eq_commutatorElement`: `{u, v}` is the commutator of any lifts of
  `diag(u, u⁻¹, 1)` and `diag(v, 1, v⁻¹)`.
* `TauCeti.coe_steinbergSymbol_eq_commutatorElement_h`: `{u, v} = ⁅h₀₁(u), h₀₂(v)⁆` for the
  diagonal lift words `TauCeti.IndexedSteinbergGroup.h`.
* `TauCeti.AlgebraicK2.map_steinbergSymbol`: Steinberg symbols are natural in ring
  homomorphisms.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §8
  (the symbols `{u, v}`).
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, Definition 5.10 (Steinberg symbols).
-/

public section

noncomputable section

open Matrix

open scoped commutatorElement

namespace TauCeti

variable {R : Type*} [Ring R]

/-! ## Steinberg symbols -/

section Symbol

/-- The invertible diagonal matrix `diag(u, u⁻¹, 1)` is elementary. It is the stabilization of
Whitehead's matrix `u ⊕ u⁻¹`. -/
theorem diagGL_inv_one_mem_elementarySubgroup (u : Rˣ) :
    diagGL ![u, u⁻¹, 1] ∈ elementarySubgroup (Fin 3) R := by
  let w : GL (Fin 1) R := GeneralLinearGroup.scalar (Fin 1) u
  have hw : finSumFinEquiv.reindexGL R (fromBlocksGL (w, w⁻¹)) ∈ elementarySubgroup (Fin 2) R :=
    (Equiv.reindexGL_mem_elementarySubgroup_iff _).2 (fromBlocksGL_inv_mem_elementarySubgroup w)
  have h : stabilizeGL R (by norm_num : 2 ≤ 3)
      (finSumFinEquiv.reindexGL R (fromBlocksGL (w, w⁻¹))) = diagGL ![u, u⁻¹, 1] := by
    have h0 : finSumFinEquiv.symm (0 : Fin (1 + 1)) = Sum.inl 0 := by decide
    have h1 : finSumFinEquiv.symm (1 : Fin (1 + 1)) = Sum.inr 0 := by decide
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_stabilizeGL_apply, w, ← map_inv, h0, h1]
  exact h ▸ map_stabilizeGL_elementarySubgroup_le _ ⟨_, hw, rfl⟩

/-- The invertible diagonal matrix `diag(u, 1, u⁻¹)` is elementary. It is obtained from
`diag(u, u⁻¹, 1)` by exchanging the last two indices. -/
theorem diagGL_one_inv_mem_elementarySubgroup (u : Rˣ) :
    diagGL ![u, 1, u⁻¹] ∈ elementarySubgroup (Fin 3) R := by
  have h : (Equiv.swap (1 : Fin 3) 2).reindexGL R (diagGL ![u, u⁻¹, 1]) = diagGL ![u, 1, u⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Equiv.swap_apply_of_ne_of_ne]
  exact h ▸ (Equiv.reindexGL_mem_elementarySubgroup_iff _).2
    (diagGL_inv_one_mem_elementarySubgroup u)

/-- For commuting units `u` and `v`, the commutator of `diag(u, u⁻¹, 1)` and `diag(v, 1, v⁻¹)`
is trivial. -/
private theorem commutatorElement_diagGL_eq_one {u v : Rˣ} (h : Commute u v) :
    ⁅diagGL ![u, u⁻¹, 1], diagGL ![v, 1, v⁻¹]⁆ = 1 := by
  rw [← map_commutatorElement, ← map_one diagGL]
  congr 1
  ext i : 1
  fin_cases i <;> simp [commutatorElement_def, h.eq]

/-- For `j' : Fin 3` different from `0` with value `j`, the diagonal lift word `h₀ⱼ(u)` lifts the
stable diagonal matrix with entries `u` at `0`, `u⁻¹` at `j'` and `1` at the remaining index. -/
private theorem toStableGL_h_zero {j : ℕ} (hj : 0 ≠ j) {j' : Fin 3} (hjj' : (j' : ℕ) = j) (u : Rˣ)
    {d : Fin 3 → Rˣ} (hd : ∀ m, (Pi.mulSingle 0 u * Pi.mulSingle j' u⁻¹ : Fin 3 → Rˣ) m = d m) :
    SteinbergGroup.toStableGL R (IndexedSteinbergGroup.h hj u) =
      StableGeneralLinearGroup.of R 3 (diagGL d) := by
  subst hjj'
  rw [SteinbergGroup.toStableGL_h hj u (Nat.zero_lt_succ 2) j'.isLt, ← funext hd]
  rfl

/-- The diagonal lift word `h₀₁(u)` lifts the stable matrix `diag(u, u⁻¹, 1)`. -/
private theorem toStableGL_h_zero_one (u : Rˣ) :
    SteinbergGroup.toStableGL R (IndexedSteinbergGroup.h (by decide : (0 : ℕ) ≠ 1) u) =
      StableGeneralLinearGroup.of R 3 (diagGL ![u, u⁻¹, 1]) :=
  toStableGL_h_zero _ (j' := 1) (Fin.val_one 1) u fun m ↦ by
    fin_cases m <;> simp

/-- The diagonal lift word `h₀₂(v)` lifts the stable matrix `diag(v, 1, v⁻¹)`. -/
private theorem toStableGL_h_zero_two (v : Rˣ) :
    SteinbergGroup.toStableGL R (IndexedSteinbergGroup.h (by decide : (0 : ℕ) ≠ 2) v) =
      StableGeneralLinearGroup.of R 3 (diagGL ![v, 1, v⁻¹]) :=
  toStableGL_h_zero _ (j' := 2) (by simp) v fun m ↦ by
    fin_cases m <;> simp

/-- The **Steinberg symbol** `{u, v} ∈ K₂(R)` of commuting units `u` and `v` of `R`: the
commutator `⁅h₀₁(u), h₀₂(v)⁆` in the Steinberg group `St(R)` of the diagonal lift words
`TauCeti.IndexedSteinbergGroup.h`, which lift the stable matrices `diag(u, u⁻¹, 1)` and
`diag(v, 1, v⁻¹)`. It is the commutator of any lifts of these two matrices
(`TauCeti.coe_steinbergSymbol_eq_commutatorElement`). -/
def steinbergSymbol (u v : Rˣ) (h : Commute u v) : AlgebraicK2 R :=
  ⟨⁅IndexedSteinbergGroup.h (by decide : (0 : ℕ) ≠ 1) u,
    IndexedSteinbergGroup.h (by decide : (0 : ℕ) ≠ 2) v⁆, by
    rw [MonoidHom.mem_ker, map_commutatorElement, toStableGL_h_zero_one, toStableGL_h_zero_two,
      ← map_commutatorElement, commutatorElement_diagGL_eq_one h, map_one]⟩

/-- **The Steinberg symbol is a commutator of diagonal lift words**: `{u, v}` is the commutator
`⁅h₀₁(u), h₀₂(v)⁆` in `St(R)` of the diagonal lift words `TauCeti.IndexedSteinbergGroup.h` at the
index pairs `(0, 1)` and `(0, 2)`, which overlap in exactly one index. -/
theorem coe_steinbergSymbol_eq_commutatorElement_h {u v : Rˣ} (h : Commute u v) :
    (steinbergSymbol u v h : SteinbergGroup R) =
      ⁅IndexedSteinbergGroup.h (by decide : (0 : ℕ) ≠ 1) u,
        IndexedSteinbergGroup.h (by decide : (0 : ℕ) ≠ 2) v⁆ :=
  (rfl)

/-- **The Steinberg symbol is independent of the lifts**: for any lifts `a` and `b` to `St(R)` of
`diag(u, u⁻¹, 1)` and `diag(v, 1, v⁻¹)`, the symbol `{u, v}` is the commutator `⁅a, b⁆`. -/
theorem coe_steinbergSymbol_eq_commutatorElement {u v : Rˣ} (h : Commute u v)
    {a b : SteinbergGroup R}
    (ha : SteinbergGroup.toStableGL R a = StableGeneralLinearGroup.of R 3 (diagGL ![u, u⁻¹, 1]))
    (hb : SteinbergGroup.toStableGL R b = StableGeneralLinearGroup.of R 3 (diagGL ![v, 1, v⁻¹])) :
    (steinbergSymbol u v h : SteinbergGroup R) = ⁅a, b⁆ :=
  MonoidHom.commutatorElement_eq_of_ker_le_center SteinbergGroup.ker_toStableGL_le_center
    ((toStableGL_h_zero_one u).trans ha.symm) ((toStableGL_h_zero_two v).trans hb.symm)

/-- The Steinberg symbol `{1, v}` is trivial. -/
@[simp]
theorem steinbergSymbol_one_left (v : Rˣ) : steinbergSymbol 1 v (Commute.one_left v) = 1 :=
  Subtype.ext <| by simp [coe_steinbergSymbol_eq_commutatorElement_h, commutatorElement_def]

/-- The Steinberg symbol `{u, 1}` is trivial. -/
@[simp]
theorem steinbergSymbol_one_right (u : Rˣ) : steinbergSymbol u 1 (Commute.one_right u) = 1 :=
  Subtype.ext <| by simp [coe_steinbergSymbol_eq_commutatorElement_h, commutatorElement_def]

/-- **Steinberg symbols are natural**: the homomorphism of `K₂` induced by a ring homomorphism
`f` sends `{u, v}` to `{f u, f v}`. -/
@[simp]
theorem AlgebraicK2.map_steinbergSymbol {S : Type*} [Ring S] (f : R →+* S) {u v : Rˣ}
    (h : Commute u v) :
    AlgebraicK2.map f (steinbergSymbol u v h) =
      steinbergSymbol (Units.map (f : R →* S) u) (Units.map (f : R →* S) v) (h.map _) := by
  refine Subtype.ext ?_
  rw [AlgebraicK2.coe_map_apply, coe_steinbergSymbol_eq_commutatorElement_h,
    coe_steinbergSymbol_eq_commutatorElement_h, map_commutatorElement, IndexedSteinbergGroup.map_h,
    IndexedSteinbergGroup.map_h]

end Symbol

end TauCeti
