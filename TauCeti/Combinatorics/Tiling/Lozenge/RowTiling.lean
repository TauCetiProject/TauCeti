/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Tiling
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Order

/-!
# Row tilings

For `ε : ℤ → Bool` the row tiling `M_ε` fills the column `x` of the plane with the type-1
lozenges `W(x, y) ∪ B(x, y - 1)` when `ε x` holds and with the unit squares `W(x, y) ∪ B(x, y)`
otherwise, so that `ε` is read along any row. These plane tilings contain no lozenge of type 2;
their laws realise the slopes on the edge `t = 0` of the slope triangle.

## Main definitions

* `TauCeti.rowTiling`: the row tiling `M_ε`, as a configuration `TriEdge → Bool`.

## Main statements

* `TauCeti.isTiling_rowTiling`: `M_ε` is a plane tiling.
* `TauCeti.rowTiling_eq_false_of_k_eq_one`: `M_ε` contains no edge of direction 2.
* `TauCeti.rowTiling_mk_zero`, `TauCeti.rowTiling_injective`: `ε x` is recovered as the membership
  of the edge `((x, 0), 1)`, so `ε ↦ M_ε` is injective.
* `TauCeti.continuous_rowTiling`: `ε ↦ M_ε` is continuous for the product topologies.
* `TauCeti.rowTiling_vadd`: translating `M_ε` by `w` shifts `ε` by the first coordinate of `w`; in
  particular `M_ε` is invariant under `e₂`, and `e₁` shifts `ε` to `x ↦ ε (x - 1)`.

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Lecture 13.
* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009), Exercise 13.
-/

public section

namespace TauCeti

/-- The row tiling `M_ε = {((x, y), 1) : ε x} ∪ {((x, y), 3) : ¬ε x}`, as a configuration: the
column `x` is filled with type-1 lozenges when `ε x` and with unit squares otherwise. -/
def rowTiling (ε : ℤ → Bool) (e : TriEdge) : Bool :=
  if e.k = 0 then ε e.v.1 else if e.k = 2 then !ε e.v.1 else false

theorem rowTiling_def (ε : ℤ → Bool) (e : TriEdge) :
    rowTiling ε e = if e.k = 0 then ε e.v.1 else if e.k = 2 then !ε e.v.1 else false := (rfl)

variable {ε : ℤ → Bool}

/-- The edge `(v, 1)` lies in `M_ε` exactly when `ε` holds at the first coordinate of `v`. -/
@[simp] theorem rowTiling_mk_zero (ε : ℤ → Bool) (v : ℤ × ℤ) :
    rowTiling ε ⟨v, 0⟩ = ε v.1 := (rfl)

@[simp] theorem rowTiling_mk_one (ε : ℤ → Bool) (v : ℤ × ℤ) : rowTiling ε ⟨v, 1⟩ = false := (rfl)

/-- The edge `(v, 3)` lies in `M_ε` exactly when `ε` fails at the first coordinate of `v`. -/
@[simp] theorem rowTiling_mk_two (ε : ℤ → Bool) (v : ℤ × ℤ) :
    rowTiling ε ⟨v, 2⟩ = !ε v.1 := (rfl)

/-- `M_ε` contains no edge of direction 2, hence no lozenge of type 2. -/
theorem rowTiling_eq_false_of_k_eq_one {e : TriEdge} (he : e.k = 1) : rowTiling ε e = false := by
  obtain ⟨v, k⟩ := e
  obtain rfl : k = 1 := he
  rfl

/-- **Row tilings are plane tilings.** `W(x, y)` contains `((x, y), 1)` or `((x, y), 3)` and
`B(x, y)` contains `((x, y + 1), 1)` or `((x, y), 3)`, according as `ε x` holds or not. -/
theorem isTiling_rowTiling (ε : ℤ → Bool) : IsTiling Set.univ {e | rowTiling ε e = true} := by
  rw [isTiling_univ_iff]
  rintro ⟨⟨x, y⟩, c⟩
  cases c <;> cases hε : ε x
  · refine ⟨⟨(x, y), 2⟩, ⟨by simp [hε], by simp⟩, ?_⟩
    rintro ⟨⟨a, b⟩, k⟩ ⟨h₁, h₂⟩
    fin_cases k <;> simp [TriEdge.ext_iff] at h₁ h₂ ⊢ <;> simp_all
  · refine ⟨⟨(x, y + 1), 0⟩, ⟨by simp [hε], by simp⟩, ?_⟩
    rintro ⟨⟨a, b⟩, k⟩ ⟨h₁, h₂⟩
    fin_cases k <;> simp [TriEdge.ext_iff] at h₁ h₂ ⊢ <;> simp_all
  · refine ⟨⟨(x, y), 2⟩, ⟨by simp [hε], by simp⟩, ?_⟩
    rintro ⟨⟨a, b⟩, k⟩ ⟨h₁, h₂⟩
    fin_cases k <;> simp [TriEdge.ext_iff] at h₁ h₂ ⊢ <;> simp_all
  · refine ⟨⟨(x, y), 0⟩, ⟨by simp [hε], by simp⟩, ?_⟩
    rintro ⟨⟨a, b⟩, k⟩ ⟨h₁, h₂⟩
    fin_cases k <;> simp [TriEdge.ext_iff] at h₁ h₂ ⊢ <;> simp_all

/-- `ε ↦ M_ε` is injective: `ε x` is the membership of `((x, 0), 1)` in `M_ε`. -/
theorem rowTiling_injective : Function.Injective rowTiling := fun ε ε' h => funext fun x => by
  simpa using congrFun h ⟨(x, 0), 0⟩

/-- `ε ↦ M_ε` is continuous for the product topologies on `ℤ → Bool` and `TriEdge → Bool`: the
membership of each edge depends on one coordinate of `ε`. -/
theorem continuous_rowTiling : Continuous rowTiling :=
  continuous_pi fun e =>
    (continuous_of_discreteTopology (f := fun b : Bool =>
      if e.k = 0 then b else if e.k = 2 then !b else false)).comp (continuous_apply e.v.1)

/-- Translating `M_ε` by `w` shifts `ε` by the first coordinate of `w`. -/
theorem rowTiling_vadd (w : ℤ × ℤ) (ε : ℤ → Bool) :
    w +ᵥ rowTiling ε = rowTiling fun x => ε (x - w.1) := by
  ext e
  simp only [vadd_config_apply, rowTiling_def, TriEdge.vadd_k, TriEdge.vadd_v, neg_add_eq_sub,
    Prod.fst_sub]

/-- `M_ε` is invariant under the translation by `e₂`. -/
@[simp] theorem rowTiling_vadd_zero_mk (b : ℤ) (ε : ℤ → Bool) :
    ((0, b) : ℤ × ℤ) +ᵥ rowTiling ε = rowTiling ε := by
  simp [rowTiling_vadd]

/-- The translation by `e₁` shifts `ε` to `x ↦ ε (x - 1)`. -/
theorem rowTiling_vadd_one_zero (ε : ℤ → Bool) :
    ((1, 0) : ℤ × ℤ) +ᵥ rowTiling ε = rowTiling fun x => ε (x - 1) :=
  rowTiling_vadd _ ε

/-- The constant sequence `ε ≡ 1` gives the all-type-1 tiling `M₁`. -/
theorem rowTiling_true (e : TriEdge) : rowTiling (fun _ => true) e = decide (e.k = 0) := by
  obtain ⟨v, k⟩ := e
  fin_cases k <;> rfl

/-- The constant sequence `ε ≡ 0` gives the all-type-3 tiling `M₃`. -/
theorem rowTiling_false (e : TriEdge) : rowTiling (fun _ => false) e = decide (e.k = 2) := by
  obtain ⟨v, k⟩ := e
  fin_cases k <;> rfl

end TauCeti
