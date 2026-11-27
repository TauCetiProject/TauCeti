/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Flag
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.RingTheory.Derivation.CyclicVector
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Oper flags of differential modules

Let `(V, D)` be a differential module of dimension `n` over a differential field `F`: `D` is an
additive endomorphism of `V` satisfying the Leibniz rule `D (f • v) = f′ • v + f • D v`
(`TauCeti.IsDifferentialModuleMap`). A `GL_n`-oper structure on `(V, D)` is a full flag
`0 = W₀ ⊂ W₁ ⊂ ⋯ ⊂ Wₙ = V`, `dim Wᵢ = i`, which is transversal to `D`: `D` maps `Wᵢ` into
`Wᵢ₊₁`, and for `0 < i < n` the map `Wᵢ / Wᵢ₋₁ → Wᵢ₊₁ / Wᵢ` it induces is an isomorphism. This
induced map is `F`-linear because `D (f • w) - f • D w = f′ • w` lies in `Wᵢ`, and both quotients
are lines, so the isomorphism condition says that `D` does not preserve `Wᵢ`.

This file proves that oper flags are the same thing as cyclic vectors up to scaling. For a
vector `v`, `TauCeti.iterateSpan F D v i` is the span of `v, D v, …, Dⁱ⁻¹ v`. If `v` is a cyclic
vector, then `i ↦ iterateSpan F D v i` is an oper flag, and every oper flag arises in this way
from any generator of its line `W₁`. Two vectors give the same flag exactly when they differ by
a nonzero scalar, because the Leibniz rule makes the spans of the first `i` iterates of `v` and of
`f • v` equal. Combined with the cyclic-vector theorem `TauCeti.exists_cyclicVector`, every
differential module over a field of characteristic zero with nonzero derivation has an oper
flag. For a connection on the punctured formal disc this is the `GL_n` case of the theorem that
every connection admits an oper structure; the Borel subgroup of the reduction is the
stabilizer of the flag.

Flags are indexed by `ℕ` rather than by `Fin (n + 1)`: the conditions `dim Wᵢ = min i n` force
`Wᵢ = V` for `i ≥ n`, so the family carries no data beyond the flag.

## Main definitions

* `TauCeti.iterateSpan R D v i`: the span of the first `i` iterates of `v` under `D`.
* `TauCeti.IsOperFlag D W`: the family `W` is a full flag transversal to `D`.

## Main results

* `TauCeti.IsDifferentialModuleMap.map_mem_iterateSpan_succ`: `D` maps the span of the first `i`
  iterates of `v` into the span of the first `i + 1`.
* `TauCeti.IsDifferentialModuleMap.iterateSpan_units_smul`: rescaling `v` by a unit does not
  change the spans of its iterates.
* `TauCeti.IsOperFlag.eq_iterateSpan`, `TauCeti.IsOperFlag.linearIndependent_iterate`: an oper
  flag is the flag of iterates of any generator of its first step, which is a cyclic vector.
* `TauCeti.IsDifferentialModuleMap.isOperFlag_iterateSpan`: the flag of iterates of a cyclic
  vector is an oper flag.
* `TauCeti.IsDifferentialModuleMap.isOperFlag_iff`: oper flags are exactly the flags of iterates
  of cyclic vectors.
* `TauCeti.IsDifferentialModuleMap.iterateSpan_eq_iterateSpan_iff`: over a domain, two vectors
  have the same spans of iterates if and only if they differ by a unit.
* `TauCeti.iterateSpan_eq_flag`: for a cyclic vector, the spans of iterates are the steps of
  Mathlib's `Module.Basis.flag` of the basis of iterates.
* `TauCeti.exists_isOperFlag`: in characteristic zero with a nonzero derivation, every
  differential module has an oper flag.

## References

* A. Beilinson, V. Drinfeld, *Opers*, arXiv:math/0501398.
* E. Frenkel, *Langlands correspondence for loop groups*, Cambridge Stud. Adv. Math. 103,
  Cambridge University Press, 2007, §4.2.
* E. Frenkel, X. Zhu, *Any flat bundle on a punctured disc has an oper structure*, Math. Res.
  Lett. 17 (2010), Remark 1.
-/

public section

open Module
open scoped Differential

namespace TauCeti

section Semiring

variable (R : Type*) {V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]

/-- The span `⟨v, D v, …, Dⁱ⁻¹ v⟩` of the first `i` iterates of `v` under an additive map
`D : V → V`. For a cyclic vector `v` of a differential module these spans form its oper flag. -/
def iterateSpan (D : V →+ V) (v : V) (i : ℕ) : Submodule R V :=
  Submodule.span R (Set.range fun j : Fin i ↦ (⇑D)^[j] v)

variable {R} {D : V →+ V} {v : V}

theorem iterateSpan_def (D : V →+ V) (v : V) (i : ℕ) :
    iterateSpan R D v i = Submodule.span R (Set.range fun j : Fin i ↦ (⇑D)^[j] v) :=
  (rfl)

theorem iterate_mem_iterateSpan {i j : ℕ} (hj : j < i) : (⇑D)^[j] v ∈ iterateSpan R D v i :=
  Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩

theorem iterateSpan_le_iff {i : ℕ} {W : Submodule R V} :
    iterateSpan R D v i ≤ W ↔ ∀ j < i, (⇑D)^[j] v ∈ W := by
  simp [iterateSpan_def, Submodule.span_le, Set.range_subset_iff, Fin.forall_iff]

/-- The vectors in `iterateSpan R D v i` are the combinations of `v, D v, …, Dⁱ⁻¹ v`. -/
theorem mem_iterateSpan_iff {i : ℕ} {w : V} :
    w ∈ iterateSpan R D v i ↔ ∃ c : Fin i → R, ∑ j, c j • (⇑D)^[j] v = w :=
  Submodule.mem_span_range_iff_exists_fun R

theorem iterateSpan_mono : Monotone (iterateSpan R D v) := fun _ _ hij ↦
  iterateSpan_le_iff.2 fun _ hj ↦ iterate_mem_iterateSpan (hj.trans_le hij)

theorem iterateSpan_succ (i : ℕ) :
    iterateSpan R D v (i + 1) = iterateSpan R D v i ⊔ R ∙ (⇑D)^[i] v := by
  refine le_antisymm (iterateSpan_le_iff.2 fun j hj ↦ ?_) (sup_le (iterateSpan_mono i.le_succ)
    ((Submodule.span_singleton_le_iff_mem _ _).2 (iterate_mem_iterateSpan i.lt_succ_self)))
  obtain hj | rfl := Nat.lt_succ_iff_lt_or_eq.1 hj
  · exact Submodule.mem_sup_left (iterate_mem_iterateSpan hj)
  · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

@[simp]
theorem iterateSpan_zero : iterateSpan R D v 0 = ⊥ := by
  simp [iterateSpan_def]

@[simp]
theorem iterateSpan_one : iterateSpan R D v 1 = R ∙ v := by
  simp [iterateSpan_def, Set.range_unique]

/-- When the first `n` iterates of `v` form a basis `b`, the spans of the iterates are the steps
`Basis.flag b k` of the flag of `b`. -/
theorem iterateSpan_eq_flag {n : ℕ} (b : Basis (Fin n) R V) (hb : ∀ i, b i = (⇑D)^[i] v)
    (k : Fin (n + 1)) : iterateSpan R D v k = b.flag k := by
  refine le_antisymm (iterateSpan_le_iff.2 fun j hj ↦ ?_) (b.flag_le_iff.2 fun i hi ↦ ?_)
  · rw [← Fin.val_mk (show j < n by omega), ← hb]
    exact Submodule.subset_span ⟨_, by simpa [Fin.lt_def] using hj, rfl⟩
  · rw [hb]
    exact iterate_mem_iterateSpan (by simpa [Fin.lt_def] using hi)

end Semiring

section CommRing

variable {R V : Type*} [CommRing R] [Differential R] [AddCommGroup V] [Module R V] {D : V →+ V}
  {v : V}

namespace IsDifferentialModuleMap

variable (hD : IsDifferentialModuleMap R D)
include hD

/-- `D` maps the span of the first `i` iterates of `v` into the span of the first `i + 1`: by the
Leibniz rule, `D (f • Dʲ v) = f′ • Dʲ v + f • Dʲ⁺¹ v`. -/
theorem map_mem_iterateSpan_succ {i : ℕ} {w : V} (hw : w ∈ iterateSpan R D v i) :
    D w ∈ iterateSpan R D v (i + 1) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨j, rfl⟩ := hw
    rw [← Function.iterate_succ_apply' (⇑D)]
    exact iterate_mem_iterateSpan (by omega)
  | zero => simp
  | add w₁ w₂ _ _ h₁ h₂ => simpa using add_mem h₁ h₂
  | smul c w hw h =>
    rw [hD.leibniz]
    exact add_mem (Submodule.smul_mem _ _ (iterateSpan_mono (Nat.le_succ i) hw))
      (Submodule.smul_mem _ _ h)

/-- The `j`-th iterate of `c • v` is a combination of `v, D v, …, Dʲ v`. -/
theorem iterate_smul_mem_iterateSpan (c : R) (j : ℕ) :
    (⇑D)^[j] (c • v) ∈ iterateSpan R D v (j + 1) := by
  induction j with
  | zero => simpa using Submodule.mem_span_singleton.2 ⟨c, rfl⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact hD.map_mem_iterateSpan_succ ih

theorem iterateSpan_smul_le (c : R) (i : ℕ) : iterateSpan R D (c • v) i ≤ iterateSpan R D v i :=
  iterateSpan_le_iff.2 fun j hj ↦ iterateSpan_mono hj (hD.iterate_smul_mem_iterateSpan c j)

/-- Rescaling `v` by a unit does not change the spans of its iterates. -/
theorem iterateSpan_units_smul (c : Rˣ) (i : ℕ) :
    iterateSpan R D (c • v) i = iterateSpan R D v i := by
  refine le_antisymm (hD.iterateSpan_smul_le (c : R) i) ?_
  have := hD.iterateSpan_smul_le (v := c • v) (c⁻¹ : Rˣ) i
  rwa [← Units.smul_def, inv_smul_smul] at this

/-- Over a domain, two vectors of a torsion-free differential module have the same spans of
iterates if and only if they differ by a unit. With
`TauCeti.IsDifferentialModuleMap.isOperFlag_iff`, oper flags therefore correspond bijectively
to cyclic vectors up to scaling. -/
theorem iterateSpan_eq_iterateSpan_iff [IsDomain R] [Module.IsTorsionFree R V] {w : V} :
    iterateSpan R D v = iterateSpan R D w ↔ ∃ c : Rˣ, c • v = w := by
  refine ⟨fun h ↦ Submodule.span_singleton_eq_span_singleton.1 ?_, ?_⟩
  · simpa using congrFun h 1
  · rintro ⟨c, rfl⟩
    exact funext fun i ↦ (hD.iterateSpan_units_smul c i).symm

end IsDifferentialModuleMap

end CommRing

section Field

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {D : V →+ V}

/-- A family `W : ℕ → Submodule F V` is an **oper flag** of `(V, D)`, for `n = finrank F V`, when
it is a full flag `0 = W₀ ⊂ W₁ ⊂ ⋯ ⊂ Wₙ = V` with `dim Wᵢ = i` (and `Wᵢ = V` for `i ≥ n`) that is
transversal to `D`: `D` maps `Wᵢ` into `Wᵢ₊₁`, and for `0 < i < n` it does not map `Wᵢ` into
itself. For a differential module the last condition says that the `F`-linear map
`Wᵢ / Wᵢ₋₁ → Wᵢ₊₁ / Wᵢ` induced by `D` between these two lines is an isomorphism. The notion is
meant for finite-dimensional `V`, which every result about it assumes. -/
structure IsOperFlag (D : V →+ V) (W : ℕ → Submodule F V) : Prop where
  /-- The subspaces increase. -/
  monotone : Monotone W
  /-- The `i`-th subspace has dimension `i`, until it fills `V`. -/
  finrank_eq (i : ℕ) : finrank F (W i) = min i (finrank F V)
  /-- Griffiths transversality: `D` raises the filtration degree by at most one. -/
  map_mem_succ {i : ℕ} {w : V} : w ∈ W i → D w ∈ W (i + 1)
  /-- Nondegeneracy: below the top, `D` does not preserve a step of the flag. -/
  exists_map_notMem {i : ℕ} : 0 < i → i < finrank F V → ∃ w ∈ W i, D w ∉ W i

namespace IsOperFlag

variable {W : ℕ → Submodule F V} (hW : IsOperFlag D W)
include hW

theorem apply_eq_top {i : ℕ} (hi : finrank F V ≤ i) : W i = ⊤ :=
  Submodule.eq_top_of_finrank_eq <| by rw [hW.finrank_eq, min_eq_right hi]

theorem apply_zero : W 0 = ⊥ :=
  Submodule.finrank_eq_zero.1 <| by simp [hW.finrank_eq]

/-- The first step of an oper flag is a line, spanned by some vector. -/
theorem exists_one_eq_span_singleton : ∃ v : V, W 1 = F ∙ v :=
  ((W 1).finrank_le_one_iff_isPrincipal.1
    (by rw [hW.finrank_eq]; exact min_le_left _ _)).principal

variable [Differential F] (hD : IsDifferentialModuleMap F D)
include hD

/-- An oper flag is the flag of iterates of any generator `v` of its first step. -/
theorem eq_iterateSpan {v : V} (hv : W 1 = F ∙ v) : W = iterateSpan F D v := by
  -- Every iterate `Dʲ v` lies in `W (j + 1)`, so `iterateSpan F D v i ≤ W i` for all `i`.
  have hiter (j : ℕ) : (⇑D)^[j] v ∈ W (j + 1) := by
    induction j with
    | zero => simp [hv]
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact hW.map_mem_succ ih
  have hle (i : ℕ) : iterateSpan F D v i ≤ W i :=
    iterateSpan_le_iff.2 fun j hj ↦ hW.monotone hj (hiter j)
  -- Up to the dimension, equality follows by induction from a dimension count.
  have heq (i : ℕ) (hi : i ≤ finrank F V) : W i = iterateSpan F D v i := by
    induction i with
    | zero => simp [hW.apply_zero]
    | succ i ih =>
      obtain rfl | hi0 := Nat.eq_zero_or_pos i
      · simp [hv]
      have ih := ih (by omega)
      -- `iterateSpan F D v i = W i` is not `D`-stable, so it is strictly smaller than
      -- `iterateSpan F D v (i + 1)`.
      have hlt : iterateSpan F D v i < iterateSpan F D v (i + 1) := by
        refine lt_of_le_of_ne (iterateSpan_mono (Nat.le_succ i)) fun h ↦ ?_
        obtain ⟨w, hw, hDw⟩ := hW.exists_map_notMem hi0 (by omega)
        rw [ih] at hw hDw
        exact hDw (h ▸ hD.map_mem_iterateSpan_succ hw)
      refine (Submodule.eq_of_le_of_finrank_le (hle (i + 1)) ?_).symm
      have := Submodule.finrank_lt_finrank_of_lt hlt
      rw [← ih, hW.finrank_eq, min_eq_left (by omega)] at this
      rw [hW.finrank_eq, min_eq_left hi]
      omega
  funext i
  obtain hi | hi := le_total i (finrank F V)
  · exact heq i hi
  · rw [hW.apply_eq_top hi, eq_comm, eq_top_iff, ← hW.apply_eq_top le_rfl, heq _ le_rfl]
    exact iterateSpan_mono hi

/-- A generator of the first step of an oper flag is a cyclic vector. -/
theorem linearIndependent_iterate {v : V} (hv : W 1 = F ∙ v) :
    LinearIndependent F fun i : Fin (finrank F V) ↦ (⇑D)^[i] v :=
  linearIndependent_of_top_le_span_of_card_eq_finrank
    (by rw [← iterateSpan_def, ← hW.eq_iterateSpan hD hv, hW.apply_eq_top le_rfl])
    (Fintype.card_fin _)

end IsOperFlag

variable [Differential F] (hD : IsDifferentialModuleMap F D)
include hD

namespace IsDifferentialModuleMap

/-- The flag of iterates `⟨v⟩ ⊂ ⟨v, D v⟩ ⊂ ⋯` of a cyclic vector `v` is an oper flag. -/
theorem isOperFlag_iterateSpan {v : V}
    (hv : LinearIndependent F fun i : Fin (finrank F V) ↦ (⇑D)^[i] v) :
    IsOperFlag D (iterateSpan F D v) := by
  have htop : iterateSpan F D v (finrank F V) = ⊤ :=
    hv.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)
  -- The first `i ≤ n` iterates of `v` are independent.
  have hvi {i : ℕ} (hi : i ≤ finrank F V) :
      LinearIndependent F fun j : Fin i ↦ (⇑D)^[j] v :=
    hv.comp (Fin.castLE hi) (Fin.castLE_injective hi)
  refine ⟨iterateSpan_mono, fun i ↦ ?_, hD.map_mem_iterateSpan_succ, fun {i} hi0 hi ↦ ?_⟩
  · obtain hi | hi := le_total i (finrank F V)
    · rw [min_eq_left hi, iterateSpan_def, finrank_span_eq_card (hvi hi), Fintype.card_fin]
    · rw [min_eq_right hi, eq_top_iff.2 (htop.ge.trans (iterateSpan_mono hi)), finrank_top]
  · -- `Dⁱ⁻¹ v` lies in the `i`-th step, while its image `Dⁱ v` does not.
    refine ⟨(⇑D)^[i - 1] v, iterate_mem_iterateSpan (by omega), ?_⟩
    rw [← Function.iterate_succ_apply' (⇑D), Nat.succ_eq_add_one, Nat.sub_add_cancel hi0]
    have := hvi (show i + 1 ≤ finrank F V by omega)
    rw [← Fin.snoc_init_self (fun j : Fin (i + 1) ↦ (⇑D)^[j] v), linearIndependent_finSnoc] at this
    have hinit : Fin.init (fun j : Fin (i + 1) ↦ (⇑D)^[j] v) = fun j : Fin i ↦ (⇑D)^[j] v := by
      ext j
      simp [Fin.init]
    simpa [iterateSpan_def, hinit] using this.2

/-- **Oper flags are flags of cyclic vectors.** A family `W` is an oper flag of the differential
module `(V, D)` if and only if it is the flag of iterates `⟨v⟩ ⊂ ⟨v, D v⟩ ⊂ ⋯` of a cyclic
vector `v`. -/
theorem isOperFlag_iff {W : ℕ → Submodule F V} :
    IsOperFlag D W ↔ ∃ v : V, (LinearIndependent F fun i : Fin (finrank F V) ↦ (⇑D)^[i] v) ∧
      W = iterateSpan F D v := by
  refine ⟨fun hW ↦ ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hW.exists_one_eq_span_singleton
    exact ⟨v, hW.linearIndependent_iterate hD hv, hW.eq_iterateSpan hD hv⟩
  · rintro ⟨v, hv, rfl⟩
    exact hD.isOperFlag_iterateSpan hv

end IsDifferentialModuleMap

/-- **`GL_n` oper reduction.** Over a field of characteristic zero whose derivation is not zero,
every differential module `(V, D)` has an oper flag: the flag of iterates of a cyclic vector,
which exists by `TauCeti.exists_cyclicVector`. -/
theorem exists_isOperFlag [CharZero F] (hd : (Differential.deriv : Derivation ℤ F F) ≠ 0) :
    ∃ W : ℕ → Submodule F V, IsOperFlag D W := by
  obtain ⟨v, hv⟩ := exists_cyclicVector F hd D hD
  exact ⟨_, hD.isOperFlag_iterateSpan hv⟩

end Field

end TauCeti
