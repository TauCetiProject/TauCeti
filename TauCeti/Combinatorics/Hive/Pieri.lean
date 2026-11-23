/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.GelfandTsetlin

/-!
# The top hive and the direct vertical Pieri rule for hives

In the product chart `Vertex.ofChart n i j`, the vertex `(x, y, z)` sits in column `i = z` of row
`j = y + z`. For an integer hive `h` with boundary `(λ, μ, γ*)`, the steps
`h(i + 1, j) - h(i, j)` along the rows form the Gelfand–Tsetlin pattern `h.toGTPattern`, with top
row `μ` and weight `γ - λ`, and `h` is recovered from `λ` and this pattern
(`TauCeti.Hive.apply_eq_gtCompletion_of_productBoundary`). Two consequences are proved directly
from the hive inequalities, without passing through tableaux.

1. **The top hive.** The output `γ = λ + μ` has exactly one integer hive, `TauCeti.Hive.topHive`,
   with value `λ₁ + ⋯ + λ_{y+z} + μ₁ + ⋯ + μ_z` at `(x, y, z)`, so
   `hiveCount (productBoundary λ μ (λ + μ)) = 1`: a pattern whose weight is its top row has every
   row equal to an initial segment of the top row.
2. **Vertical Pieri.** If every entry of `μ` is `0` or `1`, then so is every entry of the pattern,
   so each row of the product chart rises with slope one and then stays flat. The hive is
   `TauCeti.Hive.verticalPieriHive`, and it exists exactly when `γ - λ` is a `0`/`1` vector with
   `|γ| = |λ| + |μ|`, so the hive count is `1` in that case and `0` otherwise. This is the vertical
   Pieri rule `s_λ e_k = ∑ s_γ`, the sum over the `γ` with `γ / λ` a vertical strip of size `k`.

## Main definitions

* `TauCeti.Hive.topHive`: the unique integer hive with boundary `(λ, μ, (λ + μ)*)`.
* `TauCeti.Hive.verticalPieriHive`: for dominant weights `λ`, `γ` with `γ - λ` a `0`/`1` vector,
  the integer hive whose boundary is `(λ, μ, γ*)` for every `0`/`1` weight `μ` with
  `|μ| = |γ| - |λ|`.

## Main results

* `TauCeti.Hive.eq_topHive_of_boundary`, `TauCeti.Hive.hiveCount_productBoundary_add`: the top hive
  is unique.
* `TauCeti.Hive.le_and_le_add_one_of_productBoundary_of_zero_le_le_one`,
  `TauCeti.Hive.eq_verticalPieriHive_of_productBoundary_of_zero_le_le_one`,
  `TauCeti.Hive.nonempty_fixedIntegerHive_productBoundary_iff_of_zero_le_le_one`,
  `TauCeti.Hive.hiveCount_productBoundary_of_zero_le_le_one`: the direct vertical Pieri rule.

## References

* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §4, Proposition 4.
* A. Knutson and T. Tao, *The honeycomb model of GLₙ(ℂ) tensor products I: proof of the saturation
  conjecture*, J. Amer. Math. Soc. **12** (1999), Appendix 2.
* I. G. Macdonald, *Symmetric functions and Hall polynomials*, 2nd ed., Oxford University Press,
  1995, Chapter I, (5.17).
-/

public section

namespace TauCeti.Hive

variable {n : ℕ}

/-- A function `p ↦ G p.z (p.y + p.z)` of the product-chart coordinates is rhombus-concave when
`G` satisfies the three chart families of `TauCeti.Hive.isRhombusConcave_iff_ofChart`. -/
private theorem isRhombusConcave_of_chart {R : Type*} [AddCommMagma R] [LE R] {G : ℕ → ℕ → R}
    (h₁ : ∀ i j, i < j → j < n → G (i + 1) j + G i (j + 1) ≤ G i j + G (i + 1) (j + 1))
    (h₂ : ∀ i j, i < j → j < n → G i j + G (i + 2) (j + 1) ≤ G (i + 1) j + G (i + 1) (j + 1))
    (h₃ : ∀ i j, i ≤ j → j + 2 ≤ n →
      G i j + G (i + 1) (j + 2) ≤ G i (j + 1) + G (i + 1) (j + 1)) :
    IsRhombusConcave fun p : Vertex n => G p.z (p.y + p.z) := by
  refine (isRhombusConcave_iff_ofChart _).mpr
    ⟨fun i j hij hj => ?_, fun i j hij hj => ?_, fun i j hij hj => ?_⟩ <;>
    simp (disch := omega) only [Vertex.ofChart_y, Vertex.ofChart_z, Nat.sub_add_cancel]
  exacts [h₁ i j hij hj, h₂ i j hij hj, h₃ i j hij hj]

/-! ### The top hive at `γ = λ + μ` -/

section TopHive

/-- The **top hive** of `(λ, μ)`: its value at `(x, y, z)` is `λ₁ + ⋯ + λ_{y+z} + μ₁ + ⋯ + μ_z`.
Its boundary is `(λ, μ, (λ + μ)*)` (`TauCeti.Hive.boundary_topHive`), and it is the only integer
hive with that boundary (`TauCeti.Hive.eq_topHive_of_boundary`). -/
def topHive (lam μ : DominantWeight n) : IntegerHive n where
  value p := prefixSum (p.y + p.z) lam.val + prefixSum p.z μ.val
  value_cornerA' := by simp
  le_of_isRhombus' {_ _ _ _} hr := (isRhombusConcave_of_chart (n := n)
    (G := fun i j => prefixSum j lam.val + prefixSum i μ.val)
    (fun i j _ _ => by omega)
    (fun i j hij hjn => by
      have h₁ := prefixSum_succ (k := i) (by omega) μ.val
      have h₂ : prefixSum (i + 2) μ.val = prefixSum (i + 1) μ.val + μ.val ⟨i + 1, by omega⟩ :=
        prefixSum_succ (by omega) μ.val
      have := μ.antitone (show (⟨i, by omega⟩ : Fin n) ≤ ⟨i + 1, by omega⟩ from
        Fin.mk_le_mk.mpr (by omega))
      omega)
    (fun i j _ hjn => by
      have h₁ := prefixSum_succ (k := j) (by omega) lam.val
      have h₂ : prefixSum (j + 2) lam.val = prefixSum (j + 1) lam.val + lam.val ⟨j + 1, by omega⟩ :=
        prefixSum_succ (by omega) lam.val
      have := lam.antitone (show (⟨j, by omega⟩ : Fin n) ≤ ⟨j + 1, by omega⟩ from
        Fin.mk_le_mk.mpr (by omega))
      omega)).le hr

@[simp] theorem topHive_apply (lam μ : DominantWeight n) (p : Vertex n) :
    topHive lam μ p = prefixSum (p.y + p.z) lam.val + prefixSum p.z μ.val := (rfl)

@[simp] theorem topHive_zero : topHive (0 : DominantWeight n) 0 = 0 := by
  ext p; simp

/-- The top hive is additive in the pair of inputs. -/
theorem topHive_add (lam₁ lam₂ μ₁ μ₂ : DominantWeight n) :
    topHive (lam₁ + lam₂) (μ₁ + μ₂) = topHive lam₁ μ₁ + topHive lam₂ μ₂ := by
  ext p; simp only [topHive_apply, add_apply, DominantWeight.coe_add, prefixSum_add]; abel

/-- The top hive has boundary `(λ, μ, (λ + μ)*)`. -/
@[simp] theorem boundary_topHive (lam μ : DominantWeight n) :
    (topHive lam μ).boundary = productBoundary lam μ (lam + μ) := by
  ext s k
  have hk := k.isLt
  fin_cases s
  · simp [boundary_apply, prefixSum_succ hk]
  · have e₁ : n - (k + 1) + (k + 1) = n := by omega
    have e₂ : n - k + k = n := by omega
    simp [boundary_apply, e₁, e₂, prefixSum_succ hk]
  · have e : n - k = n - (k + 1) + 1 := by omega
    have hk' : n - (k + 1) < n := by omega
    have hrev : k.rev = ⟨n - (k + 1), hk'⟩ := Fin.ext (by simp)
    simp [boundary_apply, e, prefixSum_succ hk', hrev]
    abel

/-- **Uniqueness of the top hive**: every integer hive with boundary `(λ, μ, (λ + μ)*)` is
`TauCeti.Hive.topHive λ μ`. -/
theorem eq_topHive_of_boundary {lam μ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ (lam + μ)) : h = topHive lam μ := by
  set P := h.toGTPattern
  have htop : P.topRow = μ.val := topRow_toGTPattern_of_productBoundary hb
  have hw : P.rowWeight = μ.val := by
    rw [rowWeight_toGTPattern_of_productBoundary hb, DominantWeight.coe_add, add_sub_cancel_left]
  -- Each entry is at most the top-row entry above it, and each row sum is the matching prefix
  -- sum of the top row, so every row is an initial segment of the top row.
  have hrow {j : ℕ} (hj : j ≤ n) : ∀ k ∈ Finset.range j, P k j = P k n :=
    (Finset.sum_eq_sum_iff_of_le fun k hk =>
      P.entry_le_entry_of_le (Finset.mem_range.mp hk) hj le_rfl).mp (by
        rw [← P.rowSum_def, ← P.prefixSum_rowWeight hj, hw, ← htop, P.prefixSum_topRow])
  ext p
  have hp := p.sum_eq
  rw [apply_eq_gtCompletion_of_productBoundary hb, gtCompletion_def, topHive_apply,
    show n - p.x = p.y + p.z by omega, ← htop, P.prefixSum_topRow]
  exact congrArg _ (Finset.sum_congr rfl fun k hk =>
    hrow (by omega) k (Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le (by omega))))

instance (lam μ : DominantWeight n) :
    Unique (FixedIntegerHive (productBoundary lam μ (lam + μ))) where
  default := ⟨topHive lam μ, boundary_topHive lam μ⟩
  uniq h := Subtype.ext (eq_topHive_of_boundary h.property)

/-- **The top coefficient is one**: `V_{λ + μ}` occurs exactly once in `V_λ ⊗ V_μ`, as a hive
count. -/
@[simp] theorem hiveCount_productBoundary_add (lam μ : DominantWeight n) :
    hiveCount (productBoundary lam μ (lam + μ)) = 1 := by
  rw [← card_fixedIntegerHive]; exact Fintype.card_unique

end TopHive

/-! ### Vertical Pieri -/

section VerticalPieri

variable {lam μ γ : DominantWeight n}

/-- If `γ - λ` is a `0`/`1` vector, then `0 ≤ (γ - λ)₁ + ⋯ + (γ - λ)ⱼ ≤ j`. -/
private theorem prefixSum_sub_mem (hγ : ∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1)
    (j : ℕ) :
    0 ≤ prefixSum j γ.val - prefixSum j lam.val ∧ prefixSum j γ.val - prefixSum j lam.val ≤ j := by
  have h₁ := prefixSum_mono j fun i => (hγ i).1
  have h₂ := prefixSum_mono j (y := lam.val + fun _ => 1) fun i => (hγ i).2
  have h₃ : prefixSum j (fun _ : Fin n => (1 : ℤ)) = min j n := by
    simpa using prefixSum_eq_sum_range (n := n) j fun _ => (1 : ℤ)
  rw [prefixSum_add, h₃] at h₂
  omega

/-- The **vertical Pieri hive** of `λ ⊆ γ`, for `γ - λ` a `0`/`1` vector: its value at `(x, y, z)`
is `λ₁ + ⋯ + λⱼ + min z ((γ - λ)₁ + ⋯ + (γ - λ)ⱼ)` with `j = y + z`, so each row of the product
chart rises with slope one and then stays flat. Its boundary is `(λ, μ, γ*)` for the `0`/`1`
weight `μ` with `|μ| = |γ| - |λ|` (`TauCeti.Hive.boundary_verticalPieriHive`). -/
def verticalPieriHive (lam γ : DominantWeight n)
    (hγ : ∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1) : IntegerHive n where
  value p := prefixSum (p.y + p.z) lam.val +
    min (p.z : ℤ) (prefixSum (p.y + p.z) γ.val - prefixSum (p.y + p.z) lam.val)
  value_cornerA' := by simp
  le_of_isRhombus' {_ _ _ _} hr := (isRhombusConcave_of_chart (n := n)
    (G := fun i j => prefixSum j lam.val + min (i : ℤ) (prefixSum j γ.val - prefixSum j lam.val))
    (fun i j _ hjn => by
      have h₁ := prefixSum_succ (k := j) (by omega) lam.val
      have h₃ := prefixSum_succ (k := j) (by omega) γ.val
      have := hγ ⟨j, by omega⟩
      push_cast; omega)
    (fun i j _ hjn => by
      have h₁ := prefixSum_succ (k := j) (by omega) lam.val
      have h₃ := prefixSum_succ (k := j) (by omega) γ.val
      have := hγ ⟨j, by omega⟩
      push_cast; omega)
    (fun i j _ hjn => by
      have h₁ := prefixSum_succ (k := j) (by omega) lam.val
      have h₂ : prefixSum (j + 2) lam.val = prefixSum (j + 1) lam.val + lam.val ⟨j + 1, by omega⟩ :=
        prefixSum_succ (by omega) lam.val
      have h₃ := prefixSum_succ (k := j) (by omega) γ.val
      have h₄ : prefixSum (j + 2) γ.val = prefixSum (j + 1) γ.val + γ.val ⟨j + 1, by omega⟩ :=
        prefixSum_succ (by omega) γ.val
      have hle : (⟨j, by omega⟩ : Fin n) ≤ ⟨j + 1, by omega⟩ := Fin.mk_le_mk.mpr (by omega)
      have := lam.antitone hle
      have := γ.antitone hle
      have := hγ ⟨j, by omega⟩
      have := hγ ⟨j + 1, by omega⟩
      push_cast; omega)).le hr

@[simp] theorem verticalPieriHive_apply (hγ : ∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1)
    (p : Vertex n) :
    verticalPieriHive lam γ hγ p = prefixSum (p.y + p.z) lam.val +
      min (p.z : ℤ) (prefixSum (p.y + p.z) γ.val - prefixSum (p.y + p.z) lam.val) := (rfl)

/-- The vertical Pieri hive has boundary `(λ, μ, γ*)` for every `0`/`1` weight `μ` with
`|λ| + |μ| = |γ|`. -/
theorem boundary_verticalPieriHive (hγ : ∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1)
    (hμ : ∀ i, 0 ≤ μ.val i ∧ μ.val i ≤ 1) (hsum : ∑ i, γ.val i = ∑ i, lam.val i + ∑ i, μ.val i) :
    (verticalPieriHive lam γ hγ).boundary = productBoundary lam μ γ := by
  ext s k
  have hk := k.isLt
  fin_cases s
  · have h₀ := prefixSum_sub_mem hγ k
    have h₁ := prefixSum_sub_mem hγ (k + 1)
    have e := prefixSum_succ hk lam.val
    rw [Fin.eta] at e
    simp [boundary_apply]
    omega
  · have e₁ : n - (k + 1) + (k + 1) = n := by omega
    have e₂ : n - k + k = n := by omega
    have m₀ := prefixSum_eq_min_of_antitone μ.antitone hμ k
    have m₁ := prefixSum_eq_min_of_antitone μ.antitone hμ (k + 1)
    have e := prefixSum_succ hk μ.val
    rw [Fin.eta] at e
    simp [boundary_apply, e₁, e₂, prefixSum_of_le le_rfl]
    omega
  · have e : n - k = n - (k + 1) + 1 := by omega
    have hk' : n - (k + 1) < n := by omega
    have hrev : k.rev = ⟨n - (k + 1), hk'⟩ := Fin.ext (by simp)
    have h₀ := prefixSum_sub_mem hγ (n - (k + 1))
    have h₁ := prefixSum_sub_mem hγ (n - (k + 1) + 1)
    have e₁ := prefixSum_succ hk' lam.val
    have e₂ := prefixSum_succ hk' γ.val
    simp [boundary_apply, e, hrev]
    omega

/-- When the side `B → C` of an integer hive is a `0`/`1` weight, each row of the product chart
rises with slope one and then stays flat. -/
private theorem apply_eq_of_zero_le_le_one {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hμ : ∀ i, 0 ≤ μ.val i ∧ μ.val i ≤ 1)
    (p : Vertex n) :
    h p = prefixSum (p.y + p.z) lam.val +
      min (p.z : ℤ) (prefixSum (p.y + p.z) γ.val - prefixSum (p.y + p.z) lam.val) := by
  set P := h.toGTPattern
  have htop : P.topRow = μ.val := topRow_toGTPattern_of_productBoundary hb
  have hp := p.sum_eq
  rw [apply_eq_gtCompletion_of_productBoundary hb, gtCompletion_def,
    show n - p.x = p.y + p.z by omega]
  -- Row `j` of the pattern decreases weakly, and its entries lie between `μₙ` and `μ₁`.
  have hj : p.y + p.z ≤ n := by omega
  have key := prefixSum_eq_min_of_antitone (x := fun k : Fin (p.y + p.z) => P k (p.y + p.z))
    (fun a b hab => P.entry_anti hab b.isLt) (fun k => by
      have := k.isLt
      have hk := P.entry_mem_Icc k.isLt hj
      rw [htop] at hk
      have := hμ ⟨n - 1, by omega⟩
      have := hμ ⟨0, by omega⟩
      exact ⟨by linarith [hk.1], by linarith [hk.2]⟩) p.z
  rw [prefixSum_eq_sum_range p.z (fun k => P k (p.y + p.z)), min_eq_left (by omega),
    Fin.sum_univ_eq_sum_range (fun k => P k (p.y + p.z)), ← P.rowSum_def,
    ← P.prefixSum_rowWeight hj, rowWeight_toGTPattern_of_productBoundary hb, prefixSum_sub] at key
  rw [key]

/-- **Vertical strip condition**: if an integer hive has boundary `(λ, μ, γ*)` with `μ` a `0`/`1`
weight, then `γ - λ` is a `0`/`1` vector. -/
theorem le_and_le_add_one_of_productBoundary_of_zero_le_le_one {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hμ : ∀ i, 0 ≤ μ.val i ∧ μ.val i ≤ 1) (k : Fin n) :
    lam.val k ≤ γ.val k ∧ γ.val k ≤ lam.val k + 1 := by
  have := k.isLt
  have hk := h.toGTPattern.rowWeight_mem_Icc k
  rw [topRow_toGTPattern_of_productBoundary hb, rowWeight_toGTPattern_of_productBoundary hb] at hk
  have := hμ ⟨n - 1, by omega⟩
  have := hμ ⟨0, by omega⟩
  simp only [Set.mem_Icc, Pi.sub_apply] at hk
  omega

/-- **Uniqueness for vertical Pieri**: an integer hive with boundary `(λ, μ, γ*)` for a `0`/`1`
weight `μ` is `TauCeti.Hive.verticalPieriHive λ γ _`, built from the side `A → B` and the dual of
the side `C → A`. -/
theorem eq_verticalPieriHive_of_productBoundary_of_zero_le_le_one {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hμ : ∀ i, 0 ≤ μ.val i ∧ μ.val i ≤ 1) :
    h = verticalPieriHive lam γ (le_and_le_add_one_of_productBoundary_of_zero_le_le_one hb hμ) :=
  ext (apply_eq_of_zero_le_le_one hb hμ)

/-- For a `0`/`1` weight `μ`, there is at most one integer hive with boundary `(λ, μ, γ*)`. -/
theorem subsingleton_fixedIntegerHive_productBoundary_of_zero_le_le_one
    (hμ : ∀ i, 0 ≤ μ.val i ∧ μ.val i ≤ 1) :
    Subsingleton (FixedIntegerHive (productBoundary lam μ γ)) :=
  ⟨fun h₁ h₂ => Subtype.ext <|
    (eq_verticalPieriHive_of_productBoundary_of_zero_le_le_one h₁.property hμ).trans
      (eq_verticalPieriHive_of_productBoundary_of_zero_le_le_one h₂.property hμ).symm⟩

/-- **Direct vertical Pieri rule for hives**: when `μ` is a `0`/`1` weight (the highest weight of
an exterior power `Λᵏ ℂⁿ`, up to its size), the integer hives with boundary `(λ, μ, γ*)` exist
exactly when `γ - λ` is a `0`/`1` vector with `|γ| = |λ| + |μ|`. -/
theorem nonempty_fixedIntegerHive_productBoundary_iff_of_zero_le_le_one
    (hμ : ∀ i, 0 ≤ μ.val i ∧ μ.val i ≤ 1) :
    Nonempty (FixedIntegerHive (productBoundary lam μ γ)) ↔
      (∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1) ∧
        ∑ i, γ.val i = ∑ i, lam.val i + ∑ i, μ.val i :=
  ⟨fun ⟨⟨_, hb⟩⟩ => ⟨le_and_le_add_one_of_productBoundary_of_zero_le_le_one hb hμ,
    (sum_eq_of_productBoundary hb).symm⟩,
   fun ⟨hγ, hsum⟩ => ⟨⟨verticalPieriHive lam γ hγ, boundary_verticalPieriHive hγ hμ hsum⟩⟩⟩

/-- **Vertical Pieri rule as a hive count**: for a `0`/`1` weight `μ`, the hive count of
`(λ, μ, γ*)` is `1` when `γ - λ` is a `0`/`1` vector with `|γ| = |λ| + |μ|`, and `0` otherwise. -/
theorem hiveCount_productBoundary_of_zero_le_le_one (hμ : ∀ i, 0 ≤ μ.val i ∧ μ.val i ≤ 1) :
    hiveCount (productBoundary lam μ γ) =
      if (∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1) ∧
          ∑ i, γ.val i = ∑ i, lam.val i + ∑ i, μ.val i then 1 else 0 := by
  have := subsingleton_fixedIntegerHive_productBoundary_of_zero_le_le_one (lam := lam) (γ := γ) hμ
  split_ifs with hc
  · rw [← card_fixedIntegerHive]
    have : Nonempty (FixedIntegerHive (productBoundary lam μ γ)) :=
      (nonempty_fixedIntegerHive_productBoundary_iff_of_zero_le_le_one hμ).mpr hc
    exact Fintype.card_eq_one_iff_nonempty_unique.mpr
      ⟨uniqueOfSubsingleton (Classical.choice this)⟩
  · rw [hiveCount_eq_zero_iff]
    exact not_nonempty_iff.mp fun hne =>
      hc ((nonempty_fixedIntegerHive_productBoundary_iff_of_zero_le_le_one hμ).mp hne)

end VerticalPieri

/-! ### Rank-`2` checks -/

section Checks

/-- For `λ = μ = (1, 0)`, the top hive is the hive `exampleTwo` of the output `(2, 0)`. -/
theorem topHive_two_std_std : topHive ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ = exampleTwo :=
  (eq_topHive_of_boundary (boundary_exampleTwo.trans (by
    congr 1; ext i; fin_cases i <;> rfl))).symm

/-- Rank-`2` vertical Pieri checks with `μ = (1, 0)`: for `λ = (2, 0)` the outputs `(3, 0)` and
`(2, 1)` each occur once; for `λ = (1, 1)` the output `(2, 1)` occurs once, while `(2, 0)`, whose
difference `(1, -1)` with `λ` is not a `0`/`1` vector, does not occur. -/
theorem hiveCount_two_verticalPieri_checks :
    hiveCount (productBoundary ⟨![2, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![3, 0], by decide⟩) = 1
      ∧ hiveCount
        (productBoundary ⟨![2, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![2, 1], by decide⟩) = 1
      ∧ hiveCount
        (productBoundary ⟨![1, 1], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![2, 1], by decide⟩) = 1
      ∧ hiveCount
        (productBoundary ⟨![1, 1], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![2, 0], by decide⟩) = 0 := by
  simp only [hiveCount_productBoundary_of_zero_le_le_one (μ := ⟨![1, 0], by decide⟩) (by decide)]
  decide

end Checks

end TauCeti.Hive
