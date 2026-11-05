/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Integrality
import TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectedChain
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Ray
import TauCeti.RepresentationTheory.LSPath.Concatenation

/-!
# Littelmann's lowering operator preserves Lakshmibai–Seshadri paths

Let `π` be a Lakshmibai–Seshadri path of dominant shape `λ` and `αᵢ` a simple root. Littelmann's
lowering operator `f_{αᵢ}` acts on the realization of `π` by reflecting, in `sᵢ`, the piece of the
path between the last time `t₀` at which the height `⟨π(t), αᵢ^∨⟩` is minimal and the first later
time `t₁` at which it has risen by one (`TauCeti.LSPath.exists_lower_toPLPath_eq`). This file
proves that the result is again an LS path of shape `λ`: its directions are those of `π`, with the
directions `τ` of the reflected piece replaced by `sᵢ τ`, and its breaks are those of `π` and
`t₁`, except that `t₀` is dropped when `sᵢ τ` agrees with the direction before `t₀`.

The chain conditions of the new path are Littelmann's. The height does not increase just before
`t₀` and increases after it, so the chain from the direction before `t₀` can be continued to the
reflected direction after it (`TauCeti.IsAChain.exists_isAChain_simple_mul_last`). Strictly
between `t₀` and `t₁` the height at a break `a` is not an integer, so every chain at `a` lies on
the positive side of the wall of `αᵢ` and reflects in `sᵢ`. At `t₁` the height is an integer, so
`sᵢ τ ⋗ τ` is a `t₁`-chain.

The new path is assembled as break data (`TauCeti.LSPath.exists_toPLPath_eq_ofSegments`): the
reflected directions may agree with their neighbours and the new break may coincide with an old
one, and these repetitions are removed when the break data are turned into an LS path.

## Main results

* `TauCeti.LSPath.exists_toPLPath_eq_of_lower_eq_some`: **Littelmann's lowering operator
  `f_{αᵢ}` sends an LS path of dominant shape `λ` to an LS path of shape `λ`** whenever it is
  defined.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Section 4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Section 4.
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N 𝕜 V : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]
  {lam : M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-! ### Lowering an LS path -/

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The segment list of Littelmann's lowering, as produced by
`TauCeti.PLPath.lower_ofSegments_eq_of_strictly_rising`, is again indexed by a range. -/
private theorem lowered_eq_map_range {g g' : ℕ → V} (r : V → V) {s k₀ k₁ : ℕ} (θ : 𝕜)
    (hk₀₁ : k₀ < k₁) (hk₁ : k₁ ≤ s) (h₁ : ∀ n < k₀, g' n = g n)
    (h₂ : ∀ n, k₀ ≤ n → n + 1 < k₁ → g' n = r (g n))
    (h₃ : g' (k₁ - 1) = r (θ • g (k₁ - 1))) (h₄ : g' k₁ = (1 - θ) • g (k₁ - 1))
    (h₅ : ∀ n, k₁ < n → g' n = g (n - 1)) (hL : k₁ - 1 < ((List.range s).map g).length) :
    ((List.range s).map g).take k₀ ++
        ((((List.range s).map g).take (k₁ - 1)).drop k₀ ++
          [θ • ((List.range s).map g)[k₁ - 1]]).map r ++
        (1 - θ) • ((List.range s).map g)[k₁ - 1] :: ((List.range s).map g).drop k₁ =
      (List.range (s + 1)).map g' := by
  refine List.ext_getElem (by simp; omega) fun n h h' ↦ ?_
  simp only [List.getElem_append, List.getElem_cons, List.getElem_map, List.getElem_take,
    List.getElem_drop, List.getElem_range, List.length_append, List.length_map, List.length_take,
    List.length_drop, List.length_range, List.length_cons, List.length_nil,
    min_eq_left (by omega : k₀ ≤ s), min_eq_left (by omega : k₁ - 1 ≤ s)]
  split_ifs
  · exact (h₁ n (by omega)).symm
  · rw [h₂ n (by omega) (by omega)]
    congr 2
    omega
  · rw [show n = k₁ - 1 by omega, h₃]
  · exfalso
    omega
  · rw [show n = k₁ by omega, h₄]
  · rw [h₅ n (by omega)]
    congr 1
    omega

variable [P.flip.IsReduced]

/-- The directions of an LS path after lowering at the vertices `k₀ < k₁`: the directions `τ_n`
with `k₀ ≤ n < k₁` are reflected by `sᵢ`, and `τ_{k₁ - 1}` is repeated after the new break. -/
private noncomputable def lowerDir (π : LSPath P b lam) (i : b.support) (k₀ k₁ n : ℕ) :
    P.weylGroup :=
  if n < k₀ then π.natDir n
  else if n < k₁ then (weylCoxeterSystem P b).simple i * π.natDir n else π.natDir (n - 1)

/-- The break times of an LS path after lowering, with the new break `t₁` inserted at `k₁`. -/
private def lowerTime (π : LSPath P b lam) (k₁ : ℕ) (t₁ : ℚ) (n : ℕ) : ℚ :=
  if n < k₁ then π.natTime n else if n = k₁ then t₁ else π.natTime (n - 1)

section LowerData

variable {π : LSPath P b lam} {i : b.support} {k₀ k₁ n : ℕ} {t₁ : ℚ}

omit [P.flip.IsReduced] in
private theorem lowerDir_of_lt (h : n < k₀) : lowerDir π i k₀ k₁ n = π.natDir n := by
  simp [lowerDir, h]

omit [P.flip.IsReduced] in
private theorem lowerDir_of_le_of_lt (h₀ : k₀ ≤ n) (h₁ : n < k₁) :
    lowerDir π i k₀ k₁ n = (weylCoxeterSystem P b).simple i * π.natDir n := by
  simp [lowerDir, h₁, show ¬n < k₀ by omega]

omit [P.flip.IsReduced] in
private theorem lowerDir_of_le (h₀ : k₀ < k₁) (h₁ : k₁ ≤ n) :
    lowerDir π i k₀ k₁ n = π.natDir (n - 1) := by
  simp [lowerDir, show ¬n < k₀ by omega, show ¬n < k₁ by omega]

omit [P.flip.IsReduced] in
private theorem lowerTime_of_lt (h : n < k₁) : lowerTime π k₁ t₁ n = π.natTime n := by
  simp [lowerTime, h]

omit [P.flip.IsReduced] in
private theorem lowerTime_self : lowerTime π k₁ t₁ k₁ = t₁ := by
  simp [lowerTime]

omit [P.flip.IsReduced] in
private theorem lowerTime_of_lt' (h : k₁ < n) : lowerTime π k₁ t₁ n = π.natTime (n - 1) := by
  simp [lowerTime, show ¬n < k₁ by omega, show n ≠ k₁ by omega]

end LowerData

/-- **The chains of a lowered LS path.** Let `H j` be the height `⟨π(a_j), αᵢ^∨⟩` of an LS path
at its vertex `j`, with an integral least value `H k₀`, rising strictly from `k₀` up to the vertex
`k₁` and staying below `H k₀ + 1` before `k₁`. Let `t₁` be the time at which the segment `k₁ - 1`
reaches the height `H k₀ + 1`. Then consecutive directions of the lowered break data are joined
by chains for the break between them. -/
private theorem lower_chain (π : LSPath P b lam) (hlam : lam ∈ dominantChamber P b)
    (i : b.support) (H : ℕ → ℚ) (hH : ∀ j, H j = ∑ k ∈ Finset.range j,
      (π.natTime (k + 1) - π.natTime k) * (P.coroot' i (π.natDir k • lam) : ℚ))
    {k₀ k₁ : ℕ} (hk₀₁ : k₀ < k₁) (hk₁ : k₁ ≤ π.length + 1) (hz : ∃ z : ℤ, H k₀ = z)
    (hleast : ∀ j ≤ π.length + 1, H k₀ ≤ H j)
    (hrise : ∀ j, k₀ ≤ j → j < k₁ → H j < H (j + 1) ∧ H j < H k₀ + 1) {t₁ : ℚ}
    (ht₁ : (t₁ - π.natTime (k₁ - 1)) * P.coroot' i (π.natDir (k₁ - 1) • lam) =
      H k₀ + 1 - H (k₁ - 1))
    (n : ℕ) (hn : n + 1 < π.length + 2) :
    ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
      C.head.1 = lowerDir π i k₀ k₁ n ∧ C.last.1 = lowerDir π i k₀ k₁ (n + 1) ∧
        IsAChain (lowerTime π k₁ t₁ (n + 1)) lam C := by
  have hHs (k : ℕ) : H (k + 1) = H k +
      (π.natTime (k + 1) - π.natTime k) * P.coroot' i (π.natDir k • lam) := by
    rw [hH, hH, Finset.sum_range_succ]
  have hd (k : ℕ) (hk : k < π.length + 1) : 0 < π.natTime (k + 1) - π.natTime k :=
    sub_pos.mpr (π.natTime_strictMono k hk)
  -- The reflected directions lie strictly on the positive side of the wall of `αᵢ`.
  have hcpos (k : ℕ) (h₀ : k₀ ≤ k) (h₁ : k < k₁) : 0 < P.coroot' i (π.natDir k • lam) := by
    have hr := (hrise k h₀ h₁).1
    rw [hHs] at hr
    by_contra! hc
    nlinarith [hd k (by omega), (Int.cast_nonpos (R := ℚ)).mpr hc]
  obtain ⟨z, hz⟩ := hz
  rcases lt_trichotomy (n + 1) k₀ with h₁ | h₁ | h₁
  · -- Before `k₀` nothing changes.
    rw [lowerDir_of_lt (by omega), lowerDir_of_lt h₁, lowerTime_of_lt (by omega)]
    exact π.natDir_chain n (by omega)
  · -- At `k₀` the height stops decreasing: the chain ends at the reflected direction.
    obtain ⟨C, hh, hl, hC⟩ := π.natDir_chain n (by omega)
    have hneg : P.coroot' i (C.head.1 • lam) ≤ 0 := by
      have hle := hleast n (by omega)
      rw [← h₁, hHs] at hle
      rw [hh]
      by_contra! hc
      nlinarith [hd n (by omega), (Int.cast_pos (R := ℚ)).mpr hc]
    obtain ⟨D, hDh, hDl, hD⟩ := hC.exists_isAChain_simple_mul_last hlam i hneg
      (hl ▸ hcpos (n + 1) h₁.ge (by omega))
    refine ⟨D, by rw [hDh, hh, lowerDir_of_lt (by omega)], ?_, ?_⟩
    · rw [hDl, hl, lowerDir_of_le_of_lt h₁.ge (by omega)]
    · rwa [lowerTime_of_lt (by omega)]
  rcases lt_trichotomy (n + 1) k₁ with h₂ | h₂ | h₂
  · -- Strictly inside the reflected piece the height is not an integer, so the whole chain lies
    -- on the positive side and is reflected.
    obtain ⟨C, hh, hl, hC⟩ := π.natDir_chain n (by omega)
    have hint : ¬∃ z : ℤ, π.natTime (n + 1) * P.coroot' i (C.last.1 • lam) = z := by
      rintro ⟨z₁, hz₁⟩
      obtain ⟨z₂, hz₂⟩ := exists_sum_sub_natTime_mul_eq_intCast π hlam (P.coroot' i)
        (j := n + 1) (by omega)
      rw [← hH, ← hl] at hz₂
      have hlo : (z : ℚ) < z₁ + z₂ := by
        linarith [hleast n (by omega), (hrise n (by omega) (by omega)).1]
      have hhi : ((z₁ + z₂ : ℤ) : ℚ) < z + 1 := by
        push_cast
        linarith [(hrise (n + 1) (by omega) h₂).2]
      have : z < z₁ + z₂ := by exact_mod_cast hlo
      have : z₁ + z₂ < z + 1 := by exact_mod_cast hhi
      omega
    have hall := hC.coroot'_smul_pos hlam i (hl ▸ hcpos (n + 1) (by omega) h₂) hint
    refine ⟨_root_.CoxeterSystem.MinimalCosetRepChain.simpleMul hlam C i (Or.inl hall), ?_, ?_,
      ?_⟩
    · rw [_root_.CoxeterSystem.MinimalCosetRepChain.head_simpleMul, hh,
        lowerDir_of_le_of_lt (by omega) (by omega)]
    · rw [_root_.CoxeterSystem.MinimalCosetRepChain.last_simpleMul, hl,
        lowerDir_of_le_of_lt (by omega) h₂]
    · rwa [lowerTime_of_lt h₂,
        _root_.CoxeterSystem.MinimalCosetRepChain.isAChain_simpleMul_iff]
  · -- At the new break `t₁` the reflected direction `sᵢ τ` covers `τ`.
    obtain rfl : n = k₁ - 1 := by omega
    obtain ⟨z₂, hz₂⟩ := exists_sum_sub_natTime_mul_eq_intCast π hlam (P.coroot' i)
      (j := k₁ - 1) (by omega)
    rw [← hH] at hz₂
    obtain ⟨C, hh, hl, hC⟩ := exists_isAChain_simple_mul_of_coroot'_pos hlam
      (π.isMinimalCosetRep_natDir (k₁ - 1)) (hcpos (k₁ - 1) (by omega) (by omega))
      (a := t₁) ⟨z + 1 - z₂, by push_cast; linear_combination ht₁ + hz - hz₂⟩
    refine ⟨C, ?_, ?_, ?_⟩
    · rw [hh, lowerDir_of_le_of_lt (by omega) (by omega)]
    · rw [hl, h₂, lowerDir_of_le hk₀₁ le_rfl]
    · rwa [h₂, lowerTime_self]
  · -- After `t₁` nothing changes, up to the shift of indices.
    have hc := π.natDir_chain (n - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hc
    rwa [lowerDir_of_le hk₀₁ (by omega), lowerDir_of_le hk₀₁ (by omega), Nat.add_sub_cancel,
      lowerTime_of_lt' (by omega), Nat.add_sub_cancel]

/-- **The lowered break data present an LS path**, with the hypotheses of
`TauCeti.LSPath.lower_chain` and a cut time `t₁` inside the segment `k₁ - 1`. -/
private theorem exists_toPLPath_eq_lower (π : LSPath P b lam) (hlam : lam ∈ dominantChamber P b)
    (i : b.support) (H : ℕ → ℚ) (hH : ∀ j, H j = ∑ k ∈ Finset.range j,
      (π.natTime (k + 1) - π.natTime k) * (P.coroot' i (π.natDir k • lam) : ℚ))
    {k₀ k₁ : ℕ} (hk₀₁ : k₀ < k₁) (hk₁ : k₁ ≤ π.length + 1) (hz : ∃ z : ℤ, H k₀ = z)
    (hleast : ∀ j ≤ π.length + 1, H k₀ ≤ H j)
    (hrise : ∀ j, k₀ ≤ j → j < k₁ → H j < H (j + 1) ∧ H j < H k₀ + 1) {t₁ : ℚ}
    (ht₁ : (t₁ - π.natTime (k₁ - 1)) * P.coroot' i (π.natDir (k₁ - 1) • lam) =
      H k₀ + 1 - H (k₁ - 1))
    (ht₁₀ : π.natTime (k₁ - 1) ≤ t₁) (ht₁₁ : t₁ ≤ π.natTime k₁) :
    ∃ π' : LSPath P b lam, ∀ f : M →+ V, π'.toPLPath 𝕜 f = PLPath.ofSegments 𝕜
      ((List.range (π.length + 1 + 1)).map fun n ↦
        ((lowerTime π k₁ t₁ (n + 1) - lowerTime π k₁ t₁ n : ℚ) : 𝕜) •
          f (lowerDir π i k₀ k₁ n • lam)) := by
  refine exists_toPLPath_eq_ofSegments (fun n hn ↦ ?_) ?_ ?_ (fun n hn ↦ ?_)
    (lower_chain π hlam i H hH hk₀₁ hk₁ hz hleast hrise ht₁)
  · -- The reflected directions are minimal coset representatives, off the wall of `αᵢ`.
    rcases lt_or_ge n k₀ with h₀ | h₀
    · rw [lowerDir_of_lt h₀]
      exact π.isMinimalCosetRep_natDir n
    rcases lt_or_ge n k₁ with h₁ | h₁
    · rw [lowerDir_of_le_of_lt h₀ h₁]
      refine isMinimalCosetRep_simple_mul_of_coroot'_ne_zero (π.isMinimalCosetRep_natDir n)
        fun hc ↦ ?_
      have hr := (hrise n h₀ h₁).1
      rw [hH, hH, Finset.sum_range_succ, hc] at hr
      simp at hr
    · rw [lowerDir_of_le hk₀₁ h₁]
      exact π.isMinimalCosetRep_natDir (n - 1)
  · rw [lowerTime_of_lt (by omega), π.natTime_zero]
  · rw [lowerTime_of_lt' (by omega), Nat.add_sub_cancel, π.natTime_last]
  · -- The times increase weakly: the new break `t₁` lies in the segment `k₁ - 1`.
    have hmono (k : ℕ) (hk : k < π.length + 1) : π.natTime k ≤ π.natTime (k + 1) :=
      (π.natTime_strictMono k hk).le
    rcases lt_trichotomy (n + 1) k₁ with h₁ | h₁ | h₁
    · rw [lowerTime_of_lt (by omega), lowerTime_of_lt h₁]
      exact hmono n (by omega)
    · rw [lowerTime_of_lt (by omega), h₁, lowerTime_self, show n = k₁ - 1 by omega]
      exact ht₁₀
    · rcases (show n = k₁ ∨ k₁ < n by omega) with rfl | h₂
      · rw [lowerTime_self, lowerTime_of_lt' (by omega), Nat.add_sub_cancel]
        exact ht₁₁
      · rw [lowerTime_of_lt' h₂, lowerTime_of_lt' (by omega), Nat.add_sub_cancel]
        have := hmono (n - 1) (by omega)
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at this

omit [P.flip.IsReduced] in
/-- **The lowering of an LS path, computed on its presentation.** With the hypotheses of
`TauCeti.LSPath.lower_chain`, if the height `H k₁` is at least `H k₀ + 1` from `k₁` on and `t₁`
is the time at which the segment `k₁ - 1` reaches the height `H k₀ + 1`, then Littelmann's lowering
operator sends the realization of `π` to the path presented by the lowered break data. -/
private theorem lower_toPLPath_eq (π : LSPath P b lam) (f : M →+ V) (i : b.support)
    {F : Module.Dual 𝕜 V} (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (H : ℕ → ℚ)
    (hH : ∀ j, H j = ∑ k ∈ Finset.range j,
      (π.natTime (k + 1) - π.natTime k) * (P.coroot' i (π.natDir k • lam) : ℚ))
    {k₀ k₁ : ℕ} (hk₀₁ : k₀ < k₁) (hk₁ : k₁ ≤ π.length + 1)
    (hleast : ∀ j ≤ π.length + 1, H k₀ ≤ H j)
    (hrise : ∀ j, k₀ ≤ j → j < k₁ → H j < H (j + 1) ∧ H j < H k₀ + 1)
    (habove : ∀ j, k₁ ≤ j → j ≤ π.length + 1 → H k₀ + 1 ≤ H j) {θ t₁ : ℚ}
    (hθ : θ * (H k₁ - H (k₁ - 1)) = H k₀ + 1 - H (k₁ - 1))
    (ht₁ : t₁ = π.natTime (k₁ - 1) + θ * (π.natTime k₁ - π.natTime (k₁ - 1))) :
    PLPath.lower F (f (P.root i)) (π.toPLPath 𝕜 f) = some (PLPath.ofSegments 𝕜
      ((List.range (π.length + 1 + 1)).map fun n ↦
        ((lowerTime π k₁ t₁ (n + 1) - lowerTime π k₁ t₁ n : ℚ) : 𝕜) •
          f (lowerDir π i k₀ k₁ n • lam))) := by
  set s := π.length + 1
  set L := (List.range s).map fun k ↦
    ((π.natTime (k + 1) - π.natTime k : ℚ) : 𝕜) • f (π.natDir k • lam) with hL
  set j₁ := k₁ - 1 with hj₁
  have hk₁' : j₁ + 1 = k₁ := by omega
  have hHk₁ : H k₁ = H j₁ +
      (π.natTime k₁ - π.natTime j₁) * (P.coroot' i (π.natDir j₁ • lam) : ℚ) := by
    rw [hH, hH, ← hk₁', Finset.sum_range_succ]
  have hrj := hrise j₁ (by omega) (by omega)
  rw [hk₁'] at hrj
  -- The vertex heights of `L` are the heights `H`, with minimum `H k₀`.
  have hFL (j : ℕ) : F (L.take j).sum = (H (min j s) : 𝕜) := by
    rw [hH]
    exact apply_sum_take_map_range f F (P.coroot' i) hF s _ _ j
  have hFLj (j : ℕ) (hj : j ≤ s) : F (L.take j).sum = (H j : 𝕜) := by rw [hFL, min_eq_left hj]
  have hmin : PLPath.listMinHeight F L = (H k₀ : 𝕜) := by
    refine le_antisymm ?_ ?_
    · have := PLPath.listMinHeight_le_apply_sum_take (f := F) L k₀
      rwa [hFLj k₀ (by omega)] at this
    · obtain ⟨m, hm⟩ := PLPath.exists_listMinHeight_eq (f := F) L
      rw [hm, hFL]
      exact_mod_cast hleast _ (Nat.min_le_right _ _)
  have hgetL : L[k₁ - 1]'(by simp [hL]; omega) =
      ((π.natTime k₁ - π.natTime j₁ : ℚ) : 𝕜) • f (π.natDir j₁ • lam) := by
    simp only [hL, List.getElem_map, List.getElem_range, Nat.sub_add_cancel (by omega : 1 ≤ k₁)]
    rw [hj₁]
  -- Littelmann's lowering of `L` reflects the rising piece from `k₀` to the cut in `k₁ - 1`.
  rw [π.toPLPath_eq_ofSegments_natDir f, PLPath.lower_ofSegments_eq_of_strictly_rising
    (θ := (θ : 𝕜)) hk₀₁ (by simp; omega)
    (by rw [hmin, hFLj k₀ (by omega)])
    (fun j h₀ h₁ ↦ by
      rw [hFLj j (by omega), hFLj (j + 1) (by omega)]
      exact_mod_cast (hrise j h₀ h₁).1)
    (by
      rw [hFLj _ (by omega), hgetL, map_smul, hF, hmin, smul_eq_mul]
      have : H j₁ + θ * ((π.natTime k₁ - π.natTime j₁) *
          (P.coroot' i (π.natDir j₁ • lam) : ℚ)) = H k₀ + 1 := by
        linear_combination hθ - θ * hHk₁
      exact_mod_cast this)
    (by
      rw [hFLj _ (by omega), hmin]
      exact_mod_cast hrj.2.le)
    (fun j hj ↦ by
      rw [hFL, hmin]
      exact_mod_cast habove _ (le_min hj hk₁) (Nat.min_le_right _ _))]
  -- The lowered presentation is the presentation of the lowered break data.
  congr 2
  refine (lowered_eq_map_range (Module.preReflection (f (P.root i)) F) (θ : 𝕜) hk₀₁ hk₁
    (fun n hn ↦ ?_) (fun n h₀ h₁ ↦ ?_) ?_ ?_ (fun n hn ↦ ?_) (by simp; omega))
  · rw [lowerTime_of_lt (by omega), lowerTime_of_lt (by omega), lowerDir_of_lt hn]
  · rw [lowerTime_of_lt (by omega), lowerTime_of_lt (by omega),
      lowerDir_of_le_of_lt h₀ (by omega), simple_mul_smul_eq_reflection,
      P.map_reflection_eq_preReflection i hF, LinearMap.map_smul]
  · rw [hk₁', lowerTime_self, lowerTime_of_lt (by omega),
      lowerDir_of_le_of_lt (by omega) (by omega), simple_mul_smul_eq_reflection,
      P.map_reflection_eq_preReflection i hF, LinearMap.map_smul, LinearMap.map_smul, smul_smul]
    congr 1
    push_cast [ht₁]
    ring
  · rw [lowerTime_of_lt' (by omega), Nat.add_sub_cancel, lowerTime_self,
      lowerDir_of_le hk₀₁ le_rfl, hk₁', smul_smul]
    congr 1
    push_cast [ht₁]
    ring
  · rw [lowerTime_of_lt' (by omega), Nat.add_sub_cancel, lowerTime_of_lt' hn,
      lowerDir_of_le hk₀₁ hn.le, Nat.sub_add_cancel (by omega : 1 ≤ n)]

/-- **Littelmann's lowering operator preserves LS paths.** Let `π` be an LS path of dominant shape
`λ`, realized in `V` by `f`, and let `F` be a form on `V` inducing the simple coroot pairing
`⟨-, αᵢ^∨⟩`. If the lowering operator `f_{αᵢ}` along the realized simple root `f αᵢ` is defined
on `π`, then `f_{αᵢ} π` is the realization of an LS path of shape `λ`. Its directions are those
of `π` with the directions `τ` of the lowered piece replaced by `sᵢ τ`. -/
theorem exists_toPLPath_eq_of_lower_eq_some (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (i : b.support) {F : Module.Dual 𝕜 V}
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {q : PLPath 𝕜 V}
    (hq : PLPath.lower F (f (P.root i)) (π.toPLPath 𝕜 f) = some q) :
    ∃ π' : LSPath P b lam, π'.toPLPath 𝕜 f = q := by
  set s := π.length + 1
  set H : ℕ → ℚ := fun j ↦ ∑ k ∈ Finset.range j,
    (π.natTime (k + 1) - π.natTime k) * (P.coroot' i (π.natDir k • lam) : ℚ) with hH
  -- The final height exceeds the minimal height by at least one.
  have hgap : ∃ j ≤ s, H j + 1 ≤ H s := by
    set L := (List.range s).map fun k ↦
      ((π.natTime (k + 1) - π.natTime k : ℚ) : 𝕜) • f (π.natDir k • lam) with hL
    have hFL (j : ℕ) : F (L.take j).sum = (H (min j s) : 𝕜) :=
      apply_sum_take_map_range f F (P.coroot' i) hF s _ _ j
    obtain ⟨m, hm⟩ := PLPath.exists_listMinHeight_eq (f := F) L
    have h1 : ¬F (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight F < 1 := fun h ↦ by
      rw [PLPath.lower_eq_none_iff.mpr h] at hq
      cases hq
    have hπ : π.toPLPath 𝕜 f = PLPath.ofSegments 𝕜 L := π.toPLPath_eq_ofSegments_natDir f
    rw [hπ, PLPath.endpoint_ofSegments, PLPath.minHeight_ofSegments, hm, hFL,
      ← List.take_length (l := L), hFL, show L.length = s by simp [hL], min_self] at h1
    have h2 : ((H (min m s) + 1 : ℚ) : 𝕜) ≤ (H s : 𝕜) := by
      push_cast
      linarith [not_lt.mp h1]
    exact ⟨min m s, Nat.min_le_right _ _, by exact_mod_cast h2⟩
  -- The rising piece: the last vertex `k₀` of minimal height, an integer, and the first vertex
  -- `k₁` after it of height at least `H k₀ + 1`.
  have hs₁ : ∃ z : ℤ, π.natTime s = z := ⟨1, by rw [π.natTime_last, Int.cast_one]⟩
  obtain ⟨k₀, k₁, hk₀₁, hk₁, hleast, hrise, habove⟩ := exists_strictly_rising_of_isAChain hlam
    π.natTime_zero π.natDir_chain π.natTime_strictMono hs₁ i hgap
  obtain ⟨z, hz⟩ := exists_isLeast_sum_coroot'_eq_intCast_of_isAChain hlam π.natTime_zero
    π.natDir_chain π.natTime_strictMono hs₁ i
  have hleast' (j : ℕ) (hj : j ≤ s) : H k₀ ≤ H j := hleast.2 ⟨j, hj, rfl⟩
  -- The segment `j₁ = k₁ - 1`, of duration `d`, reaches the height `H k₀ + 1` after the
  -- fraction `θ` of it, at the time `t₁`.
  set j₁ := k₁ - 1
  have hk₁' : j₁ + 1 = k₁ := by omega
  have hHk₁ : H k₁ = H j₁ +
      (π.natTime k₁ - π.natTime j₁) * (P.coroot' i (π.natDir j₁ • lam) : ℚ) := by
    rw [← hk₁']
    simp only [hH, Finset.sum_range_succ]
  have hrj := hrise j₁ (by omega) (by omega)
  rw [hk₁'] at hrj
  have hab := habove k₁ le_rfl hk₁
  set θ : ℚ := (H k₀ + 1 - H j₁) / (H k₁ - H j₁)
  have hθmul : θ * (H k₁ - H j₁) = H k₀ + 1 - H j₁ := div_mul_cancel₀ _ (by linarith)
  have hθ₀ : 0 < θ := div_pos (by linarith) (by linarith)
  have hθ₁ : θ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  set d := π.natTime k₁ - π.natTime j₁
  have hd₀ : 0 < d := by
    have := π.natTime_strictMono j₁ (by omega)
    rw [hk₁'] at this
    linarith
  set t₁ := π.natTime j₁ + θ * d with ht₁
  obtain ⟨π', hπ'⟩ := exists_toPLPath_eq_lower (𝕜 := 𝕜) (V := V) π hlam i H (fun _ ↦ rfl) hk₀₁
    hk₁ ⟨z, hleast.unique hz⟩ hleast' hrise (t₁ := t₁) (by rw [← hθmul, hHk₁]; ring)
    (by nlinarith) (by nlinarith)
  refine ⟨π', (hπ' f).trans (Option.some.inj ?_)⟩
  rw [← hq, lower_toPLPath_eq π f i hF H (fun _ ↦ rfl) hk₀₁ hk₁ hleast' hrise habove hθmul ht₁]

end TauCeti.LSPath
