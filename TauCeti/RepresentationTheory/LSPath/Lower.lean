/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Integrality
import TauCeti.Data.List.Range
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
  have h1 : 1 ≤ F (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight F := not_lt.mp fun h ↦ by
    rw [PLPath.lower_eq_none_iff.mpr h] at hq
    cases hq
  -- The rising piece: the last vertex `k₀` of minimal height, an integer, and the first vertex
  -- `k₁` after it of height at least `H k₀ + 1`, reached after the fraction `θ` of the segment
  -- `j₁ = k₁ - 1`, of duration `d`, at the time `t₁`.
  obtain ⟨k₀, k₁, θ, hk₀₁, hk₁, hθ₀, hθ₁, hleast, hrise, habove, hθmul, hlow⟩ :=
    exists_lower_toPLPath_eq π hlam f i F hF (f (P.root i)) H (fun _ ↦ rfl) h1
  obtain ⟨z, hz⟩ := exists_isLeast_sum_coroot'_eq_intCast_of_isAChain hlam π.natTime_zero
    π.natDir_chain π.natTime_strictMono ⟨1, by rw [π.natTime_last, Int.cast_one]⟩ i
  have hleast' (j : ℕ) (hj : j ≤ s) : H k₀ ≤ H j := hleast.2 ⟨j, hj, rfl⟩
  set j₁ := k₁ - 1
  have hk₁' : j₁ + 1 = k₁ := by omega
  have hHk₁ : H k₁ = H j₁ +
      (π.natTime k₁ - π.natTime j₁) * (P.coroot' i (π.natDir j₁ • lam) : ℚ) := by
    rw [← hk₁']
    simp only [hH, Finset.sum_range_succ]
  set d := π.natTime k₁ - π.natTime j₁ with hd
  have hd₀ : 0 < d := by
    have := π.natTime_strictMono j₁ (by omega)
    rw [hk₁'] at this
    linarith
  set t₁ := π.natTime j₁ + θ * d with ht₁
  obtain ⟨π', hπ'⟩ := exists_toPLPath_eq_lower (𝕜 := 𝕜) (V := V) π hlam i H (fun _ ↦ rfl) hk₀₁
    hk₁ ⟨z, hleast.unique hz⟩ hleast' hrise (t₁ := t₁) (by rw [← hθmul, hHk₁]; ring)
    (by nlinarith) (by nlinarith)
  refine ⟨π', (hπ' f).trans ?_⟩
  -- The lowered presentation is the presentation of the lowered break data.
  rw [← Option.some.inj (hlow.symm.trans hq), π.map_snd_timed f]
  congr 1
  refine (List.take_append_map_append_cons_drop_map_range
    (Module.preReflection (f (P.root i)) F) _ _ hk₀₁ hk₁ (fun n hn ↦ ?_) (fun n h₀ h₁ ↦ ?_) ?_ ?_
    (fun n hn _ ↦ ?_)).symm
  · rw [lowerTime_of_lt (by omega), lowerTime_of_lt (by omega), lowerDir_of_lt hn]
  · rw [lowerTime_of_lt (by omega), lowerTime_of_lt (by omega),
      lowerDir_of_le_of_lt h₀ (by omega), simple_mul_smul_eq_reflection,
      P.map_reflection_eq_preReflection i hF, LinearMap.map_smul]
  · rw [hk₁', lowerTime_self, lowerTime_of_lt (by omega),
      lowerDir_of_le_of_lt (by omega) (by omega), simple_mul_smul_eq_reflection,
      P.map_reflection_eq_preReflection i hF, LinearMap.map_smul, ht₁, add_sub_cancel_left]
  · rw [lowerTime_of_lt' (by omega), Nat.add_sub_cancel, lowerTime_self,
      lowerDir_of_le hk₀₁ le_rfl, ht₁, hd]
    congr 2
    ring
  · rw [lowerTime_of_lt' (by omega), Nat.add_sub_cancel, lowerTime_of_lt' hn,
      lowerDir_of_le hk₀₁ hn.le, Nat.sub_add_cancel (by omega : 1 ≤ n)]

end TauCeti.LSPath
