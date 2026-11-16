/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Integrality
import TauCeti.RepresentationTheory.LSPath.Concatenation
import TauCeti.RepresentationTheory.LSPath.Linked
import TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectedChain
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Ray

/-!
# Littelmann's raising operator preserves Lakshmibai–Seshadri paths

For an LS path `π` of dominant shape `λ` and a simple root `αᵢ` with minimum height `h ≤ -1`,
`e_αᵢ` reflects by `sᵢ` the falling piece from the cut at `h + 1` to the first minimum
(`TauCeti.LSPath.exists_raise_toPLPath_eq`). The reflected list stays `TauCeti.LSPath.Linked`, so
`TauCeti.LSPath.ofLinked` gives a realization-independent LS path realizing `e_αᵢ π`
(`TauCeti.LSPath.raise_toPLPath_eq_none_and_eq_none_or_exists_eq_some`,
`TauCeti.LSPath.exists_toPLPath_eq_of_raise_eq_some`).

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Sections 1 and 4.
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}

private theorem Linked.mapIdx_simple_mul_neg (hlam : lam ∈ dominantChamber P b) {t : ℚ}
    {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam t l)
    (hmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (i : b.support) {k₀ j₁ : ℕ} (hk₀ : 0 < k₀) (hk₀j₁ : k₀ ≤ j₁) (hj₁ : j₁ < l.length)
    (hneg : ∀ k (hk : k < l.length), k₀ ≤ k → k ≤ j₁ → P.coroot' i (l[k].1 • lam) < 0)
    (hint : ∀ k (hk : k < l.length), k₀ ≤ k → k < j₁ →
      ¬∃ z : ℤ, (t + ((l.take (k + 1)).map Prod.snd).sum) * P.coroot' i (l[k].1 • lam) = z)
    (hright : ∀ k (hk : k < l.length), j₁ + 1 = k → 0 ≤ P.coroot' i (l[k].1 • lam))
    (hcut : (l[k₀ - 1]'(by omega)).1 = (l[k₀]'(by omega)).1)
    (hcutint : ∃ z : ℤ,
      (t + ((l.take k₀).map Prod.snd).sum) * P.coroot' i ((l[k₀]'(by omega)).1 • lam) = z) :
    Linked P b lam t (l.mapIdx fun k p ↦
      if k₀ ≤ k ∧ k ≤ j₁ then ((weylCoxeterSystem P b).simple i * p.1, p.2) else p) := by
  set g : ℕ → P.weylGroup × ℚ → P.weylGroup × ℚ := fun k p ↦
    if k₀ ≤ k ∧ k ≤ j₁ then ((weylCoxeterSystem P b).simple i * p.1, p.2) else p
  have hsnd : (l.mapIdx g).map Prod.snd = l.map Prod.snd :=
    List.ext_getElem (by simp) fun k _ _ ↦ by
      simp only [g, List.getElem_map, List.getElem_mapIdx]; split_ifs <;> rfl
  rw [linked_iff_getElem] at hl ⊢
  intro k hk
  have hk' : k + 1 < l.length := by simpa using hk
  rw [List.map_take, hsnd, ← List.map_take]
  obtain ⟨C, hhead, hlast, hC⟩ := hl k hk'
  simp only [List.getElem_mapIdx, g]
  by_cases hk₁ : k₀ ≤ k ∧ k ≤ j₁ <;> by_cases hk₂ : k₀ ≤ k + 1 ∧ k + 1 ≤ j₁ <;>
    simp only [hk₁, hk₂, and_self, ↓reduceIte]
  · have hall := hC.coroot'_smul_neg hlam i (by rw [hhead]; exact hneg k (by omega) hk₁.1 hk₁.2)
      (by rw [hhead]; exact hint k (by omega) hk₁.1 (by omega))
    exact ⟨_root_.CoxeterSystem.MinimalCosetRepChain.simpleMul hlam C i (Or.inr hall),
      by simp [hhead], by simp [hlast],
      _root_.CoxeterSystem.MinimalCosetRepChain.isAChain_simpleMul_iff.mpr hC⟩
  · obtain ⟨D, hDh, hDl, hD⟩ := hC.exists_isAChain_simple_mul_head hlam i
      (by rw [hhead]; exact hneg k (by omega) hk₁.1 hk₁.2)
      (by rw [hlast]; exact hright (k + 1) hk' (by omega))
    exact ⟨D, by rw [hDh, hhead], by rw [hDl, hlast], hD⟩
  · obtain rfl : k₀ = k + 1 := by omega
    have hneg1 := hneg (k + 1) hk' le_rfl hk₂.2
    set u := (weylCoxeterSystem P b).simple i * l[k + 1].1
    have hu : P.coroot' i (u • lam) = -P.coroot' i (l[k + 1].1 • lam) := by
      rw [simple_mul_smul_eq_reflection, coroot'_reflection_self]
    have hu_int : ∃ z : ℤ,
        (t + ((l.take (k + 1)).map Prod.snd).sum) * P.coroot' i (u • lam) = z := by
      obtain ⟨z, hz⟩ := hcutint; exact ⟨-z, by rw [hu]; push_cast; linear_combination -hz⟩
    obtain ⟨D, hDh, hDl, hD⟩ := exists_isAChain_simple_mul_of_coroot'_pos hlam
      (isMinimalCosetRep_simple_mul_of_coroot'_ne_zero (hmin _ (List.getElem_mem hk')) hneg1.ne)
      (hu ▸ neg_pos.mpr hneg1) hu_int
    exact ⟨D, by rw [hDh, (weylCoxeterSystem P b).simple_mul_simple_cancel_left]; exact hcut.symm,
      hDl, hD⟩
  · exact ⟨C, hhead, hlast, hC⟩

variable (b) in
private noncomputable def raiseList (i : b.support) (l : List (P.weylGroup × ℚ)) (j₀ k₁ : ℕ)
    (τ : P.weylGroup) (d θ : ℚ) : List (P.weylGroup × ℚ) :=
  (l.take j₀ ++ [(τ, θ * d)]) ++
    ((τ, (1 - θ) * d) :: (l.take k₁).drop (j₀ + 1)).map
      (fun p ↦ ((weylCoxeterSystem P b).simple i * p.1, p.2)) ++ l.drop k₁

private theorem nonneg_of_mem_raiseList (i : b.support) {l : List (P.weylGroup × ℚ)}
    (hl : ∀ p ∈ l, 0 ≤ p.2) {j₀ k₁ : ℕ} {τ : P.weylGroup} {d θ : ℚ} (hd : 0 ≤ d) (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ ≤ 1) {p : P.weylGroup × ℚ} (hp : p ∈ raiseList b i l j₀ k₁ τ d θ) : 0 ≤ p.2 := by
  simp only [raiseList, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with ((hp | rfl) | ⟨q, rfl | hq, rfl⟩) | hp
  · exact hl p (List.mem_of_mem_take hp)
  · exact mul_nonneg hθ₀ hd
  · exact mul_nonneg (sub_nonneg.mpr hθ₁) hd
  · exact hl q (List.mem_of_mem_take (List.mem_of_mem_drop hq))
  · exact hl p (List.mem_of_mem_drop hp)

private theorem sum_map_snd_raiseList (i : b.support) {l : List (P.weylGroup × ℚ)} {j₀ k₁ : ℕ}
    (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ ≤ l.length) (θ : ℚ) :
    ((raiseList b i l j₀ k₁ (l[j₀]'(by omega)).1 (l[j₀]'(by omega)).2 θ).map Prod.snd).sum =
      (l.map Prod.snd).sum := by
  have hj₀_tk : j₀ < (l.take k₁).length := by simp; omega
  conv_rhs => rw [← List.take_append_drop k₁ l, ← List.take_append_drop j₀ (l.take k₁),
    List.take_take, min_eq_left (by omega), List.drop_eq_getElem_cons hj₀_tk, List.getElem_take]
  simp only [raiseList, List.map_append, List.map_cons, List.map_map, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Function.comp_def]
  ring

private theorem linked_raiseList (hlam : lam ∈ dominantChamber P b)
    {l : List (P.weylGroup × ℚ)} (hl : Linked P b lam 0 l)
    (hlmin : ∀ p ∈ l, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1)
    (i : b.support) {j₀ k₁ : ℕ} (hj₀k₁ : j₀ < k₁) (hk₁ : k₁ ≤ l.length) (θ : ℚ)
    (hneg : ∀ k (hk : k < l.length), j₀ ≤ k → k < k₁ → P.coroot' i (l[k].1 • lam) < 0)
    (hint : ∀ k (hk : k < l.length), j₀ < k → k < k₁ →
      ¬∃ m : ℤ, ((l.take k).map Prod.snd).sum * P.coroot' i ((l[k - 1]'(by omega)).1 • lam) = m)
    (hright : ∀ (hk : k₁ < l.length), 0 ≤ P.coroot' i (l[k₁].1 • lam))
    (hcut : ∃ m : ℤ, (((l.take j₀).map Prod.snd).sum + θ * (l[j₀]'(by omega)).2) *
      P.coroot' i ((l[j₀]'(by omega)).1 • lam) = m) :
    Linked P b lam 0 (raiseList b i l j₀ k₁ (l[j₀]'(by omega)).1 (l[j₀]'(by omega)).2 θ) ∧
      ∀ p ∈ raiseList b i l j₀ k₁ (l[j₀]'(by omega)).1 (l[j₀]'(by omega)).2 θ,
        (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1 := by
  have hj₀ : j₀ < l.length := by omega
  set τ := l[j₀].1; set d := l[j₀].2; set s := (weylCoxeterSystem P b).simple i
  have hτmin := hlmin _ (List.getElem_mem hj₀)
  set Dp := l.take j₀ ++ (τ, θ * d) :: (τ, (1 - θ) * d) :: l.drop (j₀ + 1) with hDp
  have hDp_linked : Linked P b lam 0 Dp :=
    Linked.split hτmin (by
      rwa [show θ * d + (1 - θ) * d = d by ring, ← List.drop_eq_getElem_cons hj₀,
        List.take_append_drop])
  have hDpmin (p) (hp : p ∈ Dp) :
      (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) p.1 := by
    simp only [Dp, List.mem_append, List.mem_cons] at hp
    rcases hp with hp | rfl | rfl | hp <;>
      first | exact hτmin | exact hlmin p (List.mem_of_mem_take hp) |
        exact hlmin p (List.mem_of_mem_drop hp)
  have hlen_take : (l.take j₀).length = j₀ := by simp; omega
  have hDp_len : Dp.length = l.length + 1 := by simp [Dp]; omega
  have hDp_j₀ : Dp[j₀]'(by omega) = (τ, θ * d) := by
    simp only [Dp]; rw [List.getElem_append_right (by omega)]; simp [hlen_take]
  have hDp_j₀1 : Dp[j₀ + 1]'(by omega) = (τ, (1 - θ) * d) := by
    simp only [Dp]; rw [List.getElem_append_right (by omega)]; simp [hlen_take]
  have hDp_gt (k : ℕ) (hk : k < Dp.length) (hkj : j₀ + 1 < k) :
      Dp[k] = l[k - 1]'(by omega) := by
    obtain ⟨r, rfl⟩ : ∃ r, k = j₀ + 2 + r := ⟨k - j₀ - 2, by omega⟩
    simp only [Dp]; rw [List.getElem_append_right (by omega)]
    simp only [hlen_take, show j₀ + 2 + r - j₀ = r + 2 by omega, List.getElem_cons_succ,
      List.getElem_drop]; congr 1; omega
  have hDp_fst_ge (k : ℕ) (hk : k < Dp.length) (hkj : j₀ + 1 ≤ k) :
      Dp[k].1 = (l[k - 1]'(by omega)).1 := by
    rcases hkj.eq_or_lt with rfl | hkj
    · simp [hDp_j₀1, τ]
    · rw [hDp_gt k hk hkj]
  have hcum_j₀1 : ((Dp.take (j₀ + 1)).map Prod.snd).sum =
      ((l.take j₀).map Prod.snd).sum + θ * d := by
    simp only [Dp]; rw [List.take_append, List.take_of_length_le (by omega), hlen_take,
      show j₀ + 1 - j₀ = 1 by omega]; simp
  have hcum_ge (k : ℕ) (hkj : j₀ + 1 ≤ k) :
      ((Dp.take (k + 1)).map Prod.snd).sum = ((l.take k).map Prod.snd).sum := by
    have hsplit : l.take k = l.take j₀ ++ l[j₀] :: (l.drop (j₀ + 1)).take (k - (j₀ + 1)) := by
      conv_lhs => rw [show k = j₀ + (k - j₀) by omega, List.take_add,
        List.drop_eq_getElem_cons hj₀, show k - j₀ = (k - (j₀ + 1)) + 1 by omega,
        List.take_succ_cons]
    simp only [Dp]; rw [List.take_append, List.take_of_length_le (by omega), hlen_take,
      show k + 1 - j₀ = (k - (j₀ + 1)) + 2 by omega]
    simp only [List.take_succ_cons, hsplit, List.map_append, List.map_cons,
      List.sum_append, List.sum_cons, d]; ring
  have hW := Linked.mapIdx_simple_mul_neg hlam hDp_linked hDpmin i (k₀ := j₀ + 1) (j₁ := k₁)
    (by omega) (by omega) (by omega)
    (fun k hk hkj hkk₁ ↦ by
      rw [hDp_fst_ge k hk hkj]; exact hneg (k - 1) (by omega) (by omega) (by omega))
    (fun k hk hkj hkk₁ ↦ by
      rw [zero_add, hcum_ge k hkj, hDp_fst_ge k hk hkj]; exact hint k (by omega) (by omega) hkk₁)
    (fun k hk hkk ↦ by subst hkk; rw [hDp_gt (k₁ + 1) hk (by omega)]; exact hright (by omega))
    (by simp only [Nat.add_sub_cancel, hDp_j₀, hDp_j₀1])
    (by rw [zero_add, hcum_j₀1, hDp_j₀1]; exact hcut)
  have hraise : raiseList b i l j₀ k₁ τ d θ =
      Dp.mapIdx fun k p ↦ if j₀ + 1 ≤ k ∧ k ≤ k₁ then (s * p.1, p.2) else p := by
    have hDp' : Dp = (l.take j₀ ++ [(τ, θ * d)]) ++
        ((τ, (1 - θ) * d) :: (l.take k₁).drop (j₀ + 1)) ++ l.drop k₁ := by
      rw [hDp, show l.drop (j₀ + 1) = (l.take k₁).drop (j₀ + 1) ++ l.drop k₁ by
        conv_lhs => rw [← List.take_append_drop k₁ l]
        rw [List.drop_append_of_le_length (by simp; omega)]]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    have hA : (l.take j₀ ++ [(τ, θ * d)]).length = j₀ + 1 := by simp; omega
    have hB : ((τ, (1 - θ) * d) :: (l.take k₁).drop (j₀ + 1)).length = k₁ - j₀ := by simp; omega
    rw [hDp']
    refine List.ext_getElem (by simp [raiseList]) fun k _ _ ↦ ?_
    simp only [raiseList, List.getElem_mapIdx, List.getElem_append, List.getElem_map,
      List.length_append, List.length_map, hA, hB]
    split_ifs <;> first | rfl | omega
  rw [hraise]
  refine ⟨hW, fun p hp ↦ ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  have hk' : k < Dp.length := by simpa using hk
  rw [List.getElem_mapIdx]; split_ifs with hw
  · refine isMinimalCosetRep_simple_mul_of_coroot'_ne_zero (hDpmin _ (List.getElem_mem hk')) ?_
    rw [hDp_fst_ge k hk' hw.1]; exact (hneg (k - 1) (by omega) (by omega) (by omega)).ne
  · exact hDpmin _ (List.getElem_mem hk')

section Realization

private theorem preReflection_smul_apply {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (d : 𝕜) (w : P.weylGroup) :
    Module.preReflection (f (P.root i)) F (d • f (w • lam)) =
      d • f (((weylCoxeterSystem P b).simple i * w) • lam) := by
  rw [map_smul, ← P.map_reflection_eq_preReflection i hF, simple_mul_smul_eq_reflection]

private theorem apply_take_sum_dirDurations {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (π : LSPath P b lam) (f : M →+ V) (i : b.support)
    (F : Module.Dual 𝕜 V) (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (k : ℕ) :
    F (((π.dirDurations.map fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)).take k)).sum =
      ((((π.dirDurations.take k).map fun p ↦
        p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum : ℚ) : 𝕜) := by
  simp only [← List.map_take, map_list_sum, List.map_map, Rat.cast_list_sum]
  exact congrArg List.sum (List.map_congr_left fun p _ ↦ by simp [hF])

private theorem raise_toPLPath_eq_some_of_raiseList {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] (π : LSPath P b lam) (f : M →+ V)
    (i : b.support) (F : Module.Dual 𝕜 V) (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜))
    {z : ℤ} (hz : (π.toPLPath 𝕜 f).minHeight F = z)
    {j₀ k₁ : ℕ} (hj₀lt : j₀ < π.dirDurations.length) (hj₀k₁ : j₀ < k₁)
    (hk₁D : k₁ ≤ π.dirDurations.length) {τ : P.weylGroup} {d θ : ℚ}
    (hDj₀ : π.dirDurations[j₀] = (τ, d)) {hgt : ℕ → ℚ}
    (hhgt : ∀ k, hgt k =
      ((π.dirDurations.take k).map fun p ↦ p.2 * (P.coroot' i (p.1 • lam) : ℚ)).sum)
    (habove' : ∀ k ≤ j₀, (z : ℚ) + 1 ≤ hgt k)
    (hfall' : ∀ k, j₀ ≤ k → k < k₁ → hgt (k + 1) < hgt k)
    (hcross' : hgt j₀ + θ * (d * (P.coroot' i (τ • lam) : ℚ)) = z + 1)
    (hHj₀1 : hgt (j₀ + 1) ≤ z + 1) (hgtk₁ : hgt k₁ = z) {π' : LSPath P b lam}
    (hπ' : π'.toPLPath 𝕜 f = PLPath.ofSegments 𝕜
      ((raiseList b i π.dirDurations j₀ k₁ (π.dirDurations[j₀]).1 (π.dirDurations[j₀]).2 θ).map
        fun p ↦ (p.2 : 𝕜) • f (p.1 • lam))) :
    PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some (π'.toPLPath 𝕜 f) := by
  set D := π.dirDurations
  set seg : P.weylGroup × ℚ → V := fun p ↦ (p.2 : 𝕜) • f (p.1 • lam)
  have hHF (k : ℕ) : F ((D.map seg).take k).sum = (hgt k : 𝕜) := by
    rw [hhgt]; exact apply_take_sum_dirDurations π f i F hF k
  have hminF : PLPath.listMinHeight F (D.map seg) = (z : 𝕜) := by
    rwa [toPLPath_def, PLPath.minHeight_ofSegments, map_snd_timed] at hz
  have hDj₀_seg : (D.map seg)[j₀]'(by rw [List.length_map]; exact hj₀lt) =
      (d : 𝕜) • f (τ • lam) := by simp [seg, D, hDj₀]
  rw [toPLPath_def, map_snd_timed, PLPath.raise_ofSegments_eq_of_strictly_falling
    (k₀ := j₀) (k₁ := k₁) (θ := (θ : 𝕜)) hj₀k₁ (by rw [List.length_map]; exact hk₁D)]
  · rw [hπ']; congr 2
    have hσ (p : P.weylGroup × ℚ) :
        (p.2 : 𝕜) • f (((weylCoxeterSystem P b).simple i * p.1) • lam) =
          Module.preReflection (f (P.root i)) F (seg p) :=
      (preReflection_smul_apply f i F hF _ _).symm
    rw [show D[j₀] = (τ, d) from hDj₀]
    simp only [raiseList, seg, D, hDj₀_seg, List.map_append, List.map_cons, List.map_nil,
      List.map_map, List.map_take, List.map_drop, Function.comp_def, hσ, smul_smul,
      Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
    rw [preReflection_smul_apply f i F hF]
  · intro k hkj; rw [hminF, hHF]; exact_mod_cast habove' k hkj
  · intro k hjk hkk₁; rw [hHF, hHF, Rat.cast_lt]; exact hfall' k hjk hkk₁
  · rw [hminF, hHF, hDj₀_seg, map_smul, hF, smul_eq_mul]; exact_mod_cast hcross'
  · rw [hminF, hHF]; exact_mod_cast hHj₀1
  · rw [hminF, hHF]; exact_mod_cast hgtk₁

/-- **Realization-independent action of Littelmann's raising operator on LS encodings.** -/
theorem raise_toPLPath_eq_none_and_eq_none_or_exists_eq_some {𝕜₁ V₁ 𝕜₂ V₂ : Type*}
    [Field 𝕜₁] [LinearOrder 𝕜₁] [IsStrictOrderedRing 𝕜₁] [AddCommGroup V₁] [Module 𝕜₁ V₁]
    [Field 𝕜₂] [LinearOrder 𝕜₂] [IsStrictOrderedRing 𝕜₂] [AddCommGroup V₂] [Module 𝕜₂ V₂]
    (π : LSPath P b lam) (hlam : lam ∈ dominantChamber P b) (i : b.support)
    (f₁ : M →+ V₁) (F₁ : Module.Dual 𝕜₁ V₁) (hF₁ : ∀ m, F₁ (f₁ m) = (P.coroot' i m : 𝕜₁))
    (f₂ : M →+ V₂) (F₂ : Module.Dual 𝕜₂ V₂) (hF₂ : ∀ m, F₂ (f₂ m) = (P.coroot' i m : 𝕜₂)) :
    (PLPath.raise F₁ (f₁ (P.root i)) (π.toPLPath 𝕜₁ f₁) = none ∧
        PLPath.raise F₂ (f₂ (P.root i)) (π.toPLPath 𝕜₂ f₂) = none) ∨
      ∃ π' : LSPath P b lam,
        PLPath.raise F₁ (f₁ (P.root i)) (π.toPLPath 𝕜₁ f₁) = some (π'.toPLPath 𝕜₁ f₁) ∧
          PLPath.raise F₂ (f₂ (P.root i)) (π.toPLPath 𝕜₂ f₂) = some (π'.toPLPath 𝕜₂ f₂) := by
  let f₀ : M →+ ℚ := (Int.castAddHom ℚ).comp (P.coroot' i).toAddMonoidHom
  let F₀ : Module.Dual ℚ ℚ := LinearMap.id
  have hF₀ : ∀ m, F₀ (f₀ m) = (P.coroot' i m : ℚ) := fun _ ↦ rfl
  obtain ⟨z, hz, hz₁⟩ := π.exists_minHeight_eq_intCast_and_eq_intCast hlam i f₀ F₀ hF₀ f₁ F₁ hF₁
  obtain ⟨z', hz', hz₂⟩ := π.exists_minHeight_eq_intCast_and_eq_intCast hlam i f₀ F₀ hF₀ f₂ F₂ hF₂
  obtain rfl : z = z' := Int.cast_injective (hz.symm.trans hz')
  by_cases h1₀ : 1 ≤ -(π.toPLPath ℚ f₀).minHeight F₀
  · right
    obtain ⟨j₀', k₁, θ, hj₀k₁, hk₁len, hθ₀, hθ₁, habove₀, hcross₀, hfall₀, hmin₀, -⟩ :=
      π.exists_raise_toPLPath_eq hlam f₀ i F₀ hF₀ (f₀ (P.root i)) h1₀
    rw [map_snd_timed] at habove₀ hcross₀ hfall₀ hmin₀
    simp only [Rat.cast_id] at habove₀ hcross₀ hfall₀ hmin₀
    set D := π.dirDurations; set H : P.weylGroup → ℚ := fun w ↦ (P.coroot' i (w • lam) : ℚ)
    set hgt : ℕ → ℚ := fun k ↦ ((D.take k).map fun p ↦ p.2 * H p.1).sum
    set cum : ℕ → ℚ := fun k ↦ ((D.take k).map Prod.snd).sum; set j₀ : ℕ := (j₀' : ℕ)
    have hj₀lt : j₀ < D.length := length_dirDurations π ▸ j₀'.2
    have hk₁D : k₁ ≤ D.length := length_dirDurations π ▸ hk₁len
    set τ := (π.dir j₀').1; set d := π.duration j₀'
    have hDj₀ : D[j₀] = (τ, d) := by rw [getElem_dirDurations]
    have hdpos (k : ℕ) (hk : k < D.length) : 0 < D[k].2 := by
      rw [getElem_dirDurations]; exact π.duration_pos _
    have hHF₀ (k : ℕ) : F₀ ((D.map fun p ↦ p.2 • f₀ (p.1 • lam)).take k).sum = hgt k := by
      simpa only [Rat.cast_id] using apply_take_sum_dirDurations π f₀ i F₀ hF₀ k
    have hgt_succ (k : ℕ) (hk : k < D.length) : hgt (k + 1) = hgt k + D[k].2 * H D[k].1 := by
      simp only [hgt, List.map_take]
      rw [List.sum_take_succ _ _ (by simpa using hk), List.getElem_map]
    have hcum_succ (k : ℕ) (hk : k < D.length) : cum (k + 1) = cum k + D[k].2 := by
      simp only [cum, List.map_take]
      rw [List.sum_take_succ _ _ (by simpa using hk), List.getElem_map]
    have hgtk₁ : hgt k₁ = z := by rwa [hHF₀, hz] at hmin₀
    have hfall' (k : ℕ) (hjk : j₀ ≤ k) (hkk₁ : k < k₁) : hgt (k + 1) < hgt k := by
      simpa only [hHF₀] using hfall₀ k hjk hkk₁
    have habove' (k) (hkj : k ≤ j₀) : (z : ℚ) + 1 ≤ hgt k := by
      have h := habove₀ k hkj; rwa [hz, hHF₀] at h
    have hcross' : hgt j₀ + θ * (d * H τ) = z + 1 := by
      have h := hcross₀; rwa [hHF₀, hz, map_smul, smul_eq_mul, hF₀] at h
    have hnegH (k : ℕ) (hk : k < D.length) (hjk : j₀ ≤ k) (hkk₁ : k < k₁) : H D[k].1 < 0 := by
      have := hfall' k hjk hkk₁; rw [hgt_succ k hk] at this
      exact neg_of_mul_neg_right (by linarith) (hdpos k hk).le
    have hmono (m : ℕ) : ∀ k, j₀ ≤ k → k + m ≤ k₁ → hgt (k + m) ≤ hgt k :=
      Nat.rec (by simp) (fun m ih k hjk hkm ↦
        (hfall' (k + m) (by omega) (by omega)).le.trans (ih k hjk (by omega))) m
    have hbetween (k : ℕ) (hjk : j₀ < k) (hkk₁ : k < k₁) : (z : ℚ) < hgt k ∧ hgt k < z + 1 := by
      refine ⟨?_, ?_⟩
      · have h₁ := hfall' (k₁ - 1) (by omega) (by omega)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ k₁), hgtk₁] at h₁
        have h₂ := hmono (k₁ - 1 - k) k (by omega) (by omega)
        rw [show k + (k₁ - 1 - k) = k₁ - 1 by omega] at h₂; linarith
      · have hdH : d * H τ < 0 := mul_neg_of_pos_of_neg (π.duration_pos j₀')
          (by simpa [hDj₀] using hnegH j₀ hj₀lt le_rfl hj₀k₁)
        have h₂ := hmono (k - (j₀ + 1)) (j₀ + 1) (by omega) (by omega)
        rw [show j₀ + 1 + (k - (j₀ + 1)) = k by omega] at h₂
        have := hgt_succ j₀ hj₀lt; rw [hDj₀] at this
        linarith [mul_neg_of_pos_of_neg (show 0 < 1 - θ by linarith) hdH]
    have hrightH (hk : k₁ < D.length) : 0 ≤ H D[k₁].1 := by
      have hle := PLPath.listMinHeight_le_apply_sum_take (f := F₀)
        (D.map fun p ↦ p.2 • f₀ (p.1 • lam)) (k₁ + 1)
      have hz' : PLPath.listMinHeight F₀ (D.map fun p ↦ p.2 • f₀ (p.1 • lam)) = z := by
        simpa [toPLPath_def, PLPath.minHeight_ofSegments, map_snd_timed, D] using hz
      rw [hz', hHF₀, hgt_succ k₁ hk, hgtk₁] at hle
      exact nonneg_of_mul_nonneg_right (by linarith) (hdpos k₁ hk)
    have hcong (k : ℕ) (hk : k < D.length) :=
      π.linked_dirDurations.exists_sum_take_sub_mul_eq_intCast hlam (P.coroot' i) hk
    have hL_data := linked_raiseList hlam π.linked_dirDurations
      (fun _ hp ↦ π.isMinimalCosetRep_of_mem_dirDurations hp) i hj₀k₁ hk₁D θ
      (fun k hk hjk hkk₁ ↦ by dsimp only [H, D] at hnegH; exact_mod_cast hnegH k hk hjk hkk₁)
      (fun k hk hjk hkk₁ ⟨m, hm⟩ ↦ by
        obtain ⟨m', hm'⟩ := hcong (k - 1) (by omega)
        obtain ⟨h₁, h₂⟩ := hbetween k hjk hkk₁
        have hsg := hgt_succ (k - 1) (by omega); have hsc := hcum_succ (k - 1) (by omega)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hsg hsc
        have hk' : hgt k = ((m' + m : ℤ) : ℚ) := by
          simp only [H, cum, D] at hm' hsg hsc ⊢; push_cast
          linear_combination
            hsg - hsc * (P.coroot' i (π.dirDurations[k - 1].1 • lam) : ℚ) + hm' + hm
        have : z < m' + m := by exact_mod_cast hk' ▸ h₁
        have : m' + m < z + 1 := by exact_mod_cast hk' ▸ h₂
        omega)
      (fun hk ↦ by dsimp only [H, D] at hrightH; exact_mod_cast hrightH hk)
      (by
        obtain ⟨m, hm⟩ := hcong j₀ hj₀lt; refine ⟨z + 1 - m, ?_⟩
        rw [hDj₀] at hm ⊢; simp only [H] at hm hcross' ⊢
        push_cast; linear_combination hcross' - hm)
    let π' : LSPath P b lam := ofLinked _ hL_data.2
      (fun _ hp ↦ nonneg_of_mem_raiseList i (fun _ hp ↦ (π.pos_of_mem_dirDurations hp).le)
        (π.pos_of_mem_dirDurations (List.getElem_mem hj₀lt)).le hθ₀ hθ₁.le hp)
      (by rw [sum_map_snd_raiseList i hj₀k₁ hk₁D, sum_map_snd_dirDurations]) hL_data.1
    have hHj₀1 : hgt (j₀ + 1) ≤ z + 1 := by
      rcases (Nat.add_one_le_iff.mpr hj₀k₁).eq_or_lt with heq | hlt
      · rw [heq, hgtk₁]; linarith
      · exact (hbetween (j₀ + 1) (by omega) hlt).2.le
    exact ⟨π',
      raise_toPLPath_eq_some_of_raiseList π f₁ i F₁ hF₁ hz₁ hj₀lt hj₀k₁ hk₁D hDj₀
        (fun _ ↦ rfl) habove' hfall' hcross' hHj₀1 hgtk₁ (toPLPath_ofLinked f₁ _ _ _ _ _),
      raise_toPLPath_eq_some_of_raiseList π f₂ i F₂ hF₂ hz₂ hj₀lt hj₀k₁ hk₁D hDj₀
        (fun _ ↦ rfl) habove' hfall' hcross' hHj₀1 hgtk₁ (toPLPath_ofLinked f₂ _ _ _ _ _)⟩
  · left
    have hlt : (-1 : ℤ) < z := by rw [hz] at h1₀; exact_mod_cast (by linarith : (-1 : ℚ) < z)
    exact ⟨PLPath.raise_eq_none_iff.mpr (by rw [hz₁]; exact_mod_cast hlt),
      PLPath.raise_eq_none_iff.mpr (by rw [hz₂]; exact_mod_cast hlt)⟩

/-- **Littelmann's raising operator preserves Lakshmibai–Seshadri paths.** -/
theorem exists_toPLPath_eq_of_raise_eq_some {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {q : PLPath 𝕜 V}
    (hq : PLPath.raise F (f (P.root i)) (π.toPLPath 𝕜 f) = some q) :
    ∃ π' : LSPath P b lam, π'.toPLPath 𝕜 f = q := by
  rcases π.raise_toPLPath_eq_none_and_eq_none_or_exists_eq_some hlam i f F hF f F hF with
    ⟨hnone, -⟩ | ⟨π', hsome, -⟩
  · rw [hnone] at hq; cases hq
  · exact ⟨π', Option.some.inj (hsome.symm.trans hq)⟩

end Realization

end TauCeti.LSPath
