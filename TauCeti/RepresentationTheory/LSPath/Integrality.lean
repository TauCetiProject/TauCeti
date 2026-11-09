/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Basic
public import TauCeti.RepresentationTheory.LSPath.RootOperator
import TauCeti.RepresentationTheory.LSPath.Concatenation

/-!
# Integral heights and root strings of Lakshmibai–Seshadri paths

The chain conditions of an LS encoding imply integrality of its endpoint against every
integral linear form, and integrality of its minimum height against every simple coroot.
Here these facts are proved for the actual `LSPath.toPLPath` realization, so they apply directly
to the raising and lowering operators. In particular the raising and lowering strings have
lengths exactly `-min H` and `H(1) - min H`, not just their integer parts, by the
iteration criteria in `TauCeti.RepresentationTheory.LSPath.StringLength`.

The same chain conditions control the shape of the height around a lowering step. After the last
time `t₀` at which the height `⟨π(t), αᵢ^∨⟩` attains its minimum `h`, it rises strictly until it
reaches `h + 1`, and it never returns below `h + 1` afterwards
(`TauCeti.exists_isLeast_sum_coroot'_Icc_of_isAChain` and the lemmas following it). Hence
Littelmann's lowering operator `f_αᵢ` acts on an LS path by reflecting the single piece of the path
between `t₀` and the first time `t₁` at which the height is `h + 1`, cutting the segment containing
`t₁` there, and keeping the rest (`TauCeti.LSPath.exists_lower_toPLPath_eq`). This is the form in
which Littelmann proves that `f_αᵢ` preserves LS paths.

The realization may use any vector space over a linearly ordered field and any additive map
from the weight lattice. A height form on that vector space must agree with the indicated
integral form on
the lattice. No spanning assumption on the roots is imposed; central weights and zero shapes
are included.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§1, 4.
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N 𝕜 V : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]
  {lam : M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- Extend the finite list of directions constantly past its last entry, for the chain-height
summation lemmas. Only indices within the original list occur in the proofs below. -/
private def natDir (π : LSPath P b lam) (k : ℕ) : P.weylGroup :=
  (π.dir ⟨min k π.length, by omega⟩).1

/-- Extend the finite list of break times constantly past its last entry. -/
private def natTime (π : LSPath P b lam) (k : ℕ) : ℚ :=
  π.time ⟨min k (π.length + 1), by omega⟩

private theorem natTime_zero (π : LSPath P b lam) : π.natTime 0 = 0 :=
  π.time_zero

private theorem natTime_last (π : LSPath P b lam) : π.natTime (π.length + 1) = 1 := by
  simpa only [natTime, min_self, Fin.last] using π.time_last

private theorem natTime_strictMono (π : LSPath P b lam) (k : ℕ) (hk : k < π.length + 1) :
    π.natTime k < π.natTime (k + 1) := by
  apply π.strictMono_time
  simp only [Fin.mk_lt_mk, min_eq_left (by omega : k ≤ π.length + 1),
    min_eq_left (by omega : k + 1 ≤ π.length + 1)]
  omega

private theorem natDir_chain (π : LSPath P b lam) (k : ℕ) (hk : k + 1 < π.length + 1) :
    ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
      C.head.1 = π.natDir k ∧ C.last.1 = π.natDir (k + 1) ∧
        IsAChain (π.natTime (k + 1)) lam C := by
  obtain ⟨C, hhead, hlast, hC⟩ := π.exists_isAChain ⟨k, by omega⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · simpa [natDir, min_eq_left (by omega : k ≤ π.length)] using congrArg Subtype.val hhead
  · simpa [natDir, min_eq_left (by omega : k + 1 ≤ π.length)] using congrArg Subtype.val hlast
  · simpa [natTime, min_eq_left (by omega : k + 1 ≤ π.length + 1)] using hC

/-- Identify vertex heights of the native path presentation with the sums used by the
chain-integrality lemmas. -/
private theorem apply_sum_take (π : LSPath P b lam) (f : M →+ V)
    (F : Module.Dual 𝕜 V) (g : Module.Dual ℤ M) (hF : ∀ m, F (f m) = (g m : 𝕜))
    (k : ℕ) (hk : k ≤ π.length + 1) :
    F (((π.timed 𝕜 f).map Prod.snd).take k).sum =
      ((∑ j ∈ Finset.range k,
        (π.natTime (j + 1) - π.natTime j) * g (π.natDir j • lam) : ℚ) : 𝕜) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < π.length + 1 := by omega
    have hlen : k < ((π.timed 𝕜 f).map Prod.snd).length := by
      simpa [timed_def] using hk'
    rw [List.sum_take_succ _ _ hlen, map_add, ih (by omega), Finset.sum_range_succ,
      Rat.cast_add]
    congr 1
    simp only [timed_def, List.getElem_map, List.getElem_ofFn,
      map_smul, smul_eq_mul, hF, duration_def, natTime, natDir,
      Rat.cast_mul, Rat.cast_sub, Rat.cast_intCast,
      Fin.succ_mk, Fin.castSucc_mk,
      min_eq_left (by omega : k ≤ π.length),
      min_eq_left (by omega : k ≤ π.length + 1),
      min_eq_left (by omega : k + 1 ≤ π.length + 1)]

/-- The minimum height of an LS path is at most the height of its first vertex. -/
theorem minHeight_le_duration_mul_dir_zero (π : LSPath P b lam) (f : M →+ V)
    (F : Module.Dual 𝕜 V) :
    (π.toPLPath 𝕜 f).minHeight F ≤
      (π.duration 0 : 𝕜) * F (f ((π.dir 0).1 • lam)) := by
  rw [toPLPath_def, PLPath.minHeight_ofSegments]
  simpa only [timed_def, List.ofFn_succ, List.map_cons, Prod.snd,
    List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil, add_zero,
    map_smul, smul_eq_mul] using
    PLPath.listMinHeight_le_apply_sum_take (f := F) ((π.timed 𝕜 f).map Prod.snd) 1

variable [P.flip.IsReduced]

/-- The endpoint of an LS path has integral value under every height form agreeing with an
integral linear form on the weight lattice. -/
theorem exists_apply_endpoint_eq_intCast (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V)
    (F : Module.Dual 𝕜 V) (g : Module.Dual ℤ M) (hF : ∀ m, F (f m) = (g m : 𝕜)) :
    ∃ z : ℤ, F (π.toPLPath 𝕜 f).endpoint = z := by
  obtain ⟨z, hz⟩ := exists_sum_eq_intCast_of_isAChain hlam π.natTime_zero π.natDir_chain
    ⟨1, by simp [π.natTime_last]⟩ g
  refine ⟨z, ?_⟩
  have hlen : ((π.timed 𝕜 f).map Prod.snd).length = π.length + 1 := by
    simp only [List.length_map, timed_def, List.length_ofFn]
  rw [toPLPath_def, PLPath.endpoint_ofSegments, ← List.take_length
    (l := (π.timed 𝕜 f).map Prod.snd), hlen, π.apply_sum_take f F g hF _ le_rfl,
    hz, Rat.cast_intCast]

omit [P.flip.IsReduced] in
/-- The minimum height of the realization of an LS path is the least vertex height of its
encoding. -/
private theorem minHeight_eq_of_isLeast (π : LSPath P b lam) (f : M →+ V)
    (i : b.support) (F : Module.Dual 𝕜 V) (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) {q : ℚ}
    (hq : IsLeast ((fun j ↦ ∑ k ∈ Finset.range j, (π.natTime (k + 1) - π.natTime k) *
      (P.coroot' i (π.natDir k • lam) : ℚ)) '' Set.Iic (π.length + 1)) q) :
    (π.toPLPath 𝕜 f).minHeight F = q := by
  rw [toPLPath_def, PLPath.minHeight_ofSegments]
  refine le_antisymm ?_ ?_
  · obtain ⟨k, hk, hval⟩ := hq.1
    have hbound := PLPath.listMinHeight_le_apply_sum_take (f := F)
      ((π.timed 𝕜 f).map Prod.snd) k
    rw [π.apply_sum_take f F (P.coroot' i) hF k hk] at hbound
    simpa only [hval] using hbound
  · obtain ⟨k, hk⟩ := PLPath.exists_listMinHeight_eq (f := F) ((π.timed 𝕜 f).map Prod.snd)
    let n := min k (π.length + 1)
    have htake : (((π.timed 𝕜 f).map Prod.snd).take n) =
        (((π.timed 𝕜 f).map Prod.snd).take k) := by
      have hlen : ((π.timed 𝕜 f).map Prod.snd).length = π.length + 1 := by
        simp only [List.length_map, timed_def, List.length_ofFn]
      simpa only [hlen] using (List.take_eq_take_min
        (l := (π.timed 𝕜 f).map Prod.snd) (i := k)).symm
    rw [hk, ← htake, π.apply_sum_take f F (P.coroot' i) hF n (Nat.min_le_right _ _)]
    exact_mod_cast hq.2 ⟨n, Nat.min_le_right _ _, rfl⟩

/-- The minimum simple-coroot height of the actual piecewise-linear realization of an LS path
is an integer. This includes minima attained on stationary-height segments or at an endpoint. -/
theorem exists_minHeight_eq_intCast (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V)
    (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) :
    ∃ z : ℤ, (π.toPLPath 𝕜 f).minHeight F = z := by
  obtain ⟨z, hz⟩ := exists_isLeast_sum_coroot'_eq_intCast_of_isAChain hlam
    π.natTime_zero π.natDir_chain π.natTime_strictMono ⟨1, by simp [π.natTime_last]⟩ i
  exact ⟨z, by rw [π.minHeight_eq_of_isLeast f i F hF hz, Rat.cast_intCast]⟩

/-- The raising and lowering heights of an LS path are natural numbers. Their difference is
the final simple-coroot height, so they are the normal-crystal string parameters. -/
theorem exists_neg_minHeight_eq_natCast_and_apply_endpoint_sub_minHeight_eq_natCast
    (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V)
    (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) :
    ∃ ε φ : ℕ, -(π.toPLPath 𝕜 f).minHeight F = ε ∧
      F (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight F = φ := by
  obtain ⟨a, ha⟩ := π.exists_minHeight_eq_intCast hlam f i F hF
  obtain ⟨c, hc⟩ := π.exists_apply_endpoint_eq_intCast hlam f F (P.coroot' i) hF
  have ha' : 0 ≤ -a := by
    have := PLPath.minHeight_nonpos (f := F) (π.toPLPath 𝕜 f)
    rw [ha] at this
    exact_mod_cast neg_nonneg.mpr this
  have hc' : 0 ≤ c - a := by
    have := PLPath.minHeight_le_apply_endpoint (f := F) (π.toPLPath 𝕜 f)
    rw [ha, hc] at this
    exact_mod_cast sub_nonneg.mpr this
  exact ⟨(-a).toNat, (c - a).toNat, by rw [ha]; exact_mod_cast (Int.toNat_of_nonneg ha').symm,
    by rw [ha, hc]; exact_mod_cast (Int.toNat_of_nonneg hc').symm⟩

/-- **Littelmann's lowering operator on an LS path reflects one strictly rising piece.** Let `π` be
an LS path of dominant shape `λ`, realized in `V` by `f`, and let `F` be a form on `V` inducing the
simple coroot pairing `⟨-, αᵢ^∨⟩`, with minimal height `h` along the path. Write
`[v₀, …, v_l]` for the segments `vⱼ = (a_{j+1} - a_j) f (τⱼ λ)` of its distinguished presentation.
If the lowering operator `f_x`, for any `x : V`, is defined, that is `F (π 1) - h ≥ 1`, there are a
vertex `k₀`, a segment `j₁ ≥ k₀` and a fraction `0 < θ ≤ 1` such that

* the height is `h` at the vertex `k₀` and rises strictly along the segments `v_{k₀}, …, v_{j₁}`;
* it reaches `h + 1` after the fraction `θ` of the segment `v_{j₁}`, and is at least `h + 1` at
  every later vertex;
* the lowering operator reflects the piece `v_{k₀}, …, v_{j₁ - 1}, θ v_{j₁}` of the path by
  `s = Module.preReflection x F` and keeps the rest, so that `f_x π` is presented by
  `v₀, …, v_{k₀ - 1}, s v_{k₀}, …, s v_{j₁ - 1}, s (θ v_{j₁}), (1 - θ) v_{j₁}, v_{j₁ + 1}, …, v_l`.
-/
theorem exists_lower_toPLPath_eq (π : LSPath P b lam) (hlam : lam ∈ dominantChamber P b)
    (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (x : V)
    (h : 1 ≤ F (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight F) :
    ∃ (k₀ : ℕ) (j₁ : Fin (π.length + 1)) (θ : 𝕜), k₀ ≤ j₁ ∧ 0 < θ ∧ θ ≤ 1 ∧
      F (((π.timed 𝕜 f).map Prod.snd).take k₀).sum = (π.toPLPath 𝕜 f).minHeight F ∧
      (∀ j, k₀ ≤ j → j ≤ j₁ → F (((π.timed 𝕜 f).map Prod.snd).take j).sum <
        F (((π.timed 𝕜 f).map Prod.snd).take (j + 1)).sum) ∧
      F (((π.timed 𝕜 f).map Prod.snd).take j₁).sum +
          θ * F ((π.duration j₁ : 𝕜) • f ((π.dir j₁).1 • lam)) =
        (π.toPLPath 𝕜 f).minHeight F + 1 ∧
      (∀ j, j₁ < j → (π.toPLPath 𝕜 f).minHeight F + 1 ≤
        F (((π.timed 𝕜 f).map Prod.snd).take j).sum) ∧
      PLPath.lower F x (π.toPLPath 𝕜 f) = some (PLPath.ofSegments 𝕜
        (((π.timed 𝕜 f).map Prod.snd).take k₀ ++
          ((((π.timed 𝕜 f).map Prod.snd).take j₁).drop k₀ ++
            [(θ * π.duration j₁) • f ((π.dir j₁).1 • lam)]).map (Module.preReflection x F) ++
          ((1 - θ) * π.duration j₁) • f ((π.dir j₁).1 • lam) ::
            ((π.timed 𝕜 f).map Prod.snd).drop (j₁ + 1))) := by
  set L := (π.timed 𝕜 f).map Prod.snd with hL
  set s := π.length + 1
  set H : ℕ → ℚ := fun j ↦ ∑ k ∈ Finset.range j, (π.natTime (k + 1) - π.natTime k) *
    (P.coroot' i (π.natDir k • lam) : ℚ)
  have hlen : L.length = s := by simp only [L, s, List.length_map, timed_def, List.length_ofFn]
  -- Vertex heights of the realization are the heights `H` of the encoding.
  have hHF : ∀ k, F (L.take k).sum = (H (min k s) : 𝕜) := by
    intro k
    rw [← π.apply_sum_take f F (P.coroot' i) hF (min k s) (Nat.min_le_right _ _)]
    congr 2
    simpa only [hlen] using List.take_eq_take_min (l := L) (i := k)
  have hHF' : ∀ k, k ≤ s → F (L.take k).sum = (H k : 𝕜) := fun k hk ↦ by
    rw [hHF, min_eq_left hk]
  have hseg : ∀ j : Fin s, F ((π.duration j : 𝕜) • f ((π.dir j).1 • lam)) =
      ((H (j + 1) - H j : ℚ) : 𝕜) := by
    intro j
    have h₁ := hHF' (j + 1) (by omega)
    have h₀ := hHF' j (by omega)
    rw [Rat.cast_sub, ← h₁, ← h₀, List.sum_take_succ _ _ (by omega), map_add,
      add_sub_cancel_left]
    simp only [L, timed_def, List.getElem_map, List.getElem_ofFn, Fin.eta]
  -- The vertex `k₀` of minimal height, after which the height rises strictly up to the vertex
  -- `k₁`, crossing `H k₀ + 1` on the segment `k₁ - 1`.
  have hend : F (π.toPLPath 𝕜 f).endpoint = (H s : 𝕜) := by
    rw [toPLPath_def, PLPath.endpoint_ofSegments, ← hHF' s le_rfl, ← hlen, List.take_length]
  have hgap : ∃ j ≤ s, H j + 1 ≤ H s := by
    obtain ⟨k, hk⟩ := PLPath.exists_listMinHeight_eq (f := F) L
    refine ⟨min k s, Nat.min_le_right k s, ?_⟩
    have h' : ((H (min k s) + 1 : ℚ) : 𝕜) ≤ (H s : 𝕜) := by
      rw [hend, toPLPath_def, PLPath.minHeight_ofSegments, ← hL, hk, hHF] at h
      push_cast
      linarith
    exact_mod_cast h'
  obtain ⟨k₀, k₁, hk₀₁, hk₁s, hleast, hrise, hafter⟩ := exists_strictly_rising_of_isAChain hlam
    π.natTime_zero π.natDir_chain π.natTime_strictMono ⟨1, by simp [π.natTime_last]⟩ i hgap
  have hmin : (π.toPLPath 𝕜 f).minHeight F = (H k₀ : 𝕜) := π.minHeight_eq_of_isLeast f i F hF hleast
  -- The crossing segment `j₁ = k₁ - 1` and the fraction `θ` of it.
  set j₁ : Fin s := ⟨k₁ - 1, by omega⟩
  have hj₁ : (j₁ : ℕ) + 1 = k₁ := by simp only [j₁]; omega
  have hslope : 0 < H k₁ - H j₁ := by
    have := (hrise j₁ (by simp only [j₁]; omega) (by omega)).1
    rw [hj₁] at this
    linarith
  set θ : 𝕜 := (((H k₀ + 1 - H j₁) / (H k₁ - H j₁) : ℚ) : 𝕜) with hθ_def
  have hHj₁ : H j₁ < H k₀ + 1 := (hrise j₁ (by simp only [j₁]; omega) (by omega)).2
  have hθpos : 0 < θ := by
    rw [hθ_def, Rat.cast_pos]
    exact div_pos (by linarith) hslope
  have hθle : θ ≤ 1 := by
    have hq : (H k₀ + 1 - H j₁) / (H k₁ - H j₁) ≤ 1 :=
      (div_le_one hslope).mpr (by linarith [hafter k₁ le_rfl hk₁s])
    rw [hθ_def]
    exact_mod_cast hq
  have hθeq : F (L.take j₁).sum + θ * F ((π.duration j₁ : 𝕜) • f ((π.dir j₁).1 • lam)) =
      (π.toPLPath 𝕜 f).minHeight F + 1 := by
    rw [hseg, hj₁, hHF' _ (by omega), hmin, hθ_def, ← Rat.cast_mul,
      div_mul_cancel₀ _ hslope.ne']
    push_cast
    ring
  have hseg' : L[k₁ - 1]'(by omega) = (π.duration j₁ : 𝕜) • f ((π.dir j₁).1 • lam) := by
    simp only [L, timed_def, List.getElem_map, List.getElem_ofFn, j₁]
  refine ⟨k₀, j₁, θ, by simp only [j₁]; omega, hθpos, hθle, ?_, ?_, hθeq, ?_, ?_⟩
  · rw [hHF' _ (by omega), hmin]
  · intro j hk₀j hj
    rw [hHF' _ (by omega), hHF' _ (by omega), Rat.cast_lt]
    exact (hrise j hk₀j (by omega)).1
  · intro j hj
    rw [hHF, hmin]
    exact_mod_cast hafter (min j s) (le_min (by omega) hk₁s) (Nat.min_le_right j s)
  -- The lowering operator, by the general description for strictly rising heights.
  have hmin' : PLPath.listMinHeight F L = (H k₀ : 𝕜) := by
    rw [← hmin, toPLPath_def, PLPath.minHeight_ofSegments]
  rw [toPLPath_def, ← hL, PLPath.lower_ofSegments_eq_of_strictly_rising (k₀ := k₀) (k₁ := k₁)
    (θ := θ) hk₀₁ (by omega)]
  · simp only [hseg', smul_smul]
    rw [show k₁ - 1 = (j₁ : ℕ) by omega, ← hj₁]
  · rw [hmin', hHF' _ (by omega)]
  · intro j hk₀j hj
    rw [hHF' _ (by omega), hHF' _ (by omega), Rat.cast_lt]
    exact (hrise j hk₀j hj).1
  · rw [hmin', ← hmin, hseg', show k₁ - 1 = (j₁ : ℕ) by omega]
    exact hθeq
  · rw [hmin', show k₁ - 1 = (j₁ : ℕ) by omega, hHF' _ (by omega)]
    exact_mod_cast hHj₁.le
  · intro j hj
    rw [hmin', hHF]
    exact_mod_cast hafter (min j s) (le_min hj hk₁s) (Nat.min_le_right j s)

end TauCeti.LSPath
