/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.BreakData
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

/-- Identify vertex heights of the native path presentation with the sums used by the
chain-integrality lemmas. -/
private theorem apply_sum_take (π : LSPath P b lam) (f : M →+ V)
    (F : Module.Dual 𝕜 V) (g : Module.Dual ℤ M) (hF : ∀ m, F (f m) = (g m : 𝕜))
    (k : ℕ) (hk : k ≤ π.length + 1) :
    F (((π.timed 𝕜 f).map Prod.snd).take k).sum =
      ((∑ j ∈ Finset.range k,
        (π.natTime (j + 1) - π.natTime j) * g (π.natDir j • lam) : ℚ) : 𝕜) := by
  rw [π.map_snd_timed f, apply_sum_take_map_range f F g hF, min_eq_left hk]

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

/-- The height of an LS path at the break `a_j`, minus `a_j` times the slope of the segment
starting there, is an integer. -/
theorem exists_sum_sub_natTime_mul_eq_intCast (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (g : Module.Dual ℤ M) {j : ℕ} (hj : j < π.length + 1) :
    ∃ z : ℤ, ∑ k ∈ Finset.range j, (π.natTime (k + 1) - π.natTime k) * g (π.natDir k • lam) -
      π.natTime j * g (π.natDir j • lam) = z := by
  obtain ⟨z, hz⟩ := exists_sum_sub_mul_eq_intCast_of_isAChain hlam π.natTime_zero
    π.natDir_chain g hj
  exact ⟨z, by rw [← hz, Finset.sum_range_succ]; ring⟩

/-- The endpoint of an LS path has integral value under every height form agreeing with an
integral linear form on the weight lattice. -/
theorem exists_apply_endpoint_eq_intCast (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V)
    (F : Module.Dual 𝕜 V) (g : Module.Dual ℤ M) (hF : ∀ m, F (f m) = (g m : 𝕜)) :
    ∃ z : ℤ, F (π.toPLPath 𝕜 f).endpoint = z := by
  obtain ⟨z, hz⟩ := exists_sum_eq_intCast_of_isAChain hlam π.natTime_zero π.natDir_chain
    ⟨1, by simp⟩ g
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
    π.natTime_zero π.natDir_chain π.natTime_strictMono ⟨1, by simp⟩ i
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
simple coroot pairing `⟨-, αᵢ^∨⟩`. Let `H j = ∑_{k < j} (a_{k+1} - a_k) ⟨τ_k λ, αᵢ^∨⟩` be the height
of the `j`-th vertex of the encoding, and write `[v₀, …, v_l]` for the segments
`v_k = (a_{k+1} - a_k) f (τ_k λ)` of its distinguished presentation. If the lowering operator
`f_x`, for any `x : V`, is defined, that is `F (π 1) - h ≥ 1` for the minimal height `h` along the
path, there are vertices `k₀ < k₁` and a rational fraction `0 < θ ≤ 1` such that

* `H k₀` is the least vertex height, and the height rises strictly along the segments
  `v_{k₀}, …, v_{k₁ - 1}`, staying below `H k₀ + 1` before the vertex `k₁`;
* it reaches `H k₀ + 1` after the fraction `θ` of the segment `v_{k₁ - 1}`, and is at least
  `H k₀ + 1` at every later vertex;
* the lowering operator reflects the piece `v_{k₀}, …, v_{k₁ - 2}, θ v_{k₁ - 1}` of the path by
  `s = Module.preReflection x F` and keeps the rest, so that `f_x π` is presented by
  `v₀, …, v_{k₀ - 1}, s v_{k₀}, …, s v_{k₁ - 2}, s (θ v_{k₁ - 1}), (1 - θ) v_{k₁ - 1}, v_{k₁}, …,
  v_l`.
-/
theorem exists_lower_toPLPath_eq (π : LSPath P b lam) (hlam : lam ∈ dominantChamber P b)
    (f : M →+ V) (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) (x : V) (H : ℕ → ℚ)
    (hH : ∀ j, H j = ∑ k ∈ Finset.range j,
      (π.natTime (k + 1) - π.natTime k) * (P.coroot' i (π.natDir k • lam) : ℚ))
    (h : 1 ≤ F (π.toPLPath 𝕜 f).endpoint - (π.toPLPath 𝕜 f).minHeight F) :
    ∃ (k₀ k₁ : ℕ) (θ : ℚ), k₀ < k₁ ∧ k₁ ≤ π.length + 1 ∧ 0 < θ ∧ θ ≤ 1 ∧
      IsLeast (H '' Set.Iic (π.length + 1)) (H k₀) ∧
      (∀ j, k₀ ≤ j → j < k₁ → H j < H (j + 1) ∧ H j < H k₀ + 1) ∧
      (∀ j, k₁ ≤ j → j ≤ π.length + 1 → H k₀ + 1 ≤ H j) ∧
      θ * (H k₁ - H (k₁ - 1)) = H k₀ + 1 - H (k₁ - 1) ∧
      PLPath.lower F x (π.toPLPath 𝕜 f) = some (PLPath.ofSegments 𝕜
        (((π.timed 𝕜 f).map Prod.snd).take k₀ ++
          ((((π.timed 𝕜 f).map Prod.snd).take (k₁ - 1)).drop k₀ ++
            [((θ * (π.natTime k₁ - π.natTime (k₁ - 1)) : ℚ) : 𝕜) •
              f (π.natDir (k₁ - 1) • lam)]).map (Module.preReflection x F) ++
          (((1 - θ) * (π.natTime k₁ - π.natTime (k₁ - 1)) : ℚ) : 𝕜) •
            f (π.natDir (k₁ - 1) • lam) :: ((π.timed 𝕜 f).map Prod.snd).drop k₁)) := by
  rw [π.map_snd_timed f, π.toPLPath_eq_ofSegments_natDir f]
  rw [π.toPLPath_eq_ofSegments_natDir f, PLPath.endpoint_ofSegments,
    PLPath.minHeight_ofSegments] at h
  set s := π.length + 1
  set L := (List.range s).map fun k ↦
    ((π.natTime (k + 1) - π.natTime k : ℚ) : 𝕜) • f (π.natDir k • lam) with hL
  -- Vertex heights of the realization are the heights `H` of the encoding.
  have hFL (j : ℕ) : F (L.take j).sum = (H (min j s) : 𝕜) := by
    rw [hH]
    exact apply_sum_take_map_range f F (P.coroot' i) hF s _ _ j
  have hFLj (j : ℕ) (hj : j ≤ s) : F (L.take j).sum = (H j : 𝕜) := by rw [hFL, min_eq_left hj]
  -- The final height exceeds the minimal height by at least one.
  have hgap : ∃ j ≤ s, H j + 1 ≤ H s := by
    obtain ⟨m, hm⟩ := PLPath.exists_listMinHeight_eq (f := F) L
    rw [hm, hFL, ← List.take_length (l := L), hFL, show L.length = s by simp [hL],
      min_self] at h
    have h2 : ((H (min m s) + 1 : ℚ) : 𝕜) ≤ (H s : 𝕜) := by
      push_cast
      linarith
    exact ⟨min m s, Nat.min_le_right _ _, by exact_mod_cast h2⟩
  -- The rising piece: the last vertex `k₀` of minimal height and the first vertex `k₁` after it
  -- of height at least `H k₀ + 1`.
  obtain ⟨k₀, k₁, hk₀₁, hk₁, hleast, hrise, habove⟩ := exists_strictly_rising_of_isAChain hlam
    π.natTime_zero π.natDir_chain π.natTime_strictMono ⟨1, by simp⟩ i
    (by simpa only [hH] using hgap)
  simp only [← hH] at hleast hrise habove
  have hleast' (j : ℕ) (hj : j ≤ s) : H k₀ ≤ H j := hleast.2 ⟨j, hj, rfl⟩
  -- The segment `j₁ = k₁ - 1` reaches the height `H k₀ + 1` after the fraction `θ` of it.
  set j₁ := k₁ - 1 with hj₁
  have hk₁' : j₁ + 1 = k₁ := by omega
  have hHk₁ : H k₁ = H j₁ +
      (π.natTime k₁ - π.natTime j₁) * (P.coroot' i (π.natDir j₁ • lam) : ℚ) := by
    rw [hH, hH, ← hk₁', Finset.sum_range_succ]
  have hrj := hrise j₁ (by omega) (by omega)
  rw [hk₁'] at hrj
  have hab := habove k₁ le_rfl hk₁
  set θ : ℚ := (H k₀ + 1 - H j₁) / (H k₁ - H j₁)
  have hθmul : θ * (H k₁ - H j₁) = H k₀ + 1 - H j₁ := div_mul_cancel₀ _ (by linarith)
  refine ⟨k₀, k₁, θ, hk₀₁, hk₁, div_pos (by linarith) (by linarith),
    (div_le_one (by linarith)).mpr (by linarith), hleast, hrise, habove, hθmul, ?_⟩
  -- The lowering operator, by the general description for strictly rising heights.
  have hmin : PLPath.listMinHeight F L = (H k₀ : 𝕜) := by
    refine le_antisymm ?_ ?_
    · have := PLPath.listMinHeight_le_apply_sum_take (f := F) L k₀
      rwa [hFLj k₀ (by omega)] at this
    · obtain ⟨m, hm⟩ := PLPath.exists_listMinHeight_eq (f := F) L
      rw [hm, hFL]
      exact_mod_cast hleast' _ (Nat.min_le_right _ _)
  have hgetL : L[k₁ - 1]'(by simp [hL]; omega) =
      ((π.natTime k₁ - π.natTime j₁ : ℚ) : 𝕜) • f (π.natDir j₁ • lam) := by
    simp only [hL, List.getElem_map, List.getElem_range, Nat.sub_add_cancel (by omega : 1 ≤ k₁)]
    rw [hj₁]
  rw [PLPath.lower_ofSegments_eq_of_strictly_rising (θ := (θ : 𝕜)) hk₀₁ (by simp [hL]; omega)
    (by rw [hmin, hFLj k₀ (by omega)])
    (fun j h₀ h₁ ↦ by
      rw [hFLj j (by omega), hFLj (j + 1) (by omega)]
      exact_mod_cast (hrise j h₀ h₁).1)
    (by
      rw [hFLj _ (by omega), hgetL, map_smul, hF, hmin, smul_eq_mul]
      have : H j₁ + θ * ((π.natTime k₁ - π.natTime j₁) *
          (P.coroot' i (π.natDir j₁ • lam) : ℚ)) = H k₀ + 1 := by
        linear_combination hθmul - θ * hHk₁
      exact_mod_cast this)
    (by
      rw [hFLj _ (by omega), hmin]
      exact_mod_cast hrj.2.le)
    (fun j hj ↦ by
      rw [hFL, hmin]
      exact_mod_cast habove _ (le_min hj hk₁) (Nat.min_le_right _ _))]
  simp only [hgetL, smul_smul, Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
  rfl

end TauCeti.LSPath
