/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Basic
public import TauCeti.RepresentationTheory.LSPath.RootOperator

/-!
# Integral heights and root strings of Lakshmibai–Seshadri paths

The chain conditions of an LS encoding imply integrality of its endpoint against every
integral linear form, and integrality of its minimum height against every simple coroot.
Here these facts are proved for the actual `LSPath.toPLPath` realization, so they apply directly
to the raising and lowering operators. In particular the raising and lowering strings have
lengths exactly `-min H` and `H(1) - min H`, not just their integer parts, by the
iteration criteria in `TauCeti.RepresentationTheory.LSPath.StringLength`.

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

/-- The minimum simple-coroot height of the actual piecewise-linear realization of an LS path
is an integer. This includes minima attained on stationary-height segments or at an endpoint. -/
theorem exists_minHeight_eq_intCast (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V)
    (i : b.support) (F : Module.Dual 𝕜 V)
    (hF : ∀ m, F (f m) = (P.coroot' i m : 𝕜)) :
    ∃ z : ℤ, (π.toPLPath 𝕜 f).minHeight F = z := by
  obtain ⟨z, hz⟩ := exists_isLeast_sum_coroot'_eq_intCast_of_isAChain hlam
    π.natTime_zero π.natDir_chain π.natTime_strictMono ⟨1, by simp [π.natTime_last]⟩ i
  rw [toPLPath_def, PLPath.minHeight_ofSegments]
  refine ⟨z, le_antisymm ?_ ?_⟩
  · obtain ⟨k, hk, hval⟩ := hz.1
    have hbound := PLPath.listMinHeight_le_apply_sum_take (f := F)
      ((π.timed 𝕜 f).map Prod.snd) k
    rw [π.apply_sum_take f F (P.coroot' i) hF k hk] at hbound
    simpa only [hval, Rat.cast_intCast] using hbound
  · obtain ⟨k, hk⟩ := PLPath.exists_listMinHeight_eq (f := F) ((π.timed 𝕜 f).map Prod.snd)
    let n := min k (π.length + 1)
    have htake : (((π.timed 𝕜 f).map Prod.snd).take n) =
        (((π.timed 𝕜 f).map Prod.snd).take k) := by
      have hlen : ((π.timed 𝕜 f).map Prod.snd).length = π.length + 1 := by
        simp only [List.length_map, timed_def, List.length_ofFn]
      simpa only [hlen] using (List.take_eq_take_min
        (l := (π.timed 𝕜 f).map Prod.snd) (i := k)).symm
    rw [hk, ← htake, π.apply_sum_take f F (P.coroot' i) hF n (Nat.min_le_right _ _)]
    exact_mod_cast hz.2 ⟨n, Nat.min_le_right _ _, rfl⟩

/-- The raising and lowering heights of an LS path are natural numbers. Their difference is
the final simple-coroot height, so they are the normal-crystal string parameters. -/
theorem exists_stringLengths (π : LSPath P b lam)
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

end TauCeti.LSPath
