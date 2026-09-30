/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Stiemke's lemma

Stiemke's lemma is the theorem of the alternative for a linear subspace and the nonnegative
orthant: a subspace `V` of `ι → ℝ` meets the closed nonnegative orthant only in `0` exactly when
some strictly positive vector `w` is orthogonal to `V`. We prove it by separating `V` from the
convex hull of the standard basis vectors, and then transfer it to a subgroup `P` of the lattice
`ι → ℤ`: if the only nonnegative element of `P` is `0`, then `P` is orthogonal to a strictly
positive real vector.

The lattice form needs the rationality step that the real span of `P` then meets the orthant
only in `0` as well, which is not formal: a real point of the span need not be a real multiple of
a lattice point. It is proved by induction on the support. A nonzero nonnegative real point `v` of
the span yields, by an integer linear relation among the restrictions of a linearly independent
family from `P` to the complement of the support of `v`, a nonzero lattice point `q ∈ P`
supported inside the support of `v`; subtracting the largest multiple of `q` that keeps `v`
nonnegative shrinks the support.

The lattice form is what is used for Heegaard diagrams: it turns weak admissibility, a condition
on the integral periodic domains, into the existence of an area form for which every periodic
domain has signed area zero.

## Main results

* `TauCeti.exists_pos_forall_sum_mul_eq_zero_iff`: Stiemke's lemma for a real subspace.
* `TauCeti.exists_mem_ne_zero_support_subset_of_mem_span_intCast`: a nonzero vector in the real
  span of a subgroup of `ι → ℤ` has the support of a nonzero element of the subgroup inside its
  support.
* `TauCeti.eq_zero_of_mem_span_intCast_of_nonneg`: a subgroup of `ι → ℤ` whose only nonnegative
  element is `0` spans a real subspace whose only nonnegative element is `0`.
* `TauCeti.exists_pos_forall_sum_mul_intCast_eq_zero_iff`: Stiemke's lemma for a subgroup of
  `ι → ℤ`.

## References

* E. Stiemke, *Über positive Lösungen homogener linearer Gleichungen*, Math. Ann. **76** (1915),
  340–342.
-/

public section

open Finset

namespace TauCeti

variable {ι : Type*}

/-- **Stiemke's lemma.** A real subspace `V` of `ι → ℝ` meets the closed nonnegative orthant
only in `0` exactly when some strictly positive vector is orthogonal to every element of `V`. -/
theorem exists_pos_forall_sum_mul_eq_zero_iff [Fintype ι] {V : Submodule ℝ (ι → ℝ)} :
    (∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ ∀ v ∈ V, ∑ i, w i * v i = 0) ↔
      ∀ v ∈ V, 0 ≤ v → v = 0 := by
  classical
  constructor
  · rintro ⟨w, hw, hwV⟩ v hv hv₀
    have hterm := (sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hw i).le (hv₀ i)).mp
      (hwV v hv)
    funext i
    exact (mul_eq_zero.mp (hterm i (mem_univ i))).resolve_left (hw i).ne'
  · intro hV
    -- Separate the convex hull of the standard basis vectors, a compact convex set of
    -- nonnegative vectors with coordinate sum `1`, from the closed subspace `V`.
    set K := convexHull ℝ (Set.range fun i => (Pi.single i 1 : ι → ℝ))
    have hK : K ⊆ Set.Ici 0 ∩ {a | ∑ i, a i = 1} := by
      refine convexHull_min ?_ ((convex_Ici 0).inter (convex_hyperplane ?_ 1))
      · rintro _ ⟨i, rfl⟩
        exact ⟨Pi.single_nonneg.mpr zero_le_one, by simp⟩
      · exact ⟨fun a b => sum_add_distrib, fun c a => by simp [mul_sum]⟩
    have hdisj : Disjoint K (V : Set (ι → ℝ)) := by
      refine Set.disjoint_left.mpr fun a ha haV => ?_
      obtain ⟨h₀, h₁⟩ := hK ha
      have h₂ : ∑ i, a i = 1 := h₁
      rw [hV a haV h₀] at h₂
      simp at h₂
    obtain ⟨f, u, s, hfu, hus, hsf⟩ := geometric_hahn_banach_compact_closed
      (convex_convexHull ℝ _) ((Set.finite_range _).isCompact_convexHull ℝ) V.convex
      V.closed_of_finiteDimensional hdisj
    -- A functional bounded below on a subspace vanishes on it.
    have hfV (b : ι → ℝ) (hb : b ∈ V) : f b = 0 := by
      by_contra hfb
      have := hsf (((s - 1) / f b) • b) (V.smul_mem _ hb)
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfb] at this
      linarith
    have hs : s < 0 := by simpa using hsf 0 V.zero_mem
    refine ⟨fun i => -f (Pi.single i 1), fun i => ?_, fun v hv => ?_⟩
    · have := hfu _ (subset_convexHull ℝ _ (Set.mem_range_self i))
      linarith
    · have hsum := LinearMap.pi_apply_eq_sum_univ (f : (ι → ℝ) →ₗ[ℝ] ℝ) v
      have hsingle (i : ι) : (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
        funext j
        simp [Pi.single_apply, eq_comm]
      simp only [ContinuousLinearMap.coe_coe, hsingle, smul_eq_mul, hfV v hv] at hsum
      simp only [neg_mul, sum_neg_distrib, mul_comm (f _), ← hsum, neg_zero]

/-- A nonzero vector in the real span of a subgroup `P` of `ι → ℤ` has the support of a nonzero
element of `P` inside its own support. -/
theorem exists_mem_ne_zero_support_subset_of_mem_span_intCast [Finite ι]
    {P : AddSubgroup (ι → ℤ)} {v : ι → ℝ}
    (hv : v ∈ Submodule.span ℝ ((fun p : ι → ℤ => fun i => (p i : ℝ)) '' P))
    (hv₀ : v ≠ 0) : ∃ q ∈ P, q ≠ 0 ∧ Function.support q ⊆ Function.support v := by
  classical
  have := Fintype.ofFinite ι
  set c : (ι → ℤ) → ι → ℝ := fun p i => (p i : ℝ) with hc
  -- Write `v` in a linearly independent family `p` from `P` whose image spans the real span.
  obtain ⟨b, hbP, hbspan, hbli⟩ := exists_linearIndependent ℝ (c '' P)
  have : Fintype b := @Fintype.ofFinite _ hbli.finite_of_isNoetherian
  choose p hpP hpc using fun j : b => hbP j.2
  have hpli : LinearIndependent ℤ p := by
    rw [← linearIndependent_algebraMap_comp_iff (S := ℝ)]
    convert hbli using 1
    funext j i
    simp [← hpc j, hc]
  rw [← hbspan, ← Subtype.range_coe (s := b), Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨a, ha⟩ := hv
  -- The coefficients `a` are a real linear relation among the `p j` restricted to the zero set
  -- of `v`, so these restrictions also satisfy a nontrivial integer linear relation `d`.
  have hdep : ¬ LinearIndependent ℤ fun j i => if v i = 0 then p j i else 0 := by
    rw [← linearIndependent_algebraMap_comp_iff (S := ℝ), Fintype.not_linearIndependent_iff]
    refine ⟨a, funext fun i => ?_, ?_⟩
    · by_cases hi : v i = 0
      · have := congrFun ha i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
        simpa [hi, ← hpc, hc] using this
      · simp [hi]
    · by_contra ha'
      push Not at ha'
      exact hv₀ (by simp [← ha, ha'])
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨d, hd, j₀, hj₀⟩ := hdep
  refine ⟨∑ j, d j • p j, P.sum_mem fun j _ => P.zsmul_mem (hpP j) _,
    fun h => hj₀ (Fintype.linearIndependent_iff.mp hpli d h j₀), fun i hi hvi => hi ?_⟩
  simpa [hvi] using congrFun hd i

/-- A subgroup `P` of `ι → ℤ` whose only nonnegative element is `0` spans a real subspace of
`ι → ℝ` whose only nonnegative element is `0`. -/
theorem eq_zero_of_mem_span_intCast_of_nonneg [Finite ι] {P : AddSubgroup (ι → ℤ)}
    (hP : ∀ p ∈ P, 0 ≤ p → p = 0) {v : ι → ℝ}
    (hv : v ∈ Submodule.span ℝ ((fun p : ι → ℤ => fun i => (p i : ℝ)) '' P)) (hv₀ : 0 ≤ v) :
    v = 0 := by
  classical
  have := Fintype.ofFinite ι
  set V := Submodule.span ℝ ((fun p : ι → ℤ => fun i => (p i : ℝ)) '' P)
  -- Induct on a finset `S` containing the support of `v`.
  suffices h : ∀ S : Finset ι, ∀ v ∈ V, 0 ≤ v → (∀ i ∉ S, v i = 0) → v = 0 from
    h univ v hv hv₀ (by simp)
  intro S
  induction S using Finset.strongInduction with | H S ih => ?_
  intro v hv hv₀ hvS
  by_contra hne
  -- A nonzero point `q` of `P` supported in the support of `v`.
  obtain ⟨q, hqP, hq₀, hqv⟩ := exists_mem_ne_zero_support_subset_of_mem_span_intCast hv hne
  have hqS (i : ι) (hi : i ∉ S) : q i = 0 := by
    by_contra h
    exact hqv h (hvS i hi)
  have hcq : (fun i => (q i : ℝ)) ∈ V := Submodule.subset_span ⟨q, hqP, rfl⟩
  -- If `q` has no positive coordinate then `-q` is a nonzero nonnegative element of `P`.
  by_cases hpos : ∀ i, q i ≤ 0
  · exact hq₀ (neg_eq_zero.mp (hP (-q) (P.neg_mem hqP) fun i => by simpa using hpos i))
  push Not at hpos
  -- Otherwise subtract the largest multiple `t • q` of `q` keeping `v` nonnegative; this kills
  -- the coordinate `i₀` where the ratio `v i / q i` over `q i > 0` is smallest.
  obtain ⟨i₀, hi₀, hmin⟩ := (univ.filter fun i => 0 < q i).exists_min_image
    (fun i => v i / q i) (by simpa [Finset.Nonempty] using hpos)
  simp only [mem_filter, mem_univ, true_and] at hi₀ hmin
  set t := v i₀ / q i₀ with ht
  have hqi₀ : (q i₀ : ℝ) ≠ 0 := by exact_mod_cast hi₀.ne'
  have ht₀ : 0 ≤ t := div_nonneg (hv₀ i₀) (Int.cast_pos.mpr hi₀).le
  have hi₀S : i₀ ∈ S := by
    by_contra h
    exact hi₀.ne' (hqS i₀ h)
  have htq (i : ι) : t * q i ≤ v i := by
    rcases lt_or_ge 0 (q i) with h | h
    · exact (le_div_iff₀ (Int.cast_pos.mpr h)).mp (hmin i h)
    · exact (mul_nonpos_of_nonneg_of_nonpos ht₀ (Int.cast_nonpos.mpr h)).trans (hv₀ i)
  have hw := ih (S.erase i₀) (erase_ssubset hi₀S) (v - t • fun i => (q i : ℝ))
    (V.sub_mem hv (V.smul_mem t hcq)) (fun i => by simpa using htq i) fun i hi => by
      rcases eq_or_ne i i₀ with rfl | h
      · simp [ht, div_mul_cancel₀ _ hqi₀]
      · have hiS : i ∉ S := fun hiS => hi (mem_erase.mpr ⟨h, hiS⟩)
        simp [hqS i hiS, hvS i hiS]
  -- So `v = t • q`, which forces `q` to be nonnegative.
  have hvq (i : ι) : v i = t * q i := by simpa [sub_eq_zero] using congrFun hw i
  have ht₀' : 0 < t := by
    refine ht₀.lt_of_ne fun h => hne ?_
    funext i
    simp [hvq i, ← h]
  refine hq₀ (hP q hqP fun i => ?_)
  have := hv₀ i
  rw [Pi.zero_apply, hvq i] at this
  exact Int.cast_nonneg_iff.mp (nonneg_of_mul_nonneg_right this ht₀')

/-- **Stiemke's lemma for a lattice.** A subgroup `P` of `ι → ℤ` has `0` as its only nonnegative
element exactly when some strictly positive real vector is orthogonal to every element of `P`. -/
theorem exists_pos_forall_sum_mul_intCast_eq_zero_iff [Fintype ι] {P : AddSubgroup (ι → ℤ)} :
    (∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ ∀ p ∈ P, ∑ i, w i * p i = 0) ↔
      ∀ p ∈ P, 0 ≤ p → p = 0 := by
  constructor
  · rintro ⟨w, hw, hwP⟩ p hp hp₀
    have hterm := (sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (hw i).le (by exact_mod_cast hp₀ i)).mp (hwP p hp)
    funext i
    exact_mod_cast (mul_eq_zero.mp (hterm i (mem_univ i))).resolve_left (hw i).ne'
  · intro hP
    obtain ⟨w, hw, hwV⟩ := exists_pos_forall_sum_mul_eq_zero_iff.mpr fun v hv hv₀ =>
      eq_zero_of_mem_span_intCast_of_nonneg hP hv hv₀
    exact ⟨w, hw, fun p hp => hwV _ (Submodule.subset_span ⟨p, hp, rfl⟩)⟩

end TauCeti
