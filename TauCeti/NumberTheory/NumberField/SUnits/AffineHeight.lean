/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.LinearForm
public import TauCeti.NumberTheory.Height.Primitive
public import TauCeti.NumberTheory.NumberField.SUnits.Lattice

/-!
# `S`-unit multiples of small affine height

Let `K` be a number field and `S` a finite set of finite places of `K`. The projective height
`Height.mulHeight x` of a tuple `x : ι → K` does not change when `x` is scaled, while its affine
height `Height.mulHeightAff x` does, and it can be arbitrarily larger: over `ℚ`, with `S` the
`2`-adic place, the one-coordinate tuples `(2 ^ k)` are `S`-primitive of height `1` and affine
height `2 ^ k`. This file shows that scaling by a suitable `S`-unit closes the gap up to a
constant: **every `S`-primitive tuple `x` has an `S`-unit multiple `u • x` with**

`logHeightAff (u • x) ≤ logHeight x + C`,

where `C` depends only on `K` and `S`, and not on the tuple or its index type.

For an `S`-primitive `x`, the height is the product of the local sup norms `s_v` of `x` over the
infinite places and the places of `S` (`NumberField.mulHeight_eq_prod_of_isPrimitive`). The
`S`-unit lattice is cocompact in the sum-zero hyperplane
(`TauCeti.NumberField.SUnit.exists_forall_abs_log_sub_le`), so some `S`-unit `u` has weighted
logarithms within a bounded distance of the sum-zero vector with entries
`(mult v / D) * logHeight x - mult v * log s_v`, where `D` is the total multiplicity of these
places. At each place the local factor `max 1 (|u|_v * s_v)` of the affine height of `u • x`
then contributes at most `(mult v / D) * logHeight x` plus a constant, and these shares add up to
`logHeight x`. Every place is handled at once, with no coordinate singled out.

As a consequence the values of finitely many fixed linear forms at the normalized point `u • x`
have logarithmic height at most `logHeight x` plus a constant
(`TauCeti.NumberField.exists_forall_logHeight₁_apply_smul_le`). By
`TauCeti.GlobalNumberFields.abs_log_normalizedAbsValue_le_logHeight₁` this bounds the logarithm
of the normalized absolute value of each such value at every place. This normalization is how
the proof of the Subspace Theorem classifies its solutions by the sizes of the forms at each
place.

## Main results

* `TauCeti.NumberField.exists_forall_logHeightAff_smul_le`: every `S`-primitive tuple has an
  `S`-unit multiple whose affine logarithmic height exceeds its logarithmic height by at most a
  constant depending only on `K` and `S`.
* `TauCeti.NumberField.exists_forall_logHeight₁_apply_smul_le`: for finitely many linear forms,
  the same `S`-unit multiple can be chosen so that, in addition, each form takes a value of
  logarithmic height at most `logHeight x` plus a constant.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  Lemma 7.5.4 and Corollary 7.5.5.
* Ralf Stephan's `rwst/Subspace-Theorems` (Apache 2.0) formalizes Lemma 7.5.4 in
  `DiophantineApproximation/UnitNormalization.lean`, at commit
  `09835cb23557ae5ae0cf55a9c4ab9055f5d60338`.
-/

public section

open Finset Height IsDedekindDomain NumberField Real

universe u

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Every `S`-primitive tuple has an `S`-unit multiple of small affine height** (Bombieri and
Gubler, Lemma 7.5.4). There is a constant `C`, depending only on `K` and `S` and chosen before
the index type, such that every `S`-primitive tuple `x : ι → K` has an `S`-unit multiple `u • x`
with `logHeightAff (u • x) ≤ logHeight x + C`.

The unit is needed: the affine height is not invariant under scaling, and over `ℚ`, with `S` the
`2`-adic place, the one-coordinate tuples `(2 ^ k)` are `S`-primitive of height `1` but affine
height `2 ^ k`. -/
theorem exists_forall_logHeightAff_smul_le (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ C : ℝ, ∀ {ι : Type u} [Finite ι] (x : ι → K),
      (S : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive x →
      ∃ u : (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
        logHeightAff (((u : Kˣ) : K) • x) ≤ logHeight x + C := by
  obtain ⟨R, hR, happrox⟩ := SUnit.exists_forall_abs_log_sub_le S
  -- the total multiplicity of the infinite places and the places of `S`
  set D : ℝ := ∑ w : InfinitePlace K, (w.mult : ℝ) + #S with hD
  have hDpos : 0 < D := by
    have : (0 : ℝ) < ∑ w : InfinitePlace K, (w.mult : ℝ) :=
      Finset.sum_pos (fun w _ ↦ mod_cast w.mult_pos) Finset.univ_nonempty
    positivity
  refine ⟨(Fintype.card (InfinitePlace K) + #S) * R, fun {ι} _ x hx ↦ ?_⟩
  have hx0 := hx.ne_zero
  set h := logHeight x with hh_def
  have hh0 : 0 ≤ h := logHeight_nonneg x
  -- the logarithmic height of `x` is the sum of the logarithms of its local sup norms
  have hh : h = ∑ w : InfinitePlace K, (w.mult : ℝ) * log (⨆ j, w (x j)) +
      ∑ v ∈ S, log (⨆ j, FinitePlace.mk v (x j)) := by
    rw [hh_def, logHeight_eq_log_mulHeight, NumberField.mulHeight_eq_prod_of_isPrimitive S hx,
      log_prod_iSup_eq S (fun w ↦ iSup_apply_pos w hx0) (fun v _ ↦ iSup_apply_pos _ hx0)]
  -- an `S`-unit whose logarithms are close to the share `mult v / D` of the height at each place
  obtain ⟨u, hu, hu'⟩ := happrox
    (fun w ↦ w.mult / D * h - w.mult * log (⨆ j, w (x j)))
    (fun v ↦ h / D - log (⨆ j, FinitePlace.mk v (x j))) (by
      have hshare : (∑ w : InfinitePlace K, (w.mult : ℝ)) / D * h + #S * (h / D) = h := by
        field_simp
        rw [hD]
        ring
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div,
        Finset.sum_const, nsmul_eq_mul]
      linarith)
  refine ⟨u, ?_⟩
  set c : K := ((u : Kˣ) : K)
  have hc : c ≠ 0 := (u : Kˣ).ne_zero
  set y : Option ι → K := fun o ↦ o.elim 1 (c • x)
  have hy0 : y ≠ 0 := fun h ↦ one_ne_zero (congrFun h none)
  have hyS (o : Option ι) : y o ∈ (S : Set (HeightOneSpectrum (𝓞 K))).integer K := by
    cases o with
    | none => exact one_mem _
    | some j => exact (hx.unit_smul u).mem_integer j
  have hinf (w : InfinitePlace K) :
      (w.mult : ℝ) * log (⨆ o, w (y o)) ≤ w.mult / D * h + R :=
    mul_log_iSup_option_elim_smul_le w hx0 hc (Nat.cast_nonneg _) (by positivity) (by
      linarith [(abs_le.mp (hu w)).2])
  have hfin (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
      log (⨆ o, FinitePlace.mk v (y o)) ≤ h / D + R := by
    simpa using mul_log_iSup_option_elim_smul_le (FinitePlace.mk v) hx0 hc zero_le_one
      (by positivity) (by linarith [(abs_le.mp (hu' v hv)).2])
  rw [logHeightAff_eq_log_mulHeightAff, mulHeightAff_def]
  calc log (mulHeight y)
      ≤ log ((∏ w : InfinitePlace K, (⨆ o, w (y o)) ^ w.mult) *
          ∏ v ∈ S, ⨆ o, FinitePlace.mk v (y o)) :=
        log_le_log (mulHeight_pos y) (NumberField.mulHeight_le_prod S hy0 hyS)
    _ = ∑ w : InfinitePlace K, (w.mult : ℝ) * log (⨆ o, w (y o)) +
          ∑ v ∈ S, log (⨆ o, FinitePlace.mk v (y o)) :=
      log_prod_iSup_eq S (fun w ↦ zero_lt_one.trans_le (one_le_iSup_option_elim w _))
        (fun v _ ↦ zero_lt_one.trans_le (one_le_iSup_option_elim (FinitePlace.mk v) _))
    _ ≤ ∑ w : InfinitePlace K, (w.mult / D * h + R) + ∑ v ∈ S, (h / D + R) :=
      add_le_add (Finset.sum_le_sum fun w _ ↦ hinf w) (Finset.sum_le_sum hfin)
    _ = h + (Fintype.card (InfinitePlace K) + #S) * R := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      field_simp
      ring

/-- **The values of fixed linear forms at a normalized point** (Bombieri and Gubler,
Corollary 7.5.5). For finitely many linear forms `L k` on `ι → K` there is a constant `C` such
that every `S`-primitive tuple `x` has an `S`-unit multiple `u • x` whose affine logarithmic
height, and the logarithmic height of every value `L k (u • x)`, are at most `logHeight x + C`.

The value of a form is bounded through the affine heights of its coefficient vector and of the
point (`Height.logHeight₁_sum_mul_le`); no independence of the forms is used. With
`TauCeti.GlobalNumberFields.abs_log_normalizedAbsValue_le_logHeight₁` this bounds
`|log ‖L k (u • x)‖_v|` by `logHeight x + C` at every place `v`. -/
theorem exists_forall_logHeight₁_apply_smul_le (S : Finset (HeightOneSpectrum (𝓞 K)))
    {ι : Type u} {κ : Type*} [Finite ι] [Finite κ] (L : κ → Module.Dual K (ι → K)) :
    ∃ C : ℝ, ∀ x : ι → K, (S : Set (HeightOneSpectrum (𝓞 K))).IsPrimitive x →
      ∃ u : (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
        logHeightAff (((u : Kˣ) : K) • x) ≤ logHeight x + C ∧
          ∀ k, logHeight₁ (L k (((u : Kˣ) : K) • x)) ≤ logHeight x + C := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨C₀, hC₀⟩ := exists_forall_logHeightAff_smul_le (K := K) S
  -- the value of `L k` at `y` is the dot product of `y` with the coefficient vector of `L k`
  have hval (k : κ) (y : ι → K) : L k y = ∑ i, L k (Pi.single i 1) * y i := by
    have hsingle (i : ι) : (fun j ↦ if i = j then (1 : K) else 0) = Pi.single i 1 :=
      funext fun j ↦ by simp [Pi.single_apply, eq_comm]
    simpa [hsingle, mul_comm] using LinearMap.pi_apply_eq_sum_univ (L k) y
  obtain ⟨A, hA⟩ :=
    (Set.finite_range fun k ↦ logHeightAff fun i ↦ L k (Pi.single i 1)).bddAbove
  have hA' (k : κ) : logHeightAff (fun i ↦ L k (Pi.single i 1)) ≤ A := hA ⟨k, rfl⟩
  refine ⟨C₀ + (totalWeight K * log (Nat.card ι) + max A 0), fun x hx ↦ ?_⟩
  obtain ⟨u, hu⟩ := hC₀ x hx
  have hW : 0 ≤ totalWeight K * log (Nat.card ι) :=
    mul_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg _)
  refine ⟨u, by linarith [le_max_right A 0], fun k ↦ ?_⟩
  rw [hval]
  linarith [logHeight₁_sum_mul_le (fun i ↦ L k (Pi.single i 1)) (((u : Kˣ) : K) • x), hA' k,
    le_max_left A 0]

end TauCeti.NumberField
