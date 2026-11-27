/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.Big.Frobenius
public import TauCeti.RingTheory.WittVector.Big.Verschiebung

import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.MvPolynomial.Counit
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Teichmüller representatives of big Witt vectors

The Teichmüller map sends a coefficient to the Witt vector supported at index one. Its
ghosts are powers of the coefficient, so Frobenius sends a Teichmüller representative to
another Teichmüller representative. On a finite truncation set every Witt vector is a sum
of Verschiebung translates of the Teichmüller representatives of its coordinates. On an
arbitrary truncation set these sums agree with the vector upon every finite restriction.

## References

* L. Hesselholt, *The big de Rham–Witt complex*, Acta Math. 214 (2015), §1.
-/

public section

noncomputable section

namespace TauCeti.BigWittVector

open BigWitt Finset _root_.MvPolynomial

variable {S T : TruncationSet} {R A : Type*} [CommRing R] [CommRing A]

private def teichmullerFun (r : R) : BigWittVector S R :=
  mk' (Pi.single 1 r)

open scoped Classical in
private theorem coeff_teichmullerFun (r : R) (n : ℕ) :
    (teichmullerFun (S := S) r).coeff n = if n = 1 ∧ 1 ∈ S then r else 0 := by
  by_cases hn : n ∈ S
  · rcases eq_or_ne n 1 with rfl | h
    · simp [teichmullerFun, hn]
    · simp [teichmullerFun, hn, h, Pi.single_eq_of_ne]
  · rw [coeff_eq_zero_of_notMem _ _ hn]
    by_cases h : n = 1
    · subst n
      simp [hn]
    · simp [h]

private theorem map_teichmullerFun (f : R →+* A) (r : R) :
    map (S := S) f (teichmullerFun r) = teichmullerFun (f r) := by
  ext n
  simp only [coeff_map, coeff_teichmullerFun]
  split_ifs <;> simp

private theorem ghostMap_teichmullerFun (r : R) (n : S) :
    ghostMap (teichmullerFun r) n = r ^ (n : ℕ) := by
  rw [ghostMap_apply]
  calc
    _ = ghostPolynomial n (Pi.single 1 r) :=
      ghostPolynomial_congr fun _ hd ↦ coeff_mk'_of_mem _ (S.mem_of_dvd n.property hd)
    _ = _ := by
      rw [ghostPolynomial_single_one_eq_iterate (S.ne_zero_of_mem n.property),
        mul_right_iterate_apply_self, Nat.sub_add_cancel (S.pos_of_mem n.property)]

private theorem teichmullerFun_mul (r s : R) :
    teichmullerFun (S := S) (r * s) = teichmullerFun r * teichmullerFun s := by
  obtain ⟨r, rfl⟩ := counit_surjective R r
  obtain ⟨s, rfl⟩ := counit_surjective R s
  rw [← map_mul, ← map_teichmullerFun, ← map_teichmullerFun, ← map_teichmullerFun, ← map_mul]
  congr 1
  apply ghostMap_injective fun _ _ hp ↦ .of_ne_zero (Nat.cast_ne_zero.2 hp.ne_zero)
  funext n
  simp [ghostMap_teichmullerFun, mul_pow]

variable (S) in
/-- The multiplicative Teichmüller map into the big Witt ring. Its coefficient at index one is
the input whenever the truncation set is nonempty, and all other coefficients vanish. -/
def teichmuller : R →* BigWittVector S R where
  toFun := teichmullerFun
  map_one' := ext fun n ↦ by
    by_cases hn : n ∈ S
    · simp [teichmullerFun, hn, coeff_one]
    · rw [coeff_eq_zero_of_notMem _ _ hn, coeff_eq_zero_of_notMem _ _ hn]
  map_mul' := teichmullerFun_mul

open scoped Classical in
/-- The coordinates of the Teichmüller representative. -/
theorem coeff_teichmuller (r : R) (n : ℕ) :
    (teichmuller S r).coeff n = if n = 1 ∧ 1 ∈ S then r else 0 :=
  coeff_teichmullerFun r n

/-- The first coordinate recovers the input of the Teichmüller map. -/
@[simp]
theorem coeff_one_teichmuller (h : 1 ∈ S) (r : R) : (teichmuller S r).coeff 1 = r := by
  simp [coeff_teichmuller, h]

/-- The higher coordinates of a Teichmüller representative vanish. -/
@[simp]
theorem coeff_teichmuller_of_ne_one {n : ℕ} (hn : n ≠ 1) (r : R) :
    (teichmuller S r).coeff n = 0 := by
  simp [coeff_teichmuller, hn]

/-- The Teichmüller map preserves zero. -/
@[simp]
theorem teichmuller_zero : teichmuller S (0 : R) = 0 := by
  ext n
  simp [coeff_teichmuller]

/-- The ghost at index `n` of the Teichmüller representative of `r` is `r ^ n`. -/
@[simp]
theorem ghostMap_teichmuller (r : R) (n : S) : ghostMap (teichmuller S r) n = r ^ (n : ℕ) :=
  ghostMap_teichmullerFun r n

/-- Teichmüller representatives commute with homomorphisms of coefficient rings. -/
@[simp]
theorem map_teichmuller (f : R →+* A) (r : R) :
    map f (teichmuller S r) = teichmuller S (f r) :=
  map_teichmullerFun f r

/-- Restriction preserves Teichmüller representatives. -/
@[simp]
theorem restrict_teichmuller (h : T ≤ S) (r : R) :
    restrict h (teichmuller S r) = teichmuller T r := by
  ext n
  by_cases hn : n ∈ T
  · simp only [coeff_restrict_of_mem _ _ hn, coeff_teichmuller]
    rcases eq_or_ne n 1 with rfl | hne
    · simp [hn, h hn]
    · simp [hne]
  · rw [coeff_eq_zero_of_notMem _ _ hn, coeff_eq_zero_of_notMem _ _ hn]

/-- The Frobenius of a Teichmüller representative raises its coefficient to the Frobenius
index and shifts the truncation set. -/
@[simp]
theorem frobenius_teichmuller (n : ℕ) (r : R) :
    frobenius n (teichmuller S r) = teichmuller (S / n) (r ^ n) := by
  obtain ⟨r, rfl⟩ := counit_surjective R r
  rw [← map_teichmuller, frobenius_map, ← map_pow, ← map_teichmuller]
  congr 1
  apply ghostMap_injective fun _ _ hp ↦ .of_ne_zero (Nat.cast_ne_zero.2 hp.ne_zero)
  funext k
  simpa only [ghostMap_frobenius, ghostMap_teichmuller] using pow_mul r n (k : ℕ)

private theorem sum_verschiebung_teichmuller_of_ghostMap_injective
    (hinj : Function.Injective (ghostMap : BigWittVector T R →+* (T → R)))
    (h : T ≤ S) (s : Finset ℕ) (hs : ∀ n ∈ T, n ∈ s) (x : BigWittVector S R) :
    (∑ d ∈ s, verschiebung d (teichmuller (T / d) (x.coeff d))) = restrict h x := by
  apply hinj
  funext n
  let g := (Pi.evalRingHom (fun _ : T ↦ R) n).comp (ghostMap (S := T) (R := R))
  calc
    g (∑ d ∈ s, verschiebung d (teichmuller (T / d) (x.coeff d))) =
        ∑ d ∈ s, g (verschiebung d (teichmuller (T / d) (x.coeff d))) := map_sum g _ _
    _ = ∑ d ∈ (n : ℕ).divisors, (d : R) * x.coeff d ^ ((n : ℕ) / d) := by
      rw [← Finset.sum_subset (fun d hd ↦ hs d (T.mem_of_dvd n.property
        (Nat.dvd_of_mem_divisors hd)))]
      · refine Finset.sum_congr rfl fun d hd ↦ ?_
        have hdn := Nat.dvd_of_mem_divisors hd
        have hk := ghostMap_verschiebung_mul (S := T) d (teichmuller (T / d) (x.coeff d))
          ⟨(n : ℕ) / d, TruncationSet.div_mem_div n.property hdn⟩
        simpa [g, Nat.mul_div_cancel' hdn] using hk
      · intro d _ hd
        have hdn : ¬ d ∣ (n : ℕ) := fun hd' ↦ hd
          (Nat.mem_divisors.2 ⟨hd', T.ne_zero_of_mem n.property⟩)
        exact ghostMap_verschiebung_of_not_dvd _ _ hdn
    _ = g (restrict h x) := by
      rw [← ghostPolynomial_eq_sum]
      simpa only [g, RingHom.comp_apply, Pi.evalRingHom_apply, ghostMap_apply] using
        (ghostMap_restrict h x n).symm

/-- On a finite restriction, the Witt vector is the sum of Verschiebung translates of the
Teichmüller representatives of its coefficients. The sum can use any finite set containing every
index of the smaller truncation set. -/
theorem sum_verschiebung_teichmuller_eq_restrict (h : T ≤ S) (s : Finset ℕ)
    (hs : ∀ n ∈ T, n ∈ s) (x : BigWittVector S R) :
    (∑ d ∈ s, verschiebung d (teichmuller (T / d) (x.coeff d))) = restrict h x := by
  obtain ⟨x, rfl⟩ := map_surjective (counit R) (counit_surjective R) x
  have hx := sum_verschiebung_teichmuller_of_ghostMap_injective
    (fun _ _ e ↦ ghostMap_injective (fun _ _ hp ↦ .of_ne_zero (Nat.cast_ne_zero.2 hp.ne_zero)) e)
    h s hs x
  simpa only [map_sum, ← verschiebung_map, map_teichmuller, coeff_map, map_restrict] using
    congrArg (map (counit R)) hx

/-- The partial Teichmüller sum agrees with the original vector upon restriction to any truncation
set whose indices already occur in the sum. This gives convergence in the finite-restriction
topology. -/
theorem restrict_sum_verschiebung_teichmuller (h : T ≤ S) (s : Finset ℕ)
    (hs : ∀ n ∈ T, n ∈ s) (x : BigWittVector S R) :
    restrict h (∑ d ∈ s, verschiebung d (teichmuller (S / d) (x.coeff d))) = restrict h x := by
  simpa only [map_sum, restrict_verschiebung, restrict_teichmuller] using
    sum_verschiebung_teichmuller_eq_restrict h s hs x

end TauCeti.BigWittVector
