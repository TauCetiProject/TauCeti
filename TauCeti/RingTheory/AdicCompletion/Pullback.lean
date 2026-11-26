/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Pi
public import TauCeti.RingTheory.LocalRing.Pullback

/-!
# Adic completeness of pullbacks of rings

Let `f : R →+* T` and `g : S →+* T` be ring homomorphisms and `C = R ×_T S` their pullback, the
subring `f.pullback g` of `R × S` on which `f` and `g` agree. Fix a natural number `n`. This file
compares the `n`-adic filtration of `C` with the one induced from `R × S`.

* If `n ^ (k + 1)` divides `x ∈ C` in `R × S` and the `n ^ (k + 1)`-torsion of `T` is killed by
  `n`, then `n ^ k` divides `x` in `C`: writing `x = n ^ (k + 1) (a, b)`, the defect `f a - g b` is
  killed by `n ^ (k + 1)`, hence by `n`, so `(n a, n b)` lies in `C` and `x = n ^ k (n a, n b)`.
* Consequently, when `R` and `S` are `n`-adically complete, `T` is `n`-adically Hausdorff and the
  `n`-power torsion of `T` is killed by `n`, the pullback `C` is `n`-adically complete: limits are
  taken componentwise, they lie in `C` because `T` is separated, and the shifted comparison of
  filtrations turns componentwise convergence into convergence in `C`.

The torsion hypothesis is needed for the first step, the comparison of filtrations. For
`R = S = ℤ_p`, `T = ℤ ⧸ p ^ 2` and `f = g` the reduction, `n = p`, the element `(p ^ 2, 0)` of `C`
is divisible by `p ^ 2` in `ℤ_p × ℤ_p` but not by `p` in `C`, since `(p, 0) ∉ C`.

This is the completeness input for tilting fibre products of perfectoid rings, where `T` is
integral perfectoid, whose `p`-power torsion is killed by `p`.

## Main results

* `RingHom.pullback_natCast_pow_dvd_of_pow_succ_dvd`: `n ^ (k + 1) (R × S) ∩ C ⊆ n ^ k C` when the
  `n ^ (k + 1)`-torsion of `T` is killed by `n`.
* `RingHom.pullback_natCast_pow_dvd_fst`, `RingHom.pullback_natCast_pow_dvd_snd`: divisibility by
  `n ^ k` in `C` passes to the components.
* `IsHausdorff.pullback_span_natCast`: `C` is `n`-adically Hausdorff when `R` and `S` are.
* `IsPrecomplete.pullback_span_natCast`, `IsAdicComplete.pullback_span_natCast`: `C` is
  `n`-adically precomplete, respectively complete, when `R` and `S` are, `T` is `n`-adically
  Hausdorff and its `n`-power torsion is killed by `n`.

## References

* K. Česnavičius, P. Scholze, *Purity for flat cohomology*, proof of Proposition 2.1.4, p. 12.
-/

public section

open Ideal

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* T) (g : S →+* T)
  (n : ℕ)

namespace RingHom

variable {f g n} in
/-- If `n ^ (k + 1)` divides an element `x` of the pullback `R ×_T S` in `R × S`, and `n` kills
the `n ^ (k + 1)`-torsion of `T`, then `n ^ k` divides `x` in the pullback. -/
theorem pullback_natCast_pow_dvd_of_pow_succ_dvd {k : ℕ}
    (htors : ∀ y : T, (n : T) ^ (k + 1) * y = 0 → (n : T) * y = 0) {x : f.pullback g}
    (hx : (n : R × S) ^ (k + 1) ∣ (x : R × S)) : (n : f.pullback g) ^ k ∣ x := by
  obtain ⟨⟨a, b⟩, hab⟩ := hx
  have hx : f (x : R × S).1 = g (x : R × S).2 := mem_pullback.mp x.property
  rw [hab] at hx
  have hmem : ((n : R × S) * (a, b)) ∈ f.pullback g := by
    rw [mem_pullback]
    have h0 : (n : T) ^ (k + 1) * (f a - g b) = 0 := by
      simpa [mul_sub, sub_eq_zero] using hx
    simpa [mul_sub, sub_eq_zero] using htors _ h0
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  simp only [hab, Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, pow_succ, mul_assoc]

variable {f g n} in
/-- If `n ^ k` divides an element `x` of the pullback `R ×_T S`, then `n ^ k` divides its first
component. -/
theorem pullback_natCast_pow_dvd_fst {k : ℕ} {x : f.pullback g}
    (hx : (n : f.pullback g) ^ k ∣ x) : (n : R) ^ k ∣ (x : R × S).1 := by
  simpa using map_dvd (f.pullbackFst g) hx

variable {f g n} in
/-- If `n ^ k` divides an element `x` of the pullback `R ×_T S`, then `n ^ k` divides its second
component. -/
theorem pullback_natCast_pow_dvd_snd {k : ℕ} {x : f.pullback g}
    (hx : (n : f.pullback g) ^ k ∣ x) : (n : S) ^ k ∣ (x : R × S).2 := by
  simpa using map_dvd (f.pullbackSnd g) hx

end RingHom

/-- The pullback `R ×_T S` is `n`-adically Hausdorff when `R` and `S` are. -/
instance IsHausdorff.pullback_span_natCast [IsHausdorff (span {(n : R)}) R]
    [IsHausdorff (span {(n : S)}) S] :
    IsHausdorff (span {(n : f.pullback g)}) (f.pullback g) := by
  refine ⟨fun x hx ↦ Subtype.ext (Prod.ext ?_ ?_)⟩ <;>
    simp only [TauCeti.sModEq_span_singleton_pow_iff, sub_zero] at hx
  · refine IsHausdorff.haus (I := span {(n : R)}) inferInstance _ fun k ↦ ?_
    rw [TauCeti.sModEq_span_singleton_pow_iff, sub_zero]
    exact RingHom.pullback_natCast_pow_dvd_fst (hx k)
  · refine IsHausdorff.haus (I := span {(n : S)}) inferInstance _ fun k ↦ ?_
    rw [TauCeti.sModEq_span_singleton_pow_iff, sub_zero]
    exact RingHom.pullback_natCast_pow_dvd_snd (hx k)

variable {f g n}

/-- The pullback `R ×_T S` is `n`-adically precomplete when `R` and `S` are, `T` is `n`-adically
Hausdorff and the `n`-power torsion of `T` is killed by `n`. -/
theorem IsPrecomplete.pullback_span_natCast [IsPrecomplete (span {(n : R)}) R]
    [IsPrecomplete (span {(n : S)}) S] [IsHausdorff (span {(n : T)}) T]
    (htors : ∀ (k : ℕ) (y : T), (n : T) ^ k * y = 0 → (n : T) * y = 0) :
    IsPrecomplete (span {(n : f.pullback g)}) (f.pullback g) := by
  refine ⟨fun φ hφ ↦ ?_⟩
  simp only [TauCeti.sModEq_span_singleton_pow_iff] at hφ
  -- the components of `φ` are Cauchy, so converge in `R` and `S`
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (I := span {(n : R)}) inferInstance
    (f := fun k ↦ ((φ k : R × S)).1) fun hmk ↦ by
      rw [TauCeti.sModEq_span_singleton_pow_iff]
      exact RingHom.pullback_natCast_pow_dvd_fst (hφ hmk)
  obtain ⟨b, hb⟩ := IsPrecomplete.prec (I := span {(n : S)}) inferInstance
    (f := fun k ↦ ((φ k : R × S)).2) fun hmk ↦ by
      rw [TauCeti.sModEq_span_singleton_pow_iff]
      exact RingHom.pullback_natCast_pow_dvd_snd (hφ hmk)
  simp only [TauCeti.sModEq_span_singleton_pow_iff] at ha hb
  -- the limit `(a, b)` lies in the pullback because `T` is separated
  have hab : (a, b) ∈ f.pullback g := by
    refine RingHom.mem_pullback.mpr <|
      (IsHausdorff.eq_iff_smodEq (I := span {(n : T)})).mpr fun k ↦ ?_
    rw [TauCeti.sModEq_span_singleton_pow_iff]
    have hk : f (φ k : R × S).1 = g (φ k : R × S).2 :=
      RingHom.mem_pullback.mp (φ k).property
    have hfa := map_dvd f (ha k)
    have hgb := map_dvd g (hb k)
    rw [map_pow, map_natCast, map_sub] at hfa hgb
    rw [← dvd_neg, neg_sub, hk] at hfa
    simpa using dvd_add hfa hgb
  refine ⟨⟨(a, b), hab⟩, fun k ↦ ?_⟩
  rw [TauCeti.sModEq_span_singleton_pow_iff]
  -- `φ (k + 1)` is within `n ^ (k + 1)` of the limit in `R × S`, hence within `n ^ k` in `C`
  have hlim : (n : f.pullback g) ^ k ∣ φ (k + 1) - ⟨(a, b), hab⟩ :=
    RingHom.pullback_natCast_pow_dvd_of_pow_succ_dvd (htors (k + 1)) <|
      Prod.mk_dvd_mk.mpr ⟨by simpa using ha (k + 1), by simpa using hb (k + 1)⟩
  simpa using dvd_add (hφ k.le_succ) hlim

/-- The pullback `R ×_T S` is `n`-adically complete when `R` and `S` are, `T` is `n`-adically
Hausdorff and the `n`-power torsion of `T` is killed by `n`. -/
theorem IsAdicComplete.pullback_span_natCast [IsAdicComplete (span {(n : R)}) R]
    [IsAdicComplete (span {(n : S)}) S] [IsHausdorff (span {(n : T)}) T]
    (htors : ∀ (k : ℕ) (y : T), (n : T) ^ k * y = 0 → (n : T) * y = 0) :
    IsAdicComplete (span {(n : f.pullback g)}) (f.pullback g) where
  toIsHausdorff := .pullback_span_natCast f g n
  toIsPrecomplete := .pullback_span_natCast htors
