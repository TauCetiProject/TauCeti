/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import TauCeti.RingTheory.AdicCompletion.Pi
public import TauCeti.RingTheory.Pullback

/-!
# Adic completeness of fibre products of rings

Let `f : R →+* T` and `g : S →+* T` be ring homomorphisms and `C = R ×_T S` their fibre product
(Mathlib's `RingHom.pullback f g`, the subring of pairs `(r, s)` with `f r = g s`). Fix
`π = (π₁, π₂) ∈ C` and write `π_T = f π₁ = g π₂`. This file shows that `C` is `π`-adically
complete as soon as `R` and `S` are `π₁`- and `π₂`-adically complete, `T` is `π_T`-adically
separated and the `π_T`-power torsion of `T` is bounded, that is, killed by a fixed power
`π_T ^ N`.

The point is the comparison of the `π`-adic filtration of `C` with the filtration induced from
`R × S`. Divisibility by `π ^ k` in `R × S` does not imply divisibility in `C`: if
`x = π ^ k (a, b)` lies in `C`, the defect `f a - g b` is only known to be killed by `π_T ^ k`.
When `π_T`-power torsion is killed by `π_T ^ N`, the defect is killed by `π_T ^ N`, so
`(π₁ ^ N a, π₂ ^ N b)` lies in `C` and `x ∈ π ^ (k - N) C`:
`π ^ (n + N) (R × S) ∩ C ⊆ π ^ n C` (`RingHom.pullback_pow_dvd_of_pow_add_dvd`). Hence the
`π`-adic topology of `C` is the topology induced from `R × S`, and `C` is closed in `R × S`
because `T` is separated.

For `π = p` and `N = 1` this is the completeness step of the computation of the tilt of a fibre
product of `p`-adically complete rings along a ring `A'` with `A'[p ^ ∞] = A'[p]`, a condition
satisfied by every integral perfectoid ring. Without a torsion bound the comparison fails: for
`T = ℤ ⧸ p ^ 2`, the class of `1` is killed by `p ^ 2` but not by `p`.

## Main results

* `RingHom.pullback_pow_dvd_of_pow_add_dvd`: if `π ^ (n + N)` divides `x ∈ C` in `R × S` and
  the `π_T ^ (n + N)`-torsion of `T` is killed by `π_T ^ N`, then `π ^ n` divides `x` in `C`.
* `RingHom.isHausdorff_pullback`: `C` is `π`-adically separated when `R` and `S` are.
* `RingHom.isPrecomplete_pullback`: `C` is `π`-adically precomplete when `R` and `S` are,
  `T` is `π_T`-adically separated and its `π_T`-power torsion is bounded.
* `RingHom.isAdicComplete_pullback`, `RingHom.isAdicComplete_span_natCast_pullback`: the
  corresponding completeness statements, for an element of `C` and for a natural number.

## References

* K. Česnavičius, P. Scholze, *Purity for flat cohomology*, §2.1.1 and the proof of
  Proposition 2.1.4, second paragraph.
-/

public section

open Ideal

namespace RingHom

section Ring

variable {R S T : Type*} [Ring R] [Ring S] [Ring T] (f : R →+* T) (g : S →+* T)

/-- **Divisibility in a fibre product.** Let `x, π ∈ R ×_T S` with `π ^ (n + N)` dividing `x`
in `R × S`. If the `π_T ^ (n + N)`-torsion of `T` is killed by `π_T ^ N`, where
`π_T = f (pullbackFst π)`, then `π ^ n` divides `x` in `R ×_T S`. -/
theorem pullback_pow_dvd_of_pow_add_dvd {π x : f.pullback g} {n N : ℕ}
    (hT : ∀ y : T, f (f.pullbackFst g π) ^ (n + N) * y = 0 →
      f (f.pullbackFst g π) ^ N * y = 0)
    (hx : (π : R × S) ^ (n + N) ∣ (x : R × S)) : π ^ n ∣ x := by
  obtain ⟨⟨a, b⟩, hab⟩ := hx
  have hπ := f.pullback_comm_sq_apply g π
  have hx₁ : (x : R × S).1 = (π : R × S).1 ^ (n + N) * a := congr($hab.1)
  have hx₂ : (x : R × S).2 = (π : R × S).2 ^ (n + N) * b := congr($hab.2)
  -- the defect `f a - g b` is killed by `π_T ^ (n + N)`, hence by `π_T ^ N`
  have hdef : f (π : R × S).1 ^ N * (f a - g b) = 0 := by
    refine hT _ ?_
    have hfx := f.pullback_comm_sq_apply g x
    rw [hx₁, hx₂, map_mul, map_mul, map_pow, map_pow, ← hπ] at hfx
    simp only [pullbackFst, coe_comp, Subring.coe_subtype, Function.comp_apply, coe_fst]
    rw [mul_sub, hfx, sub_self]
  -- so `(π₁ ^ N a, π₂ ^ N b)` lies in the fibre product, and `x` is `π ^ n` times it
  refine ⟨⟨((π : R × S).1 ^ N * a, (π : R × S).2 ^ N * b), ?_⟩, ?_⟩
  · rw [mem_eqLocus, comp_apply, comp_apply, coe_fst, coe_snd, map_mul, map_mul, map_pow,
      map_pow, ← hπ, ← sub_eq_zero, ← mul_sub, hdef]
  · refine Subtype.ext (Prod.ext ?_ ?_)
    · simp only [Subring.coe_mul, Subring.coe_pow, Prod.fst_mul, Prod.pow_fst, hx₁, pow_add,
        mul_assoc]
    · simp only [Subring.coe_mul, Subring.coe_pow, Prod.snd_mul, Prod.pow_snd, hx₂, pow_add,
        mul_assoc]

end Ring

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* T) (g : S →+* T)

/-- A fibre product `R ×_T S` is `π`-adically separated when `R` is `π₁`-adically separated and
`S` is `π₂`-adically separated, where `π = (π₁, π₂)`. -/
theorem isHausdorff_pullback (π : f.pullback g)
    [IsHausdorff (span {f.pullbackFst g π}) R] [IsHausdorff (span {f.pullbackSnd g π}) S] :
    IsHausdorff (span {π}) (f.pullback g) where
  haus' x hx := by
    simp only [TauCeti.sModEq_span_singleton_pow_iff, sub_zero] at hx
    refine Subtype.ext (Prod.ext ?_ ?_)
    · refine IsHausdorff.haus (I := span {f.pullbackFst g π}) inferInstance _ fun n ↦ ?_
      rw [TauCeti.sModEq_span_singleton_pow_iff, sub_zero, ← map_pow]
      exact map_dvd _ (hx n)
    · refine IsHausdorff.haus (I := span {f.pullbackSnd g π}) inferInstance _ fun n ↦ ?_
      rw [TauCeti.sModEq_span_singleton_pow_iff, sub_zero, ← map_pow]
      exact map_dvd _ (hx n)

/-- A fibre product `R ×_T S` is `π`-adically precomplete, `π = (π₁, π₂)`, when `R` and `S` are
`π₁`- and `π₂`-adically precomplete, `T` is `π_T`-adically separated for `π_T = f π₁ = g π₂`,
and the `π_T`-power torsion of `T` is killed by `π_T ^ N`. -/
theorem isPrecomplete_pullback (π : f.pullback g) (N : ℕ)
    (hT : ∀ (n : ℕ) (y : T), f (f.pullbackFst g π) ^ n * y = 0 →
      f (f.pullbackFst g π) ^ N * y = 0)
    [IsPrecomplete (span {f.pullbackFst g π}) R] [IsPrecomplete (span {f.pullbackSnd g π}) S]
    [IsHausdorff (span {f (f.pullbackFst g π)}) T] :
    IsPrecomplete (span {π}) (f.pullback g) where
  prec' x hx := by
    simp only [TauCeti.sModEq_span_singleton_pow_iff] at hx ⊢
    -- the projections of a Cauchy sequence converge in `R` and in `S`
    obtain ⟨a, ha⟩ := IsPrecomplete.prec (I := span {f.pullbackFst g π}) inferInstance
      (f := fun n ↦ f.pullbackFst g (x n)) fun hmn ↦ by
        rw [TauCeti.sModEq_span_singleton_pow_iff, ← map_sub, ← map_pow]
        exact map_dvd _ (hx hmn)
    obtain ⟨b, hb⟩ := IsPrecomplete.prec (I := span {f.pullbackSnd g π}) inferInstance
      (f := fun n ↦ f.pullbackSnd g (x n)) fun hmn ↦ by
        rw [TauCeti.sModEq_span_singleton_pow_iff, ← map_sub, ← map_pow]
        exact map_dvd _ (hx hmn)
    simp only [TauCeti.sModEq_span_singleton_pow_iff] at ha hb
    have hπ : f (f.pullbackFst g π) = g (f.pullbackSnd g π) := f.pullback_comm_sq_apply g π
    -- the pair of limits lies in the fibre product, because `T` is separated
    have hab : f a = g b := by
      rw [← sub_eq_zero]
      refine IsHausdorff.haus (I := span {f (f.pullbackFst g π)}) inferInstance _ fun n ↦ ?_
      rw [TauCeti.sModEq_span_singleton_pow_iff, sub_zero]
      have hxn : f (f.pullbackFst g (x n)) = g (f.pullbackSnd g (x n)) :=
        f.pullback_comm_sq_apply g (x n)
      have h₁ := map_dvd f (ha n)
      have h₂ := map_dvd g (hb n)
      rw [map_pow, map_sub] at h₁ h₂
      rw [← hπ] at h₂
      have : f a - g b = g (f.pullbackSnd g (x n)) - g b - (f (f.pullbackFst g (x n)) - f a) := by
        rw [hxn]; ring
      rw [this]
      exact dvd_sub h₂ h₁
    let L : f.pullback g := ⟨(a, b), hab⟩
    refine ⟨L, fun n ↦ ?_⟩
    -- `x (n + N) - L` is divisible by `π ^ (n + N)` in `R × S`, hence by `π ^ n` in the fibre
    -- product, and `x n - x (n + N)` is divisible by `π ^ n` by the Cauchy condition
    have hL : π ^ n ∣ x (n + N) - L := by
      refine f.pullback_pow_dvd_of_pow_add_dvd g (hT (n + N)) ?_
      refine prod_dvd_iff.mpr ⟨?_, ?_⟩
      · exact ha (n + N)
      · exact hb (n + N)
    rw [← sub_add_sub_cancel _ (x (n + N))]
    exact dvd_add (hx (Nat.le_add_right n N)) hL

/-- A fibre product `R ×_T S` is `π`-adically complete, `π = (π₁, π₂)`, when `R` and `S` are
`π₁`- and `π₂`-adically complete, `T` is `π_T`-adically separated for `π_T = f π₁ = g π₂`, and
the `π_T`-power torsion of `T` is killed by `π_T ^ N`. -/
theorem isAdicComplete_pullback (π : f.pullback g) (N : ℕ)
    (hT : ∀ (n : ℕ) (y : T), f (f.pullbackFst g π) ^ n * y = 0 →
      f (f.pullbackFst g π) ^ N * y = 0)
    [IsAdicComplete (span {f.pullbackFst g π}) R] [IsAdicComplete (span {f.pullbackSnd g π}) S]
    [IsHausdorff (span {f (f.pullbackFst g π)}) T] :
    IsAdicComplete (span {π}) (f.pullback g) where
  toIsHausdorff := f.isHausdorff_pullback g π
  toIsPrecomplete := f.isPrecomplete_pullback g π N hT

/-- A fibre product `R ×_T S` of `p`-adically complete rings over a `p`-adically separated ring
`T` whose `p`-power torsion is killed by `p ^ N` is `p`-adically complete. For `N = 1` the
hypothesis on `T` is `T[p ^ ∞] = T[p]`. -/
theorem isAdicComplete_span_natCast_pullback (p N : ℕ)
    (hT : ∀ (n : ℕ) (y : T), (p : T) ^ n * y = 0 → (p : T) ^ N * y = 0)
    [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]
    [IsHausdorff (span {(p : T)}) T] :
    IsAdicComplete (span {(p : f.pullback g)}) (f.pullback g) := by
  have h₁ : f.pullbackFst g p = p := map_natCast _ p
  have h₂ : f.pullbackSnd g p = p := map_natCast _ p
  have : IsAdicComplete (span {f.pullbackFst g p}) R := by rw [h₁]; infer_instance
  have : IsAdicComplete (span {f.pullbackSnd g p}) S := by rw [h₂]; infer_instance
  have : IsHausdorff (span {f (f.pullbackFst g p)}) T := by rw [h₁, map_natCast]; infer_instance
  exact f.isAdicComplete_pullback g p N (by rwa [h₁, map_natCast])

end RingHom
