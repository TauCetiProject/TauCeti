/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Nonunits and domination for valuation subrings

A valuation subring `A` of a field is determined by its nonunits, and a valuation subring
dominating `A` (containing it, with every nonunit of `A` a nonunit) is `A` itself. Pulling a
valuation subring back along a field homomorphism `f` detects nonunits through `f`, so a
valuation subring dominates its pullback, and conversely a valuation subring pulls back to any
valuation subring that it dominates through `f`. A valuation subring `A` of `L` lying over a
valuation subring `B` of `K` (that is, `A.comap f = B`) keeps the units and nonunits of `B`, and
when `f` is the structure map of an algebra it contains the integral closure of `B` in `L`.

## Main results

* `ValuationSubring.mem_nonunits_comap`: nonunits of a pulled-back valuation subring.
* `ValuationSubring.eq_of_le_of_nonunits_le`: a valuation subring equals any valuation subring
  dominating it.
* `ValuationSubring.isLocalHom_restrict`: a valuation subring dominates its pullback.
* `ValuationSubring.comap_eq_of_map_maximalIdeal_le`: a valuation subring `W` of `L` pulls back to
  a valuation subring `V` of `K` when `V` maps through a ring `S` into `W`, with its maximal ideal
  landing in an ideal of `S` that is sent into the nonunits of `W`.
* `ValuationSubring.integralClosure_le_of_comap_eq`: a valuation subring of `L` lying over a
  valuation subring `B` of `K` contains the integral closure of `B` in `L`.

## References

* [Stacks Project, Tag 00IA](https://stacks.math.columbia.edu/tag/00IA) (valuation rings
  dominating a local ring).
-/

public section

open IsLocalRing

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L]

/-- An element lies in the nonunits of a pulled-back valuation subring exactly when its image
lies in the nonunits of the original one. -/
@[simp]
theorem mem_nonunits_comap {A : ValuationSubring L} {f : K →+* L} {x : K} :
    x ∈ (A.comap f).nonunits ↔ f x ∈ A.nonunits := by
  simp [mem_nonunits_iff_or, map_inv₀]

/-- A valuation subring is determined by any valuation subring dominating it: if `A ≤ B` and
every nonunit of `A` is a nonunit of `B`, then `A = B`. -/
theorem eq_of_le_of_nonunits_le {A B : ValuationSubring K} (h : A ≤ B)
    (h' : A.nonunits ≤ B.nonunits) : A = B :=
  nonunits_injective (le_antisymm h' (nonunits_le_nonunits.mpr h))

/-- The inclusion of a pulled-back valuation subring `A.comap f` into `A` is a local
homomorphism: a valuation subring dominates its pullback. -/
theorem isLocalHom_restrict (A : ValuationSubring L) (f : K →+* L) {B : ValuationSubring K}
    (hB : B = A.comap f) : IsLocalHom (f.restrict B A fun _ hx ↦ mem_comap.mp (hB ▸ hx)) := by
  refine ⟨fun ⟨x, hx⟩ ha ↦ ?_⟩
  subst hB
  rw [← notMem_maximalIdeal, ← coe_mem_nonunits_iff] at ha ⊢
  exact mem_nonunits_comap.not.mpr ha

/-- Let `ψ : S →+* L` map into a valuation subring `W` of the field `L`, sending an ideal `Q` into
the nonunits of `W`. If a valuation subring `V` of `K` maps to `S` with its maximal ideal in `Q`,
compatibly with `g : K →+* L`, then `W` dominates the image of `V`, so `W` pulls back to `V`. -/
theorem comap_eq_of_map_maximalIdeal_le {S : Type*} [CommRing S]
    {V : ValuationSubring K} {W : ValuationSubring L} (ι : V →+* S) (ψ : S →+* L) {Q : Ideal S}
    (hQ : (maximalIdeal V).map ι ≤ Q) (hmem : ∀ s, ψ s ∈ W) (hnon : ∀ s ∈ Q, ψ s ∈ W.nonunits)
    (g : K →+* L) (hg : ∀ v : V, g v = ψ (ι v)) : W.comap g = V := by
  refine (eq_of_le_of_nonunits_le (fun x hx ↦ ?_) fun x hx ↦ ?_).symm
  · simpa only [mem_comap, hg ⟨x, hx⟩] using hmem (ι ⟨x, hx⟩)
  · simpa only [mem_nonunits_comap, hg ⟨x, nonunits_subset hx⟩] using
      hnon _ (hQ (Ideal.mem_map_of_mem _ (coe_mem_nonunits_iff.mp hx)))

section LyingOver

variable {A : ValuationSubring L} {B : ValuationSubring K} {f : K →+* L}

/-- If `A` lies over `B`, an element of `K` has valuation below `1` for `B` iff its image does
for `A`. -/
theorem valuation_apply_lt_one_iff_of_comap_eq (h : A.comap f = B) (x : K) :
    A.valuation (f x) < 1 ↔ B.valuation x < 1 := by
  rw [← mem_nonunits_iff, ← mem_nonunits_iff, ← h, mem_nonunits_comap]

/-- If `A` lies over `B`, an element of `K` has valuation at most `1` for `B` iff its image does
for `A`. -/
theorem valuation_apply_le_one_iff_of_comap_eq (h : A.comap f = B) (x : K) :
    A.valuation (f x) ≤ 1 ↔ B.valuation x ≤ 1 := by
  rw [valuation_le_one_iff, valuation_le_one_iff, ← h, mem_comap]

/-- If `A` lies over `B`, a unit of `B` maps to a unit of `A`. -/
theorem valuation_apply_eq_one_of_comap_eq (h : A.comap f = B) {b : B} (hb : IsUnit b) :
    A.valuation (f b) = 1 := by
  refine le_antisymm ((valuation_apply_le_one_iff_of_comap_eq h _).mpr (B.valuation_le_one b))
    (not_lt.mp fun hlt ↦ ?_)
  exact ((valuation_eq_one_iff B b).mp hb).not_lt
    ((valuation_apply_lt_one_iff_of_comap_eq h _).mp hlt)

/-- If `A` lies over `B`, a nonunit of `B` maps to a nonunit of `A`. -/
theorem valuation_apply_lt_one_of_comap_eq (h : A.comap f = B) {b : B} (hb : ¬IsUnit b) :
    A.valuation (f b) < 1 := by
  rw [valuation_apply_lt_one_iff_of_comap_eq h]
  exact (valuation_lt_one_iff B b).mp ((mem_maximalIdeal _).mpr hb)

/-- A valuation subring of `L` lying over a valuation subring `B` of `K` contains the integral
closure of `B` in `L`. -/
theorem integralClosure_le_of_comap_eq [Algebra K L] {A : ValuationSubring L}
    (h : A.comap (algebraMap K L) = B) : (integralClosure B L).toSubring ≤ A.toSubring := by
  have : IsIntegrallyClosedIn A L :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn L).mp inferInstance
  -- `Subring.integralClosure_le_iff` asks for the instance on `A.toSubring`, whose carrier is `A`
  have : IsIntegrallyClosedIn A.toSubring L := inferInstanceAs (IsIntegrallyClosedIn A L)
  refine Subring.integralClosure_le_iff.mpr fun b ↦ ?_
  rw [IsScalarTower.algebraMap_apply B K L]
  exact (valuation_le_one_iff _ _).mp
    ((valuation_apply_le_one_iff_of_comap_eq h _).mpr (B.valuation_le_one b))

end LyingOver

end ValuationSubring
