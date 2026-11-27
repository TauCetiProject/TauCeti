/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Unimodular
public import Mathlib.RingTheory.ZMod.LocalRing

import Mathlib.RingTheory.PrincipalIdealDomain
import TauCeti.Data.ZMod.Count
import TauCeti.LinearAlgebra.Unimodular.Card
import TauCeti.LinearAlgebra.Unimodular.Extension
import TauCeti.RingTheory.LocalRing.Card

/-!
# Primitive vectors over finite rings

A vector `v : ι → R` over a finite commutative ring is *primitive* when its coordinates generate
the unit ideal, that is when it is unimodular in the sense of `Module.IsUnimodular`. Over
`R = ZMod Q` these are the residue vectors `b` with `gcd(Q, b₀, …, bₙ) = 1`, the points over which
the local density of a form modulo `Q` counts zeros. This file defines the finite set
`FormDensity.primitiveVectors ι R` and computes it:

* membership is unimodularity (`FormDensity.mem_primitiveVectors`), and modulo `Q` it is the
  condition `gcd(Q, b₀, …, bₙ) = 1` on integer lifts
  (`FormDensity.mem_primitiveVectors_zmod_iff_gcd`);
* by the Chinese remainder theorem the count is multiplicative in coprime moduli
  (`FormDensity.card_primitiveVectors_zmod_mul`);
* modulo a positive prime power there are `p ^ (r m) - p ^ ((r - 1) m)` primitive vectors of length
  `m` (`FormDensity.card_primitiveVectors_zmod_prime_pow`);
* over a finite local ring with maximal ideal `𝔪`, the primitive vectors of length `m` orthogonal
  to a fixed primitive vector number `#Rᵐ⁻¹ - #𝔪ᵐ⁻¹`, whichever primitive vector is fixed
  (`FormDensity.card_primitiveVectors_filter_dotProduct_eq_zero`).

The general facts about unimodular vectors that these rest on are in
`TauCeti.LinearAlgebra.Unimodular`, `TauCeti.LinearAlgebra.Unimodular.Card` and
`TauCeti.RingTheory.LocalRing.Card`.

## References

* T. Browning, P. Le Boudec, W. Sawin, *The Hasse principle for random Fano hypersurfaces*,
  arXiv:2006.02356v1, §5.1 and (5.10).
-/

public section

open Finset IsLocalRing

open scoped Matrix

namespace TauCeti.FormDensity

variable {ι R : Type*} [Fintype ι] [CommRing R] [Fintype R]

variable (ι R) in
/-- The primitive vectors over a finite commutative ring: the unimodular vectors, those whose
coordinates generate the unit ideal. -/
noncomputable def primitiveVectors : Finset (ι → R) := by
  classical
  exact univ.filter fun v ↦ Module.IsUnimodular R v

@[simp]
theorem mem_primitiveVectors {v : ι → R} :
    v ∈ primitiveVectors ι R ↔ Module.IsUnimodular R v := by
  simp [primitiveVectors]

/-- **Primitivity modulo `Q` as a gcd condition.** The reduction modulo `Q` of an integral vector
`b` is primitive exactly when `gcd(Q, b₀, …, bₙ) = 1`. -/
theorem mem_primitiveVectors_zmod_iff_gcd {Q : ℕ} [NeZero Q] {b : ι → ℤ} :
    (fun i ↦ (b i : ZMod Q)) ∈ primitiveVectors ι (ZMod Q) ↔ Int.gcd Q (univ.gcd b) = 1 := by
  rw [mem_primitiveVectors]
  constructor
  · -- Reducing further modulo `g = gcd(Q, b₀, …, bₙ)` gives a unimodular zero vector.
    intro h
    set g := Int.gcd Q (univ.gcd b)
    have hgQ : g ∣ Q := Int.natCast_dvd_natCast.mp (Int.gcd_dvd_left ..)
    have hzero : ⇑(ZMod.castHom hgQ (ZMod g)) ∘ (fun i ↦ (b i : ZMod Q)) = 0 := funext fun i ↦ by
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using
        (Int.gcd_dvd_right ..).trans (Finset.gcd_dvd (mem_univ i))
    obtain ⟨f, hf⟩ := Module.isUnimodular_iff.mp (hzero ▸ h.ringHom_comp (ZMod.castHom hgQ _))
    rw [map_zero] at hf
    exact ZMod.subsingleton_iff.mp (subsingleton_of_zero_eq_one hf)
  · -- Bezout: `1 = x Q + y ∑ᵢ cᵢ bᵢ`, which reduces to `1 = ∑ᵢ (y cᵢ) bᵢ` modulo `Q`.
    intro h
    obtain ⟨x, y, hxy⟩ := Int.isCoprime_iff_gcd_eq_one.mpr h
    obtain ⟨c, hc⟩ := Finset.gcd_eq_sum_mul univ b
    refine TauCeti.Module.isUnimodular_pi_iff.mpr ⟨fun i ↦ (y * c i : ℤ), ?_⟩
    have hQ := congrArg (Int.cast : ℤ → ZMod Q) hxy
    push_cast [hc, ZMod.natCast_self] at hQ
    have hsum : ∑ i, (b i : ZMod Q) * ((y * c i : ℤ) : ZMod Q) =
        y * ∑ i, (b i : ZMod Q) * c i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by push_cast; ring
    linear_combination hsum + hQ

/-- The number of primitive vectors is the number of unimodular vectors. -/
theorem card_primitiveVectors :
    #(primitiveVectors ι R) = Nat.card {v : ι → R // Module.IsUnimodular R v} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1

/-- **Chinese remainder theorem for primitive vectors.** For coprime moduli, the number of
primitive vectors modulo `Q₁ Q₂` is the product of the numbers modulo `Q₁` and modulo `Q₂`. -/
theorem card_primitiveVectors_zmod_mul {Q₁ Q₂ : ℕ} [NeZero Q₁] [NeZero Q₂]
    (h : Q₁.Coprime Q₂) :
    #(primitiveVectors ι (ZMod (Q₁ * Q₂))) =
      #(primitiveVectors ι (ZMod Q₁)) * #(primitiveVectors ι (ZMod Q₂)) := by
  simp only [card_primitiveVectors, TauCeti.Module.card_isUnimodular_zmod_mul ι h]

/-- Over the zero ring every vector is primitive, so there is exactly one primitive vector, even
for the empty index type. -/
theorem card_primitiveVectors_of_subsingleton [Subsingleton R] : #(primitiveVectors ι R) = 1 := by
  classical
  have : primitiveVectors ι R = univ := eq_univ_of_forall fun v ↦ mem_primitiveVectors.mpr
    (Module.isUnimodular_of_apply_eq_one (f := 0) (Subsingleton.elim _ _))
  rw [this, card_univ, Fintype.card_eq_one_iff]
  exact ⟨0, fun _ ↦ Subsingleton.elim _ _⟩

/-- **Counting primitive vectors modulo a prime power.** For a prime `p` and `r ≠ 0` there are
`p ^ (r m) - p ^ ((r - 1) m)` primitive vectors of length `m` modulo `p ^ r`; for `m = 0` both
sides vanish. -/
theorem card_primitiveVectors_zmod_prime_pow (p r : ℕ) [Fact p.Prime] (hr : r ≠ 0) :
    #(primitiveVectors ι (ZMod (p ^ r))) =
      p ^ (r * Fintype.card ι) - p ^ ((r - 1) * Fintype.card ι) := by
  have : NeZero r := ⟨hr⟩
  classical
  have hmax : Nat.card (IsLocalRing.maximalIdeal (ZMod (p ^ r))) = p ^ (r - 1) := by
    rw [← ZMod.card_filter_not_isUnit_prime_pow p r hr, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rw [card_primitiveVectors, TauCeti.IsLocalRing.card_isUnimodular, hmax, Nat.card_zmod,
    pow_mul, pow_mul]

section LocalRing

variable [IsLocalRing R] [DecidableEq R]

/-- Over a finite local ring, the primitive vectors of length `m` with a prescribed zero coordinate
are the primitive vectors of length `m - 1`: there are `#Rᵐ⁻¹ - #𝔪ᵐ⁻¹` of them. -/
theorem card_primitiveVectors_filter_apply_eq_zero (j : ι) :
    #{a ∈ primitiveVectors ι R | a j = 0} =
      Nat.card R ^ (Fintype.card ι - 1) - Nat.card (maximalIdeal R) ^ (Fintype.card ι - 1) := by
  classical
  have hcard : Fintype.card {i // i ≠ j} = Fintype.card ι - 1 := by simp
  rw [← hcard, ← TauCeti.IsLocalRing.card_isUnimodular, ← card_primitiveVectors]
  refine card_nbij' (fun a i ↦ a i) (fun c i ↦ if h : i = j then 0 else c ⟨i, h⟩) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_coe, mem_filter, mem_primitiveVectors,
      TauCeti.Module.isUnimodular_iff_exists_isUnit] at ha
    obtain ⟨⟨i, hi⟩, haj⟩ := ha
    have hij : i ≠ j := by
      rintro rfl
      exact not_isUnit_zero (haj ▸ hi)
    simpa [TauCeti.Module.isUnimodular_iff_exists_isUnit] using ⟨i, hij, hi⟩
  · intro c hc
    simp only [mem_coe, mem_primitiveVectors, TauCeti.Module.isUnimodular_iff_exists_isUnit] at hc
    obtain ⟨⟨i, hij⟩, hi⟩ := hc
    simp only [mem_coe, mem_filter, mem_primitiveVectors, ↓reduceDIte,
      TauCeti.Module.isUnimodular_iff_exists_isUnit]
    exact ⟨⟨i, by simpa [hij] using hi⟩, trivial⟩
  · intro a ha
    simp only [mem_coe, mem_filter] at ha
    funext i
    by_cases h : i = j
    · subst h
      simp [ha.2]
    · simp [h]
  · intro c _
    funext i
    simp [i.property]

/-- **Primitive vectors orthogonal to a primitive vector.** Over a finite local ring, for a
primitive vector `w` of length `m`, there are `#Rᵐ⁻¹ - #𝔪ᵐ⁻¹` primitive vectors `a` with
`a ⬝ᵥ w = 0`, independently of `w`. -/
theorem card_primitiveVectors_filter_dotProduct_eq_zero {w : ι → R}
    (hw : Module.IsUnimodular R w) :
    #{a ∈ primitiveVectors ι R | a ⬝ᵥ w = 0} =
      Nat.card R ^ (Fintype.card ι - 1) - Nat.card (maximalIdeal R) ^ (Fintype.card ι - 1) := by
  -- An invertible matrix `P` carries `w` to a standard basis vector `eⱼ`, so that
  -- `a ⬝ᵥ w = (a ᵥ* P⁻¹) j`; right multiplication by `P⁻¹` preserves primitivity.
  classical
  obtain ⟨j, hj⟩ := TauCeti.Module.isUnimodular_iff_exists_isUnit.mp hw
  obtain ⟨P, hP⟩ := unimodularEquiv_iff.mp (unimodularEquiv_single_of_isUnit hj j)
  have hdot (a : ι → R) : a ⬝ᵥ w = (a ᵥ* (↑P⁻¹ : Matrix ι ι R)) j := by
    have hw' : w = (↑P⁻¹ : Matrix ι ι R) *ᵥ Pi.single j 1 := by
      rw [← hP, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hw', Matrix.dotProduct_mulVec, dotProduct_single, mul_one]
  rw [← card_primitiveVectors_filter_apply_eq_zero j]
  refine card_nbij' (· ᵥ* (↑P⁻¹ : Matrix ι ι R)) (· ᵥ* (P : Matrix ι ι R)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_coe, mem_filter, mem_primitiveVectors] at ha ⊢
    exact ⟨(P⁻¹).isUnimodular_vecMul_iff.mpr ha.1, hdot a ▸ ha.2⟩
  · intro b hb
    simp only [mem_coe, mem_filter, mem_primitiveVectors] at hb ⊢
    refine ⟨P.isUnimodular_vecMul_iff.mpr hb.1, ?_⟩
    rw [hdot, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.vecMul_one, hb.2]
  · intro a _
    simp [Matrix.vecMul_vecMul]
  · intro b _
    simp [Matrix.vecMul_vecMul]

end LocalRing

end TauCeti.FormDensity
