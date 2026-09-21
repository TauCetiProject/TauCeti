/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.RayClass.Finite
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone

/-!
# Fundamental cones for congruence subgroups of number-field units

For a modulus `𝔪`, its congruence units form a finite-index subgroup of the full unit group.
Consequently a fundamental cone for the congruence units is obtained from Mathlib's
`NumberField.mixedEmbedding.fundamentalCone` by taking one translate for every unit coset.

The resulting `rayFundamentalDomain 𝔪` is a measurable cone. Every point of nonzero mixed norm can
be moved into it by a unit congruent to one modulo `𝔪`. For the trivial modulus it is exactly
Mathlib's fundamental cone. These are the geometric properties needed to count algebraic integers
in a fixed ray class; boundary regularity is developed separately.

As with Mathlib's cone, the word “fundamental” is modulo torsion: different translates can meet
along the action of roots of unity. The representative comparison theorem below makes this overlap
explicit instead of claiming literal uniqueness.

## Main definitions

* `TauCeti.GlobalNumberFields.rayUnitRepresentative`: a normalized representative of a coset of
  the congruence units;
* `TauCeti.GlobalNumberFields.rayFundamentalDomain`: the finite union of the corresponding
  translates of Mathlib's fundamental cone.

## Main results

* `TauCeti.GlobalNumberFields.exists_unitsCongruenceSubgroup_smul_mem_rayFundamentalDomain`:
  every point of nonzero norm has a congruence-unit translate in the domain;
* `TauCeti.GlobalNumberFields.rayFundamentalDomain_one`: the trivial modulus recovers Mathlib's
  fundamental cone;
* `TauCeti.GlobalNumberFields.measurableSet_rayFundamentalDomain`: the domain is measurable.

## References

The finite-union construction is the standard ray-class refinement of the fundamental cone; see
S. Lang, *Algebraic Number Theory*, Chapter VI, Section 2.
-/

public section

open NumberField NumberField.mixedEmbedding

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- A representative of a coset of the units congruent to one modulo `𝔪`.

The identity coset is normalized to have representative `1`. This normalization makes the
fundamental domain for the trivial modulus agree literally with Mathlib's fundamental cone, rather
than with an unspecified unit translate of it. -/
noncomputable def rayUnitRepresentative (𝔪 : Modulus K)
    (q : (𝓞 K)ˣ ⧸ unitsCongruenceSubgroup 𝔪) : (𝓞 K)ˣ := by
  classical
  exact if q = 1 then 1 else q.out

/-- The representative of the identity coset is the identity unit. -/
@[simp]
theorem rayUnitRepresentative_one (𝔪 : Modulus K) : rayUnitRepresentative 𝔪 1 = 1 := by
  simp [rayUnitRepresentative]

/-- The chosen representative maps back to the coset it represents. -/
@[simp]
theorem rayUnitRepresentative_mk (𝔪 : Modulus K)
    (q : (𝓞 K)ˣ ⧸ unitsCongruenceSubgroup 𝔪) :
    QuotientGroup.mk (rayUnitRepresentative 𝔪 q) = q := by
  by_cases hq : q = 1
  · subst q
    simp
  · simpa only [rayUnitRepresentative, hq, ↓reduceIte] using QuotientGroup.out_eq' q

/-- Comparing a unit with the representative of its inverse coset gives a congruence unit. -/
theorem rayUnitRepresentative_mk_inv_mul_mem (𝔪 : Modulus K) (u : (𝓞 K)ˣ) :
    rayUnitRepresentative 𝔪 (QuotientGroup.mk u⁻¹) * u ∈ unitsCongruenceSubgroup 𝔪 := by
  have h := QuotientGroup.eq.mp (rayUnitRepresentative_mk 𝔪 (QuotientGroup.mk u⁻¹))
  have hinv := (unitsCongruenceSubgroup 𝔪).inv_mem h
  simpa [mul_comm] using hinv

/-- The **ray fundamental domain** associated to a modulus. A point belongs when applying the
inverse of one chosen unit-coset representative puts it in Mathlib's fundamental cone.

Equivalently, this is the union of the translates
`rayUnitRepresentative 𝔪 q • fundamentalCone K` over the finite quotient of the unit group by the
congruence units. -/
def rayFundamentalDomain (𝔪 : Modulus K) : Set (mixedSpace K) :=
  {x | ∃ q : (𝓞 K)ˣ ⧸ unitsCongruenceSubgroup 𝔪,
    (rayUnitRepresentative 𝔪 q)⁻¹ • x ∈ fundamentalCone K}

/-- Membership in the ray fundamental domain, unfolded to a chosen unit coset. -/
@[simp]
theorem mem_rayFundamentalDomain_iff {𝔪 : Modulus K} {x : mixedSpace K} :
    x ∈ rayFundamentalDomain 𝔪 ↔
      ∃ q : (𝓞 K)ˣ ⧸ unitsCongruenceSubgroup 𝔪,
        (rayUnitRepresentative 𝔪 q)⁻¹ • x ∈ fundamentalCone K :=
  Iff.rfl

/-- The ray fundamental domain is the finite union of the preimages of Mathlib's fundamental cone
under the chosen representative actions. -/
theorem rayFundamentalDomain_eq_iUnion (𝔪 : Modulus K) :
    rayFundamentalDomain 𝔪 =
      ⋃ q : (𝓞 K)ˣ ⧸ unitsCongruenceSubgroup 𝔪,
        (fun x ↦ (rayUnitRepresentative 𝔪 q)⁻¹ • x) ⁻¹' fundamentalCone K := by
  ext x
  simp

/-- The ray fundamental domain is measurable. It is a finite union of unit translates of
Mathlib's measurable fundamental cone. -/
theorem measurableSet_rayFundamentalDomain (𝔪 : Modulus K) :
    MeasurableSet (rayFundamentalDomain 𝔪) := by
  let _ := (unitsCongruenceSubgroup 𝔪).fintypeQuotientOfFiniteIndex
  rw [rayFundamentalDomain_eq_iUnion]
  exact MeasurableSet.iUnion fun q ↦
    (measurableSet_fundamentalCone K).preimage
      (by
        simpa only [unitSMul_smul] using
          (continuous_const_mul
            (mixedEmbedding K
              (algebraMap (𝓞 K) K ((rayUnitRepresentative 𝔪 q)⁻¹ : (𝓞 K)ˣ) : K))).measurable)

/-- Every point of the ray fundamental domain has positive mixed norm. -/
theorem norm_pos_of_mem_rayFundamentalDomain {𝔪 : Modulus K} {x : mixedSpace K}
    (hx : x ∈ rayFundamentalDomain 𝔪) : 0 < mixedEmbedding.norm x := by
  obtain ⟨q, hq⟩ := mem_rayFundamentalDomain_iff.mp hx
  simpa only [norm_unit_smul] using fundamentalCone.norm_pos_of_mem hq

/-- The ray fundamental domain is stable under multiplication by a nonzero real scalar. -/
theorem smul_mem_rayFundamentalDomain {𝔪 : Modulus K} {x : mixedSpace K}
    (hx : x ∈ rayFundamentalDomain 𝔪) {c : ℝ} (hc : c ≠ 0) :
    c • x ∈ rayFundamentalDomain 𝔪 := by
  obtain ⟨q, hq⟩ := mem_rayFundamentalDomain_iff.mp hx
  refine mem_rayFundamentalDomain_iff.mpr ⟨q, ?_⟩
  have heq :
      (rayUnitRepresentative 𝔪 q)⁻¹ • (c • x) =
        c • ((rayUnitRepresentative 𝔪 q)⁻¹ • x) := by
    simpa only [unitSMul_smul] using
      (mul_smul_comm c
        (mixedEmbedding K
          (algebraMap (𝓞 K) K ((rayUnitRepresentative 𝔪 q)⁻¹ : (𝓞 K)ˣ) : K)) x)
  rw [heq]
  exact fundamentalCone.smul_mem_of_mem hq hc

/-- Multiplication by a nonzero real scalar preserves membership in the ray fundamental domain. -/
theorem smul_mem_rayFundamentalDomain_iff {𝔪 : Modulus K} {x : mixedSpace K}
    {c : ℝ} (hc : c ≠ 0) :
    c • x ∈ rayFundamentalDomain 𝔪 ↔ x ∈ rayFundamentalDomain 𝔪 := by
  refine ⟨fun h ↦ ?_, fun h ↦ smul_mem_rayFundamentalDomain h hc⟩
  convert smul_mem_rayFundamentalDomain h (inv_ne_zero hc)
  rw [eq_inv_smul_iff₀ hc]

/-- Every point of nonzero mixed norm can be moved into the ray fundamental domain by a unit
congruent to one modulo `𝔪`. -/
theorem exists_unitsCongruenceSubgroup_smul_mem_rayFundamentalDomain (𝔪 : Modulus K)
    {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
    ∃ u : (𝓞 K)ˣ, u ∈ unitsCongruenceSubgroup 𝔪 ∧ u • x ∈ rayFundamentalDomain 𝔪 := by
  obtain ⟨u, hu⟩ := fundamentalCone.exists_unit_smul_mem hx
  let q : (𝓞 K)ˣ ⧸ unitsCongruenceSubgroup 𝔪 := QuotientGroup.mk u⁻¹
  let r : (𝓞 K)ˣ := rayUnitRepresentative 𝔪 q
  refine ⟨r * u, rayUnitRepresentative_mk_inv_mul_mem 𝔪 u, ?_⟩
  refine mem_rayFundamentalDomain_iff.mpr ⟨q, ?_⟩
  have heq : r⁻¹ • ((r * u) • x) = u • x := by
    rw [← mul_smul]
    congr 1
    group
  rw [heq]
  exact hu

/-- For the trivial modulus every unit coset is the identity coset. -/
private theorem rayUnitQuotient_one_eq_one
    (q : (𝓞 K)ˣ ⧸ unitsCongruenceSubgroup (Modulus.one K)) : q = 1 := by
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.mk_one]
  exact QuotientGroup.eq.mpr (by simp)

/-- The ray fundamental domain for the trivial modulus is Mathlib's fundamental cone. -/
@[simp]
theorem rayFundamentalDomain_one :
    rayFundamentalDomain (Modulus.one K) = fundamentalCone K := by
  ext x
  constructor
  · rintro ⟨q, hq⟩
    rw [rayUnitQuotient_one_eq_one q] at hq
    simpa using hq
  · intro hx
    exact mem_rayFundamentalDomain_iff.mpr ⟨1, by simpa using hx⟩

/-- If two chosen translates contain points in the same unit orbit, then the unit
carrying the corresponding points of Mathlib's fundamental cone to one another is torsion.

This is the precise finite-overlap statement inherited from Mathlib's fundamental cone; it avoids
asserting uniqueness before roots of unity are accounted for in the ray-class count. -/
theorem rayUnitRepresentative_inv_mul_mem_torsion
    {𝔪 : Modulus K} {x : mixedSpace K}
    {q q' : (𝓞 K)ˣ ⧸ unitsCongruenceSubgroup 𝔪} {u : (𝓞 K)ˣ}
    (hx : (rayUnitRepresentative 𝔪 q)⁻¹ • x ∈ fundamentalCone K)
    (hux : (rayUnitRepresentative 𝔪 q')⁻¹ • (u • x) ∈ fundamentalCone K) :
    (rayUnitRepresentative 𝔪 q')⁻¹ * u * rayUnitRepresentative 𝔪 q ∈
      NumberField.Units.torsion K := by
  let y := (rayUnitRepresentative 𝔪 q)⁻¹ • x
  have hy : y ∈ fundamentalCone K := hx
  have heq :
      ((rayUnitRepresentative 𝔪 q')⁻¹ * u * rayUnitRepresentative 𝔪 q) • y =
        (rayUnitRepresentative 𝔪 q')⁻¹ • (u • x) := by
    dsimp only [y]
    rw [← mul_smul, ← mul_smul]
    congr 1
    group
  exact (fundamentalCone.unit_smul_mem_iff_mem_torsion hy _).mp (heq ▸ hux)

end TauCeti.GlobalNumberFields
