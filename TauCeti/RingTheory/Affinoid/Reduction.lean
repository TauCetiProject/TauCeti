/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Reduction
public import TauCeti.RingTheory.Affinoid.PowerBounded
import TauCeti.RingTheory.Affinoid.ValueGroup

/-!
# Canonical reduction maps of affinoid algebras

Every algebra homomorphism of affinoid algebras induces a ring homomorphism on their
canonical reductions `A° / A°°`. Its kernel consists of the classes of power-bounded elements
whose images have supremum seminorm less than one. These maps preserve identities and
composition. No continuity or contractivity for the chosen complete algebra norms is assumed.

Injectivity on canonical reductions is equivalent to preservation of the supremum seminorm.
The forward implication uses the value-group exponent to rescale a power of an element to
supremum seminorm one. This criterion does not require reducedness of either algebra; it is
not a claim of injectivity on the original algebras.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §6.3.1.
-/

public section

open TauCeti TauCeti.Huber

namespace AlgHom

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {A B C : Type*}
    [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
    [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
    [NormedCommRing C] [NormedAlgebra K C] [IsUltrametricDist C] [CompleteSpace C]

/-- An affinoid algebra homomorphism restricts to the power-bounded subrings. -/
def powerBoundedMap (f : A →ₐ[K] B) (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) : powerBoundedSubring A →+* powerBoundedSubring B :=
  f.toRingHom.restrict _ _ fun a ha ↦ mem_powerBoundedSubring.mpr <|
    hB.isPowerBounded_iff_supSeminorm_le_one.mpr <|
      (hA.supSeminorm_map_le hB f a).trans
        (hA.isPowerBounded_iff_supSeminorm_le_one.mp (mem_powerBoundedSubring.mp ha))

@[simp]
theorem coe_powerBoundedMap (f : A →ₐ[K] B) (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (a : powerBoundedSubring A) :
    (f.powerBoundedMap hA hB a : B) = f a := (rfl)

/-- Restriction of the identity to the power-bounded subring is the identity. -/
@[simp]
theorem powerBoundedMap_id (hA : IsAffinoidAlgebra K A) :
    (AlgHom.id K A).powerBoundedMap hA hA = RingHom.id _ := by
  ext a
  simp

/-- Restriction to power-bounded elements commutes with composition. -/
theorem powerBoundedMap_comp (g : B →ₐ[K] C) (f : A →ₐ[K] B)
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (hC : IsAffinoidAlgebra K C) :
    (g.comp f).powerBoundedMap hA hC =
      (g.powerBoundedMap hB hC).comp (f.powerBoundedMap hA hB) := by
  ext a
  simp

/-- The homomorphism on canonical reductions induced by an affinoid algebra homomorphism. -/
def reductionMap (f : A →ₐ[K] B) (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) : CanonicalReduction A →+* CanonicalReduction B :=
  Ideal.quotientMap _ (f.powerBoundedMap hA hB) fun a ha ↦ by
    rw [Ideal.mem_comap, mem_topologicallyNilpotentIdeal, coe_powerBoundedMap,
      hB.isTopologicallyNilpotent_iff_supSeminorm_lt_one]
    exact (hA.supSeminorm_map_le hB f a).trans_lt
      (hA.isTopologicallyNilpotent_iff_supSeminorm_lt_one.mp
        (mem_topologicallyNilpotentIdeal.mp ha))

/-- Reduction commutes with the map on power-bounded elements. -/
@[simp]
theorem reductionMap_mk (f : A →ₐ[K] B) (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (a : powerBoundedSubring A) :
    f.reductionMap hA hB (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (f.powerBoundedMap hA hB a) := by
  exact Ideal.quotientMap_mk

/-- The reduction map of the identity is the identity. -/
@[simp]
theorem reductionMap_id (hA : IsAffinoidAlgebra K A) :
    (AlgHom.id K A).reductionMap hA hA = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  ext a
  simp

/-- Reduction maps commute with composition. -/
theorem reductionMap_comp (g : B →ₐ[K] C) (f : A →ₐ[K] B)
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (hC : IsAffinoidAlgebra K C) :
    (g.comp f).reductionMap hA hC = (g.reductionMap hB hC).comp (f.reductionMap hA hB) := by
  apply Ideal.Quotient.ringHom_ext
  ext a
  simp [powerBoundedMap_comp g f hA hB hC]

/-- A class lies in the kernel precisely when its image has supremum seminorm less than one. -/
@[simp↓]
theorem reductionMap_mk_eq_zero_iff (f : A →ₐ[K] B) (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (a : powerBoundedSubring A) :
    f.reductionMap hA hB (Ideal.Quotient.mk _ a) = 0 ↔ supSeminorm K (f a) < 1 := by
  rw [reductionMap_mk, Ideal.Quotient.eq_zero_iff_mem, mem_topologicallyNilpotentIdeal,
    coe_powerBoundedMap, hB.isTopologicallyNilpotent_iff_supSeminorm_lt_one]

/-- Injectivity of the reduction map is equivalent to reflection of the open supremum unit ball
on power-bounded elements. -/
theorem injective_reductionMap_iff (f : A →ₐ[K] B) (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) :
    Function.Injective (f.reductionMap hA hB) ↔
      ∀ a : powerBoundedSubring A, supSeminorm K (f a) < 1 → supSeminorm K (a : A) < 1 := by
  constructor
  · intro h a ha
    rw [injective_iff_map_eq_zero] at h
    have hz := h _ ((f.reductionMap_mk_eq_zero_iff hA hB a).mpr ha)
    exact hA.isTopologicallyNilpotent_iff_supSeminorm_lt_one.mp
      ((mem_topologicallyNilpotentIdeal).mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  · intro h
    apply Ideal.quotientMap_injective'
    intro a ha
    rw [Ideal.mem_comap, mem_topologicallyNilpotentIdeal, coe_powerBoundedMap,
      hB.isTopologicallyNilpotent_iff_supSeminorm_lt_one] at ha
    exact mem_topologicallyNilpotentIdeal.mpr <|
      hA.isTopologicallyNilpotent_iff_supSeminorm_lt_one.mpr (h a ha)

/-- A homomorphism of affinoid algebras preserves the supremum seminorm if and only if it is
injective on canonical reductions. Neither algebra is required to be reduced. -/
theorem injective_reductionMap_iff_supSeminorm_eq (f : A →ₐ[K] B)
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) :
    Function.Injective (f.reductionMap hA hB) ↔
      ∀ a : A, supSeminorm K (f a) = supSeminorm K a := by
  rw [f.injective_reductionMap_iff hA hB]
  constructor
  · intro h a
    apply le_antisymm (hA.supSeminorm_map_le hB f a)
    by_contra! hlt
    have ha : 0 < supSeminorm K a := (supSeminorm_nonneg _).trans_lt hlt
    obtain ⟨m, hm, hscale⟩ := hA.exists_supSeminorm_smul_pow_eq_one
    obtain ⟨c, hc⟩ := hscale a ha
    let u := (c : K) • a ^ m
    have hm0 : m ≠ 0 := by omega
    have hu : u ∈ powerBoundedSubring A := mem_powerBoundedSubring.mpr <|
      hA.isPowerBounded_iff_supSeminorm_le_one.mpr hc.le
    have hnorm : supSeminorm K (f u) < 1 := by
      have hpow := pow_lt_pow_left₀ hlt (supSeminorm_nonneg _) hm0
      have hcpos : 0 < ‖(c : K)‖ := norm_pos_iff.mpr c.ne_zero
      have hc' : ‖(c : K)‖ * supSeminorm K a ^ m = 1 := by
        rwa [hA.supSeminorm_smul, hA.supSeminorm_pow a hm0] at hc
      simpa only [u, map_smul, map_pow, hB.supSeminorm_smul,
        hB.supSeminorm_pow (f a) hm0, hc'] using mul_lt_mul_of_pos_left hpow hcpos
    exact (h ⟨u, hu⟩ hnorm).ne hc
  · intro h a ha
    rwa [h] at ha

end AlgHom
