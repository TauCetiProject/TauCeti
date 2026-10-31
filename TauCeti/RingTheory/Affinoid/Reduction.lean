/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Reduction
public import TauCeti.RingTheory.Affinoid.PowerBounded
import TauCeti.RingTheory.Affinoid.MaximumModulus
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

The same rescaling shows that the supremum seminorm of a nonzero affinoid algebra `A` is
multiplicative exactly when `A° / A°°` is a domain: two elements of supremum seminorm one have
nonzero classes, and the class of their product is nonzero precisely when the product again has
supremum seminorm one. Since the kernel of the supremum seminorm is the nilradical, it is a
multiplicative norm exactly when moreover `A` is reduced. The canonical reduction of a Tate
algebra is a domain, because there the supremum seminorm is the multiplicative Gauss norm.

## Main results

* `AlgHom.reductionMap`: the ring homomorphism `A° / A°° → B° / B°°` induced by `A →ₐ[K] B`.
* `AlgHom.injective_reductionMap_iff_supSeminorm_eq`: it is injective exactly when the
  homomorphism preserves supremum seminorms.
* `TauCeti.IsAffinoidAlgebra.isDomain_canonicalReduction_iff`: for nonzero `A`, the canonical
  reduction is a domain exactly when `|f g|sup = |f|sup |g|sup` for all `f` and `g`.
* `TauCeti.IsAffinoidAlgebra.exists_absoluteValue_coe_eq_supSeminorm_iff`: for nonzero `A`, the
  supremum seminorm is a multiplicative norm exactly when `A` is reduced and `A° / A°°` is a
  domain.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§6.2 and 6.3.1.
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

namespace TauCeti

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IsAffinoidAlgebra

variable {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]
    [CompleteSpace A]

/-- **The supremum seminorm is multiplicative when the canonical reduction is a domain.** -/
@[simp]
theorem supSeminorm_mul (hA : IsAffinoidAlgebra K A) [IsDomain (CanonicalReduction A)]
    (f g : A) : supSeminorm K (f * g) = supSeminorm K f * supSeminorm K g := by
  have hprime := (Ideal.Quotient.isDomain_iff_prime (topologicallyNilpotentIdeal A)).mp ‹_›
  refine le_antisymm (hA.supSeminorm_mul_le f g) ?_
  rcases (supSeminorm_nonneg (K := K) f).eq_or_lt with hf | hf
  · simpa [← hf] using supSeminorm_nonneg (K := K) (f * g)
  rcases (supSeminorm_nonneg (K := K) g).eq_or_lt with hg | hg
  · simpa [← hg] using supSeminorm_nonneg (K := K) (f * g)
  -- Rescale powers of `f` and `g` to elements `u` and `v` of supremum seminorm one. Their
  -- classes in the domain `A° / A°°` are nonzero, so `u * v` also has supremum seminorm one.
  obtain ⟨m, hm, hscale⟩ := hA.exists_supSeminorm_smul_pow_eq_one
  have hm0 : m ≠ 0 := by omega
  obtain ⟨c, hc⟩ := hscale f hf
  obtain ⟨d, hd⟩ := hscale g hg
  let u : powerBoundedSubring A := ⟨(c : K) • f ^ m, mem_powerBoundedSubring.mpr <|
    hA.isPowerBounded_iff_supSeminorm_le_one.mpr hc.le⟩
  let v : powerBoundedSubring A := ⟨(d : K) • g ^ m, mem_powerBoundedSubring.mpr <|
    hA.isPowerBounded_iff_supSeminorm_le_one.mpr hd.le⟩
  have hu : u ∉ topologicallyNilpotentIdeal A := by
    rw [hA.mem_topologicallyNilpotentIdeal_iff_supSeminorm_lt_one]
    exact hc.not_lt
  have hv : v ∉ topologicallyNilpotentIdeal A := by
    rw [hA.mem_topologicallyNilpotentIdeal_iff_supSeminorm_lt_one]
    exact hd.not_lt
  have huv : supSeminorm K ((u * v : powerBoundedSubring A) : A) = 1 := by
    refine le_antisymm (hA.isPowerBounded_iff_supSeminorm_le_one.mp
      (mem_powerBoundedSubring.mp (u * v).2)) (not_lt.mp ?_)
    rw [← hA.mem_topologicallyNilpotentIdeal_iff_supSeminorm_lt_one]
    exact fun h ↦ (hprime.mem_or_mem h).elim hu hv
  have huv' : ((u * v : powerBoundedSubring A) : A) = ((c : K) * d) • (f * g) ^ m := by
    simp only [u, v, Subring.coe_mul, smul_mul_smul_comm, mul_pow]
  rw [huv', hA.supSeminorm_smul, hA.supSeminorm_pow _ hm0, norm_mul] at huv
  rw [hA.supSeminorm_smul, hA.supSeminorm_pow _ hm0] at hc hd
  -- Comparing `‖c d‖ |f g|sup ^ m = 1 = ‖c‖ |f|sup ^ m * ‖d‖ |g|sup ^ m` gives the claim.
  have hcd : ‖(c : K)‖ * ‖(d : K)‖ ≠ 0 := by simp
  refine ((pow_left_inj₀ (supSeminorm_nonneg _)
    (mul_nonneg (supSeminorm_nonneg f) (supSeminorm_nonneg g)) hm0).mp ?_).ge
  refine mul_left_cancel₀ hcd ?_
  rw [huv, mul_pow, ← one_mul (1 : ℝ)]
  nth_rewrite 1 [← hc, ← hd]
  ring

/-- **The canonical reduction of a nonzero affinoid algebra is a domain exactly when its
supremum seminorm is multiplicative.** -/
theorem isDomain_canonicalReduction_iff [Nontrivial A] (hA : IsAffinoidAlgebra K A) :
    IsDomain (CanonicalReduction A) ↔
      ∀ f g : A, supSeminorm K (f * g) = supSeminorm K f * supSeminorm K g := by
  refine ⟨fun _ ↦ hA.supSeminorm_mul, fun h ↦ ?_⟩
  rw [Ideal.Quotient.isDomain_iff_prime]
  refine ⟨(Ideal.ne_top_iff_one _).mpr ?_, fun {a b} hab ↦ ?_⟩
  · rw [hA.mem_topologicallyNilpotentIdeal_iff_supSeminorm_lt_one]
    simp
  · simp only [hA.mem_topologicallyNilpotentIdeal_iff_supSeminorm_lt_one, Subring.coe_mul,
      h] at hab ⊢
    by_contra! hne
    exact absurd hab (not_lt.mpr (one_le_mul_of_one_le_of_one_le hne.1 hne.2))

/-- The supremum seminorm of a reduced affinoid algebra whose canonical reduction is a domain,
bundled as an absolute value. -/
noncomputable def supAbsoluteValue (hA : IsAffinoidAlgebra K A) [IsReduced A]
    [IsDomain (CanonicalReduction A)] : AbsoluteValue A ℝ where
  toFun := supSeminorm K
  map_mul' := hA.supSeminorm_mul
  nonneg' := supSeminorm_nonneg
  eq_zero' _ := by rw [hA.supSeminorm_eq_zero_iff, isNilpotent_iff_eq_zero]
  add_le' f g := (hA.supSeminorm_add_le f g).trans
    (max_le_add_of_nonneg (supSeminorm_nonneg f) (supSeminorm_nonneg g))

@[simp]
theorem coe_supAbsoluteValue (hA : IsAffinoidAlgebra K A) [IsReduced A]
    [IsDomain (CanonicalReduction A)] : ⇑hA.supAbsoluteValue = supSeminorm K :=
  (rfl)

/-- **The supremum seminorm of a nonzero affinoid algebra is a multiplicative norm exactly when
`A` is reduced and its canonical reduction `A° / A°°` is a domain.** -/
theorem exists_absoluteValue_coe_eq_supSeminorm_iff [Nontrivial A]
    (hA : IsAffinoidAlgebra K A) :
    (∃ v : AbsoluteValue A ℝ, ⇑v = supSeminorm K) ↔
      IsReduced A ∧ IsDomain (CanonicalReduction A) := by
  refine ⟨fun ⟨v, hv⟩ ↦ ⟨⟨fun f hf ↦ ?_⟩, hA.isDomain_canonicalReduction_iff.mpr fun f g ↦ ?_⟩,
    fun ⟨_, _⟩ ↦ ⟨hA.supAbsoluteValue, hA.coe_supAbsoluteValue⟩⟩
  · rw [← v.eq_zero, hv, hA.supSeminorm_eq_zero_iff]
    exact hf
  · simp only [← hv, map_mul]

end IsAffinoidAlgebra

namespace MvPowerSeries

/-- The canonical reduction of a Tate algebra `K⟨X₁, …, Xₙ⟩` is a domain, since its supremum
seminorm is the multiplicative Gauss norm. -/
instance isDomain_canonicalReduction {n : ℕ} :
    IsDomain (CanonicalReduction
      (_root_.MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1))) :=
  isAffinoidAlgebra_tate.isDomain_canonicalReduction_iff.mpr fun f g ↦ by simp [norm_mul]

end MvPowerSeries

end TauCeti
