/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Reduction
public import TauCeti.RingTheory.Affinoid.PowerBounded
public import TauCeti.RingTheory.Nagata
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Maps.Strict.Basic
import TauCeti.RingTheory.Affinoid.Integral.Equation
import TauCeti.RingTheory.Affinoid.MinimalPolynomial
import TauCeti.RingTheory.Affinoid.Multiplicative
import TauCeti.RingTheory.Affinoid.NoetherNormalization
import TauCeti.RingTheory.Affinoid.QuotientNorm
import TauCeti.RingTheory.Affinoid.SpectralRadius
import TauCeti.RingTheory.Affinoid.ValueGroup
import TauCeti.RingTheory.FiniteType.Pi
import TauCeti.RingTheory.IntegralClosure.Pi
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniqueFactorization
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall
import TauCeti.RingTheory.UniversallyJapanese
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Module
import Mathlib.Topology.Maps.Strict.Group

/-!
# Canonical reduction maps of affinoid algebras and the Grauert–Remmert finiteness theorem

Every algebra homomorphism of affinoid algebras induces a `𝓀[K]`-algebra homomorphism on their
canonical reductions `A° / A°°`. Its kernel consists of the classes of power-bounded elements
whose images have supremum seminorm less than one. These maps preserve identities and
composition. No continuity or contractivity for the chosen complete algebra norms is assumed.

Injectivity on canonical reductions is equivalent to preservation of the supremum seminorm.
The forward implication uses the value-group exponent to rescale a power of an element to
supremum seminorm one. This criterion does not require reducedness of either algebra; it is
not a claim of injectivity on the original algebras. Conversely, injectivity on canonical
reductions forces every element of the kernel to be nilpotent, since the supremum seminorm
vanishes only on nilpotents. When `f` is surjective with nilpotent kernel — for instance the
quotient map onto the reduced quotient `A ⧸ nilradical A` — the induced map on canonical
reductions is an isomorphism of `𝓀[K]`-algebras.

For a strict homomorphism (`Topology.IsStrictMap`, for instance any finite homomorphism by
`TauCeti.IsAffinoidAlgebra.isStrictMap_of_finite`) the kernel of the reduction map is determined
by the kernel of `f`: it is the radical of the reduction of `ker f ∩ A°`. If `f a` is topologically
nilpotent, strictness puts some `f (a ^ n)` into the image of the unit ball of `A`, so `a ^ n` is
a topologically nilpotent element plus an element of `ker f`. Hence a strict homomorphism is
injective on canonical reductions exactly when its kernel is nilpotent, and a strict
homomorphism out of a reduced affinoid algebra is injective exactly when it is injective on
canonical reductions.

An integral homomorphism induces an integral map on canonical reductions. A power-bounded `f`
satisfies an integral equation whose coefficients have supremum seminorm at most `|f|sup ^ k`
(`TauCeti.IsAffinoidAlgebra.exists_monic_aeval_eq_zero_supSeminorm_coeff_le`), so at most one,
and the reduction of that equation is an integral equation for the residue class of `f`.

For a nonzero affinoid algebra `A`, the canonical reduction `A° / A°°` is a domain exactly when
the supremum seminorm of `A` is multiplicative; this restates
`TauCeti.IsAffinoidAlgebra.supSeminorm_mul_iff_isPrime` for the reduction carrier. For an affinoid
Tate algebra `K⟨X₁, …, Xₙ⟩` over a complete field this recovers that its canonical reduction is a
domain from multiplicativity of the Gauss norm (`TauCeti.MvPowerSeries.isDomain_canonicalReduction`
establishes this in general without completeness of `K` or finiteness of the variable set).

Finally, we prove the **Grauert–Remmert finiteness theorem**: the canonical reduction of any
affinoid `K`-algebra is a finite-type `𝓀[K]`-algebra (hence Noetherian and Nagata), and every
integral (in particular, every finite) homomorphism of affinoid algebras induces a finite map on
canonical reductions:
* Over an integrally closed affinoid domain `A` whose canonical reduction is a domain, if `B` is
  integral and `A`-torsion-free then `CanonicalReduction B` is `CanonicalReduction A`-torsion-free
  (`AlgHom.isTorsionFree_reductionMap`), by multiplicativity of the supremum seminorm under `A`
  scalars (`TauCeti.IsAffinoidAlgebra.supSeminorm_smul_of_isTorsionFree`). Over any reduced
  affinoid algebra `A`, linear independence over `CanonicalReduction A` lifts to linear
  independence over `A` (`AlgHom.linearIndependent_of_reductionMap`) by rescaling a nontrivial
  `A`-relation using `TauCeti.IsAffinoidAlgebra.exists_supSeminorm_smul_pow_eq_one`.
* For an affinoid domain `B` and a finite injective Noether normalisation `T → B` from a Tate
  algebra `T = K⟨X₁, …, X_d⟩` with canonical reduction `R₀ = CanonicalReduction T`, localising
  `B₀ = CanonicalReduction B` at `R₀⁰` gives a reduced algebra `E₀` over `Frac(R₀)` of dimension at
  most `finrank_{Frac(T)} Frac(B)`. Since `R₀ ≃ 𝓀[K][X₁, …, X_d]` is Nagata
  (`TauCeti.Ring.IsUniversallyJapanese.isNagata_of_finiteType`), the integral closure of `R₀` in
  `E₀` is module-finite over `R₀` (`TauCeti.Ring.IsNagata.finite_integralClosure`); no assumption
  on the residue characteristic or perfection of `𝓀[K]` is needed. Because `R₀` is Noetherian and
  `B₀` embeds `R₀`-linearly into that integral closure, `B₀` is finite over `R₀`, hence of finite
  type over `𝓀[K]`.
* For an arbitrary affinoid algebra `A` (possibly with nilpotents and multiple irreducible
  components), `A` is Noetherian so `minimalPrimes A` is finite, and each `A ⧸ 𝔭` is a completely
  normed affinoid domain. The product of the reduction maps
  `CanonicalReduction A → ∏ 𝔭, CanonicalReduction (A ⧸ 𝔭)` is injective (by
  `TauCeti.IsAffinoidAlgebra.exists_mem_minimalPrimes_supSeminorm_eq`) and integral into a
  finite-type `𝓀[K]`-algebra, so the Artin–Tate lemma (`fg_of_fg_of_fg`) gives
  `Algebra.FiniteType 𝓀[K] (CanonicalReduction A)`
  (`TauCeti.IsAffinoidAlgebra.finiteType_canonicalReduction`).
* Every affinoid homomorphism `f : A →ₐ[K] B` induces a finite-type `𝓀[K]`-algebra homomorphism
  `CanonicalReduction A →ₐ[𝓀[K]] CanonicalReduction B` on canonical reductions
  (`AlgHom.finiteType_reductionMap`), and when `f` is integral (in particular, finite) its
  reduction map is also integral and hence finite (`AlgHom.finite_reductionMap`).

## Main results

* `AlgHom.reductionMap`: the `𝓀[K]`-algebra homomorphism `A° / A°° →ₐ[𝓀[K]] B° / B°°` induced by
  `A →ₐ[K] B`.
* `AlgHom.injective_reductionMap_iff_supSeminorm_eq`: it is injective exactly when the
  homomorphism preserves supremum seminorms.
* `AlgHom.bijective_reductionMap_of_surjective_of_ker_le_nilradical`,
  `AlgHom.reductionAlgEquivOfKerLeNilradical`: a surjective homomorphism with nilpotent kernel
  induces a `𝓀[K]`-algebra isomorphism on canonical reductions.
* `AlgHom.ker_le_nilradical_of_injective_reductionMap`: injectivity on canonical reductions
  forces a nilpotent kernel.
* `AlgHom.comap_ker_reductionMap_eq_radical`, `AlgHom.ker_reductionMap_eq_radical_map`: for a
  strict homomorphism, the kernel of the reduction map is the radical generated by `A°°` and
  `ker f ∩ A°`.
* `AlgHom.injective_reductionMap_iff_ker_le_nilradical`: a strict homomorphism is injective on
  canonical reductions exactly when its kernel is nilpotent.
* `AlgHom.injective_reductionMap_iff_injective`: for reduced `A`, a strict homomorphism is
  injective on canonical reductions exactly when it is injective.
* `AlgHom.isIntegral_powerBoundedMap`, `AlgHom.isIntegral_reductionMap`: an integral
  homomorphism is integral on power-bounded subrings and on canonical reductions.
* `AlgHom.reductionMap_mul_eq_zero_iff`, `AlgHom.isTorsionFree_reductionMap`,
  `AlgHom.linearIndependent_of_reductionMap`: torsion-freeness and lifting of linear independence
  on canonical reductions of affinoid algebras.
* `TauCeti.IsAffinoidAlgebra.finiteType_canonicalReduction`,
  `TauCeti.IsAffinoidAlgebra.isNoetherianRing_canonicalReduction`,
  `TauCeti.IsAffinoidAlgebra.isNagata_canonicalReduction`: the canonical reduction of any
  affinoid `K`-algebra is a finite-type `𝓀[K]`-algebra, hence Noetherian and Nagata.
* `AlgHom.finiteType_reductionMap`, `AlgHom.finite_reductionMap`: **Grauert–Remmert finiteness
  theorem** — every homomorphism of affinoid algebras induces a finite-type map on canonical
  reductions, and every integral (in particular, every finite) homomorphism induces a finite map
  on canonical reductions.
* `TauCeti.IsAffinoidAlgebra.isDomain_canonicalReduction_iff`: for nonzero `A`, the canonical
  reduction is a domain exactly when `|f g|sup = |f|sup |g|sup` for all `f` and `g`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§6.2, 6.3.1,
  6.3.4 and 6.3.5.

The statements and proofs for strict homomorphisms adapt William Coram's
`comap_ker_reductionMap_eq_radical_of_isStrictMap`,
`ker_reductionMap_eq_radical_map_of_isStrictMap` and
`injective_reductionMap_of_isStrictMap_of_ker_le_nilradical` in
`PhD/TauCeti/Code/RigidAnalyticGeometry/Affinoid/ReductionFunctor.lean` at commit
`eefb3d91f34b27d0bc7822140fa85fecae029884` of <https://github.com/WilliamCoram/PhD>.
-/

public section

open TauCeti TauCeti.Huber Filter Topology
open scoped NormedField Valued nonZeroDivisors

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

/-- The `𝓀[K]`-algebra homomorphism on canonical reductions induced by an affinoid algebra
homomorphism. -/
noncomputable def reductionMap (f : A →ₐ[K] B) (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) : CanonicalReduction A →ₐ[𝓀[K]] CanonicalReduction B :=
  { Ideal.quotientMap _ (f.powerBoundedMap hA hB) fun a ha ↦ by
      rw [Ideal.mem_comap, mem_topologicallyNilpotentIdeal, coe_powerBoundedMap,
        hB.isTopologicallyNilpotent_iff_supSeminorm_lt_one]
      exact (hA.supSeminorm_map_le hB f a).trans_lt
        (hA.isTopologicallyNilpotent_iff_supSeminorm_lt_one.mp
          (mem_topologicallyNilpotentIdeal.mp ha)) with
    commutes' := fun x ↦ by
      obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective (R := 𝒪[K]) x
      rw [RingHom.toFun_eq_coe, algebraMap_canonicalReduction_residue,
        algebraMap_canonicalReduction_residue, Ideal.quotientMap_mk]
      exact congrArg (Ideal.Quotient.mk _) (Subtype.ext (by simp)) }

/-- Reduction commutes with the map on power-bounded elements. -/
@[simp]
theorem reductionMap_mk (f : A →ₐ[K] B) (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (a : powerBoundedSubring A) :
    f.reductionMap hA hB (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (f.powerBoundedMap hA hB a) := by
  rw [reductionMap, AlgHom.coe_mk, Ideal.quotientMap_mk]

/-- The reduction map of the identity is the identity. -/
@[simp]
theorem reductionMap_id (hA : IsAffinoidAlgebra K A) :
    (AlgHom.id K A).reductionMap hA hA = AlgHom.id 𝓀[K] (CanonicalReduction A) := by
  apply AlgHom.toRingHom_injective
  apply Ideal.Quotient.ringHom_ext
  ext a
  simp

/-- Reduction maps commute with composition. -/
theorem reductionMap_comp (g : B →ₐ[K] C) (f : A →ₐ[K] B)
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (hC : IsAffinoidAlgebra K C) :
    (g.comp f).reductionMap hA hC = (g.reductionMap hB hC).comp (f.reductionMap hA hB) := by
  apply AlgHom.toRingHom_injective
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
    rw [reductionMap, AlgHom.coe_mk]
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
        rwa [supSeminorm_smul, supSeminorm_pow a hm0] at hc
      simpa only [u, map_smul, map_pow, supSeminorm_smul,
        supSeminorm_pow (f a) hm0, hc'] using mul_lt_mul_of_pos_left hpow hcpos
    exact (h ⟨u, hu⟩ hnorm).ne hc
  · intro h a ha
    rwa [h] at ha

/-- An integral homomorphism of affinoid algebras restricts to an integral map of power-bounded
subrings: every power-bounded element of `B` is integral over the image of `A°`. -/
theorem isIntegral_powerBoundedMap (f : A →ₐ[K] B) (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (hf : f.toRingHom.IsIntegral) :
    (f.powerBoundedMap hA hB).IsIntegral := by
  intro b
  let := f.toRingHom.toAlgebra
  have : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun c ↦ (f.commutes c).symm
  have : Algebra.IsIntegral A B := ⟨hf⟩
  -- An integral equation of `b` over `A` whose coefficients have `|·|sup ≤ 1`.
  obtain ⟨p, hp, hpb, hc⟩ := hA.exists_monic_aeval_eq_zero_supSeminorm_coeff_le hB (b : B)
  have hb : supSeminorm K (b : B) ≤ 1 :=
    hB.isPowerBounded_iff_supSeminorm_le_one.mp (mem_powerBoundedSubring.mp b.property)
  have hlifts : p ∈ Polynomial.lifts (powerBoundedSubring A).subtype :=
    (Polynomial.lifts_iff_coeff_lifts p).mpr fun i ↦
      ⟨⟨p.coeff i, mem_powerBoundedSubring.mpr <| hA.isPowerBounded_iff_supSeminorm_le_one.mpr <|
        (hc i).trans (pow_le_one₀ (supSeminorm_nonneg _) hb)⟩, rfl⟩
  obtain ⟨q, hqp, -, hq⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp
  refine ⟨q, hq, Subtype.val_injective ?_⟩
  -- In `B`, evaluating `q` along `A° → B°` evaluates its image `p` along `f`.
  have hcomp : (powerBoundedSubring B).subtype.comp (f.powerBoundedMap hA hB) =
      f.toRingHom.comp (powerBoundedSubring A).subtype := rfl
  have h := Polynomial.hom_eval₂ q (f.powerBoundedMap hA hB) (powerBoundedSubring B).subtype b
  rw [hcomp, ← Polynomial.eval₂_map, hqp] at h
  exact h.trans hpb

/-- **Integral homomorphisms are integral on canonical reductions.** An integral homomorphism of
affinoid algebras induces an integral map from the canonical reduction of `A` to that of `B`. -/
theorem isIntegral_reductionMap (f : A →ₐ[K] B) (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (hf : f.toRingHom.IsIntegral) :
    (f.reductionMap hA hB).toRingHom.IsIntegral := by
  have hcomp : (f.reductionMap hA hB).toRingHom.comp (Ideal.Quotient.mk _) =
      (Ideal.Quotient.mk _).comp (f.powerBoundedMap hA hB) :=
    RingHom.ext (f.reductionMap_mk hA hB)
  have h := (f.isIntegral_powerBoundedMap hA hB hf).trans _
    (Ideal.Quotient.mk (topologicallyNilpotentIdeal B))
    (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
  rw [← hcomp] at h
  exact RingHom.IsIntegral.tower_top _ _ h

/-- **Injectivity on canonical reductions forces a nilpotent kernel** [BGR, 6.3.1/3]: if `f` is
injective on canonical reductions, every element of the kernel of `f` is nilpotent. -/
theorem ker_le_nilradical_of_injective_reductionMap (f : A →ₐ[K] B)
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (h : Function.Injective (f.reductionMap hA hB)) : RingHom.ker f ≤ nilradical A := by
  intro a ha
  rw [mem_nilradical, ← hA.supSeminorm_eq_zero_iff,
    ← (f.injective_reductionMap_iff_supSeminorm_eq hA hB).mp h a, RingHom.mem_ker.mp ha,
    supSeminorm_zero]

/-- **The kernel on canonical reductions of a strict homomorphism** [BGR, 6.3.1/4]. If `f` is
strict, a power-bounded element of `A` has reduction in the kernel of the reduction map of `f`
exactly when one of its powers is a topologically nilpotent element plus an element of the kernel
of `f`. -/
theorem comap_ker_reductionMap_eq_radical (f : A →ₐ[K] B) (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (hf : IsStrictMap f) :
    (RingHom.ker (f.reductionMap hA hB)).comap (Ideal.Quotient.mk _) =
      (topologicallyNilpotentIdeal A ⊔ RingHom.ker (f.powerBoundedMap hA hB)).radical := by
  refine le_antisymm (fun a ha ↦ ?_) ?_
  · rw [Ideal.mem_comap, RingHom.mem_ker, reductionMap_mk_eq_zero_iff] at ha
    -- The powers of `f a` tend to zero inside the range of `f`, whose topology is the quotient
    -- topology: the image of the unit ball of `A` is a neighbourhood of zero there.
    let g : A →+ B := f
    have hopen : IsOpen (g.rangeRestrict '' Metric.ball 0 1) :=
      (AddMonoidHom.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mp hf).isOpenMap _
        Metric.isOpen_ball
    have h0 : 0 ∈ g.rangeRestrict '' Metric.ball 0 1 :=
      ⟨0, Metric.mem_ball_self one_pos, map_zero _⟩
    have hlim : Tendsto (fun n ↦ g.rangeRestrict ((a : A) ^ n)) atTop (𝓝 0) := by
      rw [tendsto_subtype_rng]
      simpa [g, IsTopologicallyNilpotent] using
        hB.isTopologicallyNilpotent_iff_supSeminorm_lt_one.mpr ha
    obtain ⟨n, b, hb, hbn⟩ := (hlim.eventually (hopen.mem_nhds h0)).exists
    have hfb : f b = f ((a : A) ^ n) := by simpa [g] using congr_arg Subtype.val hbn
    -- The element `b` has `|b|sup ≤ ‖b‖ < 1`, and `a ^ n - b` lies in the kernel of `f`.
    have hbsup : supSeminorm K b < 1 :=
      (supSeminorm_le_norm b).trans_lt (mem_ball_zero_iff.mp hb)
    have hbA : b ∈ powerBoundedSubring A := mem_powerBoundedSubring.mpr <|
      hA.isPowerBounded_iff_supSeminorm_le_one.mpr hbsup.le
    refine ⟨n, ?_⟩
    rw [← add_sub_cancel (⟨b, hbA⟩ : powerBoundedSubring A) (a ^ n)]
    refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
    · exact mem_topologicallyNilpotentIdeal.mpr <|
        hA.isTopologicallyNilpotent_iff_supSeminorm_lt_one.mpr hbsup
    · rw [RingHom.mem_ker, ← Subtype.coe_inj]
      simp [hfb]
  · -- The kernel of a map into the reduced ring `B° / B°°` is radical.
    have hrad : (RingHom.ker (f.reductionMap hA hB)).IsRadical := fun x ⟨n, hn⟩ ↦
      RingHom.mem_ker.mpr <| IsReduced.eq_zero _ ⟨n, by simpa using hn⟩
    refine (hrad.comap _).radical_le_iff.mpr (sup_le (fun a ha ↦ ?_) (fun a ha ↦ ?_))
    · rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
    · rw [Ideal.mem_comap, RingHom.mem_ker, reductionMap_mk, RingHom.mem_ker.mp ha, map_zero]

/-- **The kernel of the reduction map of a strict homomorphism** [BGR, 6.3.1/4]: if `f` is
strict, the kernel of the reduction map of `f` is the radical of the reduction of the
power-bounded part of the kernel of `f`. -/
theorem ker_reductionMap_eq_radical_map (f : A →ₐ[K] B) (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (hf : IsStrictMap f) :
    RingHom.ker (f.reductionMap hA hB) =
      ((RingHom.ker (f.powerBoundedMap hA hB)).map (Ideal.Quotient.mk _)).radical := by
  have hmk := Ideal.Quotient.mk_surjective (I := topologicallyNilpotentIdeal A)
  rw [← Ideal.map_comap_of_surjective _ hmk (RingHom.ker (f.reductionMap hA hB)),
    f.comap_ker_reductionMap_eq_radical hA hB hf,
    Ideal.map_radical_of_surjective hmk (by rw [Ideal.mk_ker]; exact le_sup_left),
    Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]

/-- **Injectivity on canonical reductions of a strict homomorphism** [BGR, 6.3.1/3 and 6.3.1/5]:
a strict homomorphism is injective on canonical reductions exactly when its kernel consists of
nilpotent elements. -/
theorem injective_reductionMap_iff_ker_le_nilradical (f : A →ₐ[K] B)
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (hf : IsStrictMap f) :
    Function.Injective (f.reductionMap hA hB) ↔ RingHom.ker f ≤ nilradical A := by
  refine ⟨f.ker_le_nilradical_of_injective_reductionMap hA hB, fun hker ↦ ?_⟩
  -- A power-bounded element of the kernel of `f` is nilpotent, hence topologically nilpotent.
  have hle : RingHom.ker (f.powerBoundedMap hA hB) ≤ topologicallyNilpotentIdeal A := by
    intro a ha
    have hnil : IsNilpotent (a : A) := mem_nilradical.mp <| hker <| RingHom.mem_ker.mpr <| by
      simpa using congr_arg Subtype.val (RingHom.mem_ker.mp ha)
    rw [mem_topologicallyNilpotentIdeal, hA.isTopologicallyNilpotent_iff_supSeminorm_lt_one,
      hA.supSeminorm_eq_zero_iff.mpr hnil]
    exact one_pos
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ha : a ∈ (RingHom.ker (f.reductionMap hA hB)).comap (Ideal.Quotient.mk _) :=
    Ideal.mem_comap.mpr (RingHom.mem_ker.mpr hx)
  rw [f.comap_ker_reductionMap_eq_radical hA hB hf, sup_eq_left.mpr hle,
    (isRadical_topologicallyNilpotentIdeal A).radical] at ha
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

/-- A homomorphism out of a reduced affinoid algebra which is injective on canonical reductions is
injective [BGR, 6.3.1/6]. -/
theorem injective_of_injective_reductionMap [IsReduced A] (f : A →ₐ[K] B)
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (h : Function.Injective (f.reductionMap hA hB)) : Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  exact IsReduced.eq_zero a <| f.ker_le_nilradical_of_injective_reductionMap hA hB h ha

/-- **Strict homomorphisms out of reduced affinoid algebras** [BGR, 6.3.1/6]: a strict
homomorphism out of a reduced affinoid algebra is injective exactly when it is injective on
canonical reductions, that is, exactly when it preserves supremum seminorms
(`AlgHom.injective_reductionMap_iff_supSeminorm_eq`). -/
theorem injective_reductionMap_iff_injective [IsReduced A] (f : A →ₐ[K] B)
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (hf : IsStrictMap f) :
    Function.Injective (f.reductionMap hA hB) ↔ Function.Injective f := by
  refine ⟨f.injective_of_injective_reductionMap hA hB, fun hinj ↦ ?_⟩
  rw [f.injective_reductionMap_iff_ker_le_nilradical hA hB hf,
    (RingHom.injective_iff_ker_eq_bot f).mp hinj]
  exact bot_le

/-- **Surjections with nilpotent kernel induce bijections on canonical reductions** [BGR, 6.3.1/2]:
every surjective affinoid homomorphism whose kernel is contained in the nilradical induces a
bijection on canonical reductions. In particular `A` and `A ⧸ nilradical A` have isomorphic
canonical reductions. -/
theorem bijective_reductionMap_of_surjective_of_ker_le_nilradical (f : A →ₐ[K] B)
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ nilradical A) :
    Function.Bijective (f.reductionMap hA hB) := by
  have hsup (a : A) : supSeminorm K (f a) = supSeminorm K a :=
    supSeminorm_map_of_ker_le_nilradical hf hker a
  refine ⟨(f.injective_reductionMap_iff_supSeminorm_eq hA hB).mpr hsup, fun y ↦ ?_⟩
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := hf b
  have ha' : a ∈ powerBoundedSubring A := by
    rw [mem_powerBoundedSubring, hA.isPowerBounded_iff_supSeminorm_le_one, ← hsup, ha]
    exact hB.isPowerBounded_iff_supSeminorm_le_one.mp (mem_powerBoundedSubring.mp b.property)
  refine ⟨Ideal.Quotient.mk _ ⟨a, ha'⟩, ?_⟩
  rw [reductionMap_mk]
  exact congrArg (Ideal.Quotient.mk _) (Subtype.ext ha)

/-- A surjective affinoid homomorphism with nilpotent kernel induces a `𝓀[K]`-algebra isomorphism
on canonical reductions [BGR, 6.3.1/2]. -/
noncomputable def reductionAlgEquivOfKerLeNilradical (f : A →ₐ[K] B)
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ nilradical A) :
    CanonicalReduction A ≃ₐ[𝓀[K]] CanonicalReduction B :=
  AlgEquiv.ofBijective (f.reductionMap hA hB)
    (f.bijective_reductionMap_of_surjective_of_ker_le_nilradical hA hB hf hker)

@[simp]
theorem coe_reductionAlgEquivOfKerLeNilradical (f : A →ₐ[K] B)
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ nilradical A) :
    ⇑(f.reductionAlgEquivOfKerLeNilradical hA hB hf hker) = ⇑(f.reductionMap hA hB) :=
  AlgEquiv.coe_ofBijective _ _

@[simp]
theorem toAlgHom_reductionAlgEquivOfKerLeNilradical (f : A →ₐ[K] B)
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ nilradical A) :
    (f.reductionAlgEquivOfKerLeNilradical hA hB hf hker :
      CanonicalReduction A →ₐ[𝓀[K]] CanonicalReduction B) = f.reductionMap hA hB :=
  AlgEquiv.toAlgHom_ofBijective _ _

theorem reductionAlgEquivOfKerLeNilradical_mk (f : A →ₐ[K] B)
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ nilradical A) (a : powerBoundedSubring A) :
    f.reductionAlgEquivOfKerLeNilradical hA hB hf hker (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (f.powerBoundedMap hA hB a) :=
  (AlgEquiv.ofBijective_apply _ _ _).trans (f.reductionMap_mk hA hB a)

@[simp]
theorem reductionAlgEquivOfKerLeNilradical_symm_reductionMap (f : A →ₐ[K] B)
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ nilradical A) (x : CanonicalReduction A) :
    (f.reductionAlgEquivOfKerLeNilradical hA hB hf hker).symm (f.reductionMap hA hB x) = x :=
  AlgEquiv.ofBijective_symm_apply_apply _ _ x

@[simp]
theorem reductionMap_reductionAlgEquivOfKerLeNilradical_symm (f : A →ₐ[K] B)
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ nilradical A) (y : CanonicalReduction B) :
    f.reductionMap hA hB ((f.reductionAlgEquivOfKerLeNilradical hA hB hf hker).symm y) = y :=
  AlgEquiv.ofBijective_apply_symm_apply _ _ y

@[simp]
theorem reductionAlgEquivOfKerLeNilradical_symm_mk_powerBoundedMap (f : A →ₐ[K] B)
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ nilradical A) (a : powerBoundedSubring A) :
    (f.reductionAlgEquivOfKerLeNilradical hA hB hf hker).symm
      (Ideal.Quotient.mk _ (f.powerBoundedMap hA hB a)) = Ideal.Quotient.mk _ a := by
  rw [← reductionMap_mk, reductionAlgEquivOfKerLeNilradical_symm_reductionMap]

end AlgHom

namespace TauCeti

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IsAffinoidAlgebra

variable {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]
    [CompleteSpace A]

/-- **The canonical reduction of a nonzero affinoid algebra is a domain exactly when its
supremum seminorm is multiplicative.** -/
theorem isDomain_canonicalReduction_iff [Nontrivial A] (hA : IsAffinoidAlgebra K A) :
    IsDomain (CanonicalReduction A) ↔
      ∀ f g : A, supSeminorm K (f * g) = supSeminorm K f * supSeminorm K g := by
  rw [Ideal.Quotient.isDomain_iff_prime, hA.supSeminorm_mul_iff_isPrime]

end IsAffinoidAlgebra

end TauCeti

section GrauertRemmert

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "Tate " σ:max => _root_.MvPowerSeries.IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

namespace AlgHom

section Lifting

variable {A B : Type*}
    [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
    [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]

/-- **Torsion-freeness passes to canonical reductions.** Let `A` be an integrally closed affinoid
domain whose canonical reduction is a domain. If `g : A →ₐ[K] B` is integral into an affinoid
algebra `B` and every nonzero element of `A` acts without torsion on `B`, then
`CanonicalReduction A` acts without zero-divisors on `CanonicalReduction B`. -/
theorem reductionMap_mul_eq_zero_iff [IsDomain A] [IsIntegrallyClosed A]
    [IsDomain (CanonicalReduction A)] (g : A →ₐ[K] B) (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (hg_int : g.toRingHom.IsIntegral)
    (hg_reg : ∀ {a : A}, a ≠ 0 → ∀ {b : B}, g a * b = 0 → b = 0)
    (x : CanonicalReduction A) (y : CanonicalReduction B) :
    g.reductionMap hA hB x * y = 0 ↔ x = 0 ∨ y = 0 := by
  refine ⟨fun hxy ↦ ?_, ?_⟩
  · by_contra! hne
    obtain ⟨hx, hy⟩ := hne
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have ha1 : supSeminorm K (a : A) = 1 := by
      have hle : supSeminorm K (a : A) ≤ 1 :=
        hA.isPowerBounded_iff_supSeminorm_le_one.mp (mem_powerBoundedSubring.mp a.property)
      have hge : ¬ supSeminorm K (a : A) < 1 := fun hlt ↦ hx <|
        Ideal.Quotient.eq_zero_iff_mem.mpr <| mem_topologicallyNilpotentIdeal.mpr
          (hA.isTopologicallyNilpotent_iff_supSeminorm_lt_one.mpr hlt)
      exact hle.antisymm (not_lt.mp hge)
    let : Algebra A B := g.toRingHom.toAlgebra
    have : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun c ↦ (g.commutes c).symm
    have : Algebra.IsIntegral A B := ⟨hg_int⟩
    have : Module.IsTorsionFree A B := .of_smul_eq_zero fun r m hrm ↦
      or_iff_not_imp_left.mpr fun hr ↦ by
        rw [RingHom.smul_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hrm
        exact hg_reg hr hrm
    -- Multiplicativity `|g a * b|sup = |a|sup * |b|sup` forces `|b|sup < 1`.
    have hmulA := hA.isDomain_canonicalReduction_iff.mp inferInstance
    have hmul : supSeminorm K (g a * (b : B)) = supSeminorm K (a : A) * supSeminorm K (b : B) := by
      have := hB.supSeminorm_smul_of_isTorsionFree (A := A) (a := (a : A))
        (fun u ↦ hmulA u a) (b : B)
      simpa only [RingHom.smul_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using this
    rw [reductionMap_mk, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
      mem_topologicallyNilpotentIdeal, hB.isTopologicallyNilpotent_iff_supSeminorm_lt_one] at hxy
    have hlt : supSeminorm K (b : B) < 1 := by
      simpa [coe_powerBoundedMap, hmul, ha1] using hxy
    exact hy <| Ideal.Quotient.eq_zero_iff_mem.mpr <| mem_topologicallyNilpotentIdeal.mpr
      (hB.isTopologicallyNilpotent_iff_supSeminorm_lt_one.mpr hlt)
  · rintro (rfl | rfl) <;> simp

/-- Module-theoretic form of `AlgHom.reductionMap_mul_eq_zero_iff`: under the algebra structures
induced by `g : A →ₐ[K] B` and its reduction map, `CanonicalReduction B` is
`CanonicalReduction A`-torsion-free whenever `A` is an integrally closed affinoid domain with
domain canonical reduction and `B` is integral and `A`-torsion-free. -/
theorem isTorsionFree_reductionMap [IsDomain A] [IsIntegrallyClosed A]
    [IsDomain (CanonicalReduction A)] (g : A →ₐ[K] B) (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (hg_int : g.toRingHom.IsIntegral)
    (hg_reg : ∀ {a : A}, a ≠ 0 → ∀ {b : B}, g a * b = 0 → b = 0) :
    @Module.IsTorsionFree (CanonicalReduction A) (CanonicalReduction B) _ _
      (g.reductionMap hA hB).toRingHom.toAlgebra.toModule := by
  let := (g.reductionMap hA hB).toRingHom.toAlgebra
  refine .of_smul_eq_zero fun r m hrm ↦ ?_
  rw [RingHom.smul_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hrm
  exact (g.reductionMap_mul_eq_zero_iff hA hB hg_int hg_reg r m).mp hrm

/-- **Linear independence over `CanonicalReduction A` lifts to `A`.**
For any reduced affinoid algebra `A`, homomorphism `g : A →ₐ[K] B` into an affinoid algebra `B`,
and family `v : ι → powerBoundedSubring B`, linear independence of the reductions of `v` in
`CanonicalReduction B` over `CanonicalReduction A` implies linear independence of `v` in `B`
over `A`. -/
theorem linearIndependent_of_reductionMap [IsReduced A] {ι : Type*} (g : A →ₐ[K] B)
    (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B) (v : ι → powerBoundedSubring B)
    (hli : @LinearIndependent ι (CanonicalReduction A) (CanonicalReduction B)
      (fun i ↦ Ideal.Quotient.mk _ (v i)) _ _
      (g.reductionMap hA hB).toRingHom.toAlgebra.toModule) :
    @LinearIndependent ι A B (fun i ↦ (v i : B)) _ _ g.toRingHom.toAlgebra.toModule := by
  classical
  let : Algebra A B := g.toRingHom.toAlgebra
  let : Algebra (CanonicalReduction A) (CanonicalReduction B) :=
    (g.reductionMap hA hB).toRingHom.toAlgebra
  rw [linearIndependent_iff'] at hli ⊢
  intro s f hf i₀ hi₀
  by_contra hfi₀
  have : Nontrivial A := ⟨⟨f i₀, 0, hfi₀⟩⟩
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i ↦ supSeminorm K (f i)) ⟨i₀, hi₀⟩
  have hpos_j : 0 < supSeminorm K (f j) :=
    ((supSeminorm_nonneg (f i₀)).lt_of_ne'
      (mt (hA.isReduced_iff_supSeminorm_eq_zero.mp inferInstance (f i₀)) hfi₀)).trans_le
        (hmax i₀ hi₀)
  obtain ⟨m, hm, hscale⟩ := hA.exists_supSeminorm_smul_pow_eq_one
  obtain ⟨c, hc⟩ := hscale (f j) hpos_j
  have hpow : supSeminorm K (f j ^ (m - 1)) = supSeminorm K (f j) ^ (m - 1) :=
    (m - 1).eq_zero_or_pos.elim (fun h0 ↦ by simp [h0]) (fun hk ↦ supSeminorm_pow (f j) hk.ne')
  have hbound {i : ι} (hi : i ∈ s) : supSeminorm K ((c : K) • (f j ^ (m - 1) * f i)) ≤ 1 := by
    have hc' : ‖(c : K)‖ * (supSeminorm K (f j) ^ (m - 1) * supSeminorm K (f j)) = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hm, ← supSeminorm_pow (f j) (by omega), ← supSeminorm_smul]
      exact hc
    rw [supSeminorm_smul, ← hc']
    refine mul_le_mul_of_nonneg_left ((hA.supSeminorm_mul_le _ _).trans ?_) (norm_nonneg _)
    rw [hpow]
    exact mul_le_mul_of_nonneg_left (hmax i hi) (pow_nonneg (supSeminorm_nonneg _) _)
  let u (i : ι) : powerBoundedSubring A :=
    ⟨if i ∈ s then (c : K) • (f j ^ (m - 1) * f i) else 0, by
      rw [mem_powerBoundedSubring, hA.isPowerBounded_iff_supSeminorm_le_one]
      split_ifs with hi
      · exact hbound hi
      · simp [supSeminorm_zero]⟩
  have hsum : (∑ i ∈ s, Ideal.Quotient.mk (topologicallyNilpotentIdeal A) (u i) •
      Ideal.Quotient.mk (topologicallyNilpotentIdeal B) (v i)) = 0 := by
    suffices h0 : (∑ i ∈ s, g.powerBoundedMap hA hB (u i) * v i) = 0 by
      rw [← map_zero (Ideal.Quotient.mk (topologicallyNilpotentIdeal B)), ← h0, map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by
        rw [RingHom.smul_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          reductionMap_mk, map_mul]
    refine Subtype.ext ?_
    rw [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero]
    have heq : ∀ i ∈ s, ((g.powerBoundedMap hA hB (u i) * v i : powerBoundedSubring B) : B) =
        g ((c : K) • f j ^ (m - 1)) * (f i • (v i : B)) := fun i hi ↦ by
      simp only [MulMemClass.coe_mul, coe_powerBoundedMap, u, hi, ↓reduceIte,
        RingHom.smul_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_smul, map_mul,
        smul_mul_assoc, mul_assoc]
    rw [Finset.sum_congr rfl heq, ← Finset.mul_sum, hf, mul_zero]
  have huj := hli s (fun i ↦ Ideal.Quotient.mk _ (u i)) hsum j hj
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_topologicallyNilpotentIdeal,
    hA.isTopologicallyNilpotent_iff_supSeminorm_lt_one] at huj
  exact huj.ne (by simpa only [u, hj, ↓reduceIte, ← pow_succ, Nat.sub_add_cancel hm] using hc)

end Lifting

section TateDomain

variable {σ : Type*} [_root_.Finite σ] {B : Type*} [NormedCommRing B] [NormedAlgebra K B]
    [IsUltrametricDist B] [CompleteSpace B]

/-- Localising `CanonicalReduction B` at `(CanonicalReduction (Tate σ))⁰` yields a
finite-dimensional algebra over `FractionRing (CanonicalReduction (Tate σ))`. -/
private theorem finiteDimensional_localization_canonicalReduction
    (g : Tate σ →ₐ[K] B) (hB : IsAffinoidAlgebra K B) (hg_fin : g.Finite) :
    letI : Algebra (CanonicalReduction (Tate σ)) (CanonicalReduction B) :=
      (g.reductionMap isAffinoidAlgebra_tate hB).toRingHom.toAlgebra
    FiniteDimensional (FractionRing (CanonicalReduction (Tate σ)))
      (Localization (Algebra.algebraMapSubmonoid (CanonicalReduction B)
        (CanonicalReduction (Tate σ))⁰)) := by
  classical
  let : Algebra (Tate σ) B := g.toRingHom.toAlgebra
  have : Module.Finite (Tate σ) B := hg_fin
  let M := Localization (Algebra.algebraMapSubmonoid B (Tate σ)⁰)
  let R0 := CanonicalReduction (Tate σ)
  let B0 := CanonicalReduction B
  let : Algebra R0 B0 := (g.reductionMap isAffinoidAlgebra_tate hB).toRingHom.toAlgebra
  let E0 := Localization (Algebra.algebraMapSubmonoid B0 R0⁰)
  have : Module.Free (FractionRing R0) E0 := .of_divisionRing _ _
  suffices hlt : Module.rank (FractionRing R0) E0 <
      (Module.finrank (FractionRing (Tate σ)) M + 1 : ℕ) from
    Module.rank_lt_aleph0_iff.mp (hlt.trans Cardinal.natCast_lt_aleph0)
  by_contra! hge
  obtain ⟨w, hw⟩ := natCast_le_rank_iff.mp hge
  have hwR : LinearIndependent R0 w := (LinearIndependent.iff_fractionRing R0 _).mpr hw
  have : IsLocalizedModule R0⁰ (IsScalarTower.toAlgHom R0 B0 E0).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr Localization.isLocalization
  obtain ⟨u, hu⟩ :=
    IsLocalizedModule.linearIndependent_lift R0⁰ (IsScalarTower.toAlgHom R0 B0 E0).toLinearMap hwR
  choose v hv using fun i ↦ Ideal.Quotient.mk_surjective (u i)
  have hv_li : LinearIndependent (Tate σ) (fun i ↦ (v i : B)) :=
    g.linearIndependent_of_reductionMap isAffinoidAlgebra_tate hB v (by simpa only [hv] using hu)
  have hM_li : LinearIndependent (FractionRing (Tate σ)) (algebraMap B M ∘ fun i ↦ (v i : B)) :=
    hv_li.localization_localization (FractionRing (Tate σ)) (Tate σ)⁰ M
  have hcard := hM_li.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  omega

/-- **Finiteness on canonical reductions of a Noether normalisation of an affinoid domain.**
If `B` is an affinoid domain and `g : K⟨X⟩ →ₐ[K] B` is finite and injective, then
`g.reductionMap` is finite. No perfection or characteristic assumption on `K` or `𝓀[K]` is
made. -/
private theorem finite_reductionMap_of_tate_of_isDomain [IsDomain B] (g : Tate σ →ₐ[K] B)
    (hB : IsAffinoidAlgebra K B) (hg_inj : Function.Injective g) (hg_fin : g.Finite) :
    (g.reductionMap isAffinoidAlgebra_tate hB).Finite := by
  let R0 := CanonicalReduction (Tate σ)
  let B0 := CanonicalReduction B
  let : Algebra R0 B0 := (g.reductionMap isAffinoidAlgebra_tate hB).toRingHom.toAlgebra
  have : Module.IsTorsionFree R0 B0 :=
    g.isTorsionFree_reductionMap isAffinoidAlgebra_tate hB hg_fin.to_isIntegral
      fun ht _ hb ↦ (mul_eq_zero.mp hb).resolve_left ((map_ne_zero_iff g hg_inj).mpr ht)
  let F0 := FractionRing R0
  let S := Algebra.algebraMapSubmonoid B0 R0⁰
  let E0 := Localization S
  have hS : S ≤ B0⁰ := by
    rintro _ ⟨r, hr, rfl⟩
    have hreg (x : B0) (hx : algebraMap R0 B0 r * x = 0) : x = 0 := by
      rw [← Algebra.smul_def] at hx
      exact (smul_eq_zero.mp hx).resolve_left (mem_nonZeroDivisors_iff_ne_zero.mp hr)
    exact mem_nonZeroDivisors_iff.mpr
      ⟨fun x hx ↦ hreg x hx, fun x hx ↦ hreg x ((mul_comm (algebraMap R0 B0 r) x).trans hx)⟩
  have hinj : Function.Injective (algebraMap B0 E0) := IsLocalization.injective E0 hS
  have : FiniteDimensional F0 E0 :=
    finiteDimensional_localization_canonicalReduction g hB hg_fin
  have : Algebra.EssFiniteType R0 F0 := .of_isLocalization F0 R0⁰
  have : Algebra.EssFiniteType R0 E0 := .comp R0 F0 E0
  have : TauCeti.Ring.IsNagata R0 :=
    TauCeti.Ring.IsUniversallyJapanese.isNagata_of_finiteType 𝓀[K] R0
  have : Module.Finite R0 (integralClosure R0 E0) :=
    TauCeti.Ring.IsNagata.finite_integralClosure E0
  have : Algebra.IsIntegral R0 B0 := ⟨g.isIntegral_reductionMap isAffinoidAlgebra_tate hB
    hg_fin.to_isIntegral⟩
  let ι := (IsScalarTower.toAlgHom R0 B0 E0).codRestrict (integralClosure R0 E0) fun b ↦
    (Algebra.IsIntegral.isIntegral (R := R0) b).algebraMap
  have hι : Function.Injective ι.toLinearMap := by
    rw [AlgHom.coe_toLinearMap]
    exact (AlgHom.injective_codRestrict _ _ _).mpr
      (by simpa only [IsScalarTower.coe_toAlgHom'] using hinj)
  exact Module.Finite.of_injective ι.toLinearMap hι

end TateDomain

end AlgHom

namespace TauCeti.IsAffinoidAlgebra

variable {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]

/-- For an affinoid domain `A`, `CanonicalReduction A` is a finite-type `𝓀[K]`-algebra. -/
private theorem finiteType_canonicalReduction_of_isDomain [IsDomain A]
    (hA : IsAffinoidAlgebra K A) : Algebra.FiniteType 𝓀[K] (CanonicalReduction A) := by
  obtain ⟨d, g, hg_inj, hg_fin⟩ := hA.exists_finite_injective
  let R0 := CanonicalReduction (Tate (Fin d))
  let : Algebra R0 (CanonicalReduction A) :=
    (g.reductionMap isAffinoidAlgebra_tate hA).toRingHom.toAlgebra
  have : IsScalarTower 𝓀[K] R0 (CanonicalReduction A) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        (g.reductionMap isAffinoidAlgebra_tate hA).commutes]
  have : Module.Finite R0 (CanonicalReduction A) :=
    g.finite_reductionMap_of_tate_of_isDomain hA hg_inj hg_fin
  exact Algebra.FiniteType.trans (R := 𝓀[K]) (S := R0) (A := CanonicalReduction A)
    inferInstance inferInstance

/-- **Canonical reductions of affinoid algebras are of finite type over `𝓀[K]`**
[BGR, §6.3.5]. Every affinoid `K`-algebra `A` (without reducedness or domain hypotheses) has a
finitely generated canonical reduction over the residue field `𝓀[K]`. -/
theorem finiteType_canonicalReduction (hA : IsAffinoidAlgebra K A) :
    Algebra.FiniteType 𝓀[K] (CanonicalReduction A) := by
  rcases subsingleton_or_nontrivial A with _ | _
  · have : Subsingleton (CanonicalReduction A) := inferInstance
    exact ⟨⟨∅, Subsingleton.elim _ _⟩⟩
  have := hA.isNoetherianRing
  have : _root_.Finite (minimalPrimes A) :=
    (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
  have hclosed (𝔭 : minimalPrimes A) : IsClosed (𝔭.val : Set A) := hA.isClosed_ideal 𝔭.val
  have hprime (𝔭 : minimalPrimes A) : 𝔭.val.IsPrime := 𝔭.property.1.1
  have hdom (𝔭 : minimalPrimes A) : IsDomain (A ⧸ 𝔭.val) := Ideal.Quotient.isDomain 𝔭.val
  have hft (𝔭 : minimalPrimes A) : Algebra.FiniteType 𝓀[K] (CanonicalReduction (A ⧸ 𝔭.val)) :=
    finiteType_canonicalReduction_of_isDomain (hA.quotient 𝔭.val)
  let P := ∀ 𝔭 : minimalPrimes A, CanonicalReduction (A ⧸ 𝔭.val)
  let hAlg (𝔭 : minimalPrimes A) :
      Algebra (CanonicalReduction A) (CanonicalReduction (A ⧸ 𝔭.val)) :=
    ((Ideal.Quotient.mkₐ K 𝔭.val).reductionMap hA (hA.quotient 𝔭.val)).toRingHom.toAlgebra
  have hTower (𝔭 : minimalPrimes A) :
      IsScalarTower 𝓀[K] (CanonicalReduction A) (CanonicalReduction (A ⧸ 𝔭.val)) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  have hinj : Function.Injective (algebraMap (CanonicalReduction A) P) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨𝔭, h𝔭, hsup⟩ := hA.exists_mem_minimalPrimes_supSeminorm_eq (a : A)
    have h0 := congrFun hx ⟨𝔭, h𝔭⟩
    rw [Pi.algebraMap_apply, Pi.zero_apply, RingHom.algebraMap_toAlgebra,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.reductionMap_mk_eq_zero_iff,
      Ideal.Quotient.mkₐ_eq_mk, hsup] at h0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr <| mem_topologicallyNilpotentIdeal.mpr <|
      hA.isTopologicallyNilpotent_iff_supSeminorm_lt_one.mpr h0
  have : Algebra.IsIntegral (CanonicalReduction A) P :=
    ⟨fun y ↦ TauCeti.isIntegral_pi_iff.mpr fun 𝔭 ↦
      (Ideal.Quotient.mkₐ K 𝔭.val).isIntegral_reductionMap hA (hA.quotient 𝔭.val)
        (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective) (y 𝔭)⟩
  have : Algebra.FiniteType (CanonicalReduction A) P :=
    .of_restrictScalars_finiteType 𝓀[K] (CanonicalReduction A) P
  have : Module.Finite (CanonicalReduction A) P := Algebra.IsIntegral.finite
  exact ⟨fg_of_fg_of_fg 𝓀[K] (CanonicalReduction A) P Algebra.FiniteType.out
    Module.Finite.fg_top hinj⟩

/-- The canonical reduction of an affinoid algebra is a Noetherian ring [BGR, §6.3.5]. -/
theorem isNoetherianRing_canonicalReduction (hA : IsAffinoidAlgebra K A) :
    IsNoetherianRing (CanonicalReduction A) := by
  have := hA.finiteType_canonicalReduction
  exact Algebra.FiniteType.isNoetherianRing 𝓀[K] (CanonicalReduction A)

/-- The canonical reduction of an affinoid algebra is a Nagata ring. -/
theorem isNagata_canonicalReduction (hA : IsAffinoidAlgebra K A) :
    TauCeti.Ring.IsNagata (CanonicalReduction A) := by
  have := hA.finiteType_canonicalReduction
  exact TauCeti.Ring.IsUniversallyJapanese.isNagata_of_finiteType 𝓀[K] (CanonicalReduction A)

end TauCeti.IsAffinoidAlgebra

namespace AlgHom

variable {A B : Type*}
    [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]
    [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]

/-- Every homomorphism of affinoid `K`-algebras induces a finite-type `𝓀[K]`-algebra homomorphism on
canonical reductions [BGR, §6.3.5]. -/
theorem finiteType_reductionMap (f : A →ₐ[K] B) (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) :
    (f.reductionMap hA hB).FiniteType :=
  AlgHom.FiniteType.of_comp_finiteType (f := Algebra.ofId 𝓀[K] (CanonicalReduction A)) <| by
    rw [Algebra.comp_ofId, AlgHom.FiniteType, AlgHom.toRingHom_eq_coe, Algebra.toRingHom_ofId,
      RingHom.finiteType_algebraMap]
    exact hB.finiteType_canonicalReduction

/-- **Grauert–Remmert finiteness theorem** [BGR, 6.3.5/1]: every integral (in particular, every
finite) homomorphism of affinoid algebras induces a finite homomorphism on their canonical
reductions. -/
theorem finite_reductionMap (f : A →ₐ[K] B) (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (hf : f.toRingHom.IsIntegral) :
    (f.reductionMap hA hB).Finite :=
  (f.isIntegral_reductionMap hA hB hf).to_finite (f.finiteType_reductionMap hA hB)

end AlgHom

end GrauertRemmert
