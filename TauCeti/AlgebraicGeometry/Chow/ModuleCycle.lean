/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Chow.ClosedImmersion
public import TauCeti.AlgebraicGeometry.Chow.TopDimension
public import TauCeti.RingTheory.Length.Support
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Basic
import TauCeti.RingTheory.Length.Localization
import TauCeti.RingTheory.Length

/-!
# The cycle of a finite module

Let `M` be a finite module over a Noetherian ring `R`, with support of dimension at most `d`.
Its cycle `moduleCycle M hM` in `Z_d(Spec R)` counts each component of dimension `d` with
the length of the localization at its generic point. It is effective and additive in short
exact sequences. For a prime quotient of dimension `d` it is the basis cycle of the prime.
Along an affine closed immersion its pushforward is the cycle of the same module with
scalars restricted to the ambient ring.

The grading uses the dimension of the closure of a point in the ambient spectrum,
`dim (R ⧸ p)`. The module and the ring may have different dimensions.

## References

* [The Stacks Project, Section 42.10](https://stacks.math.columbia.edu/tag/02QV).
-/

public section

open AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.Chow

variable {R : Type*} [CommRing R] {d : ℕ}

variable [IsNoetherianRing R] (M : Type*) [AddCommGroup M] [Module R M]

section

variable [Module.Finite R M]

/-- The cycle of a finite module of support dimension at most `d`, in the dimension-`d` subgroup
of the integral algebraic cycles on `Spec R`. -/
noncomputable def moduleCycle (hM : Module.supportDim R M ≤ d) :
    cyclesOfDimension (Spec (.of R)) d := by
  refine (cyclesOfDimensionEquivFinsupp _ _).symm ?_
  let coeff (p : PrimeSpectrum R) : ℤ :=
    (Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M)).toNat
  refine Finsupp.ofSupportFinite (fun p ↦ coeff p.val) ?_
  let f (p : pointsOfDimension (Spec (.of R)) d) := (p.val : PrimeSpectrum R).asIdeal
  have hf : Function.Injective f := fun _ _ h ↦ Subtype.ext (PrimeSpectrum.ext h)
  refine (((Module.annihilator R M).finite_minimalPrimes_of_isNoetherianRing R).preimage
    hf.injOn).subset fun p hp ↦ ?_
  apply Module.mem_minimalPrimes_annihilator_of_ringKrullDim_quotient_eq
    (p := (p.val : PrimeSpectrum R)) hM _ (mem_pointsOfDimension_spec_iff.mp p.property)
  by_contra h
  apply hp
  have := Module.notMem_support_iff.mp h
  simp [coeff]

/-- At a point of dimension `d`, the cycle coefficient is the length of the localized module. -/
@[simp]
theorem moduleCycle_apply (hM : Module.supportDim R M ≤ d) {p : PrimeSpectrum R}
    (hp : ringKrullDim (R ⧸ p.asIdeal) = d) :
    (moduleCycle M hM : AlgebraicCycle (Spec (.of R)) ℤ) (p : Spec (.of R)) =
      (Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M)).toNat := by
  let q : pointsOfDimension (Spec (.of R)) d := ⟨p, mem_pointsOfDimension_spec_iff.2 hp⟩
  unfold moduleCycle
  exact cyclesOfDimensionEquivFinsupp_symm_apply (Spec (.of R)) d _ q

/-- For a finite module with zero-dimensional or empty support over a local ring, the
coefficient at the closed point is its length over the original ring. -/
@[simp]
theorem moduleCycle_apply_closedPoint [IsLocalRing R] (hM : Module.supportDim R M ≤ 0) :
    (moduleCycle M (d := 0) hM : AlgebraicCycle (Spec (.of R)) ℤ) (IsLocalRing.closedPoint R) =
      (Module.length R M).toNat := by
  have hd : ringKrullDim (R ⧸ IsLocalRing.maximalIdeal R) = 0 :=
    ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 inferInstance)
  refine (moduleCycle_apply M hM (p := IsLocalRing.closedPoint R) (d := 0) hd).trans ?_
  exact congrArg (fun n : ℕ∞ ↦ (n.toNat : ℤ)) (Module.length_localizedModule_of_le_isUnit M
    (S := (IsLocalRing.maximalIdeal R).primeCompl) fun _ hx ↦ IsLocalRing.notMem_maximalIdeal.mp hx)

/-- The module cycle is effective. -/
theorem moduleCycle_nonneg (hM : Module.supportDim R M ≤ d) : 0 ≤ moduleCycle M hM := by
  intro x
  let p : PrimeSpectrum R := x
  by_cases hp : ringKrullDim (R ⧸ p.asIdeal) = d
  · exact (moduleCycle_apply M hM hp).symm ▸ Int.natCast_nonneg _
  · exact (apply_eq_zero_of_notMem_pointsOfDimension (moduleCycle M hM).property
      (mt mem_pointsOfDimension_spec_iff.mp hp)).ge

/-- The points with nonzero coefficient are exactly the primes of the support whose closures
have dimension `d`. -/
@[simp]
theorem mem_support_moduleCycle (hM : Module.supportDim R M ≤ d) {p : PrimeSpectrum R} :
    (p : Spec (.of R)) ∈ (moduleCycle M hM : AlgebraicCycle (Spec (.of R)) ℤ).support ↔
      p ∈ Module.support R M ∧ ringKrullDim (R ⧸ p.asIdeal) = d := by
  -- Unfold membership at the scheme point before using its prime-spectrum description.
  change (moduleCycle M hM : AlgebraicCycle (Spec (.of R)) ℤ) p ≠ 0 ↔ _
  by_cases hp : ringKrullDim (R ⧸ p.asIdeal) = d
  · have hfin := Module.length_ne_top_iff.2
      (Module.isFiniteLength_localizedModule_of_ringKrullDim_quotient_eq hM hp)
    simp only [moduleCycle_apply M hM hp, ne_eq, Int.natCast_eq_zero,
      ENat.toNat_eq_zero, hfin, or_false, Module.length_eq_zero_iff, hp, and_true,
      Module.mem_support_iff, not_subsingleton_iff_nontrivial]
  · have hz := apply_eq_zero_of_notMem_pointsOfDimension (moduleCycle M hM).property
      (mt mem_pointsOfDimension_spec_iff.mp hp)
    simp [hp, hz]

/-- A module of support dimension strictly less than `d` contributes no `d`-cycle. -/
theorem moduleCycle_eq_zero_of_supportDim_lt (hM : Module.supportDim R M < d) :
    moduleCycle M hM.le = 0 := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun p ↦ ?_)
  apply Function.notMem_support.mp
  rintro hp
  obtain ⟨hs, hd⟩ := (mem_support_moduleCycle M hM.le (p := p)).1 hp
  exact ((Module.ringKrullDim_quotient_le_supportDim_of_mem_support hs).trans_lt hM).ne hd

end

/-- The cycle of the zero module is zero in every dimension. -/
@[simp]
theorem moduleCycle_of_subsingleton [Subsingleton M] :
    moduleCycle (R := R) M (d := d) (by simp [Module.supportDim_eq_bot_of_subsingleton]) = 0 :=
  moduleCycle_eq_zero_of_supportDim_lt M (by simp [Module.supportDim_eq_bot_of_subsingleton])

variable {M} [Module.Finite R M] {N P : Type*} [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- The cycle of the middle term of a short exact sequence is the sum of the outer cycles.
A dimension bound on the middle term bounds both other supports. -/
theorem moduleCycle_eq_add_of_exact (f : N →ₗ[R] M) (g : M →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hM : Module.supportDim R M ≤ d) :
    let _ := Module.Finite.of_injective f hf
    let _ := Module.Finite.of_surjective g hg
    moduleCycle M hM = moduleCycle N ((Module.supportDim_le_of_injective f hf).trans hM) +
      moduleCycle P ((Module.supportDim_le_of_surjective g hg).trans hM) := by
  intro hNfin hPfin
  let hN := (Module.supportDim_le_of_injective f hf).trans hM
  let hP := (Module.supportDim_le_of_surjective g hg).trans hM
  apply (cyclesOfDimensionEquivFinsupp _ _).injective
  refine DFunLike.ext _ _ fun q ↦ ?_
  let p : PrimeSpectrum R := q.val
  have hp : ringKrullDim (R ⧸ p.asIdeal) = d := mem_pointsOfDimension_spec_iff.mp q.property
  have he := Module.length_eq_add_of_exact (LocalizedModule.map p.asIdeal.primeCompl f)
    (LocalizedModule.map p.asIdeal.primeCompl g) (LocalizedModule.map_injective _ f hf)
    (LocalizedModule.map_surjective _ g hg) (LocalizedModule.map_exact _ f g hfg)
  have hlen := congrArg ENat.toNat he
  rw [ENat.toNat_add (Module.length_ne_top_iff.2
    (Module.isFiniteLength_localizedModule_of_ringKrullDim_quotient_eq hN hp))
    (Module.length_ne_top_iff.2
      (Module.isFiniteLength_localizedModule_of_ringKrullDim_quotient_eq hP hp))] at hlen
  simp only [map_add, Finsupp.add_apply, cyclesOfDimensionEquivFinsupp_apply]
  refine (moduleCycle_apply M hM hp).trans (Eq.trans ?_
    (congrArg₂ (· + ·) (moduleCycle_apply N hN hp) (moduleCycle_apply P hP hp)).symm)
  exact_mod_cast hlen

/-- The top-dimensional cycle of `R/p` for a prime `p` is its basis cycle with coefficient one. -/
@[simp]
theorem moduleCycle_quotient_prime (p : PrimeSpectrum R) (hd : ringKrullDim (R ⧸ p.asIdeal) = d) :
    moduleCycle (R ⧸ p.asIdeal) ((Module.supportDim_quotient_eq_ringKrullDim _).trans hd).le =
      cyclesOfDimensionBasis (Spec (.of R)) d ⟨p, mem_pointsOfDimension_spec_iff.2 hd⟩ := by
  classical
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun q ↦ ?_)
  rw [coe_cyclesOfDimensionBasis, Function.locallyFinsuppWithin.single_apply]
  by_cases h : q = p
  · subst q
    simp [moduleCycle_apply _ _ hd]
    rfl
  · rw [ite_eq_right h]
    apply Function.notMem_support.mp
    intro hq
    obtain ⟨hs, hdim⟩ := (mem_support_moduleCycle _ _ (p := q)).1 hq
    have hmin := Module.mem_minimalPrimes_annihilator_of_ringKrullDim_quotient_eq
      ((Module.supportDim_quotient_eq_ringKrullDim _).trans hd).le hs hdim
    rw [Ideal.annihilator_quotient, Ideal.minimalPrimes_eq_subsingleton_self] at hmin
    exact h (PrimeSpectrum.ext hmin)

/-- For an affine closed immersion `Spec S → Spec R`, pushing forward the cycle of a finite
`S`-module gives its cycle as an `R`-module. -/
theorem cyclesPushforward_moduleCycle {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] (hs : Function.Surjective (algebraMap R S))
    (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] {d : ℕ} (hM : Module.supportDim S M ≤ d) :
    let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let _ := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (algebraMap R S)) hs
    let _ := isNoetherianRing_of_surjective R S (algebraMap R S) hs
    let _ : Module.Finite R S := .of_surjective (Algebra.linearMap R S) hs
    let _ := Module.Finite.trans (R := R) S M
    cyclesPushforward i (moduleCycle M hM) =
      moduleCycle M ((Module.supportDim_eq_of_surjective hs).trans_le hM) := by
  intro i hi hS hRS hRM
  let hR := (Module.supportDim_eq_of_surjective (M := M) hs).trans_le hM
  apply (cyclesOfDimensionEquivFinsupp _ _).injective
  refine DFunLike.ext _ _ fun x ↦ ?_
  simp only [cyclesOfDimensionEquivFinsupp_apply]
  by_cases hx : x.val ∈ Set.range i
  · -- The closure dimension and the localized length agree at corresponding points.
    obtain ⟨q, hq⟩ := hx
    have hqd : q ∈ pointsOfDimension (Spec (.of S)) d := by
      obtain ⟨n, hn, hnd⟩ := mem_pointsOfDimension.mp x.property
      exact mem_pointsOfDimension.mpr ⟨n, (i.height_apply_eq_height q).symm.trans (hq ▸ hn), hnd⟩
    have hdim := mem_pointsOfDimension_spec_iff.mp hqd
    have hpd := mem_pointsOfDimension_spec_iff.mp x.property
    rw [← hq] at hpd ⊢
    rw [cyclesPushforward_apply]
    refine (moduleCycle_apply M hM hdim).trans (Eq.trans ?_ (moduleCycle_apply M hR hpd).symm)
    let Q : PrimeSpectrum S := q
    exact congrArg (fun n : ℕ∞ ↦ (n.toNat : ℤ))
      (Module.length_localizedModule_under_of_surjective M hs Q.asIdeal).symm
  · -- The kernel annihilates the restricted module, so its support lies in the image.
    rw [cyclesPushforward_apply_of_notMem_range _ hx, eq_comm]
    apply Function.notMem_support.mp
    intro h
    have hxM := ((mem_support_moduleCycle M hR (p := x.val)).1 h).1
    apply hx
    suffices (x.val : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) from this
    rw [range_comap_of_surjective S (algebraMap R S) hs]
    exact ((Ideal.ker_le_comap (algebraMap R S)).trans_eq Module.comap_annihilator).trans
      (Module.annihilator_le_of_mem_support hxM)

end TauCeti.AlgebraicGeometry.Chow
