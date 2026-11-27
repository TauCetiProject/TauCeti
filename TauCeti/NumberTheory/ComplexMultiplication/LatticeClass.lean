/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ComplexMultiplication.IdealLattice

/-!
# Ideal classes and lattices with complex multiplication

Let `K` be an imaginary quadratic field, oriented by a non-real embedding `σ : K →+* ℂ`, and let `O`
be an order of `K`. By `TauCeti.GlobalNumberFields.NumberFieldOrder.exists_periodPair_lattice_eq`,
every nonzero fractional ideal `I` of `O` gives a lattice `σ(I)`, whose multiplier ring (its left
order `Submodule.leftOrder`) is `σ(O)` when `I` is proper. This file proves that this is a bijection
between the ideal classes of proper fractional ideals and the homothety classes
(`PeriodPair.Homothetic`) of lattices with multiplier ring `σ(O)`:

* two nonzero fractional ideals have the same class exactly when their lattices are homothetic
  (`mk_eq_mk_iff_homothetic`): a homothety `c σ(I) = σ(J)` has `c = σ(x)` for some
  `x ∈ Kˣ`, and then `J = x I`;
* every lattice whose multiplier ring is `σ(O)` is homothetic to `σ(I)` for a proper fractional
  ideal `I` (`exists_isProper_lattice_smul_eq`): rescale it to `ℤ + ℤ τ`; a non-real multiplier
  `σ(x) = a + b τ` with `x ∈ O` shows `τ = σ(t)` with `t = (x - a) / b ∈ K`, and `ℤ + ℤ t` is
  stable under `O`, so it is the fractional ideal `O + O t`.

This is the oriented ideal-lattice dictionary at the level of homothety classes. By
`PeriodPair.weierstrassCurve_smul` homothetic lattices give isomorphic Weierstrass curves.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.exists_eq_spanSingleton_mul_of_lattice_eq_smul`:
  homothetic ideal lattices come from homothetic ideals.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.mk_eq_mk_iff_homothetic`: the ideal
  class is the homothety class of the lattice.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.exists_isProper_lattice_smul_eq`: every lattice
  with multiplier ring `σ(O)` is homothetic to the lattice of a proper ideal.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, 2nd ed., Wiley, 2013, §10.C.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Graduate Texts in
  Mathematics 151, Springer, 1994, §II.1.
-/

public section

open NumberField FractionalIdeal

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] {O : NumberFieldOrder K} {σ : K →+* ℂ}

/-- Membership in a lattice `σ(I)`. -/
private lemma mem_lattice_iff_of_coe_eq {L : PeriodPair}
    {I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} (hL : (L.lattice : Set ℂ) = σ '' I)
    (z : ℂ) : z ∈ L.lattice ↔ ∃ y ∈ I, σ y = z := by
  rw [← SetLike.mem_coe, hL]
  rfl

/-- **Homothetic ideal lattices come from homothetic ideals.** If the lattices `σ(I)` and `σ(J)`
of two fractional ideals satisfy `σ(J) = c σ(I)`, then `J = x I` for an `x ∈ Kˣ` with `σ(x) = c`.
-/
theorem exists_eq_spanSingleton_mul_of_lattice_eq_smul
    {I J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K} {L L' : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' I) (hL' : (L'.lattice : Set ℂ) = σ '' J) (c : ℂˣ)
    (h : L'.lattice = (c • L).lattice) :
    ∃ x : Kˣ, σ x = c ∧ spanSingleton (nonZeroDivisors O.toSubalgebra) (x : K) * I = J := by
  have hJ : ∀ z, (∃ y ∈ J, σ y = z) ↔ ∃ w, (∃ y ∈ I, σ y = w) ∧ (c : ℂ) * w = z := fun z ↦ by
    rw [← mem_lattice_iff_of_coe_eq hL', h, PeriodPair.mem_lattice_smul_iff]
    simp only [mem_lattice_iff_of_coe_eq hL]
  -- `σ(I)` contains the nonzero period `ω₁`.
  obtain ⟨y₀, hy₀, hσy₀⟩ := (mem_lattice_iff_of_coe_eq hL _).mp L.ω₁_mem_lattice
  replace hσy₀ : σ y₀ ≠ 0 := hσy₀ ▸ L.ω₁_ne_zero
  obtain ⟨y₁, -, e⟩ := (hJ _).mpr ⟨_, ⟨y₀, hy₀, rfl⟩, rfl⟩
  have hx : σ (y₁ / y₀) = c := by rw [map_div₀, e, mul_div_cancel_right₀ _ hσy₀]
  have hx0 : y₁ / y₀ ≠ 0 := fun h0 ↦ c.ne_zero (by rw [← hx, h0, map_zero])
  refine ⟨Units.mk0 _ hx0, hx, FractionalIdeal.ext fun z ↦ ?_⟩
  rw [mem_singleton_mul, Units.val_mk0]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z', hz', e'⟩ := (hJ _).mpr ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rwa [σ.injective (e'.trans (by rw [map_mul, hx]) : σ z' = σ (y₁ / y₀ * y))] at hz'
  · intro hz
    obtain ⟨_, ⟨y, hy, rfl⟩, e'⟩ := (hJ _).mp ⟨z, hz, rfl⟩
    exact ⟨y, hy, σ.injective (by rw [← e', map_mul, hx])⟩

/-- **The ideal class is the homothety class of the lattice.** Two nonzero fractional ideals have
the same class exactly when their lattices are homothetic. -/
theorem mk_eq_mk_iff_homothetic {I J : O.nonzeroFractionalIdeals} {L L' : PeriodPair}
    (hL : (L.lattice : Set ℂ) = σ '' (I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K))
    (hL' : (L'.lattice : Set ℂ) = σ '' (J : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)) :
    IdealClassMonoid.mk O I = IdealClassMonoid.mk O J ↔ L.Homothetic L' := by
  rw [IdealClassMonoid.mk_eq_mk_iff, PeriodPair.homothetic_def]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨Units.map σ.toMonoidHom x, SetLike.coe_injective ?_⟩
    rw [hL', lattice_smul_eq_image_spanSingleton_mul hL x, hx]
  · rintro ⟨c, hc⟩
    obtain ⟨x, -, hx⟩ := exists_eq_spanSingleton_mul_of_lattice_eq_smul hL hL' c hc
    exact ⟨x, hx⟩

/-- A nonreal embedding takes a nonreal value on every order: `K` is the fraction field of `O`, so
if `σ` were real on `O` it would be real on `K`. -/
private lemma exists_mem_im_ne_zero (hσ : ¬ ComplexEmbedding.IsReal σ) (O : NumberFieldOrder K) :
    ∃ x ∈ O.toSubalgebra, (σ x).im ≠ 0 := by
  by_contra! h
  refine hσ (ComplexEmbedding.isReal_iff.mpr (RingHom.ext fun y ↦ ?_))
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := O.toSubalgebra) y
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_eq_iff_im]
  simp [Complex.div_im, h _ a.property, h _ b.property]

/-- The elements of the fractional ideal `O + O t` are the sums `o₁ + o₂ t` with `o₁, o₂ ∈ O`. -/
private lemma mem_spanSingleton_one_sup_spanSingleton_iff {t z : K} :
    z ∈ spanSingleton (nonZeroDivisors O.toSubalgebra) (1 : K) ⊔ spanSingleton _ t ↔
      ∃ o₁ ∈ O.toSubalgebra, ∃ o₂ ∈ O.toSubalgebra, o₁ + o₂ * t = z := by
  rw [← mem_coeToSubmodule, coeToSubmodule_sup, Submodule.mem_sup]
  simp only [mem_coeToSubmodule, mem_spanSingleton, Algebra.smul_def, mul_one, Subtype.exists]
  constructor
  · rintro ⟨_, ⟨o₁, ho₁, rfl⟩, _, ⟨o₂, ho₂, rfl⟩, rfl⟩
    exact ⟨o₁, ho₁, o₂, ho₂, rfl⟩
  · rintro ⟨o₁, ho₁, o₂, ho₂, rfl⟩
    exact ⟨_, ⟨o₁, ho₁, rfl⟩, _, ⟨o₂, ho₂, rfl⟩, rfl⟩

/-- **Every lattice with complex multiplication by `O` comes from a proper ideal.** If the
multiplier ring of `L` is `σ(O)`, then a rescaling of the lattice of `L` is `σ(I)` for a proper
fractional ideal `I` of `O`. -/
theorem exists_isProper_lattice_smul_eq (hσ : ¬ ComplexEmbedding.IsReal σ) {L : PeriodPair}
    (hL : L.lattice.leftOrder = O.toSubalgebra.map σ.toIntAlgHom) :
    ∃ I : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K, O.IsProperFractionalIdeal I ∧
      ∃ c : ℂˣ, ((c • L).lattice : Set ℂ) = σ '' I := by
  -- An element `x` of `O` with a non-real image.
  obtain ⟨x, hxO, him⟩ := exists_mem_im_ne_zero hσ O
  -- Rescale `L` to the lattice `ℤ + ℤ τ`.
  set c := Units.mk0 L.ω₁⁻¹ (inv_ne_zero L.ω₁_ne_zero)
  set L' := c • L
  have hω₁ : L'.ω₁ = 1 := by simp [L', c, L.ω₁_ne_zero]
  have hL'R : L'.lattice.leftOrder = O.toSubalgebra.map σ.toIntAlgHom := by
    rw [PeriodPair.leftOrder_lattice_smul, hL]
  have hmulR : ∀ o ∈ O.toSubalgebra, ∀ z ∈ L'.lattice, σ o * z ∈ L'.lattice := fun o ho ↦ by
    rw [← Submodule.mem_leftOrder_iff, hL'R]
    exact ⟨o, ho, rfl⟩
  -- `σ x = a + b τ`, with `b ≠ 0` because `σ x` is not real.
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp (hmulR x hxO _ L'.ω₁_mem_lattice)
  simp only [hω₁, mul_one] at hab
  have hb : (b : ℂ) ≠ 0 := fun hb ↦ him (by rw [← hab, hb]; simp)
  set t : K := (x - a) / b
  have ht : σ t = L'.ω₂ := by
    simp only [t, map_div₀, map_sub, map_intCast]
    rw [← hab]
    field_simp
    ring
  -- The fractional ideal `O + O t`.
  set I := spanSingleton (nonZeroDivisors O.toSubalgebra) (1 : K) ⊔ spanSingleton _ t
  have hlat : (L'.lattice : Set ℂ) = σ '' I := by
    ext w
    simp only [SetLike.mem_coe, Set.mem_image, I, mem_spanSingleton_one_sup_spanSingleton_iff]
    constructor
    · intro hw
      obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hw
      refine ⟨m + n * t, ⟨m, intCast_mem _ m, n, intCast_mem _ n, rfl⟩, ?_⟩
      rw [map_add, map_mul, map_intCast, map_intCast, ht, hω₁, mul_one]
    · rintro ⟨_, ⟨o₁, ho₁, o₂, ho₂, rfl⟩, rfl⟩
      rw [map_add, map_mul, ht]
      refine add_mem ?_ (hmulR o₂ ho₂ _ L'.ω₂_mem_lattice)
      simpa [hω₁] using hmulR o₁ ho₁ _ L'.ω₁_mem_lattice
  refine ⟨I, ?_, c, hlat⟩
  rw [isProperFractionalIdeal_def]
  have hmap : (O.multiplierRing I).map σ = O.toSubalgebra.toSubring.map σ :=
    (toSubring_leftOrder_lattice_eq_map hlat).symm.trans
      ((congrArg _ hL'R).trans (SetLike.coe_injective (by simp)))
  rw [← Subring.comap_map_eq_self_of_injective σ.injective (O.multiplierRing I), hmap,
    Subring.comap_map_eq_self_of_injective σ.injective]

end NumberFieldOrder

end TauCeti.GlobalNumberFields
