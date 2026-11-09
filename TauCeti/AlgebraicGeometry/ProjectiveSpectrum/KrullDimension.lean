/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.KrullDimension.Basic
import TauCeti.Topology.KrullDimension.Basic

/-!
# The Krull dimension of `Proj`

For an `ℕ`-graded commutative ring `A`, the projective spectrum `Proj A` has Krull dimension at
most `dim A - 1`: `topologicalKrullDim (Proj 𝒜) + 1 ≤ ringKrullDim A`.

A point of `Proj A` is a relevant homogeneous prime `p`, one not containing the irrelevant ideal
`A₊`. Its generizations in `Proj A` are smaller relevant homogeneous primes, so a chain of
generizations of length `n` is a chain of primes of `A` of length `n` ending in `p`. The ideal
`p + A₊` is proper, because its degree-zero part is the degree-zero part of `p`, and it strictly
contains `p`. A maximal ideal containing it extends the chain by one step.

For the projective space of lines in a vector space `V` of dimension `n` over a field, `A` is a
polynomial ring in `n` variables and the bound says that this projective space has dimension at
most `n - 1`. This is the ambient bound used to recognize dense orbits in projective spaces by
their dimension.

## Main results

* `ProjectiveSpectrum.sup_irrelevant_ne_top`: a relevant homogeneous prime and the irrelevant
  ideal generate a proper ideal.
* `AlgebraicGeometry.Proj.coheight_add_one_le_ringKrullDim`: the codimension of a point of
  `Proj A` is less than `dim A`.
* `AlgebraicGeometry.Proj.topologicalKrullDim_add_one_le_ringKrullDim`:
  `topologicalKrullDim (Proj 𝒜) + 1 ≤ ringKrullDim A`.

## References

* Stacks Project, Tag 00JS (Krull dimension) and Tag 00JM (`Proj` of a graded ring).
-/

public section

open Order Topology

variable {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

namespace ProjectiveSpectrum

/-- The sum of a relevant homogeneous prime and the irrelevant ideal is a proper ideal: its
degree-zero part is that of the prime. -/
theorem sup_irrelevant_ne_top (x : ProjectiveSpectrum 𝒜) :
    x.asHomogeneousIdeal.toIdeal ⊔ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≠ ⊤ := by
  intro htop
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top (x := (1 : A)))
  -- The degree-zero component of `1 = a + b` is `1`, lies in the homogeneous ideal `x`, and
  -- receives no contribution from `b ∈ A₊`.
  have hb0 : GradedRing.proj 𝒜 0 b = 0 := (HomogeneousIdeal.mem_irrelevant_iff 𝒜 b).mp hb
  have ha0 : GradedRing.proj 𝒜 0 a ∈ x.asHomogeneousIdeal :=
    x.asHomogeneousIdeal.isHomogeneous.mem_iff.mp ha 0
  have h1 : GradedRing.proj 𝒜 0 (a + b) = 1 := by
    rw [hab]
    exact DirectSum.decompose_of_mem_same 𝒜 SetLike.GradedOne.one_mem
  rw [map_add, hb0, add_zero] at h1
  rw [h1] at ha0
  exact x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ha0)

end ProjectiveSpectrum

namespace AlgebraicGeometry.Proj

/-- The codimension of a point of `Proj A`, for the specialization order, is less than the Krull
dimension of `A`: a chain of generizations of the point is a chain of primes of `A`, which a
maximal ideal containing the irrelevant ideal extends by one step. -/
theorem coheight_add_one_le_ringKrullDim (x : Proj 𝒜) :
    (coheight x : WithBot ℕ∞) + 1 ≤ ringKrullDim A := by
  let f : Proj 𝒜 → (PrimeSpectrum A)ᵒᵈ := fun y ↦
    OrderDual.toDual ⟨y.asHomogeneousIdeal.toIdeal, y.isPrime⟩
  -- In the specialization order `y ≤ z` says that `z` specializes to `y`, so the ideal of `z`
  -- is contained in that of `y`.
  have hf : StrictMono f := by
    refine Monotone.strictMono_of_injective (fun y z hyz ↦ ?_) fun y z hyz ↦ ?_
    · have hzy : z.asHomogeneousIdeal ≤ y.asHomogeneousIdeal :=
        (ProjectiveSpectrum.as_ideal_le_as_ideal 𝒜 z y).mpr
          ((ProjectiveSpectrum.le_iff_mem_closure 𝒜 z y).mpr (specializes_iff_mem_closure.mp hyz))
      exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp (toIdeal_le_toIdeal_iff.mpr hzy)
    · exact ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective
        (congrArg PrimeSpectrum.asIdeal (OrderDual.toDual.injective hyz)))
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ (ProjectiveSpectrum.sup_irrelevant_ne_top 𝒜 x)
  have hlt : (⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩ : PrimeSpectrum A) <
      ⟨m, hm.isPrime⟩ := by
    refine lt_of_le_of_ne (le_sup_left.trans hle) fun heq ↦ x.not_irrelevant_le ?_
    have : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ x.asHomogeneousIdeal.toIdeal :=
      (le_sup_right.trans hle).trans (congrArg PrimeSpectrum.asIdeal heq).ge
    exact this
  calc (coheight x : WithBot ℕ∞) + 1
      ≤ (height (⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩ : PrimeSpectrum A) : WithBot ℕ∞) +
          1 := by
        gcongr
        exact_mod_cast (coheight_le_coheight_apply_of_strictMono f hf x).trans_eq
          (coheight_toDual _)
    _ ≤ height (⟨m, hm.isPrime⟩ : PrimeSpectrum A) := by
        exact_mod_cast height_add_one_le hlt
    _ ≤ ringKrullDim A := height_le_krullDim _

/-- **The Krull dimension of `Proj`.** The projective spectrum of an `ℕ`-graded commutative ring
`A` has Krull dimension at most `dim A - 1`. -/
theorem topologicalKrullDim_add_one_le_ringKrullDim :
    topologicalKrullDim (Proj 𝒜) + 1 ≤ ringKrullDim A := by
  rw [TauCeti.topologicalKrullDim_eq_iSup_coheight]
  cases isEmpty_or_nonempty (Proj 𝒜) with
  | inl h => simp
  | inr h =>
    obtain ⟨x⟩ := id h
    obtain ⟨d, hd⟩ : ∃ d : ℕ∞, (d : WithBot ℕ∞) = ringKrullDim A :=
      WithBot.ne_bot_iff_exists.mp fun (h : ringKrullDim A = ⊥) ↦ by
        have hx := coheight_add_one_le_ringKrullDim 𝒜 x
        rw [h, le_bot_iff, WithBot.add_eq_bot] at hx
        simp at hx
    have hle (y : Proj 𝒜) : coheight y + 1 ≤ d := by
      exact_mod_cast hd ▸ coheight_add_one_le_ringKrullDim 𝒜 y
    rw [← hd, ← WithBot.coe_iSup (OrderTop.bddAbove _)]
    exact_mod_cast (ENat.iSup_add (fun y : Proj 𝒜 ↦ coheight y)).trans_le (iSup_le hle)

end AlgebraicGeometry.Proj
