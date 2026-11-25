/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.RingTheory.Valuation.Center
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# The specialization map of an adic spectrum

For a ring `A` with a topology and a subring `A⁺`, a point `x` of `Spa(A, A⁺)` is at most `1` on
`A⁺`, so the elements of `A⁺` of value strictly below `1` at `x` form a prime ideal of `A⁺`: the
centre of `x` on `A⁺` (`Valuation.centerIdeal`). A continuous valuation is strictly below `1` at
every topologically nilpotent element, so this prime contains every element of `A⁺` that is
topologically nilpotent in `A`. It is therefore a point of the closed subset

```text
reductionSpectrum A⁺ = V(A°° ∩ A⁺) ⊆ Spec A⁺.
```

When `A⁺` is a ring of integral elements of a Huber ring, its elements topologically nilpotent in
`A` form the ideal `A°°` of `A⁺`, and `reductionSpectrum A⁺` is the image of the closed embedding
`Spec(A⁺/A°°) → Spec A⁺`. The resulting map

```text
sp : Spa(A, A⁺) → Spec(A⁺/A°°),   x ↦ {a ∈ A⁺ : |a(x)| < 1}
```

is the specialization map of Gleason, Definition 4.1. Over a Tate ring it is the map from the
generic fibre to the reduction that drives the specialization theory of v-sheaves. This file
constructs it with no hypothesis on `A` or `A⁺`, shows that the preimage of the basic open `D(a)`
is the locus `{x : |a(x)| = 1}`, and deduces continuity. Over a Huber ring that locus is a
quasi-compact rational subset, so the map is spectral. The construction is natural: it
intertwines the pullback of adic spectra along a continuous ring map with the pullback of prime
spectra along its restriction to the plus rings.

## Main definitions

* `TauCeti.ValuationSpectrum.reductionSpectrum`: the closed subset of `Spec A⁺` of primes
  containing every element of `A⁺` topologically nilpotent in `A`.
* `TauCeti.ValuationSpectrum.specialization`: the specialization map
  `Spa(A, A⁺) → reductionSpectrum A⁺`.

## Main results

* `TauCeti.ValuationSpectrum.mem_specialization_asIdeal_iff`: `a ∈ sp(x)` exactly when
  `|a(x)| < 1`.
* `TauCeti.ValuationSpectrum.specialization_preimage_basicOpen`: the preimage of `D(a)` is the
  locus `{x : |a(x)| = 1}`.
* `TauCeti.ValuationSpectrum.continuous_specialization`: the specialization map is continuous.
* `TauCeti.ValuationSpectrum.isSpectralMap_specialization`: over a Huber ring it is spectral.
* `TauCeti.ValuationSpectrum.specialization_spaComap`: naturality in the pair `(A, A⁺)`.

## References

* I. Gleason, *Specialization maps for Scholze's category of diamonds*, arXiv:2012.05483,
  Definition 4.1 and Proposition 4.2.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, Remark 7.4.12.
-/

public section

open Topology TopologicalSpace

namespace TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-! ### The space of the reduction -/

/-- The space of the reduction of `(A, A⁺)`: the primes of `A⁺` containing every element of
`A⁺` that is topologically nilpotent in `A`, as the zero locus in `Spec A⁺` of these elements.
When `A⁺` is a ring of integral elements of a Huber ring these elements form the ideal `A°°` of
`A⁺`, and this closed subset is the image of `Spec(A⁺/A°°)`. -/
def reductionSpectrum (Aplus : Subring A) : Set (PrimeSpectrum Aplus) :=
  PrimeSpectrum.zeroLocus {a : Aplus | IsTopologicallyNilpotent (a : A)}

/-- A prime of `A⁺` lies in the reduction spectrum exactly when it contains every element of `A⁺`
that is topologically nilpotent in `A`. -/
@[simp]
theorem mem_reductionSpectrum_iff {Aplus : Subring A} {𝔭 : PrimeSpectrum Aplus} :
    𝔭 ∈ reductionSpectrum Aplus ↔
      ∀ a : Aplus, IsTopologicallyNilpotent (a : A) → a ∈ 𝔭.asIdeal := by
  rw [reductionSpectrum, PrimeSpectrum.mem_zeroLocus]
  exact ⟨fun h a ha ↦ h ha, fun h a ha ↦ h a ha⟩

/-- The reduction spectrum is closed in `Spec A⁺`. -/
theorem isClosed_reductionSpectrum (Aplus : Subring A) : IsClosed (reductionSpectrum Aplus) :=
  PrimeSpectrum.isClosed_zeroLocus _

/-! ### The specialization map -/

/-- The **specialization map** `Spa(A, A⁺) → reductionSpectrum A⁺ ⊆ Spec A⁺`, sending `x` to
the prime `{a ∈ A⁺ : |a(x)| < 1}` of `A⁺` (Gleason, Definition 4.1): the centre of `x` on `A⁺`.
It lies in the reduction spectrum because a continuous valuation is strictly below `1` at every
topologically nilpotent element. For a ring of integral elements of a Huber ring the reduction
spectrum is `Spec(A⁺/A°°)`. -/
noncomputable def specialization {Aplus : Subring A} (x : spa Aplus) : reductionSpectrum Aplus :=
  ⟨⟨Valuation.centerIdeal Aplus (x : Spv A).valuation
      (fun a ↦ valuation_le_one_of_mem_spa x.property a.property),
      Valuation.isPrime_centerIdeal _⟩,
    mem_reductionSpectrum_iff.mpr fun _ ha ↦ Valuation.mem_centerIdeal.mpr <|
      Valuation.IsContinuous.lt_one_of_isTopologicallyNilpotent
        ((isContinuous_def _).mp ((mem_spa_iff _ _).mp x.property).1) ha⟩

/-- The prime ideal underlying `specialization x` is the centre of `x` on `A⁺`. -/
theorem specialization_asIdeal {Aplus : Subring A} (x : spa Aplus) :
    (specialization x : PrimeSpectrum Aplus).asIdeal =
      Valuation.centerIdeal Aplus (x : Spv A).valuation
        (fun a ↦ valuation_le_one_of_mem_spa x.property a.property) :=
  (rfl)

/-- **The specialization map is characterized by `a ∈ sp(x) ↔ |a(x)| < 1`** for `a ∈ A⁺`. -/
@[simp]
theorem mem_specialization_asIdeal_iff {Aplus : Subring A} (x : spa Aplus) (a : Aplus) :
    a ∈ (specialization x : PrimeSpectrum Aplus).asIdeal ↔ (x : Spv A).valuation a < 1 := by
  rw [specialization_asIdeal, Valuation.mem_centerIdeal,
    Algebra.algebraMap_ofSubsemiring_apply]

/-- Off its specialization, a point of `Spa(A, A⁺)` takes the value `1`. -/
theorem notMem_specialization_asIdeal_iff {Aplus : Subring A} (x : spa Aplus) (a : Aplus) :
    a ∉ (specialization x : PrimeSpectrum Aplus).asIdeal ↔ (x : Spv A).valuation a = 1 := by
  rw [specialization_asIdeal, Valuation.notMem_centerIdeal_iff,
    Algebra.algebraMap_ofSubsemiring_apply]

/-- **The preimage of `D(a)` under specialization is the locus `{x : |a(x)| = 1}`.** -/
theorem specialization_preimage_basicOpen {Aplus : Subring A} (a : Aplus) :
    specialization ⁻¹' (Subtype.val ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum Aplus))) =
      {x : spa Aplus | (x : Spv A).valuation a = 1} := by
  ext x
  rw [Set.mem_preimage, Set.mem_preimage, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
    Set.mem_ofPred_eq]
  exact notMem_specialization_asIdeal_iff x a

/-- The basic opens `D(a)` of `Spec A⁺`, traced on the reduction spectrum, form a basis of its
topology. -/
theorem isTopologicalBasis_reductionSpectrum (Aplus : Subring A) :
    IsTopologicalBasis (Set.range fun a : Aplus ↦
      (Subtype.val ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum Aplus)) :
        Set (reductionSpectrum Aplus))) := by
  have := (Topology.IsInducing.subtypeVal (t := reductionSpectrum Aplus)).isTopologicalBasis
    PrimeSpectrum.isTopologicalBasis_basic_opens
  rwa [← Set.range_comp] at this

/-- **The specialization map is continuous.** -/
theorem continuous_specialization (Aplus : Subring A) :
    Continuous (specialization (Aplus := Aplus)) := by
  refine (isTopologicalBasis_reductionSpectrum Aplus).continuous_iff.mpr ?_
  rintro _ ⟨a, rfl⟩
  rw [specialization_preimage_basicOpen, ← val_preimage_rationalSubset_singleton_one]
  exact isOpen_val_preimage_rationalSubset Aplus {1} a

/-- **The specialization map of a Huber ring is spectral**: it is continuous, and preimages of
quasi-compact opens of the reduction spectrum are quasi-compact. -/
theorem isSpectralMap_specialization [IsTopologicalRing A] [Huber.IsHuberRing A]
    (Aplus : Subring A) : IsSpectralMap (specialization (Aplus := Aplus)) := by
  refine isSpectralMap_of_isTopologicalBasis (isTopologicalBasis_reductionSpectrum Aplus)
    (continuous_specialization Aplus) ?_
  rintro _ ⟨a, rfl⟩
  rw [specialization_preimage_basicOpen, ← val_preimage_rationalSubset_singleton_one]
  exact isCompact_of_mem_spaRationalFamily
    (val_preimage_rationalSubset_mem_spaRationalFamily_of_isUnit_mem Aplus
      (Finset.mem_singleton_self 1) isUnit_one)

/-! ### Naturality -/

variable {B : Type*} [CommRing B] [TopologicalSpace B]

/-- **Naturality of specialization**: for a continuous ring map `φ : A → B` carrying `A⁺` into
`B⁺`, specializing the pullback of a point of `Spa(B, B⁺)` is pulling back its specialization
along `φ⁺ : A⁺ → B⁺`, that is, `sp_A ∘ Spa(φ) = Spec(φ⁺) ∘ sp_B`. -/
theorem specialization_spaComap {φ : A →+* B} (hφ : Continuous φ) {Aplus : Subring A}
    {Bplus : Subring B} (hplus : ∀ a ∈ Aplus, φ a ∈ Bplus) (x : spa Bplus) :
    (specialization (spaComap φ hφ Aplus Bplus hplus x) : PrimeSpectrum Aplus) =
      PrimeSpectrum.comap (φ.restrict Aplus Bplus hplus) (specialization x) := by
  ext a
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, mem_specialization_asIdeal_iff,
    mem_specialization_asIdeal_iff, spaComap_val, RingHom.coe_restrict_apply]
  exact (valuation_map_lt_one_iff rfl (a : A)).symm

end TauCeti.ValuationSpectrum
