/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.RingTheory.Huber.Pair
public import TauCeti.RingTheory.Valuation.Center
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Center
import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Center
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent
import TauCeti.Topology.Spectral.LocallyProConstructible

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

The map lifts specializations: if `sp(x)` specializes to `𝔭`, a vertical specialization of `x`
maps to `𝔭`. Its valuation ring is the composite of that of `x` with a valuation ring of the
residue field dominating `𝔭`, and it is again continuous because it refines `x`. A spectral map
of spectral spaces that lifts specializations is closed, so over a Huber ring the specialization
map is closed. Over a Tate ring it is also surjective, by the existence of points with prescribed
centre (`TauCeti.ValuationSpectrum.forall_isTopologicallyNilpotent_mem_iff_exists_mem_spa`).
Together these give the specialization theorem for Tate Huber pairs: the map is surjective,
spectral and closed (Gleason, Proposition 4.2).

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
* `TauCeti.ValuationSpectrum.specializingMap_specialization`: it lifts specializations.
* `TauCeti.ValuationSpectrum.isClosedMap_specialization`: over a Huber ring it is closed.
* `TauCeti.ValuationSpectrum.specialization_surjective`: over a Tate ring it is surjective.
* `TauCeti.ValuationSpectrum.exists_tate_specialization`: the specialization theorem for Tate
  Huber pairs, that the map characterized by `a ∈ sp(x) ↔ |a(x)| < 1` is surjective, spectral
  and closed.
* `TauCeti.ValuationSpectrum.specialization_spaComap`: naturality in the pair `(A, A⁺)`.

## References

* I. Gleason, *Specialization maps for Scholze's category of diamonds*, arXiv:2012.05483,
  Definition 4.1 and Proposition 4.2.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, Remark 7.4.12.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Chapter 4, for vertical
  specializations as composites of valuation rings.
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

/-- The specialization of `x` is `𝔭` exactly when `𝔭` consists of the elements of `A⁺` of value
strictly below `1` at `x`. -/
theorem specialization_eq_iff {Aplus : Subring A} {x : spa Aplus} {𝔭 : reductionSpectrum Aplus} :
    specialization x = 𝔭 ↔
      ∀ a : Aplus, (x : Spv A).valuation a < 1 ↔ a ∈ (𝔭 : PrimeSpectrum Aplus).asIdeal := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro rfl a
    exact (mem_specialization_asIdeal_iff x a).symm
  · exact Subtype.ext <| PrimeSpectrum.ext <| Ideal.ext fun a ↦
      (mem_specialization_asIdeal_iff x a).trans (h a)

/-! ### Closedness -/

/-- **Specialization lifts specializations.** If `sp(x)` specializes to `𝔭` in the reduction
spectrum, then `x` specializes in `Spa(A, A⁺)` to a point `x'` with `sp(x') = 𝔭`. This holds for
every subring `A⁺` of a commutative ring `A` with a topology in which addition is separately
continuous. -/
theorem specializingMap_specialization [SeparatelyContinuousAdd A] (Aplus : Subring A) :
    SpecializingMap (specialization (Aplus := Aplus)) := by
  intro x 𝔭 h
  have hle : (specialization x : PrimeSpectrum Aplus) ≤ 𝔭 :=
    (PrimeSpectrum.le_iff_specializes _ _).mpr (h.map continuous_subtypeVal)
  obtain ⟨x', hxx', hsupp, hle1, hlt⟩ := exists_specializes_supp_eq_and_valuation_lt_one_iff_mem
    Aplus.subtype (fun a ↦ valuation_le_one_of_mem_spa x.property a.property)
    (𝔭 : PrimeSpectrum Aplus).asIdeal fun a ha ↦ hle ((mem_specialization_asIdeal_iff x a).mpr ha)
  -- `x'` has the support of `x`, so it is continuous along with `x`
  have hcont : x'.IsContinuous :=
    ((mem_spa_iff _ _).mp x.property).1.of_specializes_of_supp_eq hxx' hsupp
  have hx' : x' ∈ spa Aplus := (mem_spa_iff _ _).mpr ⟨hcont, fun a ha ↦
    (valuation_le_iff x' a 1).mp (by rw [map_one]; exact hle1 ⟨a, ha⟩)⟩
  exact ⟨⟨x', hx'⟩, IsInducing.subtypeVal.specializes_iff.mp hxx', specialization_eq_iff.mpr hlt⟩

/-- **The specialization map of a Huber ring is closed**: it is a spectral map between spectral
spaces that lifts specializations. -/
theorem isClosedMap_specialization [IsTopologicalRing A] [Huber.IsHuberRing A]
    (Aplus : Subring A) : IsClosedMap (specialization (Aplus := Aplus)) := by
  have := (isClosed_reductionSpectrum Aplus).spectralSpace
  have hf := isSpectralMap_specialization Aplus
  exact (hf.isLocallySpectralMap.isClosedMap_iff_specializingMap
    SpectralSpace.isLocallySpectralSpace SpectralSpace.isLocallySpectralSpace hf).mpr
    (specializingMap_specialization Aplus)

/-! ### Tate pairs -/

/-- **The specialization map of a Tate Huber pair is surjective**: every prime of `A⁺`
containing `A°°` is `{a ∈ A⁺ : |a(x)| < 1}` for some point `x` of `Spa(A, A⁺)`. -/
theorem specialization_surjective [IsTopologicalRing A] [Huber.IsTateRing A]
    (P : Huber.Pair A) : Function.Surjective (specialization (Aplus := P.plus)) := by
  rintro ⟨𝔭, h𝔭⟩
  obtain ⟨x, hx, hx𝔭⟩ := (forall_isTopologicallyNilpotent_mem_iff_exists_mem_spa P 𝔭.asIdeal).mp
    (mem_reductionSpectrum_iff.mp h𝔭)
  exact ⟨⟨x, hx⟩, specialization_eq_iff.mpr hx𝔭⟩

/-- **The specialization theorem for Tate Huber pairs** (Gleason, Proposition 4.2). For a Tate
ring `A` with a ring of integral elements `A⁺`, some map `sp : Spa(A, A⁺) → Spec(A⁺ ⧸ A°°)`
satisfies `a ∈ sp(x) ↔ |a(x)| < 1` for every `a ∈ A⁺`, and it is surjective, spectral and closed.
The characterization determines the map, which is `TauCeti.ValuationSpectrum.specialization`. -/
theorem exists_tate_specialization [IsTopologicalRing A] [Huber.IsTateRing A]
    (P : Huber.Pair A) :
    ∃ sp : spa P.plus → reductionSpectrum P.plus,
      (∀ x a, a ∈ (sp x : PrimeSpectrum P.plus).asIdeal ↔ (x : Spv A).valuation (a : A) < 1) ∧
        Function.Surjective sp ∧ IsSpectralMap sp ∧ IsClosedMap sp :=
  ⟨specialization, mem_specialization_asIdeal_iff, specialization_surjective P,
    isSpectralMap_specialization P.plus, isClosedMap_specialization P.plus⟩

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
