/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tilde.Hartogs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Regular.Flat
import TauCeti.RingTheory.CohenMacaulay.Normal
import TauCeti.RingTheory.Depth.WeaklyRegular
import TauCeti.RingTheory.IntegralClosure.GoingDown
import TauCeti.RingTheory.KrullDimension.Fiber

/-!
# Sections of `Spec B` over the preimage of a punctured spectrum

Let `A` be a local ring with maximal ideal `𝔪`, let `B` be an `A`-algebra, and let `W` be an open
subset of `Spec B` containing every prime of `B` not lying over `𝔪`; for instance the preimage of
the punctured spectrum `Spec A ∖ {𝔪}`. This file gives conditions under which restriction
`Γ(Spec B, 𝒪) → Γ(W, 𝒪)` is bijective, so that `B` is recovered from the sections over `W`:

* `B` is flat over a Noetherian `A` of depth at least two. A weakly regular pair in `𝔪` stays
  weakly regular on `B`, and its basic opens lie in `W`.
* `B` is integral over `A`, Noetherian, and of depth at least two at each maximal ideal. The
  primes outside `W` lie over `𝔪`, hence are maximal, so this is the algebraic Hartogs principle
  for `Spec B`.
* `A` is a Noetherian integrally closed local domain of dimension at least two and `B` is a finite
  torsion-free `A`-algebra whose localizations at maximal ideals are normal domains. By going
  down, these localizations have the dimension of `A`, so they have depth at least two by the
  `(S₂)` property of normal local domains.

These results are the section-recovery input used by Stacks, Lemmas 58.20.2 (0BLK) and 58.20.3
(0BM9); no statement here mentions étale covers. When `A` has depth at least two, the first case
recovers a finite étale `A`-algebra as the ring of sections of its spectrum over the preimage of
the punctured spectrum, as needed for 0BLK. The last case is the corresponding step of a corrected
form of 0BM9: Stacks omits the hypothesis that `B` is torsion-free over `A`, without which 0BM9 is
false (for `B = A × A/𝔪` the sections over the preimage of the punctured spectrum are just `A`),
so the theorem assumes `Module.IsTorsionFree A B`.

## Main results

* `TauCeti.AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_flat`: the flat case.
* `TauCeti.AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_isIntegral`: the integral case,
  an affine form of Stacks, Lemma 58.20.1 (0BM8).
* `TauCeti.AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_isIntegrallyClosed`: the finite
  normal case.

## References

* [Stacks Project, Lemma 58.20.1](https://stacks.math.columbia.edu/tag/0BM8).
* [Stacks Project, Lemma 58.20.2](https://stacks.math.columbia.edu/tag/0BLK).
* [Stacks Project, Lemma 58.20.3](https://stacks.math.columbia.edu/tag/0BM9).
* [Stacks Project, Lemma 31.5.11](https://stacks.math.columbia.edu/tag/0E9I).
-/

public section

universe u

open CategoryTheory Opposite TopologicalSpace IsLocalRing RingTheory.Sequence
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.StructureSheaf

namespace TauCeti.AlgebraicGeometry.Spec

variable {A : Type*} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Let `B` be a flat algebra over a Noetherian local ring `A` of depth at least two, and `W` an
open subset of `Spec B` containing every prime not lying over the maximal ideal of `A`. Then
restriction of sections of `Spec B` from `Spec B` to `W` is bijective. -/
theorem presheaf_map_leTop_bijective_of_flat [IsLocalRing A] [IsNoetherianRing A]
    [Module.Flat A B] (hdepth : 2 ≤ depth (ModuleCat.of A A)) (W : (Spec (.of B)).Opens)
    (hW : ∀ p : PrimeSpectrum B, p.asIdeal.under A ≠ maximalIdeal A → p ∈ W) :
    Function.Bijective ((Spec (.of B)).presheaf.map W.leTop.op) := by
  -- The maximal ideal of `A` contains a weakly regular pair.
  obtain ⟨rs, hlen, hmem, hab⟩ :=
    exists_isWeaklyRegular_of_le_depth (ModuleCat.of A A) (n := 2) hdepth
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  -- It stays weakly regular on `B`, and its basic opens lie in `W`.
  have hD (r : A) (hr : r ∈ maximalIdeal A) :
      PrimeSpectrum.basicOpen (algebraMap A B r) ≤ W := fun p hp ↦
    hW p fun h ↦ hp <| Ideal.mem_comap.mp <| by rwa [← Ideal.under_def, h]
  rw [Spec.presheaf_map_leTop_bijective_iff]
  exact StructureSheaf.toOpenₗ_bijective_of_isWeaklyRegular hab.of_flat (hD a (hmem a (by simp)))
    (hD b (hmem b (by simp)))

/-- Let `B` be a Noetherian integral algebra over a local ring `A` such that every localization of
`B` at a maximal ideal has depth at least two, and `W` an open subset of `Spec B` containing every
prime not lying over the maximal ideal of `A`. Then restriction of sections of `Spec B` from
`Spec B` to `W` is bijective. -/
@[stacks 0BM8 "affine form"]
theorem presheaf_map_leTop_bijective_of_isIntegral [IsLocalRing A] [Algebra.IsIntegral A B]
    [IsNoetherianRing B]
    (hdepth : ∀ (𝔮 : Ideal B) [𝔮.IsMaximal],
      2 ≤ depth (ModuleCat.of (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔮)))
    (W : (Spec (.of B)).Opens)
    (hW : ∀ p : PrimeSpectrum B, p.asIdeal.under A ≠ maximalIdeal A → p ∈ W) :
    Function.Bijective ((Spec (.of B)).presheaf.map W.leTop.op) := by
  rw [Spec.presheaf_map_leTop_bijective_iff]
  refine StructureSheaf.toOpenₗ_bijective_of_two_le_depth W fun p hp ↦ ?_
  -- A prime outside `W` lies over the maximal ideal of `A`, so it is maximal.
  have : p.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) _
    (by rw [not_not.mp (mt (hW p) hp)]; infer_instance)
  let e : LocalizedModule p.asIdeal.primeCompl B ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal :=
    (IsLocalizedModule.iso p.asIdeal.primeCompl
      (Algebra.linearMap B (Localization.AtPrime p.asIdeal))).extendScalarsOfIsLocalization
      p.asIdeal.primeCompl _
  rw [depth_eq_of_linearEquiv e]
  exact hdepth p.asIdeal

/-- Let `A` be a Noetherian integrally closed local domain of dimension at least two and `B` a
finite torsion-free `A`-algebra whose localizations at maximal ideals are normal domains. If `W`
is an open subset of `Spec B` containing every prime not lying over the maximal ideal of `A`, then
restriction of sections of `Spec B` from `Spec B` to `W` is bijective. -/
theorem presheaf_map_leTop_bijective_of_isIntegrallyClosed [IsLocalRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A] [Module.Finite A B] [Module.IsTorsionFree A B]
    (hdim : 2 ≤ ringKrullDim A)
    (hnormal : ∀ (𝔮 : Ideal B) [𝔮.IsMaximal],
      IsDomain (Localization.AtPrime 𝔮) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔮))
    (W : (Spec (.of B)).Opens)
    (hW : ∀ p : PrimeSpectrum B, p.asIdeal.under A ≠ maximalIdeal A → p ∈ W) :
    Function.Bijective ((Spec (.of B)).presheaf.map W.leTop.op) := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  refine presheaf_map_leTop_bijective_of_isIntegral (fun 𝔮 _ ↦ ?_) W hW
  obtain ⟨_, _⟩ := hnormal 𝔮
  -- By going down, `B_𝔮` has the dimension of `A`.
  refine two_le_depth_of_isIntegrallyClosed ?_
  rw [Ideal.ringKrullDim_localization_atPrime_eq_height_under A,
    eq_maximalIdeal (inferInstance : (𝔮.under A).IsMaximal),
    maximalIdeal_height_eq_ringKrullDim]
  exact hdim

end TauCeti.AlgebraicGeometry.Spec
