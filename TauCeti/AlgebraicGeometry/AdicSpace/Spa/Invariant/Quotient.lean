/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Action
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Invariant
public import TauCeti.RingTheory.Huber.Pair.Invariant
public import TauCeti.Topology.Algebra.GroupAction.Quotient

/-!
# The orbit space of the adic spectrum

Let a finite group `G` act on a Huber ring `A` by continuous ring automorphisms preserving `A⁺`
(`IsInvariantSubring G A⁺`), so that `G` acts on `Spa(A, A⁺)` by homeomorphisms. Let
`φ : (R, R⁺) → (A, A⁺)` be a morphism of Huber pairs with underlying map `algebraMap R A`, where
`G` acts by `R`-algebra automorphisms and every invariant of `A` comes from `R`. Then the fibres of
`Spa(A, A⁺) → Spa(R, R⁺)` are the `G`-orbits of `Spa(A, A⁺)`. If moreover `R` is a Tate ring,
`R → A` is injective and inducing and `R⁺ ⊇ A⁺ ∩ R`, this map is an open quotient map and
identifies the orbit space `Spa(A, A⁺) / G`, with the quotient topology, with `Spa(R, R⁺)`.

The main instance is the invariant Huber pair `(Aᴳ, A^{+G})` of a finite group acting on a Tate
ring (`TauCeti.Huber.invariantPair`), with `φ` its inclusion: restriction of valuations to the
invariants gives `Spa(A, A⁺) / G ≅ Spa(Aᴳ, A^{+G})`. Nothing is assumed about the order of `G`.

## Main definitions

* `TauCeti.Huber.Pair.Hom.orbitRelQuotientHomeomorphOfIsInvariant`: the homeomorphism
  `Spa(A, A⁺) / G ≃ₜ Spa(R, R⁺)` induced by `φ`.
* `TauCeti.Huber.invariantSpectrumHomeomorph`: the homeomorphism
  `Spa(A, A⁺) / G ≃ₜ Spa(Aᴳ, A^{+G})` induced by restricting valuations to the invariants.

## Main results

* `TauCeti.Huber.Pair.Hom.spaComap_eq_spaComap_iff_mem_orbit_of_isInvariant`: the fibres of
  `Spa(A, A⁺) → Spa(R, R⁺)` are the orbits of the action of `G` on `Spa(A, A⁺)`.
* `TauCeti.Huber.Pair.Hom.isOpenQuotientMap_spaComap_of_isInvariant`: over a Tate ring `R`, this
  map is surjective, open and a quotient map.
* `TauCeti.Huber.invariantPair.spaComap_inclusion_eq_spaComap_inclusion_iff`: the fibres of
  `Spa(A, A⁺) → Spa(Aᴳ, A^{+G})` are the `G`-orbits.
* `TauCeti.Huber.invariantPair.isOpenQuotientMap_spaComap_inclusion`: this map is surjective,
  open and a quotient map.
* `TauCeti.Huber.invariantPair.spaComap_inclusion_preimage_rationalSubset`: the preimage of the
  rational subset `U(T / s)` of `Spa(Aᴳ, A^{+G})` is the rational subset `U(T / s)` of
  `Spa(A, A⁺)`, which is `G`-stable
  (`TauCeti.Huber.invariantPair.smul_mem_preimage_rationalSubset_iff`).

## References

* D. Hansen, *Quotients of adic spaces by finite groups*, Math. Res. Lett. 28 (2021),
  Theorem 3.1.
-/

public section

namespace TauCeti.Huber.Pair.Hom

open ValuationSpectrum Topology

variable {R A : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CommRing A]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] [Algebra R A]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G A] [Algebra.IsInvariant R A G]
  [SMulCommClass G R A] [ContinuousConstSMul G A] {T : Pair A} [IsInvariantSubring G T.plus]

/-- **The fibres of `Spa(A, A⁺) → Spa(R, R⁺)` are the `G`-orbits** of the action of `G` on
`Spa(A, A⁺)`, for a finite group `G` acting on `A` by continuous `R`-algebra automorphisms
preserving `A⁺`, with every invariant coming from `R`, and a morphism of Huber pairs
`φ : (R, R⁺) → (A, A⁺)` with underlying map `algebraMap R A`. -/
theorem spaComap_eq_spaComap_iff_mem_orbit_of_isInvariant [IsHuberRing R] {S : Pair R}
    {φ : Hom S T} (hφ : φ.toRingHom = algebraMap R A) {x y : spa T.plus} :
    φ.spaComap x = φ.spaComap y ↔ x ∈ MulAction.orbit G y := by
  rw [eq_comm, spaComap_eq_spaComap_iff_of_isInvariant (G := G) hφ, MulAction.mem_orbit_iff]
  simp only [Subtype.ext_iff, val_smul, eq_comm]

variable [IsTateRing R] [FaithfulSMul R A] {S : Pair R}

/-- **The orbit space of `Spa(A, A⁺)` is the adic spectrum of the invariants.** For a finite group
`G` acting on `A` by continuous `R`-algebra automorphisms preserving `A⁺`, where `R → A` is an
injective inducing ring map from a Tate ring whose image contains every invariant, a morphism of
Huber pairs `φ : (R, R⁺) → (A, A⁺)` with underlying map `algebraMap R A` and `R⁺ ⊇ A⁺ ∩ R`
identifies the orbit space `Spa(A, A⁺) / G`, with the quotient topology, with `Spa(R, R⁺)`. -/
noncomputable def orbitRelQuotientHomeomorphOfIsInvariant {φ : Hom S T}
    (hφ : φ.toRingHom = algebraMap R A) (hι : IsInducing (algebraMap R A))
    (hS : T.plus.comap (algebraMap R A) ≤ S.plus) :
    MulAction.orbitRel.Quotient G (spa T.plus) ≃ₜ spa S.plus :=
  (isQuotientMap_spaComap_of_isInvariant (G := G) hφ hι hS
      fun g _ ha ↦ IsInvariantSubring.smul_mem g ha).orbitRelQuotientHomeomorph
    fun _ _ ↦ spaComap_eq_spaComap_iff_mem_orbit_of_isInvariant hφ

/-- The orbit of a point of `Spa(A, A⁺)` corresponds to its image in `Spa(R, R⁺)`. -/
@[simp]
theorem orbitRelQuotientHomeomorphOfIsInvariant_mk {φ : Hom S T}
    (hφ : φ.toRingHom = algebraMap R A) (hι : IsInducing (algebraMap R A))
    (hS : T.plus.comap (algebraMap R A) ≤ S.plus) (x : spa T.plus) :
    orbitRelQuotientHomeomorphOfIsInvariant (G := G) hφ hι hS (Quotient.mk _ x) = φ.spaComap x :=
  IsQuotientMap.orbitRelQuotientHomeomorph_mk _ _ x

/-- The image in `Spa(R, R⁺)` of a point of `Spa(A, A⁺)` corresponds to its orbit. -/
@[simp]
theorem orbitRelQuotientHomeomorphOfIsInvariant_symm_spaComap {φ : Hom S T}
    (hφ : φ.toRingHom = algebraMap R A) (hι : IsInducing (algebraMap R A))
    (hS : T.plus.comap (algebraMap R A) ≤ S.plus) (x : spa T.plus) :
    (orbitRelQuotientHomeomorphOfIsInvariant (G := G) hφ hι hS).symm (φ.spaComap x) =
      Quotient.mk _ x :=
  IsQuotientMap.orbitRelQuotientHomeomorph_symm_apply _ _ x

include G in
/-- **`Spa(A, A⁺) → Spa(R, R⁺)` is an open quotient map** for a finite group `G` acting on `A` by
continuous `R`-algebra automorphisms preserving `A⁺`, where `R → A` is an injective inducing ring
map from a Tate ring whose image contains every invariant, and a morphism of Huber pairs
`φ : (R, R⁺) → (A, A⁺)` with underlying map `algebraMap R A` and `R⁺ ⊇ A⁺ ∩ R`. -/
theorem isOpenQuotientMap_spaComap_of_isInvariant {φ : Hom S T}
    (hφ : φ.toRingHom = algebraMap R A) (hι : IsInducing (algebraMap R A))
    (hS : T.plus.comap (algebraMap R A) ≤ S.plus) : IsOpenQuotientMap φ.spaComap := by
  have h : φ.spaComap =
      orbitRelQuotientHomeomorphOfIsInvariant (G := G) hφ hι hS ∘ Quotient.mk _ :=
    funext fun x ↦ (orbitRelQuotientHomeomorphOfIsInvariant_mk hφ hι hS x).symm
  rw [h]
  exact (orbitRelQuotientHomeomorphOfIsInvariant hφ hι hS).isOpenQuotientMap.comp
    MulAction.isOpenQuotientMap_quotientMk

end TauCeti.Huber.Pair.Hom

namespace TauCeti.Huber

open ValuationSpectrum Topology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G A] [ContinuousConstSMul G A]
  (P : Pair A)

namespace invariantPair

omit [IsTopologicalRing A] [IsTateRing A] [Finite G] [ContinuousConstSMul G A] in
/-- The algebra map of the fixed subring, which underlies `invariantPair.inclusion`, is
inducing. -/
theorem isInducing_algebraMap : IsInducing (algebraMap (FixedPoints.subring A G) A) := by
  rw [Algebra.algebraMap_ofSubring, Subring.coe_subtype]
  exact IsInducing.subtypeVal

/-- The plus ring `A^{+G}` of the invariant pair is the preimage of `A⁺` under the algebra map of
the fixed subring. -/
theorem comap_algebraMap_plus :
    P.plus.comap (algebraMap (FixedPoints.subring A G) A) = (invariantPair G P).plus := by
  rw [invariantPair_plus, Algebra.algebraMap_ofSubring]

variable [IsInvariantSubring G P.plus]

/-- Restriction to the invariants is constant on `G`-orbits of `Spa(A, A⁺)`. -/
@[simp]
theorem spaComap_inclusion_smul (g : G) (x : spa P.plus) :
    (inclusion G P).spaComap (g • x) = (inclusion G P).spaComap x :=
  (inclusion G P).spaComap_smul_eq_spaComap
    (fun g r ↦ by rw [toRingHom_inclusion]; exact smul_algebraMap g r) g x

/-- **The fibres of `Spa(A, A⁺) → Spa(Aᴳ, A^{+G})` are the `G`-orbits.** Two points of
`Spa(A, A⁺)` have the same restriction to the invariants exactly when they are conjugate under
`G`. No hypothesis is made on the order of `G`. -/
theorem spaComap_inclusion_eq_spaComap_inclusion_iff {x y : spa P.plus} :
    (inclusion G P).spaComap x = (inclusion G P).spaComap y ↔ x ∈ MulAction.orbit G y :=
  Pair.Hom.spaComap_eq_spaComap_iff_mem_orbit_of_isInvariant (toRingHom_inclusion P)

end invariantPair

variable [IsInvariantSubring G P.plus]

/-- **The orbit space of the adic spectrum** (Hansen, Theorem 3.1). For a finite group `G` acting
by continuous ring automorphisms on a Tate ring `A` and preserving `A⁺`, restriction of
valuations to the invariants identifies the orbit space `Spa(A, A⁺) / G`, with the quotient
topology, with `Spa(Aᴳ, A^{+G})`. No hypothesis is made on the order of `G`, and none on
completeness or sheafiness of `(A, A⁺)`. -/
noncomputable def invariantSpectrumHomeomorph :
    MulAction.orbitRel.Quotient G (spa P.plus) ≃ₜ spa (invariantPair G P).plus :=
  Pair.Hom.orbitRelQuotientHomeomorphOfIsInvariant (G := G) (invariantPair.toRingHom_inclusion P)
    (invariantPair.isInducing_algebraMap G) (invariantPair.comap_algebraMap_plus G P).le

/-- The orbit of a point of `Spa(A, A⁺)` corresponds to its restriction to the invariants. -/
@[simp]
theorem invariantSpectrumHomeomorph_mk (x : spa P.plus) :
    invariantSpectrumHomeomorph G P (Quotient.mk _ x) =
      (invariantPair.inclusion G P).spaComap x :=
  Pair.Hom.orbitRelQuotientHomeomorphOfIsInvariant_mk _ _ _ x

/-- The restriction of a point of `Spa(A, A⁺)` to the invariants corresponds to its orbit. -/
@[simp]
theorem invariantSpectrumHomeomorph_symm_spaComap (x : spa P.plus) :
    (invariantSpectrumHomeomorph G P).symm ((invariantPair.inclusion G P).spaComap x) =
      Quotient.mk _ x :=
  Pair.Hom.orbitRelQuotientHomeomorphOfIsInvariant_symm_spaComap _ _ _ x

namespace invariantPair

/-- **Restriction to the invariants is an open quotient map** `Spa(A, A⁺) → Spa(Aᴳ, A^{+G})`. -/
theorem isOpenQuotientMap_spaComap_inclusion :
    IsOpenQuotientMap (inclusion G P).spaComap :=
  Pair.Hom.isOpenQuotientMap_spaComap_of_isInvariant (G := G) (toRingHom_inclusion P)
    (isInducing_algebraMap G) (comap_algebraMap_plus G P).le

omit [IsInvariantSubring G P.plus] in
/-- **Rational subsets of `Spa(Aᴳ, A^{+G})` pull back to rational subsets.** The preimage of the
rational subset `U(T / s)` of `Spa(Aᴳ, A^{+G})`, with `T` and `s` invariant, is the rational subset
of `Spa(A, A⁺)` cut out by the same elements of `A`. -/
theorem spaComap_inclusion_preimage_rationalSubset (T : Finset (FixedPoints.subring A G))
    (s : FixedPoints.subring A G) :
    (inclusion G P).spaComap ⁻¹' (Subtype.val ⁻¹' rationalSubset (invariantPair G P).plus T s) =
      Subtype.val ⁻¹' rationalSubset P.plus (T.map (Function.Embedding.subtype _)) s := by
  classical
  rw [Pair.Hom.spaComap_preimage_rationalSubset, Finset.map_eq_image, toRingHom_inclusion,
    Algebra.algebraMap_ofSubring, Function.Embedding.coe_subtype, Subring.coe_subtype]

/-- **The rational subset cut out by invariant elements is `G`-stable.** For `T` and `s` in `Aᴳ`,
a point `x` of `Spa(A, A⁺)` lies in the rational subset `U(T / s)` exactly when `g • x` does. -/
theorem smul_mem_preimage_rationalSubset_iff (T : Finset (FixedPoints.subring A G))
    (s : FixedPoints.subring A G) (g : G) (x : spa P.plus) :
    g • x ∈ Subtype.val ⁻¹' rationalSubset P.plus (T.map (Function.Embedding.subtype _)) s ↔
      x ∈ Subtype.val ⁻¹' rationalSubset P.plus (T.map (Function.Embedding.subtype _)) s := by
  simp only [← spaComap_inclusion_preimage_rationalSubset, Set.mem_preimage,
    spaComap_inclusion_smul]

end invariantPair

end TauCeti.Huber
