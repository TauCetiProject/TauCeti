/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Generalizing
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Invariant
public import TauCeti.RingTheory.Huber.Pair.Invariant
public import TauCeti.Topology.Algebra.GroupAction.Quotient
import Mathlib.Algebra.Polynomial.Lifts
import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.LyingOver
import TauCeti.RingTheory.Valuation.RootMonic

/-!
# The adic spectrum over the invariants of a finite group

Let a finite group `G` act on a topological ring `A` by continuous ring automorphisms preserving a
subring `A⁺`, and let `R → A` be an inducing ring map whose image contains every invariant
(`Algebra.IsInvariant R A G`), for instance the inclusion of the fixed subring `Aᴳ` with the
subspace topology. Write `R⁺` for the preimage of `A⁺` in `R`, so `A^{+G} = A⁺ ∩ Aᴳ` for the fixed
subring. This file shows that `Spa(A, A⁺)` is the full preimage of `Spa(R, R⁺)` in `Spv A`
(`TauCeti.ValuationSpectrum.mem_spa_iff_comap_mem_spa_comap_of_isInvariant`): continuity can be
tested on `R` (`TauCeti.ValuationSpectrum.isContinuous_comap_algebraMap_iff_of_isInvariant`), and
every element of `A⁺` is a root of its orbit polynomial, whose coefficients lie in `A⁺` and are
invariant, so lie in the image of `R⁺`.

For a morphism of Huber pairs `(R, R⁺) → (A, A⁺)` with underlying map `algebraMap R A`, the map
`Spa(A, A⁺) → Spa(R, R⁺)` is therefore surjective when `R → A` is injective. When moreover `G`
acts by `R`-algebra automorphisms (`SMulCommClass G R A`), its fibres are the `G`-orbits for
`(g • y)(a) = y(g⁻¹ • a)`. When `R` is a Tate ring, a morphism of Huber pairs out of `(R, R⁺)`
that is surjective on adic spectra induces a quotient map
(`TauCeti.Huber.Pair.Hom.isQuotientMap_spaComap_of_isTateRing`), so if `G` acts by `R`-algebra
automorphisms, `Spa(R, R⁺)` is the quotient of `Spa(A, A⁺)` by `G` as a topological space.
Nothing is assumed about the order of `G`, which may be divisible by the residue characteristic.

If `G` preserves `A⁺` (`IsInvariantSubring G A⁺`), it acts on `Spa(A, A⁺)` by homeomorphisms. For
the invariant Huber pair `(Aᴳ, A^{+G})` of a finite group acting on a Tate ring, this identifies
the orbit space `Spa(A, A⁺) / G`, with the quotient topology, with `Spa(Aᴳ, A^{+G})`.

## Main definitions

* `TauCeti.Huber.invariantSpectrumHomeomorph`: the homeomorphism
  `Spa(A, A⁺) / G ≃ₜ Spa(Aᴳ, A^{+G})` induced by restricting valuations to the invariants.

## Main results

* `TauCeti.ValuationSpectrum.mem_spa_iff_comap_mem_spa_comap_of_isInvariant`: `Spa(A, A⁺)` is the
  preimage of `Spa(R, R⁺)` in `Spv A`.
* `TauCeti.Huber.Pair.Hom.spaComap_eq_spaComap_iff_of_isInvariant`: the fibres of
  `Spa(A, A⁺) → Spa(R, R⁺)` are the `G`-orbits when `G` acts by `R`-algebra automorphisms.
* `TauCeti.Huber.Pair.Hom.surjective_spaComap_of_isInvariant`: the map is surjective.
* `TauCeti.Huber.Pair.Hom.isQuotientMap_spaComap_of_isInvariant`: over a Tate ring `R`, it is a
  quotient map.
* `TauCeti.ValuationSpectrum.smul_mem_spa_iff`: `G` preserves `Spa(A, A⁺)` when it preserves `A⁺`.
* `TauCeti.Huber.invariantPair.spaComap_inclusion_eq_spaComap_inclusion_iff`: the fibres of
  `Spa(A, A⁺) → Spa(Aᴳ, A^{+G})` are the `G`-orbits.
* `TauCeti.Huber.invariantPair.isOpenQuotientMap_spaComap_inclusion`: this map is surjective,
  open and a quotient map.
* `TauCeti.Huber.invariantPair.spaComap_inclusion_preimage_rationalSubset`: the preimage of the
  rational subset `U(T / s)` of `Spa(Aᴳ, A^{+G})` is the rational subset `U(T / s)` of
  `Spa(A, A⁺)`.

## References

* D. Hansen, *Quotients of adic spaces by finite groups*, Math. Res. Lett. 28 (2021),
  Theorem 3.1.
-/

public section

open Polynomial

namespace TauCeti.ValuationSpectrum

section Action

variable {G A : Type*} [Group G] [CommRing A] [TopologicalSpace A] [MulSemiringAction G A]
  [ContinuousConstSMul G A] {Aplus : Subring A} [IsInvariantSubring G Aplus]

/-- A group acting on `A` by continuous ring automorphisms preserving `A⁺` preserves
`Spa(A, A⁺)`. -/
theorem smul_mem_spa_iff (g : G) {v : Spv A} : g • v ∈ spa Aplus ↔ v ∈ spa Aplus := by
  have key (g : G) {v : Spv A} (hv : v ∈ spa Aplus) : g • v ∈ spa Aplus :=
    comap_mem_spa (continuous_const_smul g⁻¹) (fun _ ha ↦ IsInvariantSubring.smul_mem g⁻¹ ha) hv
  exact ⟨fun h ↦ inv_smul_smul g v ▸ key g⁻¹ h, key g⟩

/-- The action of `G` on `Spa(A, A⁺)` for an action on `A` by continuous ring automorphisms
preserving `A⁺`: `(g • v)(a) = v(g⁻¹ • a)`. -/
instance : SMul G (spa Aplus) :=
  ⟨fun g v ↦ ⟨g • v.val, (smul_mem_spa_iff g).mpr v.property⟩⟩

/-- The underlying point of `g • v` in `Spv A`. -/
@[simp]
theorem coe_smul (g : G) (v : spa Aplus) : ((g • v : spa Aplus) : Spv A) = g • (v : Spv A) :=
  (rfl)

/-- The action of `G` on `Spa(A, A⁺)` is the restriction of its action on `Spv A`. -/
instance : MulAction G (spa Aplus) :=
  Subtype.coe_injective.mulAction _ coe_smul

/-- `G` acts on `Spa(A, A⁺)` by homeomorphisms. -/
instance : ContinuousConstSMul G (spa Aplus) :=
  ⟨fun g ↦ ((continuous_const_smul g).comp continuous_subtypeVal).subtype_mk _⟩

end Action

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (G : Type*) [Group G] [Finite G]
  [MulSemiringAction G A] [Algebra.IsInvariant R A G] [TopologicalSpace R] [TopologicalSpace A]
  [IsTopologicalRing A] [ContinuousConstSMul G A]

include G in
/-- **`Spa(A, A⁺)` is the preimage of the adic spectrum of the invariants.** If a finite group `G`
acts on a topological ring `A` by continuous ring automorphisms preserving a subring `A⁺`, and
`R → A` is an inducing ring map whose image contains every invariant, then a point of `Spv A` lies
in `Spa(A, A⁺)` exactly when its restriction lies in `Spa(R, R⁺)`, where `R⁺` is the preimage of
`A⁺`. -/
theorem mem_spa_iff_comap_mem_spa_comap_of_isInvariant (hι : Topology.IsInducing (algebraMap R A))
    {Aplus : Subring A} (hplus : ∀ g : G, ∀ a ∈ Aplus, g • a ∈ Aplus) {y : Spv A} :
    y ∈ spa Aplus ↔ comap (algebraMap R A) y ∈ spa (Aplus.comap (algebraMap R A)) := by
  classical
  refine ⟨comap_mem_spa hι.continuous fun _ ha ↦ ha, fun hy ↦ ?_⟩
  refine (mem_spa_iff _ _).mpr ⟨(isContinuous_comap_algebraMap_iff_of_isInvariant G hι).mp
    ((mem_spa_iff _ _).mp hy).1, fun a ha ↦ ?_⟩
  cases nonempty_fintype G
  -- the orbit polynomial of `a` has coefficients in `A⁺`, which are invariant, so come from `R⁺`
  have hlift : MulSemiringAction.charpoly G a ∈ lifts Aplus.subtype :=
    mem_lifts _ |>.mpr ⟨∏ g : G, (X - C (⟨g • a, hplus g a ha⟩ : Aplus)), by
      simp [Polynomial.map_prod, MulSemiringAction.charpoly_eq]⟩
  have hcoeff (l : ℕ) : y.valuation ((MulSemiringAction.charpoly G a).coeff l) ≤ 1 := by
    obtain ⟨⟨b, hb⟩, hbl⟩ := (lifts_iff_coeff_lifts _).mp hlift l
    obtain ⟨r, hr⟩ := Algebra.IsInvariant.isInvariant (A := R) (G := G) _
      (MulSemiringAction.smul_coeff_charpoly a l)
    rw [← hr, valuation_map_le_one_iff rfl]
    refine valuation_le_one_of_mem_spa hy ?_
    rw [Subring.mem_comap, hr, ← hbl]
    exact hb
  have hle : y.valuation a ≤ 1 := y.valuation.le_one_of_root_monic
    (MulSemiringAction.monic_charpoly G a) (fun l _ ↦ hcoeff l)
    (MulSemiringAction.eval_charpoly G a)
  rwa [← valuation_le_iff, map_one]

end TauCeti.ValuationSpectrum

namespace TauCeti.Huber.Pair.Hom

open ValuationSpectrum

variable {R A : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CommRing A]
  [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] [Algebra R A]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G A] [Algebra.IsInvariant R A G]

section Huber

variable [IsHuberRing R] {S : Pair R} {T : Pair A}

/-- **The fibres of `Spa(A, A⁺) → Spa(R, R⁺)` are the `G`-orbits.** For a finite group `G` acting
on `A` by `R`-algebra automorphisms with every invariant coming from `R`, and a morphism of Huber
pairs `φ : (R, R⁺) → (A, A⁺)` with underlying map `algebraMap R A`, two points `x` and `y` of
`Spa(A, A⁺)` have the same image in `Spa(R, R⁺)` exactly when `y = g • x` for some `g ∈ G`,
where `(g • x)(a) = x(g⁻¹ • a)`. -/
theorem spaComap_eq_spaComap_iff_of_isInvariant [SMulCommClass G R A] {φ : Hom S T}
    (hφ : φ.toRingHom = algebraMap R A) {x y : spa T.plus} :
    φ.spaComap x = φ.spaComap y ↔
      ∃ g : G, (y : Spv A) = comap (MulSemiringAction.toRingHom G A g⁻¹) x := by
  rw [← comap_algebraMap_eq_comap_algebraMap_iff_of_isInvariant (R := R), Subtype.ext_iff,
    spaComap_val, spaComap_val, hφ]

variable [ContinuousConstSMul G A]

include G in
/-- **`Spa(A, A⁺)` surjects onto the adic spectrum of the invariants.** Let a finite group `G`
act on `A` by continuous ring automorphisms preserving `A⁺`, and let `R → A` be an injective
inducing ring map whose image contains every invariant. A morphism of Huber pairs
`φ : (R, R⁺) → (A, A⁺)` with underlying map `algebraMap R A` and `R⁺ ⊇ A⁺ ∩ R` (hence
`R⁺ = A⁺ ∩ R`) induces a surjection `Spa(A, A⁺) → Spa(R, R⁺)`. -/
theorem surjective_spaComap_of_isInvariant [FaithfulSMul R A] {φ : Hom S T}
    (hφ : φ.toRingHom = algebraMap R A) (hι : Topology.IsInducing (algebraMap R A))
    (hS : T.plus.comap (algebraMap R A) ≤ S.plus) (hT : ∀ g : G, ∀ a ∈ T.plus, g • a ∈ T.plus) :
    Function.Surjective φ.spaComap := by
  intro x
  have := Algebra.IsInvariant.isIntegral R A G
  obtain ⟨y, hy⟩ := comap_algebraMap_surjective_of_isIntegral (A := R) (B := A) x.val
  have hmem : y ∈ spa T.plus := (mem_spa_iff_comap_mem_spa_comap_of_isInvariant G hι hT).mpr
    (spa_antitone hS (hy ▸ x.property))
  exact ⟨⟨y, hmem⟩, Subtype.ext <| by rw [spaComap_val, hφ, hy]⟩

end Huber

variable [IsTateRing R] [ContinuousConstSMul G A] {S : Pair R} {T : Pair A}

include G in
/-- **The adic spectrum of the invariants is the quotient of `Spa(A, A⁺)`.** Let a finite group
`G` act on `A` by continuous ring automorphisms preserving `A⁺`, and let `R → A` be an injective
inducing ring map from a Tate ring whose image contains every invariant. A morphism of Huber pairs
`φ : (R, R⁺) → (A, A⁺)` with underlying map `algebraMap R A` and `R⁺ ⊇ A⁺ ∩ R` induces a quotient
map `Spa(A, A⁺) → Spa(R, R⁺)`. When `G` moreover acts by `R`-algebra automorphisms, its fibres
are the `G`-orbits (`spaComap_eq_spaComap_iff_of_isInvariant`). -/
theorem isQuotientMap_spaComap_of_isInvariant [FaithfulSMul R A] {φ : Hom S T}
    (hφ : φ.toRingHom = algebraMap R A) (hι : Topology.IsInducing (algebraMap R A))
    (hS : T.plus.comap (algebraMap R A) ≤ S.plus) (hT : ∀ g : G, ∀ a ∈ T.plus, g • a ∈ T.plus) :
    Topology.IsQuotientMap φ.spaComap :=
  φ.isQuotientMap_spaComap_of_isTateRing (surjective_spaComap_of_isInvariant hφ hι hS hT)

end TauCeti.Huber.Pair.Hom

namespace TauCeti.Huber

open ValuationSpectrum Topology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G A] [ContinuousConstSMul G A]
  (P : Pair A) [IsInvariantSubring G P.plus]

namespace invariantPair

/-- Restriction to the invariants is constant on `G`-orbits of `Spa(A, A⁺)`. -/
@[simp]
theorem spaComap_inclusion_smul (g : G) (x : spa P.plus) :
    (inclusion G P).spaComap (g • x) = (inclusion G P).spaComap x :=
  Subtype.ext <| by
    rw [Pair.Hom.spaComap_val, Pair.Hom.spaComap_val, coe_smul, toRingHom_inclusion]
    exact comap_algebraMap_smul (R := FixedPoints.subring A G) g x.val

/-- **The fibres of `Spa(A, A⁺) → Spa(Aᴳ, A^{+G})` are the `G`-orbits.** Two points of
`Spa(A, A⁺)` have the same restriction to the invariants exactly when they are conjugate under
`G`. No hypothesis is made on the order of `G`. -/
theorem spaComap_inclusion_eq_spaComap_inclusion_iff {x y : spa P.plus} :
    (inclusion G P).spaComap x = (inclusion G P).spaComap y ↔ x ∈ MulAction.orbit G y := by
  rw [eq_comm, Pair.Hom.spaComap_eq_spaComap_iff_of_isInvariant (G := G)
    (R := FixedPoints.subring A G) (toRingHom_inclusion (G := G) P), MulAction.mem_orbit_iff]
  simp only [Subtype.ext_iff, coe_smul, smul_def, eq_comm]

end invariantPair

/-- **The orbit space of the adic spectrum** (Hansen, Theorem 3.1). For a finite group `G` acting
by continuous ring automorphisms on a Tate ring `A` and preserving `A⁺`, restriction of
valuations to the invariants identifies the orbit space `Spa(A, A⁺) / G`, with the quotient
topology, with `Spa(Aᴳ, A^{+G})`. No hypothesis is made on the order of `G`, and none on
completeness or sheafiness of `(A, A⁺)`. -/
noncomputable def invariantSpectrumHomeomorph :
    MulAction.orbitRel.Quotient G (spa P.plus) ≃ₜ spa (invariantPair G P).plus :=
  (Pair.Hom.isQuotientMap_spaComap_of_isInvariant (G := G)
      (invariantPair.toRingHom_inclusion (G := G) P) IsInducing.subtypeVal
      (invariantPair_plus (G := G) P).ge
      fun g _ ha ↦ IsInvariantSubring.smul_mem g ha).orbitRelQuotientHomeomorph
    fun _ _ ↦ invariantPair.spaComap_inclusion_eq_spaComap_inclusion_iff G P

/-- The orbit of a point of `Spa(A, A⁺)` corresponds to its restriction to the invariants. -/
@[simp]
theorem invariantSpectrumHomeomorph_mk (x : spa P.plus) :
    invariantSpectrumHomeomorph G P (Quotient.mk _ x) =
      (invariantPair.inclusion G P).spaComap x := by
  rw [invariantSpectrumHomeomorph, IsQuotientMap.orbitRelQuotientHomeomorph_mk]

/-- The restriction of a point of `Spa(A, A⁺)` to the invariants corresponds to its orbit. -/
@[simp]
theorem invariantSpectrumHomeomorph_symm_spaComap (x : spa P.plus) :
    (invariantSpectrumHomeomorph G P).symm ((invariantPair.inclusion G P).spaComap x) =
      Quotient.mk _ x :=
  (invariantSpectrumHomeomorph G P).symm_apply_eq.2 (invariantSpectrumHomeomorph_mk G P x).symm

namespace invariantPair

/-- **Restriction to the invariants is an open quotient map** `Spa(A, A⁺) → Spa(Aᴳ, A^{+G})`. -/
theorem isOpenQuotientMap_spaComap_inclusion :
    IsOpenQuotientMap (inclusion G P).spaComap := by
  have h : (inclusion G P).spaComap = invariantSpectrumHomeomorph G P ∘ Quotient.mk _ :=
    funext fun x ↦ (invariantSpectrumHomeomorph_mk G P x).symm
  rw [h]
  exact (invariantSpectrumHomeomorph G P).isOpenQuotientMap.comp
    MulAction.isOpenQuotientMap_quotientMk

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
    Function.Embedding.coe_subtype, Subring.coe_subtype]

end invariantPair

end TauCeti.Huber
