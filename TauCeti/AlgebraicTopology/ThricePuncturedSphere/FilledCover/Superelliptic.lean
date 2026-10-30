/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.AnalyticBelyiPair
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Superelliptic

/-!
# The compact superelliptic curve `y ^ 4 = t (t - 1)` as an analytic Belyi pair

Over the thrice-punctured sphere `ℂ ∖ {0, 1}` the points of the affine curve `y ^ 4 = t (t - 1)`
form a connected four-sheeted cover `TauCeti.ThricePuncturedSphere.superellipticProj` of the
`t`-line. Filling its punctures gives the compact Riemann surface of the algebraic function
`y = (t ^ 2 - t) ^ (1/4)`, and the extension of `t` to it is a Belyi map. This file builds this
analytic Belyi pair `TauCeti.AnalyticBelyiPair.superelliptic` and computes its invariants from the
cover, that is from the equation:

* **Degree.** The Belyi map `β = t` has degree `4`, the number of fourth roots of `t (t - 1)`.
* **Ramification.** Over `0` and over `1` there is a single point, of local multiplicity `4`, and
  over `∞` there are two points, each of local multiplicity `2`. Indeed the components of the cover
  over the punctured discs about `0`, `1` and `∞` are the cycles of the monodromy permutations
  `σ0`, `σ1` and `σinf` of the cover, whose cycle data are `[4], [4], [2, 2]`, and these cycle
  lengths are the local multiplicities of `β`. All three of `0`, `1` and `∞` are branch values.
* **Genus.** The monodromy triple of the pair has one cycle over each of `0` and `1` and two over
  `∞`, so its Euler characteristic is `1 + 1 + 2 - 4 = 0` and its genus is `1`: this is the
  Riemann–Hurwitz count `2 g - 2 = 4 · (-2) + (3 + 3 + 1 + 1) = 0`.
* **Automorphisms.** The automorphisms `y ↦ ζ y` of the cover, for `ζ` a fourth root of unity,
  extend to the compact curve, and they are all the automorphisms of the pair: the automorphism
  group is cyclic of order `4`, equal to the degree, so the pair is regular.

Since an analytic Belyi pair is determined up to isomorphism by the isomorphism class of its
monodromy triple, the superelliptic curve is, up to isomorphism, the unique analytic Belyi pair
whose monodromy triple is the Euclidean torus triple `TauCeti.PermutationTriple.torusTriple`
(`TauCeti.AnalyticBelyiPair.nonempty_iso_superelliptic_iff`).

## Main declarations

* `TauCeti.ThricePuncturedSphere.superellipticConnectedCover`: the superelliptic curve over
  `ℂ ∖ {0, 1}` as a connected cover of degree `4`.
* `TauCeti.AnalyticBelyiPair.superelliptic`: its filled analytic Belyi pair, with Belyi map
  `t` (`TauCeti.AnalyticBelyiPair.β_superelliptic_incl`).
* `TauCeti.AnalyticBelyiPair.degree_β_superelliptic`: the Belyi map has degree `4`.
* `TauCeti.AnalyticBelyiPair.map_localMultiplicity_fiber_zero_superelliptic`,
  `map_localMultiplicity_fiber_one_superelliptic`, `map_localMultiplicity_fiber_inf_superelliptic`:
  the ramification partitions `[4]`, `[4]` and `[2, 2]`.
* `TauCeti.AnalyticBelyiPair.branchValues_β_superelliptic`: the branch values are `0`, `1`, `∞`.
* `TauCeti.AnalyticBelyiPair.genus_monodromyTriple_superelliptic`: genus one.
* `TauCeti.AnalyticBelyiPair.superellipticIsoMulEquiv`: the automorphism group of the pair is the
  group of fourth roots of unity, acting by `y ↦ ζ y`.
* `TauCeti.AnalyticBelyiPair.isRegular_monodromyTriple_superelliptic`: the pair is regular.
* `TauCeti.AnalyticBelyiPair.nonempty_iso_superelliptic_iff`: the superelliptic curve is the
  analytic Belyi pair of the torus triple.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §8 (the Riemann surface of an algebraic function, Theorem 8.9) and §17 (the Riemann–Hurwitz
  formula, Theorem 17.14).
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2.7 (filling the punctures of a finite cover) and §2.7 (deck groups and regular covers).
-/

public noncomputable section

namespace TauCeti

open Equiv.Perm Function Set ThricePuncturedSphere PermutationTriple RiemannSurface
  PunctureFilling

open scoped OnePoint

namespace ThricePuncturedSphere

/-- **The superelliptic curve `y ^ 4 = t (t - 1)` over `ℂ ∖ {0, 1}`, as a connected cover of
degree `4`.** Its total space is `TauCeti.ThricePuncturedSphere.superellipticCurve` and its
projection is `(t, y) ↦ t` (`TauCeti.ThricePuncturedSphere.superellipticConnectedCover_proj`). -/
-- The body is exposed so that the total space of the cover is the superelliptic curve by
-- definition.
@[expose]
def superellipticConnectedCover :
    ConnectedCover (X := TopCat.of ThricePuncturedSphere) basePt 4 where
  cover := ConnectedCoveringSpace.mk
    (TopCat.ofHom ⟨superellipticProj, isCoveringMap_superellipticProj.continuous⟩)
    isCoveringMap_superellipticProj
  nonempty_equiv_fin := by
    have h := natCard_superellipticProj_preimage_singleton basePt
    have : Finite (superellipticProj ⁻¹' {basePt}) := Nat.finite_of_card_ne_zero (by omega)
    exact ⟨@Finite.equivFinOfCardEq _ this _ h⟩

/-- The projection of the superelliptic cover is `(t, y) ↦ t`. -/
@[simp]
theorem superellipticConnectedCover_proj :
    ⇑superellipticConnectedCover.cover.proj = superellipticProj :=
  (rfl)

end ThricePuncturedSphere

namespace AnalyticBelyiPair

/-- **The compact superelliptic curve `y ^ 4 = t (t - 1)`, with Belyi map `β = t`.** It is the
filled analytic Belyi pair of the superelliptic cover of `ℂ ∖ {0, 1}`: the compact Riemann surface
of the algebraic function `(t ^ 2 - t) ^ (1/4)`, with the extension of `t`
(`TauCeti.AnalyticBelyiPair.β_superelliptic_incl`). -/
-- The body is exposed so that the points of the affine curve are points of its surface by
-- definition.
@[expose]
def superelliptic : AnalyticBelyiPair.{0} :=
  superellipticConnectedCover.toAnalyticBelyiPair

/-- **The Belyi map of the superelliptic curve is `t`** on the points `(t, y)` of the affine curve
over `ℂ ∖ {0, 1}`, which are points of the compact curve by the inclusion of the superelliptic cover
into its filled cover. -/
@[simp]
theorem β_superelliptic_incl (q : superellipticCurve) :
    superelliptic.β (incl (FilledCover.chart _) q) =
      (((q : ThricePuncturedSphere × ℂ).1 : ℂ) : OnePoint ℂ) := by
  simp only [superelliptic, ConnectedCover.coe_β_toAnalyticBelyiPair]
  -- `simp` cannot use `FilledCover.fillMap_incl` itself: `q` lives in `superellipticCurve`, not
  -- syntactically in the total space of the cover.
  exact (FilledCover.fillMap_incl superellipticProj q).trans (by simp)

/-- **The Belyi map of the superelliptic curve has degree `4`.** -/
@[simp]
theorem degree_β_superelliptic : degree superelliptic.β = 4 :=
  superellipticConnectedCover.degree_toAnalyticBelyiPair

/-- A numbering of the fibre of the superelliptic curve over `1/2` is by `Fin 4`. -/
private theorem eq_four_of_restrict_preimage_singleton_equiv {n : ℕ}
    (ν : superelliptic.restrict ⁻¹' {basePt} ≃ Fin n) : n = 4 :=
  (superelliptic.degree_β_eq_of_restrict_preimage_singleton_equiv ν).symm.trans
    degree_β_superelliptic

/-- The cycle data of the monodromy triple of the superelliptic curve are `[4], [4], [2, 2]`, for
any numbering of its fibre over `1/2`: these are the cycle data of the cover, computed from the
equation in `TauCeti.ThricePuncturedSphere.cycleData_monodromyTriple_superellipticProj`. -/
theorem cycleData_monodromyTriple_superelliptic {n : ℕ}
    (ν : superelliptic.restrict ⁻¹' {basePt} ≃ Fin n) :
    (superelliptic.isCoveringMap_restrict.monodromyTriple ν).cycleData = ({4}, {4}, {2, 2}) := by
  obtain rfl := eq_four_of_restrict_preimage_singleton_equiv ν
  obtain ⟨ν'⟩ := superellipticConnectedCover.nonempty_equiv_fin
  exact (cycleData_eq_of_equivalent (IsoClass.mk_eq_mk_iff.1
      (superellipticConnectedCover.isoClass_monodromyTriple_toAnalyticBelyiPair ν ν'))).trans
    (cycleData_monodromyTriple_superellipticProj ν')

/-- **The ramification of the superelliptic curve over `0` is `[4]`**: a single point, of local
multiplicity `4`. -/
theorem map_localMultiplicity_fiber_zero_superelliptic :
    (superelliptic.β.finite_fiber ((0 : ℂ) : OnePoint ℂ)).toFinset.val.map
      (localMultiplicity superelliptic.β) = {4} := by
  obtain ⟨ν⟩ := superelliptic.nonempty_restrict_preimage_singleton_equiv basePt
  rw [superelliptic.map_localMultiplicity_fiber_zero ν, fullCycleType_def, ← cycleData_σ0,
    cycleData_monodromyTriple_superelliptic]

/-- **The ramification of the superelliptic curve over `1` is `[4]`**: a single point, of local
multiplicity `4`. -/
theorem map_localMultiplicity_fiber_one_superelliptic :
    (superelliptic.β.finite_fiber ((1 : ℂ) : OnePoint ℂ)).toFinset.val.map
      (localMultiplicity superelliptic.β) = {4} := by
  obtain ⟨ν⟩ := superelliptic.nonempty_restrict_preimage_singleton_equiv basePt
  rw [superelliptic.map_localMultiplicity_fiber_one ν, fullCycleType_def, ← cycleData_σ1,
    cycleData_monodromyTriple_superelliptic]

/-- **The ramification of the superelliptic curve over `∞` is `[2, 2]`**: two points, each of
local multiplicity `2`. -/
theorem map_localMultiplicity_fiber_inf_superelliptic :
    (superelliptic.β.finite_fiber ∞).toFinset.val.map (localMultiplicity superelliptic.β) =
      {2, 2} := by
  obtain ⟨ν⟩ := superelliptic.nonempty_restrict_preimage_singleton_equiv basePt
  rw [superelliptic.map_localMultiplicity_fiber_inf ν, fullCycleType_def, ← cycleData_σinf,
    cycleData_monodromyTriple_superelliptic]

/-- **The branch values of the superelliptic curve are `0`, `1` and `∞`.** -/
@[simp]
theorem branchValues_β_superelliptic :
    superelliptic.β.branchValues =
      {((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), (∞ : OnePoint ℂ)} := by
  -- A value over which some point has local multiplicity greater than one is a branch value.
  have key {y : OnePoint ℂ} {e : ℕ} (he : 1 < e)
      (h : e ∈ (superelliptic.β.finite_fiber y).toFinset.val.map
        (localMultiplicity superelliptic.β)) : y ∈ superelliptic.β.branchValues := by
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 h
    exact (superelliptic.β.mem_branchValues_iff y).2 ⟨x, by simpa using hx, he⟩
  refine subset_antisymm superelliptic.branchValues_subset ?_
  rintro y (rfl | rfl | rfl)
  · exact key (e := 4) (by norm_num) (by simp [map_localMultiplicity_fiber_zero_superelliptic])
  · exact key (e := 4) (by norm_num) (by simp [map_localMultiplicity_fiber_one_superelliptic])
  · exact key (e := 2) (by norm_num) (by simp [map_localMultiplicity_fiber_inf_superelliptic])

/-- **The superelliptic curve has genus one**: the genus of its monodromy triple is `1`, for any
numbering of its fibre over `1/2`. The cycles of the triple are the points over `0`, `1` and `∞`,
with lengths the local multiplicities `[4], [4], [2, 2]`, so its Euler characteristic is
`1 + 1 + 2 - 4 = 0`. This is the Riemann–Hurwitz count `2 g - 2 = 4 · (-2) + (3 + 3 + 1 + 1)`. -/
theorem genus_monodromyTriple_superelliptic {n : ℕ}
    (ν : superelliptic.restrict ⁻¹' {basePt} ≃ Fin n) :
    (superelliptic.isCoveringMap_restrict.monodromyTriple ν).genus = 1 := by
  obtain rfl := eq_four_of_restrict_preimage_singleton_equiv ν
  rw [genus_def, eulerChar_eq_cycleCounts, cycleCounts_eq_card_cycleData,
    cycleData_monodromyTriple_superelliptic]
  norm_num

/-- **The automorphisms of the superelliptic curve are `y ↦ ζ y`** for the fourth roots of unity
`ζ`: these automorphisms of the cover over `ℂ ∖ {0, 1}` extend to the compact curve
(`TauCeti.AnalyticBelyiPair.superellipticIsoMulEquiv_apply_incl`), and they are all its
automorphisms over the Riemann sphere. -/
def superellipticIsoMulEquiv : rootsOfUnity 4 ℂ ≃* superelliptic.Iso superelliptic :=
  superellipticDeckMulEquiv.trans superellipticConnectedCover.deckMulEquivIso

/-- The automorphism `TauCeti.AnalyticBelyiPair.superellipticIsoMulEquiv ζ` of the superelliptic
curve is `(t, y) ↦ (t, ζ y)` on the affine curve over `ℂ ∖ {0, 1}`. -/
@[simp]
theorem superellipticIsoMulEquiv_apply_incl (ζ : rootsOfUnity 4 ℂ) (q : superellipticCurve) :
    superellipticIsoMulEquiv ζ (incl (FilledCover.chart _) q) =
      incl (FilledCover.chart _) (ζ • q) :=
  (superellipticConnectedCover.deckMulEquivIso_apply_incl _ q).trans
    (congrArg (incl _) (superellipticDeckMulEquiv_apply ζ q))

/-- The automorphism group of the superelliptic curve is cyclic. -/
instance isCyclic_iso_superelliptic : IsCyclic (superelliptic.Iso superelliptic) :=
  isCyclic_of_surjective superellipticIsoMulEquiv superellipticIsoMulEquiv.surjective

/-- **The superelliptic curve has four automorphisms**, as many as its degree. -/
theorem natCard_iso_superelliptic : Nat.card (superelliptic.Iso superelliptic) = 4 :=
  (Nat.card_congr superellipticConnectedCover.deckMulEquivIso.toEquiv).symm.trans
    natCard_deck_superellipticProj

/-- **The superelliptic curve is a regular Belyi pair**: its monodromy triple is regular, for any
numbering of its fibre over `1/2`. -/
theorem isRegular_monodromyTriple_superelliptic {n : ℕ}
    (ν : superelliptic.restrict ⁻¹' {basePt} ≃ Fin n) :
    (superelliptic.isCoveringMap_restrict.monodromyTriple ν).IsRegular := by
  obtain rfl := eq_four_of_restrict_preimage_singleton_equiv ν
  exact (isRegular_monodromyTriple_iff_natCard_iso ν).2 natCard_iso_superelliptic

/-- **The monodromy triple of the superelliptic curve is the torus triple**, up to relabelling,
for any numbering of its fibre over `1/2`. -/
theorem isoClass_monodromyTriple_superelliptic_eq_torusTriple
    (ν : superelliptic.restrict ⁻¹' {basePt} ≃ Fin 4) :
    IsoClass.mk (superelliptic.isCoveringMap_restrict.monodromyTriple ν) =
      IsoClass.mk torusTriple := by
  obtain ⟨ν'⟩ := superellipticConnectedCover.nonempty_equiv_fin
  exact (superellipticConnectedCover.isoClass_monodromyTriple_toAnalyticBelyiPair ν ν').trans
    (isoClass_monodromyTriple_superellipticProj_eq_torusTriple ν')

/-- **The superelliptic curve is the analytic Belyi pair of the torus triple**: an analytic Belyi
pair is isomorphic to the superelliptic curve exactly when its monodromy triple is isomorphic to
`TauCeti.PermutationTriple.torusTriple`, for any numbering of its fibre over `1/2`. -/
theorem nonempty_iso_superelliptic_iff {P : AnalyticBelyiPair.{0}}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin 4) :
    Nonempty (P.Iso superelliptic) ↔
      IsoClass.mk (P.isCoveringMap_restrict.monodromyTriple ν) = IsoClass.mk torusTriple := by
  obtain ⟨ν'⟩ := superelliptic.nonempty_restrict_preimage_singleton_equiv basePt
  let ν'' := ν'.trans (finCongr degree_β_superelliptic)
  rw [nonempty_iso_iff_isoClass_monodromyTriple_eq ν ν'',
    isoClass_monodromyTriple_superelliptic_eq_torusTriple]

end AnalyticBelyiPair

end TauCeti
