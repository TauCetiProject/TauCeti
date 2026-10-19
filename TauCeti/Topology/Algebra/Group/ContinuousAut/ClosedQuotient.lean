/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.ClosedSubgroup
public import TauCeti.Topology.Algebra.Group.ContinuousAut.Congruence
public import TauCeti.Topology.Algebra.Group.ContinuousAut.ConjClasses

/-!
# Continuous automorphisms of characteristic quotients

A continuous automorphism `φ` of a topological group `G` that maps a normal subgroup `N` onto
itself induces a continuous automorphism `x N ↦ φ x N` of the quotient topological group `G ⧸ N`.
For a topologically characteristic `N` this is a homomorphism
`ContinuousAut.mapClosedQuotient : ContinuousAut G →* ContinuousAut (G ⧸ N)`. It carries the inner
automorphism of `g` to the inner automorphism of `g N`, so it descends to the continuous outer
automorphism groups, `ContinuousOut.mapClosedQuotient : ContinuousOut G →* ContinuousOut (G ⧸ N)`.
Both maps are compatible with the actions on conjugacy classes, and both are continuous for the
congruence topologies: the preimage in `G` of a topologically characteristic open normal subgroup
of `G ⧸ N` is a topologically characteristic open normal subgroup of `G`.

The case of interest is a closed `N`, where the quotient `G ⧸ N` is again Hausdorff, and profinite
when `G` is; this is what the name records. The construction itself does not use closedness, so
no closedness hypothesis is imposed. The abstract automorphism underlying
`ContinuousAut.mapClosedQuotient hN φ` is the congruence coordinate `ContinuousAut.mapQuotient hN φ`
(`ContinuousAut.toMulAut_mapClosedQuotient`).

## Main definitions

* `TauCeti.ContinuousAut.mapClosedQuotient`: the continuous automorphism of `G ⧸ N` induced by a
  continuous automorphism of `G`, for a topologically characteristic normal subgroup `N`.
* `TauCeti.ContinuousOut.mapClosedQuotient`: the induced map on continuous outer automorphism
  groups.

## Main results

* `TauCeti.ContinuousAut.mapClosedQuotient_mk`, `TauCeti.ContinuousOut.mapClosedQuotient_mk`: the
  maps are computed on classes.
* `TauCeti.ContinuousAut.mapClosedQuotient_conj`: inner automorphisms go to inner automorphisms.
* `TauCeti.IsTopCharacteristic.comap_mk`: the preimage of a topologically characteristic subgroup
  of `G ⧸ N` is topologically characteristic in `G`.
* `TauCeti.ContinuousAut.continuous_mapClosedQuotient`,
  `TauCeti.ContinuousOut.continuous_mapClosedQuotient`: continuity for the congruence topologies.
* `TauCeti.ContinuousAut.mapClosedQuotient_smul_conjClasses_map`,
  `TauCeti.ContinuousOut.mapClosedQuotient_smul_conjClasses_map`: compatibility with the actions
  on conjugacy classes.

## References

* L. Ribes, P. Zalesskii, *Profinite Groups*, 2nd ed., §4.4.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] {N : Subgroup G}

namespace ContinuousAut

section Basic

variable (hN : IsTopCharacteristic G N) [N.Normal]

/-- The continuous automorphism `x N ↦ φ x N` of the quotient `G ⧸ N` induced by a continuous
automorphism `φ` of `G`, for a topologically characteristic normal subgroup `N`. -/
def mapClosedQuotient : ContinuousAut G →* ContinuousAut (G ⧸ N) where
  toFun φ := φ.quotientCongr N N (isTopCharacteristic_iff_map_eq.mp hN φ)
  map_one' := ContinuousMulEquiv.ext fun q ↦ by
    induction q using QuotientGroup.induction_on with
    | H x => simp only [ContinuousMulEquiv.quotientCongr_mk, one_apply]
  map_mul' φ ψ := ContinuousMulEquiv.ext fun q ↦ by
    induction q using QuotientGroup.induction_on with
    | H x => simp only [ContinuousMulEquiv.quotientCongr_mk, mul_apply]

/-- The induced automorphism of `G ⧸ N` sends the class of `x` to the class of `φ x`. -/
@[simp]
theorem mapClosedQuotient_mk (φ : ContinuousAut G) (x : G) :
    mapClosedQuotient hN φ (x : G ⧸ N) = (φ x : G ⧸ N) :=
  ContinuousMulEquiv.quotientCongr_mk φ N N (isTopCharacteristic_iff_map_eq.mp hN φ) x

/-- The abstract automorphism underlying `mapClosedQuotient hN φ` is the congruence coordinate
`mapQuotient hN φ`. -/
@[simp]
theorem toMulAut_mapClosedQuotient (φ : ContinuousAut G) :
    toMulAut (mapClosedQuotient hN φ) = mapQuotient hN φ :=
  MulEquiv.ext fun q ↦ by
    induction q using QuotientGroup.induction_on with
    | H x => simp

end Basic

/-- The induced automorphism of the quotient carries the inner automorphism of `g` to the inner
automorphism of the class of `g`. -/
@[simp]
theorem mapClosedQuotient_conj [IsTopologicalGroup G] (hN : IsTopCharacteristic G N) [N.Normal]
    (g : G) : mapClosedQuotient hN (conj g) = conj (g : G ⧸ N) :=
  ContinuousMulEquiv.ext fun q ↦ by
    induction q using QuotientGroup.induction_on with
    | H x => simp

/-- The induced automorphism of the quotient is compatible with the actions on conjugacy classes:
it sends the image of a class `c` of `G` to the image of `φ • c`. -/
theorem mapClosedQuotient_smul_conjClasses_map (hN : IsTopCharacteristic G N) [N.Normal]
    (φ : ContinuousAut G) (c : ConjClasses G) :
    mapClosedQuotient hN φ • ConjClasses.map (QuotientGroup.mk' N) c =
      ConjClasses.map (QuotientGroup.mk' N) (φ • c) := by
  obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
  simp [ConjClasses.map_mk]

end ContinuousAut

/-- The preimage in `G` of a topologically characteristic subgroup of a characteristic quotient
`G ⧸ N` is topologically characteristic. -/
theorem IsTopCharacteristic.comap_mk (hN : IsTopCharacteristic G N) [N.Normal]
    {M : Subgroup (G ⧸ N)} (hM : IsTopCharacteristic (G ⧸ N) M) :
    IsTopCharacteristic G (M.comap (QuotientGroup.mk' N)) := by
  refine isTopCharacteristic_iff_le_comap.mpr fun φ x hx ↦ ?_
  have := isTopCharacteristic_iff_le_comap.mp hM (ContinuousAut.mapClosedQuotient hN φ) hx
  simpa using this

namespace ContinuousAut

variable (hN : IsTopCharacteristic G N) [N.Normal]

/-- The induced map `ContinuousAut G →* ContinuousAut (G ⧸ N)` is continuous for the congruence
topologies: each coordinate of the target factors through a coordinate of the source. -/
theorem continuous_mapClosedQuotient : Continuous (mapClosedQuotient hN) := by
  refine continuous_iff_forall_continuous_mapQuotient.mpr fun ⟨M, hM⟩ ↦ ?_
  let _ : TopologicalSpace (MulAut ((G ⧸ N) ⧸ (M : Subgroup (G ⧸ N)))) := ⊥
  have := discreteTopology_bot (MulAut ((G ⧸ N) ⧸ (M : Subgroup (G ⧸ N))))
  -- The preimage of `M` in `G` is an open normal subgroup, topologically characteristic.
  obtain ⟨M', hmem⟩ : ∃ M' : OpenNormalSubgroup G,
      ∀ y : G, y ∈ (M' : Subgroup G) ↔ (y : G ⧸ N) ∈ (M : Subgroup (G ⧸ N)) :=
    ⟨{ toOpenSubgroup := OpenSubgroup.comap (QuotientGroup.mk' N) QuotientGroup.continuous_mk
          M.toOpenSubgroup
       isNormal' := Subgroup.Normal.comap M.isNormal' _ },
      fun _ ↦ OpenSubgroup.mem_comap (hf := QuotientGroup.continuous_mk)⟩
  have hM' : IsTopCharacteristic G (M' : Subgroup G) := by
    rw [show (M' : Subgroup G) = (M : Subgroup (G ⧸ N)).comap (QuotientGroup.mk' N) from
      Subgroup.ext hmem]
    exact hN.comap_mk hM
  refine ((mapQuotient hM).comp (mapClosedQuotient hN)).continuous_iff_isOpen_ker.mpr <|
    Subgroup.isOpen_mono (fun φ hφ ↦ ?_) (isOpen_ker_mapQuotient M' hM')
  rw [MonoidHom.mem_ker, ← map_one (mapQuotient hM'), mapQuotient_eq_iff] at hφ
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← map_one (mapQuotient hM), mapQuotient_eq_iff]
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hx := hφ x
  rw [one_apply, QuotientGroup.eq] at hx
  rw [mapClosedQuotient_mk, one_apply, QuotientGroup.eq, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul]
  exact (hmem _).mp hx

end ContinuousAut

namespace ContinuousOut

variable [IsTopologicalGroup G] (hN : IsTopCharacteristic G N) [N.Normal]

/-- The map `ContinuousOut G →* ContinuousOut (G ⧸ N)` induced by
`ContinuousAut.mapClosedQuotient`, which carries inner automorphisms to inner automorphisms. -/
def mapClosedQuotient : ContinuousOut G →* ContinuousOut (G ⧸ N) :=
  QuotientGroup.map _ _ (ContinuousAut.mapClosedQuotient hN) <| by
    rintro _ ⟨g, rfl⟩
    exact ⟨g, (ContinuousAut.mapClosedQuotient_conj hN g).symm⟩

/-- The induced map on outer automorphism groups is computed on representatives. -/
@[simp]
theorem mapClosedQuotient_mk (φ : ContinuousAut G) :
    mapClosedQuotient hN (φ : ContinuousOut G) =
      (ContinuousAut.mapClosedQuotient hN φ : ContinuousOut (G ⧸ N)) :=
  QuotientGroup.map_mk _ _ _ _ φ

/-- The induced map on outer automorphism groups is continuous for the quotients of the
congruence topologies. -/
theorem continuous_mapClosedQuotient : Continuous (mapClosedQuotient hN) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr <|
    (QuotientGroup.continuous_mk.comp (ContinuousAut.continuous_mapClosedQuotient hN)).congr
      fun φ ↦ (mapClosedQuotient_mk hN φ).symm

/-- The induced map on outer automorphism groups is compatible with the actions on conjugacy
classes: it sends the image of a class `c` of `G` to the image of `φ • c`. -/
theorem mapClosedQuotient_smul_conjClasses_map (φ : ContinuousOut G) (c : ConjClasses G) :
    mapClosedQuotient hN φ • ConjClasses.map (QuotientGroup.mk' N) c =
      ConjClasses.map (QuotientGroup.mk' N) (φ • c) := by
  induction φ using QuotientGroup.induction_on with
  | H φ =>
    rw [mapClosedQuotient_mk, mk_smul_conjClasses, mk_smul_conjClasses,
      ContinuousAut.mapClosedQuotient_smul_conjClasses_map]

end ContinuousOut

end TauCeti
