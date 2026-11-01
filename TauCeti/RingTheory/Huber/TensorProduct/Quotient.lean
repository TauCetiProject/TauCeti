/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Map

import Mathlib.LinearAlgebra.TensorProduct.RightExactness


/-!
# Open quotients of completed tensor products

Let `A → B`, `A → C`, `A → B'` and `A → C'` be adic homomorphisms of Huber rings, and let
`φ : B → B'` and `ψ : C → C'` be ring homomorphisms compatible with the structure maps that
are open quotient maps (continuous, open and surjective). This file shows that
`φ ⊗ ψ : B ⊗[A] C → B' ⊗[A] C'` is an open quotient map for the two tensor topologies, and that so
is the induced map `B ⊗̂_A C → B' ⊗̂_A C'` of separated completed tensor rings.

The images of compatible pairs of definition along `φ` and `ψ` are again compatible pairs of
definition (`TauCeti.Huber.TensorDatum.map`), and `φ ⊗ ψ` carries the neighbourhood basis of
zero of the source datum onto that of the image datum
(`TauCeti.Huber.TensorDatum.idealImage_map`). Openness follows, and completion preserves open
surjections of first-countable nonarchimedean groups.

This is the right-exactness input for presentations of completed tensor products: completed
base change of an open quotient of completed weighted restricted power series is an open
quotient of the base-changed power series.

## Main definitions

* `TauCeti.Huber.TensorDatum.map`: the image of a tensor datum along open quotient maps of the
  two factors.

## Main results

* `TauCeti.Huber.TensorDatum.ringOfDefinition_map`, `TauCeti.Huber.TensorDatum.idealImage_map`:
  the ring of definition and the neighbourhoods of zero of the image datum are the images of
  those of the original datum.
* `TauCeti.Huber.isOpenQuotientMap_mapRingHom_tensorTopology`: `φ ⊗ ψ` is an open quotient map
  for the tensor topologies.
* `TauCeti.Huber.CompletedTensor.isOpenQuotientMap_map`: the induced map of completed tensor
  rings is an open quotient map.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, proof of Proposition 3.7.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.2, proof of Proposition 1.2.2.
-/

public section

open TensorProduct Algebra.TensorProduct Topology Filter

namespace TauCeti.Huber

variable {A B C B' C' : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing B'] [CommRing C']
  [Algebra A B] [Algebra A C] [Algebra A B'] [Algebra A C']
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace B']
  [TopologicalSpace C'] [IsTopologicalRing B'] [IsTopologicalRing C']
  {φ : B →+* B'} {ψ : C →+* C'}
  (hφA : φ.comp (algebraMap A B) = algebraMap A B')
  (hψA : ψ.comp (algebraMap A C) = algebraMap A C')

namespace TensorDatum

/-- **The image of a tensor datum along open quotient maps.** If `φ : B → B'` and `ψ : C → C'`
are open quotient maps compatible with the structure maps, the images of the pairs of definition
of `B` and `C` (`TauCeti.Huber.PairOfDefinition.map`), together with the same pair of definition
of `A`, are compatible pairs of definition for `B'` and `C'`. -/
def map (D : TensorDatum A B C) (hφ : IsOpenQuotientMap φ) (hψ : IsOpenQuotientMap ψ) :
    TensorDatum A B' C' where
  base := D.base
  left := D.left.map φ hφ
  right := D.right.map ψ hψ
  algebraMap_mem_left a ha := by
    rw [PairOfDefinition.map_ringOfDefinition, ← hφA]
    exact Subring.mem_map.mpr ⟨_, D.algebraMap_mem_left a ha, rfl⟩
  algebraMap_mem_right a ha := by
    rw [PairOfDefinition.map_ringOfDefinition, ← hψA]
    exact Subring.mem_map.mpr ⟨_, D.algebraMap_mem_right a ha, rfl⟩
  map_idealOfDefinition_left := by
    rw [PairOfDefinition.map_idealOfDefinition, ← D.map_idealOfDefinition_left, Ideal.map_map]
    congr 1
    exact RingHom.ext fun a ↦ Subtype.ext (by simp [← hφA])
  map_idealOfDefinition_right := by
    rw [PairOfDefinition.map_idealOfDefinition, ← D.map_idealOfDefinition_right, Ideal.map_map]
    congr 1
    exact RingHom.ext fun a ↦ Subtype.ext (by simp [← hψA])

variable (D : TensorDatum A B C) (hφ : IsOpenQuotientMap φ) (hψ : IsOpenQuotientMap ψ)

/-- The image datum keeps the pair of definition of `A`. -/
@[simp] theorem map_base : (D.map hφA hψA hφ hψ).base = D.base := (rfl)

/-- The pair of definition of `B'` in the image datum is the image of that of `B`. -/
@[simp] theorem map_left : (D.map hφA hψA hφ hψ).left = D.left.map φ hφ := (rfl)

/-- The pair of definition of `C'` in the image datum is the image of that of `C`. -/
@[simp] theorem map_right : (D.map hφA hψA hφ hψ).right = D.right.map ψ hψ := (rfl)

/-- The ring of definition of the image datum is the image of the ring of definition under
`φ ⊗ ψ`. -/
theorem ringOfDefinition_map :
    (D.map hφA hψA hφ hψ).ringOfDefinition =
      D.ringOfDefinition.map (mapRingHom (RingHom.id A) φ ψ hφA hψA) := by
  simp only [ringOfDefinition_eq_sup, map_left, map_right, PairOfDefinition.map_ringOfDefinition,
    Subring.map_sup, Subring.map_map, mapRingHom_comp_includeLeftRingHom,
    mapRingHom_comp_includeRight]

/-- **The neighbourhoods of zero of the image datum are the images of those of the original
datum**: `φ ⊗ ψ` carries the image of `Jⁿ` onto the image of `J'ⁿ`, for the ideals of definition
`J` and `J'` of the two data. -/
theorem idealImage_map (n : ℕ) :
    (D.map hφA hψA hφ hψ).idealImage n =
      (D.idealImage n).map (mapRingHom (RingHom.id A) φ ψ hφA hψA).toAddMonoidHom := by
  set D' := D.map hφA hψA hφ hψ
  set f : B ⊗[A] C →+* B' ⊗[A] C' := mapRingHom (RingHom.id A) φ ψ hφA hψA
  have hF : D'.ringOfDefinition = D.ringOfDefinition.map f := D.ringOfDefinition_map hφA hψA hφ hψ
  have hbase (a : A) : f (algebraMap A (B ⊗[A] C) a) = algebraMap A (B' ⊗[A] C') a := by
    simp [f, ← hφA]
  -- the restriction `g : F → F'` of `f` is surjective and carries `Jⁿ` onto `J'ⁿ`
  let g : D.ringOfDefinition →+* D'.ringOfDefinition :=
    f.restrict _ _ fun x hx ↦ hF ▸ Subring.mem_map.mpr ⟨x, hx, rfl⟩
  have hg : Function.Surjective g := by
    rintro ⟨_, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subring.mem_map.mp (hF ▸ hy)
    exact ⟨⟨x, hx⟩, rfl⟩
  have hgbase (a : D.base.ringOfDefinition) :
      g (D.toRingOfDefinition a) = D'.toRingOfDefinition a :=
    Subtype.ext <| (RingHom.coe_restrict_apply ..).trans <|
      (congrArg f (coe_toRingOfDefinition D a)).trans <|
        (hbase a).trans (coe_toRingOfDefinition D' a).symm
  have hJ : D'.idealOfDefinition ^ n = (D.idealOfDefinition ^ n).map g := by
    rw [Ideal.map_pow, idealOfDefinition_def, idealOfDefinition_def, Ideal.map_map]
    congr 2
    exact RingHom.ext fun a ↦ (hgbase a).symm
  ext x
  simp only [mem_idealImage, hJ, Ideal.mem_map_iff_of_surjective g hg, AddSubgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩

end TensorDatum

variable [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  [IsAdicHom (algebraMap A B')] [IsAdicHom (algebraMap A C')]

/-- **Tensor products of open quotient maps are open quotient maps.** If `φ : B → B'` and
`ψ : C → C'` are open quotient maps compatible with adic structure maps, then
`φ ⊗ ψ : B ⊗[A] C → B' ⊗[A] C'` is an open quotient map for the tensor topologies. -/
theorem isOpenQuotientMap_mapRingHom_tensorTopology (hφ : IsOpenQuotientMap φ)
    (hψ : IsOpenQuotientMap ψ) :
    letI := tensorTopology A B C
    letI := tensorTopology A B' C'
    IsOpenQuotientMap (mapRingHom (RingHom.id A) φ ψ hφA hψA) := by
  let _ := tensorTopology A B C
  let _ := tensorTopology A B' C'
  have _ := isTopologicalRing_tensorTopology A B C
  have _ := isTopologicalRing_tensorTopology A B' C'
  have _ := isHuberRing_tensorTopology A B' C'
  obtain ⟨D⟩ := TensorDatum.nonempty A B C
  set f : B ⊗[A] C →+* B' ⊗[A] C' := mapRingHom (RingHom.id A) φ ψ hφA hψA
  refine ⟨?_, ?_, ?_⟩
  · -- `f` is Mathlib's `Algebra.TensorProduct.map` of the corresponding algebra maps
    let φ' : B →ₐ[A] B' := { φ with commutes' := RingHom.congr_fun hφA }
    let ψ' : C →ₐ[A] C' := { ψ with commutes' := RingHom.congr_fun hψA }
    have hf : f = (Algebra.TensorProduct.map φ' ψ').toRingHom :=
      Algebra.TensorProduct.ringHom_ext (by ext; simp [f, φ']) (by ext; simp [f, ψ'])
    rw [hf]
    exact Algebra.TensorProduct.map_surjective φ' ψ' hφ.surjective hψ.surjective
  · refine (RingHom.continuous_tensorTopology_iff f).mpr ⟨?_, ?_⟩
    · rw [mapRingHom_comp_includeLeftRingHom]
      exact (isAdicHom_includeLeft_tensorTopology A B' C').continuous.comp hφ.continuous
    · rw [AlgHom.toRingHom_eq_coe, mapRingHom_comp_includeRight]
      exact (isAdicHom_includeRight_tensorTopology A B' C').continuous.comp hψ.continuous
  · -- `f` carries the neighbourhood basis of `D` onto that of the image datum
    rw [IsTopologicalAddGroup.isOpenMap_iff_nhds_zero]
    intro s hs
    obtain ⟨n, -, hn⟩ := (hasBasis_tensorTopology A B C D).mem_iff.mp hs
    refine mem_of_superset ((hasBasis_tensorTopology A B' C' (D.map hφA hψA hφ hψ)).mem_of_mem
      (i := n) trivial) ?_
    rw [D.idealImage_map hφA hψA hφ hψ n, AddSubgroup.coe_map]
    exact (Set.image_mono hn).trans (Set.image_preimage_subset _ _)

namespace CompletedTensor

/-- **Completed tensor products of open quotient maps are open quotient maps.** If
`φ : B → B'` and `ψ : C → C'` are open quotient maps compatible with adic structure maps, the
induced map `B ⊗̂_A C → B' ⊗̂_A C'` of separated completed tensor rings is an open quotient map. -/
theorem isOpenQuotientMap_map (hφ : IsOpenQuotientMap φ) (hψ : IsOpenQuotientMap ψ) :
    IsOpenQuotientMap (map (RingHom.id A) φ ψ hφA hψA hφ.continuous hψ.continuous) :=
  isOpenQuotientMap_of_comp_toCompletion _ (continuous_map ..) _
    (isOpenQuotientMap_mapRingHom_tensorTopology hφA hψA hφ hψ) (map_comp_toCompletion ..)

end CompletedTensor

end TauCeti.Huber
