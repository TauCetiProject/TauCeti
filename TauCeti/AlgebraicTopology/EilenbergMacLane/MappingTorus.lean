/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.Geometry.Manifold.Instances.KleinBottle
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map
public import TauCeti.Topology.MappingTorus.Basic
import TauCeti.Analysis.Complex.Circle.Basic
import TauCeti.AlgebraicTopology.EilenbergMacLane.HomotopyEquiv
import TauCeti.AlgebraicTopology.UniversalCover.Circle.EilenbergMacLane
import TauCeti.Topology.Homotopy.HomotopyEquiv
import TauCeti.Topology.Homotopy.HomotopyGroup.Covering
import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence
import TauCeti.Topology.MappingTorus.Covering

/-!
# Aspherical mapping tori and the Klein bottle

Let `φ` be a self-homeomorphism of a space `F`. Its mapping torus `MappingTorus φ` is covered by
the cylinder `F × ℝ` (`TauCeti.MappingTorus.isAddQuotientCoveringMap_coverMap`), and the zero
section `x ↦ (x, 0)` of the cylinder is a homotopy equivalence
(`ContinuousMap.HomotopyEquiv.prodZeroSection`). A covering map is bijective on the homotopy groups
of dimension at least two, so the inclusion `x ↦ [x, 0]` of the fibre is too
(`TauCeti.MappingTorus.bijective_homotopyGroupMap_incl`). Hence the mapping torus is aspherical
exactly when it is path connected and every homotopy group of `F` of dimension at least two
vanishes, at every base point of `F` (`TauCeti.MappingTorus.isAspherical_iff`). The base points of
all path components of `F` enter because the mapping torus can be path connected when `F` is not:
the swap of two points has the circle as its mapping torus. In particular the mapping torus of a
self-homeomorphism of an aspherical space is aspherical (`TauCeti.IsAspherical.mappingTorus`), and
so is the smooth mapping torus of a diffeomorphism of an aspherical manifold
(`TauCeti.IsAspherical.smoothMappingTorus`), which is homeomorphic to a topological one.

The Klein bottle is the smooth mapping torus of complex conjugation of the circle
(`TauCeti.KleinBottle`). Since the circle is aspherical, so is the Klein bottle
(`TauCeti.KleinBottle.isAspherical`): all its homotopy groups of dimension at least two vanish, and
every power map, squaring in particular, is surjective on them
(`TauCeti.KleinBottle.surjective_pow_homotopyGroup`). This is the example showing that the
hypothesis of Theorems 5.15 and C of Barraud, Damian, Humilière and Oancea on closed
characteristics in cotangent bundles of non-orientable manifolds, that squaring is not surjective
on some higher homotopy group, is needed: it fails for the Klein bottle, and so does their
conclusion, since the flat unit cotangent bundle of the Klein bottle carries no contractible closed
characteristic (a fact not proved here). For real projective space `RPⁿ` with `n ≥ 2`
the hypothesis holds (`TauCeti.RealProjectiveSpace.not_surjective_pow_homotopyGroup`).

## Main results

* `TauCeti.MappingTorus.bijective_homotopyGroupMap_incl`: the inclusion of the fibre of a mapping
  torus is bijective on `π_(n + 2)`.
* `TauCeti.MappingTorus.isAspherical_iff`: asphericity of a mapping torus.
* `TauCeti.IsAspherical.mappingTorus`, `TauCeti.IsAspherical.smoothMappingTorus`: the mapping torus
  of a self-homeomorphism, and the smooth mapping torus of a diffeomorphism, of an aspherical space
  are aspherical.
* `TauCeti.KleinBottle.isAspherical`: the Klein bottle is aspherical.
* `TauCeti.KleinBottle.surjective_pow_homotopyGroup`: every power map is surjective on the higher
  homotopy groups of the Klein bottle.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Proposition 4.1 (covering
  spaces and higher homotopy groups) and Section 1.B (`K(G, 1)` spaces).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Theorems 5.15 and C.
-/

public section

noncomputable section

open Metric
open scoped ContDiff Manifold Topology Topology.Homotopy

namespace TauCeti

namespace MappingTorus

variable {F : Type*} [TopologicalSpace F] (φ : F ≃ₜ F)

/-- **The fibre of a mapping torus carries its higher homotopy groups.** The inclusion
`x ↦ [x, 0]` of `F` into the mapping torus of `φ` induces a bijection
`π_(n + 2)(F, x) → π_(n + 2)(MappingTorus φ, [x, 0])`. -/
theorem bijective_homotopyGroupMap_incl (x : F) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin (n + 2)) (incl φ)
      (rfl : incl φ x = incl φ x)) := by
  -- The inclusion is the zero section `x ↦ (x, 0)` of the cylinder `F × ℝ`, a homotopy
  -- equivalence, followed by the covering map of the cylinder onto the mapping torus.
  let := action φ
  let s := ContinuousMap.HomotopyEquiv.prodZeroSection F ℝ
  have hq : Function.Bijective (HomotopyGroup.map (N := Fin (n + 2)) (coverMap φ)
      (rfl : coverMap φ (s x) = coverMap φ (s x))) :=
    HomotopyGroup.map_bijective (isAddQuotientCoveringMap_coverMap φ).isCoveringMap rfl
  have h := hq.comp (s.isWeakHomotopyEquivalence.bijective (n + 2) x)
  rw [HomotopyGroup.map_comp_map] at h
  exact (HomotopyGroup.bijective_map_congr (ContinuousMap.ext fun _ ↦ by simp [s]) _ _).1 h

/-- **Asphericity of a mapping torus.** The mapping torus of a self-homeomorphism `φ` of `F` is
aspherical exactly when it is path connected and every homotopy group of `F` of dimension at least
two is trivial, at every base point of `F`. -/
theorem isAspherical_iff (z : MappingTorus φ) :
    IsAspherical (MappingTorus φ) z ↔
      PathConnectedSpace (MappingTorus φ) ∧ ∀ (x : F) (n : ℕ), Subsingleton (π_ (n + 2) F x) := by
  refine ⟨fun h ↦ ⟨h.pathConnectedSpace, fun x n ↦ ?_⟩, fun ⟨hX, h⟩ ↦ ?_⟩
  · have := (h.of_basepoint (incl φ x)).subsingleton_homotopyGroup n
    exact (Equiv.ofBijective _ (bijective_homotopyGroupMap_incl φ x n)).subsingleton
  · obtain ⟨⟨x, t⟩, rfl⟩ := mk_surjective φ z
    refine IsAspherical.of_basepoint (IsAspherical.mk (x := incl φ x) hX fun n ↦ ?_) _
    have := h x n
    exact (Equiv.ofBijective _ (bijective_homotopyGroupMap_incl φ x n)).symm.subsingleton

end MappingTorus

namespace IsAspherical

/-- **The mapping torus of a self-homeomorphism of an aspherical space is aspherical**, at every
base point. -/
theorem mappingTorus {F : Type*} [TopologicalSpace F] {x : F} (h : IsAspherical F x)
    (φ : F ≃ₜ F) (z : MappingTorus φ) : IsAspherical (MappingTorus φ) z := by
  have := h.pathConnectedSpace
  exact (MappingTorus.isAspherical_iff φ z).2
    ⟨inferInstance, fun x' n ↦ (h.of_basepoint x').subsingleton_homotopyGroup n⟩

/-- **The smooth mapping torus of a diffeomorphism of an aspherical manifold is aspherical**, at
every base point: it is homeomorphic to the topological mapping torus of the inverse
diffeomorphism. -/
theorem smoothMappingTorus {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω} {x : M} (h : IsAspherical M x)
    (φ : M ≃ₘ^n⟮I, I⟯ M) (z : SmoothMappingTorus φ) : IsAspherical (SmoothMappingTorus φ) z :=
  let e := SmoothMappingTorus.homeomorphMappingTorus φ
  (h.mappingTorus φ.toHomeomorph.symm (e z)).of_homotopyEquiv e.symm.toHomotopyEquiv z

end IsAspherical

namespace KleinBottle

attribute [local instance] finrank_real_complex_fact'

/-- **The Klein bottle is aspherical**: it is the smooth mapping torus of complex conjugation of
the circle, which is aspherical. -/
theorem isAspherical (z : KleinBottle) : IsAspherical KleinBottle z :=
  ((Circle.isAspherical 1).of_homotopyEquiv Circle.homeomorphSphere.toHomotopyEquiv
    1).smoothMappingTorus conjCircleDiffeomorph z

/-- **Every power map is surjective on the higher homotopy groups of the Klein bottle**, since they
are trivial. For `d = 2` this says that `π_(n + 2)(K) ⊗ ℤ/2` vanishes for the Klein bottle `K`. -/
theorem surjective_pow_homotopyGroup (z : KleinBottle) (n d : ℕ) :
    Function.Surjective fun a : π_ (n + 2) KleinBottle z ↦ a ^ d :=
  have := (isAspherical z).subsingleton_homotopyGroup n
  fun b ↦ ⟨b, Subsingleton.elim _ _⟩

end KleinBottle

end TauCeti
