/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.BaseChange
public import TauCeti.AlgebraicGeometry.GroupScheme.CentralIsogeny.Basic
public import TauCeti.AlgebraicGeometry.GroupScheme.Isogeny.BaseChange

/-!
# Base change of central isogenies of group schemes

This file proves that central kernels of group-scheme morphisms remain central after arbitrary
base change, by identifying the point groups before and after base change through the pullback
adjunction (`TauCeti.GroupScheme.baseChangePointMulEquiv`). Consequently, central isogenies over
a commutative ring remain so after base change along a morphism between affine bases. For a
commutative source, the base-changed isogeny is central without any centrality
hypothesis. The group-scheme base change is the pullback functor on the over category, lifted to
group objects.

## Main declarations

* `TauCeti.GroupScheme.baseChangePointMulEquiv_pointMap`: the point-group identification
  intertwines a base-changed morphism with the original morphism.
* `TauCeti.GroupScheme.HasCentralKernel.baseChange`: central kernels remain central after arbitrary
  base change.
* `TauCeti.GroupScheme.IsCentralIsogeny.baseChange`: central isogenies remain central after base
  change.
* `TauCeti.GroupScheme.IsIsogeny.baseChange_isCentral_of_isCommMonObj`: the base change of an
  isogeny from a commutative source is a central isogeny.

## References

* J. S. Milne, *Algebraic Groups* (2017), §18.a.

The base-change argument follows
`TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogeny.baseChange`.

This is the base-change stability needed for the central-isogeny interface in Layer 6 of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory
open scoped CategoryTheory.MonObj
namespace TauCeti.GroupScheme

open AlgebraicGeometry

universe u

section BaseChange

variable {X Y : Scheme.{u}} {G H : Grp (Over X)}

/-- The point-group identification intertwines a base-changed morphism with the original
morphism. -/
theorem baseChangePointMulEquiv_pointMap
    (s : Y ⟶ X) (f : G ⟶ H) (T : Over Y)
    (p : T ⟶ ((Over.pullback s).mapGrp.obj G).X) :
    baseChangePointMulEquiv s H T
        (pointMap ((Over.pullback s).mapGrp.map f) T p) =
      pointMap f ((Over.map s).obj T) (baseChangePointMulEquiv s G T p) := by
  simp only [baseChangePointMulEquiv_apply, pointMap_apply,
    Functor.mapGrp_map_hom_hom]
  exact ((Over.mapPullbackAdj s).homEquiv_naturality_right_symm p f.hom.hom)

/-- Arbitrary base change preserves central kernels of group-scheme morphisms. -/
theorem HasCentralKernel.baseChange
    (s : Y ⟶ X) {f : G ⟶ H} (hf : HasCentralKernel f) :
    HasCentralKernel ((Over.pullback s).mapGrp.map f) := by
  rw [hasCentralKernel_iff_pointMap_ker_le_center]
  intro T p hp
  rw [Subgroup.mem_center_iff]
  intro q
  let eG := baseChangePointMulEquiv s G T
  have hp₀ : pointMap ((Over.pullback s).mapGrp.map f) T p = 1 :=
    (MonoidHom.mem_ker).mp hp
  have hp' : pointMap f ((Over.map s).obj T) (eG p) = 1 := by
    rw [← baseChangePointMulEquiv_pointMap, hp₀, map_one]
  have hf' := (hasCentralKernel_iff_pointMap_ker_le_center f).mp hf
  have hc := Subgroup.mem_center_iff.mp
    (hf' ((Over.map s).obj T) ((MonoidHom.mem_ker).mpr hp')) (eG q)
  apply eG.injective
  simpa only [map_mul] using hc

end BaseChange

section Ring

variable {k L : Type u} [CommRing k] [CommRing L]
variable {G H : Grp (Over (Spec (CommRingCat.of k)))}

/-- Base change along a morphism between spectra of commutative rings preserves central
isogenies. -/
theorem IsCentralIsogeny.baseChange
    (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)) {f : G ⟶ H}
    (hf : IsCentralIsogeny f) :
    IsCentralIsogeny ((Over.pullback s).mapGrp.map f) := by
  rw [isCentralIsogeny_iff]
  have hi := hf.isIsogeny.baseChange s
  exact ⟨hi.isFinite, hi.flat, hi.surjective, hf.hasCentralKernel.baseChange s⟩

/-- The base change of an isogeny from a commutative group scheme is a central isogeny. -/
theorem IsIsogeny.baseChange_isCentral_of_isCommMonObj
    (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)) {f : G ⟶ H}
    (hf : IsIsogeny f) [IsCommMonObj G.X] :
    IsCentralIsogeny ((Over.pullback s).mapGrp.map f) := by
  let _ : IsCommMonObj ((Over.pullback s).mapGrp.obj G).X := by
    exact ((Over.pullback s).mapCommMon.obj (.mk G.X)).comm
  exact (hf.baseChange s).isCentral_of_isCommMonObj

end Ring

end TauCeti.GroupScheme
