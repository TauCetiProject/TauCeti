/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Classical

/-!
# Classical local systems and pullback

The identification of the zeroth homology of `C_*(Ω_b B; R)` with the group ring of the opposite
fundamental group is natural in based maps `f : (B, b) → (B', b')`: the class of the image of a
Moore loop is the image of its class under `π₁(f)` (`MooreLoopSpace.loopClass_map`), and the
degree-zero ring map `loopChainDegreeZero` intertwines `C_*(Ωf)` with the map of group rings
(`loopChainDegreeZero_loopChainMap`).

The module `Classical` builds the DG local system of a classical local system; the isomorphism
between the pullback of the DG local system of `L` and the DG local system of the pullback of `L`
is not proved here: it is the combination of the naturality below with the monodromy of the
pullback.

## Main results

* `TauCeti.MooreLoopSpace.loopClass_map`: the class of the image of a loop.
* `TauCeti.zerothClass_map`: naturality of `zerothClass`.
* `TauCeti.loopChainDegreeZero_loopChainMap`: naturality of `loopChainDegreeZero`.
-/

public section

noncomputable section

open MulOpposite

namespace TauCeti

section Naturality

variable {B B' : Type*} [TopologicalSpace B] [TopologicalSpace B'] {b : B} {b' : B'}
  {R : Type*} [CommRing R]

/-- **The class of the image of a Moore loop** is the image of its class under the map of
fundamental groups. -/
theorem MooreLoopSpace.loopClass_map (f : C(B, B')) (hf : f b = b') (γ : MooreLoopSpace B b) :
    loopClass (MooreLoopSpace.map f hf γ) = FundamentalGroup.mapOfEq f hf (loopClass γ) := by
  rw [FundamentalGroup.mapOfEq_apply, MooreLoopSpace.loopClass_def, MooreLoopSpace.loopClass_def,
    ← Path.Homotopic.Quotient.mk_map]
  have h : (MooreLoopSpace.map f hf γ).toPath = (γ.toPath.map f.continuous).cast hf.symm hf.symm :=
    by
    ext s
    simp [MooreLoopSpace.toPath_apply, MoorePath.map_apply]
  rw [h]
  rfl

/-- **Naturality of the class of `0`-chains**: the class of the image of a `0`-chain under
`C_*(Ωf)` is the image of its class under the map of group rings of the opposite fundamental
groups. -/
theorem zerothClass_map (f : C(B, B')) (hf : f b = b')
    (c : NormalizedCubicalChain (MooreLoopSpace B b) R 0) :
    zerothClass B' b' R
        (NormalizedCubicalChain.map R (MooreLoopSpace.map f hf).toContinuousMap 0 c) =
      MonoidAlgebra.mapDomainRingHom R (FundamentalGroup.mapOfEq f hf).op
        (zerothClass B b R c) := by
  induction c using NormalizedCubicalChain.induction_zero with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul r γ =>
    have h : (↑(MooreLoopSpace.map f hf) : C(MooreLoopSpace B b, MooreLoopSpace B' b')).comp
        (SingularCube.point γ) =
        SingularCube.point (MooreLoopSpace.map f hf γ) :=
      ContinuousMap.ext fun x ↦ by simp [SingularCube.point_apply]
    simp [NormalizedCubicalChain.map_ofCube, h, zerothClass_ofCube_point,
      MooreLoopSpace.loopClass_map]

/-- **Naturality of the degree-zero ring map**: it intertwines `C_*(Ωf)` with the map of group
rings induced by `π₁(f)`. -/
theorem loopChainDegreeZero_loopChainMap (f : C(B, B')) (hf : f b = b')
    (a : loopChainAlgebra B b R) :
    loopChainDegreeZero B' b' R (loopChainMap R f hf a) =
      MonoidAlgebra.mapDomainRingHom R (FundamentalGroup.mapOfEq f hf).op
        (loopChainDegreeZero B b R a) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n y =>
    rw [← DirectSum.lof_eq_of R]
    change loopChainDegreeZero B' b' R (loopChainMap R f hf (cubicalChainLof _ R n y)) = _
    rw [loopChainMap_lof, loopChainDegreeZero_lof, loopChainDegreeZero_lof]
    cases n with
    | zero =>
      rw [zerothComponent_zero, zerothComponent_zero]
      exact zerothClass_map f hf y
    | succ n =>
      rw [zerothComponent_eq_zero n.succ_ne_zero, zerothComponent_eq_zero n.succ_ne_zero,
        map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

end Naturality

end TauCeti
