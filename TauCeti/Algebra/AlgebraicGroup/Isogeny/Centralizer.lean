/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Map
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.RingTheory.Etale.Reduced

/-!
# Centralizers under separable isogenies

For an isogeny `π : G → G'` of smooth affine groups with étale kernel, the differential
identifies their Lie algebras. The centralizer of `x` in `G` is the scheme-theoretic inverse
image of the centralizer of `dπ(x)` in `G'`. This gives a comparison of the actual defining
ideals, and therefore of their points over every coefficient algebra.

In characteristic zero, Cartier's theorem supplies smoothness and reducedness of the finite
kernel, so no smoothness or étale-kernel hypothesis is required. Centrality, connectedness and
semisimplicity are not needed either. In particular the comparison applies to central
isogenies of semisimple complex groups.

This does not identify the two centralizers or their component groups: the restricted map is
`BialgHom.centralizerMap`, not an isomorphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 18.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §1.3.
-/

public section

open Derivation

namespace TauCeti.CommHopfAlgCat.IsIsogeny

universe u

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k} {f : H ⟶ K}

/-- An isogeny of smooth affine groups with étale kernel pulls a Lie algebra centralizer
back to the centralizer of the corresponding source element, including its scheme structure.
The coordinate arrow `f : H ⟶ K` represents `Spec K → Spec H`. -/
theorem map_centralizerHopfIdeal_of_etaleKernel
    [Algebra.Smooth k H] [Algebra.Smooth k K] (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    (centralizerHopfIdeal H (dualCotangentMap f.hom x)).map f.hom =
      centralizerHopfIdeal K x :=
  f.hom.map_centralizerHopfIdeal_eq_of_injective
    (hf.dualCotangentMap_bijective_of_etaleKernel hker).injective x

/-- In characteristic zero, every finite-type affine isogeny pulls back centralizers of
Lie algebra elements. In particular this applies to semisimple central isogenies, without
asserting that centralizers or component groups are invariant. Finite type of `K` follows
from finite type of `H` and finiteness of the isogeny. -/
theorem map_centralizerHopfIdeal_of_charZero [CharZero k]
    [Algebra.FiniteType k H] (hf : IsIsogeny f)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    haveI := hf.finiteType_target
    (centralizerHopfIdeal H (dualCotangentMap f.hom x)).map f.hom =
      centralizerHopfIdeal K x := by
  let _ := hf.finiteType_target
  let _ : Algebra.Smooth k H :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k H)
  let _ : Algebra.Smooth k K :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k K)
  let Q := _root_.CommHopfAlgCat.quotient K (kernelHopfIdeal f)
  let _ : Module.Finite k Q := moduleFinite_quotient_kernelHopfIdeal hf.finite
  let _ : _root_.IsReduced Q := HopfAlgebra.isReduced_of_charZero k Q
  exact hf.map_centralizerHopfIdeal_of_etaleKernel (algebraEtale_of_finite_of_isReduced k Q) x

end TauCeti.CommHopfAlgCat.IsIsogeny
