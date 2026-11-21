/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Central
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.ComponentGroup
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Map
import TauCeti.Algebra.AlgebraicGroup.Isogeny.Etale
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.RingTheory.RingHom.Quotient
import Mathlib.RingTheory.RingHom.Finite

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

The restricted map `BialgHom.centralizerMap` is itself an isogeny: it is the base change of
`π` along the closed immersion of the target centralizer. This does not identify the two
centralizers or their component groups, and does not assert an isomorphism. In particular,
surjectivity on points follows over algebraically closed fields, not over arbitrary value
algebras.

Over an algebraically closed field, the `ComponentGroup` section specializes the general
centralizer component-group surjectivity, exactness, and injectivity results from
`TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.ComponentGroup` to isogenies
and central isogenies (without assuming smoothness in
`centralizerComponentGroupMap_surjective_of_etaleKernel`).

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
  exact hf.map_centralizerHopfIdeal_of_etaleKernel
    hf.algebraEtale_quotient_kernelHopfIdeal_of_charZero x

private theorem centralizerMap_of_map_eq
    [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [Module.Finite k (Bialgebra.CotangentSpace k K)]
    (hf : IsIsogeny f) (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (hideal : (centralizerHopfIdeal H (dualCotangentMap f.hom x)).map f.hom =
      centralizerHopfIdeal K x) :
    IsIsogeny (_root_.CommHopfAlgCat.ofHom (f.hom.centralizerMap x)) := by
  have hI := congrArg HopfIdeal.toIdeal hideal
  -- The direct ring-hom coercion and the coercion through AlgHom have the same values.
  have hcoe : f.hom.toAlgHom.toRingHom = (f.hom : H →+* K) := by
    ext a
    rfl
  have h := (RingHom.finite_isStableUnderBaseChange.and
    RingHom.FaithfullyFlat.isStableUnderBaseChange).quotientMap (f.hom : H →+* K)
      (centralizerHopfIdeal H (dualCotangentMap f.hom x)).toIdeal
      (hcoe ▸ ⟨hf.finite, hf.faithfullyFlat⟩)
  rw [HopfIdeal.map_toIdeal] at hI
  have h' := (RingHom.finite_respectsIso.and RingHom.FaithfullyFlat.respectsIso).left
    _ (Ideal.quotEquivOfEq hI) h
  have hmap : (f.hom.centralizerMap x).toAlgHom.toRingHom =
      (Ideal.quotEquivOfEq hI).toRingHom.comp
        (Ideal.quotientMap _ (f.hom : H →+* K) Ideal.le_comap_map) := by
    ext a
    simp only [RingHom.comp_apply, Ideal.quotientMap_mk, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, Ideal.quotEquivOfEq_mk, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, BialgHom.coe_toAlgHom]
    exact f.hom.centralizerMap_mk x a
  apply (isIsogeny_iff _).mpr
  rw [_root_.CommHopfAlgCat.hom_ofHom, AlgHom.Finite, hmap]
  exact h'

/-- An isogeny with injective differential restricts to an isogeny between the centralizers
of corresponding Lie algebra elements. The coordinate map is finite and faithfully flat,
not necessarily bijective. -/
theorem centralizerMap_of_injective
    [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [Module.Finite k (Bialgebra.CotangentSpace k K)]
    (hf : IsIsogeny f) (hinj : Function.Injective (dualCotangentMap f.hom))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    IsIsogeny (_root_.CommHopfAlgCat.ofHom (f.hom.centralizerMap x)) :=
  hf.centralizerMap_of_map_eq x
    (f.hom.map_centralizerHopfIdeal_eq_of_injective hinj x)

/-- A separable isogeny between smooth affine groups restricts to an isogeny on
Lie-element centralizers. The étale-kernel hypothesis ensures injectivity of the differential. -/
theorem centralizerMap_of_etaleKernel
    [Algebra.Smooth k H] [Algebra.Smooth k K] (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    IsIsogeny (_root_.CommHopfAlgCat.ofHom (f.hom.centralizerMap x)) :=
  hf.centralizerMap_of_injective
    (hf.dualCotangentMap_bijective_of_etaleKernel hker).injective x

/-- In characteristic zero, a finite-type affine isogeny restricts to an isogeny on
centralizers of Lie algebra elements. This includes semisimple central isogenies, but does
not require centrality, connectedness or semisimplicity. -/
theorem centralizerMap_of_charZero [CharZero k] [Algebra.FiniteType k H]
    (hf : IsIsogeny f) (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    haveI := hf.finiteType_target
    IsIsogeny (_root_.CommHopfAlgCat.ofHom (f.hom.centralizerMap x)) := by
  let _ := hf.finiteType_target
  exact hf.centralizerMap_of_map_eq x (hf.map_centralizerHopfIdeal_of_charZero x)

section ComponentGroup

open FiniteTypeCommHopfAlgCat

variable {H' K' : FiniteTypeCommHopfAlgCat.{u, u} k} {g : H' ⟶ K'} [IsAlgClosed k]

/-- An isogeny of finite-type affine groups with étale kernel induces a surjection
`A_K(x) ↠ A_H(df(x))`. -/
theorem centralizerComponentGroupMap_surjective_of_etaleKernel (hg : IsIsogeny g.hom)
    (hker : Algebra.Etale k (K' ⧸ (kernelHopfIdeal g.hom).toIdeal))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K')) :
    Function.Surjective (centralizerComponentGroupMap g x) :=
  centralizerComponentGroupMap_surjective_of_injective_of_injective_differential g hg.injective
    (hg.dualCotangentMap_bijective_of_etaleKernel hker).injective x

/-- In characteristic zero, an isogeny `φ : G' → G` induces a surjection
`π₀(C_G'(x)) →* π₀(C_G(dφ x))` of centralizer component groups. This includes central isogenies
of semisimple groups, for which the map need not be injective. -/
theorem centralizerComponentGroupMap_surjective_of_charZero [CharZero k] (hg : IsIsogeny g.hom)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K')) :
    Function.Surjective (centralizerComponentGroupMap g x) :=
  centralizerComponentGroupMap_surjective g hg.injective x
    (hg.map_centralizerHopfIdeal_of_charZero x)

/-- For an isogeny `g` with injective differential, the sequence
`π₀(ker g ∩ C_K(x)) → A_K(x) → A_H(dg(x))` is exact at `A_K(x)` (and surjective at `A_H(dg(x))`
by `centralizerComponentGroupMap_surjective_of_injective_of_injective_differential`). -/
theorem mulExact_centralizerComponentGroupMap_of_injective_differential (hg : IsIsogeny g.hom)
    (hinj : Function.Injective (dualCotangentMap (toBialgHom g)))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K')) :
    let c : quotient H' (centralizerHopfIdeal H' (dualCotangentMap (toBialgHom g) x)) ⟶
        quotient K' (centralizerHopfIdeal K' x) :=
      ofHom ((toBialgHom g).centralizerMap x)
    Function.MulExact
      (mapComponentGroup (mkQuotient (quotient K' (centralizerHopfIdeal K' x))
        (CommHopfAlgCat.kernelHopfIdeal c.hom)))
      (centralizerComponentGroupMap g x) :=
  mulExact_centralizerComponentGroupMap_of_faithfullyFlat_of_injective_differential g
    hg.faithfullyFlat hinj x

/-- **Central-isogeny exact sequence on centralizer component groups.** For an isogeny `g` with
injective differential and central kernel, the natural sequence
`π₀(ker g) → A_K(x) → A_H(dg(x))` is exact at `A_K(x)` (and surjective at `A_H(dg(x))` by
`centralizerComponentGroupMap_surjective_of_injective_of_injective_differential`). -/
theorem mulExact_centralizerComponentGroupMap_of_isCentral (hg : IsIsogeny g.hom)
    (hinj : Function.Injective (dualCotangentMap (toBialgHom g)))
    (hcent : (kernelHopfIdeal g.hom).IsCentral)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K')) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K' (centralizerHopfIdeal_le_of_isCentral hcent x)))
      (centralizerComponentGroupMap g x) :=
  mulExact_centralizerComponentGroupMap_of_faithfullyFlat_of_injective_differential_of_isCentral g
    hg.faithfullyFlat hinj hcent x

/-- For a central isogeny with injective differential, `A_K(x) → A_H(dg(x))` is injective (hence
an isomorphism, combined with
`centralizerComponentGroupMap_surjective_of_injective_of_injective_differential`) if and only if
every rational point of `ker g` lies in `C_K(x)°(k)`. -/
theorem injective_centralizerComponentGroupMap_iff_of_isCentral (hg : IsIsogeny g.hom)
    (hinj : Function.Injective (dualCotangentMap (toBialgHom g)))
    (hcent : (kernelHopfIdeal g.hom).IsCentral)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K')) :
    Function.Injective (centralizerComponentGroupMap g x) ↔
      CommHopfAlgCat.quotientPointsSubgroup K'.obj (kernelHopfIdeal g.hom)
          (CommAlgCat.of k k) ≤
        CommHopfAlgCat.quotientPointsSubgroup K'.obj (centralizerHopfIdeal K' x).identityComponent
          (CommAlgCat.of k k) :=
  by
    exact
 injective_centralizerComponentGroupMap_iff_of_faithfullyFlat_of_injective_differential_of_isCentral
      g hg.faithfullyFlat hinj hcent x

end ComponentGroup

end TauCeti.CommHopfAlgCat.IsIsogeny

namespace TauCeti.CommHopfAlgCat.IsCentralIsogeny

open TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {H K : FiniteTypeCommHopfAlgCat.{u, u} k} {f : H ⟶ K}

/-- Characteristic-zero central-isogeny exactness at `A_K(x)` in
`π₀(ker f) → A_K(x) → A_H(df(x))` (with surjectivity at `A_H(df(x))` given separately by
`IsIsogeny.centralizerComponentGroupMap_surjective_of_charZero`). -/
theorem mulExact_centralizerComponentGroupMap_of_charZero (hf : IsCentralIsogeny f.hom)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K
        (centralizerHopfIdeal_le_of_isCentral hf.isCentral_kernelHopfIdeal x)))
      (centralizerComponentGroupMap f x) :=
  hf.isIsogeny.mulExact_centralizerComponentGroupMap_of_isCentral
    hf.isIsogeny.dualCotangentMap_bijective_of_charZero.injective
    hf.isCentral_kernelHopfIdeal x

end TauCeti.CommHopfAlgCat.IsCentralIsogeny

namespace TauCeti.CommHopfAlgCat.IsIsogeny

open FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
  {H K : FiniteTypeCommHopfAlgCat.{u, u} k} {f : H ⟶ K}

/-- In characteristic zero, every isogeny from a geometrically connected affine group is central
and therefore gives exactness at `A_K(x)` in `π₀(ker f) → A_K(x) → A_H(df(x))` (with
surjectivity at `A_H(df(x))` given separately by
`IsIsogeny.centralizerComponentGroupMap_surjective_of_charZero`). -/
theorem mulExact_centralizerComponentGroupMap_of_connected_of_charZero (hf : IsIsogeny f.hom)
    (hK : geometricallyConnectedCommHopfAlgProperty k K.obj)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K
        (centralizerHopfIdeal_le_of_isCentral
          (hf.isCentralIsogeny_of_charZero hK).isCentral_kernelHopfIdeal x)))
      (centralizerComponentGroupMap f x) :=
  (hf.isCentralIsogeny_of_charZero hK).mulExact_centralizerComponentGroupMap_of_charZero x

end TauCeti.CommHopfAlgCat.IsIsogeny
