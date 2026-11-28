/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Central
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Centralizer.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.ComponentGroup

/-!
# Centralizer component groups under isogenies

Over an algebraically closed field `k`, this file specializes the centralizer component-group
surjectivity, exactness, and injectivity results from
`TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.ComponentGroup` to isogenies and
central isogenies (without assuming smoothness in
`centralizerComponentGroupMap_surjective_of_etaleKernel`). For the underlying scheme-level isogeny
comparison over arbitrary fields, see `TauCeti.Algebra.AlgebraicGroup.Isogeny.Centralizer.Basic`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 18.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §1.3 and §6.1.
-/

public section

open Derivation

namespace TauCeti.CommHopfAlgCat.IsIsogeny

open FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] {H' K' : FiniteTypeCommHopfAlgCat.{u, u} k} {g : H' ⟶ K'}
  [IsAlgClosed k]

/-- An isogeny of finite-type affine groups with étale kernel induces a surjection
`A_K(x) ↠ A_H(df(x))`. -/
theorem centralizerComponentGroupMap_surjective_of_etaleKernel (hg : IsIsogeny g.hom)
    (hker : Algebra.Etale k (K' ⧸ (kernelHopfIdeal g.hom).toIdeal))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K')) :
    Function.Surjective (centralizerComponentGroupMap g x) :=
  centralizerComponentGroupMap_surjective_of_injective_coordinateMap_of_injective_differential
    g hg.injective (hg.dualCotangentMap_bijective_of_etaleKernel hker).injective x

/-- In characteristic zero, an isogeny `φ : G' → G` induces a surjection
`π₀(C_G'(x)) →* π₀(C_G(dφ x))` of centralizer component groups. This includes central isogenies
of semisimple groups, for which the map need not be injective. -/
theorem centralizerComponentGroupMap_surjective_of_charZero [CharZero k] (hg : IsIsogeny g.hom)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K')) :
    Function.Surjective (centralizerComponentGroupMap g x) :=
  centralizerComponentGroupMap_surjective g hg.injective x
    (hg.map_centralizerHopfIdeal_of_charZero x)

/-- For an isogeny `g` with injective differential, the sequence
`π₀(ker g ∩ C_K(x)) → A_K(x) → A_H(dg(x))` is exact at `A_K(x)` (and surjective at `A_H(dg(x))` by
`centralizerComponentGroupMap_surjective_of_injective_coordinateMap_of_injective_differential`). -/
theorem mulExact_centralizerComponentGroupMap_of_injective_differential (hg : IsIsogeny g.hom)
    (hinj : Function.Injective (dualCotangentMap (toBialgHom g)))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K')) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K'
        (le_sup_right : centralizerHopfIdeal K' x ≤
          kernelHopfIdeal g.hom ⊔ centralizerHopfIdeal K' x)))
      (centralizerComponentGroupMap g x) :=
  mulExact_centralizerComponentGroupMap_of_faithfullyFlat_of_injective_differential g
    hg.faithfullyFlat hinj x

/-- **Central-isogeny exact sequence on centralizer component groups.** For an isogeny `g` with
injective differential and central kernel, the natural sequence
`π₀(ker g) → A_K(x) → A_H(dg(x))` is exact at `A_K(x)` (and surjective at `A_H(dg(x))` by
`centralizerComponentGroupMap_surjective_of_injective_coordinateMap_of_injective_differential`). -/
theorem mulExact_centralizerComponentGroupMap_of_injective_differential_of_isCentral
    (hg : IsIsogeny g.hom)
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
`centralizerComponentGroupMap_surjective_of_injective_coordinateMap_of_injective_differential`) if
and only if every rational point of `ker g` lies in `C_K(x)°(k)`. -/
theorem injective_centralizerComponentGroupMap_iff_of_injective_differential_of_isCentral
    (hg : IsIsogeny g.hom)
    (hinj : Function.Injective (dualCotangentMap (toBialgHom g)))
    (hcent : (kernelHopfIdeal g.hom).IsCentral)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K')) :
    Function.Injective (centralizerComponentGroupMap g x) ↔
      CommHopfAlgCat.quotientPointsSubgroup K'.obj (kernelHopfIdeal g.hom)
          (CommAlgCat.of k k) ≤
        CommHopfAlgCat.quotientPointsSubgroup K'.obj
          (centralizerHopfIdeal K' x).identityComponent (CommAlgCat.of k k) :=
injective_centralizerComponentGroupMap_iff_of_faithfullyFlat_of_injective_differential_of_isCentral
    g hg.faithfullyFlat hinj hcent x

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
  hf.isIsogeny.mulExact_centralizerComponentGroupMap_of_injective_differential_of_isCentral
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
