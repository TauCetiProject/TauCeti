/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation
public import TauCeti.Algebra.Bialgebra.GroupLike.Map

/-!
# Group-like evaluation in commutative Hopf algebras

For a commutative Hopf algebra over a domain whose group-like elements span, evaluation
identifies the group algebra on those elements with the original Hopf algebra. This categorical
isomorphism is natural in morphisms between such algebras.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u

variable {k : Type u} [CommRing k] [IsDomain k]
variable {H K : _root_.CommHopfAlgCat.{u} k}

/-- The categorical isomorphism given by evaluation on the group-like elements of a
torsion-free commutative Hopf algebra when they span its carrier. -/
noncomputable def evaluationIso {H : _root_.CommHopfAlgCat.{u} k} [Module.IsTorsionFree k H]
    (hH : Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := H))) = ⊤) :
    _root_.CommHopfAlgCat.of k (_root_.MonoidAlgebra k (_root_.GroupLike k H)) ≅ H :=
  _root_.CommHopfAlgCat.isoMk (TauCeti.GroupLike.evaluationBialgEquiv k H hH)

/-- Evaluation commutes with a morphism of torsion-free commutative Hopf algebras whose
group-like elements span their carriers. -/
theorem evaluationIso_naturality
    [Module.IsTorsionFree k H] [Module.IsTorsionFree k K]
    (hH : Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := H))) = ⊤)
    (hK : Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := K))) = ⊤)
    (f : H ⟶ K) :
    (evaluationIso hH).hom ≫ f =
      _root_.CommHopfAlgCat.ofHom
        (_root_.MonoidAlgebra.mapDomainBialgHom k (TauCeti.GroupLike.map f.hom)) ≫
          (evaluationIso hK).hom := by
  apply _root_.CommHopfAlgCat.hom_ext
  apply _root_.MonoidAlgebra.bialgHom_ext
  · intro x
    simp only [_root_.CommHopfAlgCat.hom_comp, _root_.BialgHom.comp_apply,
      _root_.CommHopfAlgCat.hom_ofHom, _root_.MonoidAlgebra.mapDomainBialgHom_single]
    simp [evaluationIso, TauCeti.GroupLike.evaluationBialgHom_single,
      TauCeti.GroupLike.val_map]
  · apply AlgHom.ext
    intro r
    simp [evaluationIso, MonoidAlgebra.singleOneAlgHom_apply]

end TauCeti.CommHopfAlgCat
