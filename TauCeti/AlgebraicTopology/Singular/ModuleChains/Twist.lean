/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import TauCeti.Algebra.Homology.Embedding.DownNatAdd
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Resolution
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.RepresentationTheory.Rep.Ihom
import TauCeti.Algebra.Homology.Embedding.MapExtend

/-!
# The singular chains twisted by a character

Let a group `G` act on a space `Y` and let `χ : G →* kˣ` be a character with values in the units of
a commutative ring `k`. Tensoring the equivariant singular chains of `Y`
(`TauCeti.singularChainsRep`) with the one-dimensional representation `k_χ` of `χ` gives the
complex of representations `k_χ ⊗ C(Y; k)`, the singular chains of `Y` twisted by `χ`.

Forgetting the action of `G`, the twisted chains are the singular chains of `Y`: in each degree,
`k ⊗ C_q(Y) ≅ C_q(Y)` by the left unitor (`TauCeti.singularChainsRepTwistForget₂Iso`), also after
placing both complexes `n` degrees higher (`TauCeti.singularChainsRepTwistExtendForget₂Iso`). If
`G` acts freely on `Y`, the twisted chains are projective representations
(`TauCeti.projective_tensorLeft_singularChainsRep_X`), as the untwisted ones are.

## Main definitions

* `TauCeti.singularChainsRepTwistForget₂Iso`: forgetting the action, the twisted chains of `Y` are
  the singular chains of `Y`.
* `TauCeti.singularChainsRepTwistExtendForget₂Iso`: forgetting the action, the twisted chains of
  `Y` placed `n` degrees higher are the singular chains of `Y` placed `n` degrees higher.

## Main results

* `TauCeti.projective_tensorLeft_singularChainsRep_X`: the twisted singular chains of a free
  `G`-space are projective representations.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections I.4 and III.1.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace TauCeti

variable {k : Type u} [CommRing k] {Y : TopCat.{u}}

section Monoid

variable {G : Type u} [Monoid G] [MulAction G Y] [ContinuousConstSMul G Y] (χ : G →* kˣ)

variable (k Y) in
/-- **Forgetting the action, the twisted chains are the singular chains.** Forgetting the action
of `G`, the singular chains of `Y` twisted by the character `χ` are the singular chains of `Y`: in
each degree, `k ⊗ C_q(Y) ≅ C_q(Y)` by the left unitor. -/
def singularChainsRepTwistForget₂Iso :
    ((forget₂ (Rep.{u} k G) (ModuleCat.{u} k)).mapHomologicalComplex _).obj
        (((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
          (singularChainsRep k Y G)) ≅
      (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of k k) :=
  HomologicalComplex.Hom.isoOfComponents (fun q ↦ (TensorProduct.lid k
    (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of k k)).X q)).toModuleIso) fun i j _ ↦ by
      refine ModuleCat.hom_ext (TensorProduct.ext' fun (a : k)
        (x : ((singularChains k).obj Y).X i) ↦ ?_)
      -- evaluate on `a ⊗ x`: the differential of the twist is `𝟙 ⊗ ∂`
      change ((singularChains k).obj Y).d i j (a • x) =
        a • ((singularChainsRep k Y G).d i j).hom x
      rw [singularChainsRep_d_hom_apply k Y G i j x, map_smul]
      -- the two sides differ only in the module structure on the twisted carrier
      rfl

/-- In each degree, `TauCeti.singularChainsRepTwistForget₂Iso` is the left unitor
`k ⊗ C_q(Y) ≅ C_q(Y)`. -/
@[simp]
theorem singularChainsRepTwistForget₂Iso_hom_f (q : ℕ) :
    (singularChainsRepTwistForget₂Iso k Y χ).hom.f q =
      (TensorProduct.lid k
        (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of k k)).X q)).toModuleIso.hom :=
  (rfl)

variable (k Y) in
/-- **Forgetting the action, the twisted shifted chains are the shifted singular chains.**
Forgetting the action of `G`, the singular chains of `Y` twisted by the character `χ` and placed
`n` degrees higher are the singular chains of `Y` placed `n` degrees higher. -/
def singularChainsRepTwistExtendForget₂Iso (n : ℕ) :
    ((forget₂ (Rep.{u} k G) (ModuleCat.{u} k)).mapHomologicalComplex _).obj
        ((((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex _).obj
          (singularChainsRep k Y G)).extend (ComplexShape.embeddingDownNatAdd n)) ≅
      ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of k k)).extend
        (ComplexShape.embeddingDownNatAdd n) :=
  HomologicalComplex.mapExtendIso _ _ _ ≪≫
    ((ComplexShape.embeddingDownNatAdd n).extendFunctor _).mapIso
      (singularChainsRepTwistForget₂Iso k Y χ)

/-- In degree `q + n`, `TauCeti.singularChainsRepTwistExtendForget₂Iso` is
`TauCeti.singularChainsRepTwistForget₂Iso` in degree `q`, up to the identifications of the
terms of both shifted complexes. -/
@[simp]
theorem singularChainsRepTwistExtendForget₂Iso_hom_f (n q : ℕ) :
    (singularChainsRepTwistExtendForget₂Iso k Y χ n).hom.f (q + n) =
      (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)).map
          (HomologicalComplex.extendXIso _ (ComplexShape.embeddingDownNatAdd n)
            (ComplexShape.embeddingDownNatAdd_f n q)).hom ≫
        (singularChainsRepTwistForget₂Iso k Y χ).hom.f q ≫
          (HomologicalComplex.extendXIso _ (ComplexShape.embeddingDownNatAdd n)
            (ComplexShape.embeddingDownNatAdd_f n q)).inv := by
  rw [singularChainsRepTwistExtendForget₂Iso, Iso.trans_hom, HomologicalComplex.comp_f,
    HomologicalComplex.mapExtendIso_hom_f _ _ _ (ComplexShape.embeddingDownNatAdd_f n q),
    Functor.mapIso_hom, ComplexShape.Embedding.extendFunctor_map,
    HomologicalComplex.extendMap_f _ _ (ComplexShape.embeddingDownNatAdd_f n q), Category.assoc,
    Iso.inv_hom_id_assoc]

end Monoid

section Group

variable {G : Type u} [Group G] [MulAction G Y] [ContinuousConstSMul G Y] (χ : G →* kˣ)

/-- **The twisted singular chains of a free `G`-space are projective**: twisting by the
one-dimensional representation of `χ` keeps the free representations of the singular chains
projective. -/
instance projective_tensorLeft_singularChainsRep_X [IsCancelSMul G Y] (q : ℕ) :
    Projective ((((tensorLeft (Rep.of (Representation.ofLinearCharacter χ))).mapHomologicalComplex
      _).obj (singularChainsRep k Y G)).X q) :=
  Rep.projective_tensorObj _ _

end Group

end TauCeti
