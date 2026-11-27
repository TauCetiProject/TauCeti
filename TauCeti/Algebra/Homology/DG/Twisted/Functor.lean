/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Category
public import TauCeti.Algebra.Homology.DG.Twisted.Coefficients

/-!
# The twisted complex as a functor of the coefficient module

Let `m` be a twisting cocycle on a finite set `P` of generators graded by `ind`, with values in a
differential graded algebra `A`. The twisted complex `M ⊗ ⟨P⟩`
(`TauCeti.TwistingCocycle.twistedCochainComplex`) is functorial in the DG right module `M`: a
morphism `f : M ⟶ N` acts on `M ⊗ ⟨P⟩ = P → M` coefficientwise, through
`TauCeti.TwistingCocycle.twistedCochainComplexMap`. This file packages that construction, and its
functoriality `TauCeti.TwistingCocycle.twistedCochainComplexMap_id` and
`TauCeti.TwistingCocycle.twistedCochainComplexMap_comp`, as a functor on the category
`TauCeti.DGRightModuleCat` of DG right modules.

## Main definitions

* `TauCeti.TwistingCocycle.twistedCochainComplexFunctor`: the twisted complex as a functor of the
  coefficient module.
* `TauCeti.TwistingCocycle.twistedCochainComplexMapIso`: the isomorphism of twisted complexes
  induced by an isomorphism of coefficient modules.

## Main results

* `TauCeti.TwistingCocycle.twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply_apply`:
  the map induced by `f : M ⟶ N` applies `f` to the coefficient of each generator.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {P : Type uP} {ind : P → ℤ}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}

namespace TwistingCocycle

variable [Fintype P] (m : TwistingCocycle 𝒜 d P ind) {M N : DGRightModuleCat.{uR, uA, uM} h}

/-- For a morphism `f : M ⟶ N` of DG right modules, the induced map of twisted complexes applies
`f` to the coefficient of each generator. -/
@[simp]
theorem twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply_apply (f : M ⟶ N) (k : ℤ)
    (g : (m.twistedCochainComplex M.differential M.isDGRightModule).X k) (x : P) :
    (twistedCochainComplexXEquiv m.mem_graded m.twisting N.isDGRightModule k
        (((m.twistedCochainComplexMap M.isDGRightModule N.isDGRightModule f).f k).hom g) :
          P → N) x =
      f ((twistedCochainComplexXEquiv m.mem_graded m.twisting M.isDGRightModule k g : P → M) x) :=
  congrFun (m.twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply _ _ f k g) x

variable (h) in
/-- **The twisted complex as a functor of the coefficient module**: `M ↦ M ⊗ ⟨P⟩`. Its body is
exposed so that its objects are the twisted complexes. -/
@[expose] noncomputable def twistedCochainComplexFunctor :
    DGRightModuleCat.{uR, uA, uM} h ⥤ CochainComplex (ModuleCat.{max uP uM} R) ℤ where
  obj M := m.twistedCochainComplex M.differential M.isDGRightModule
  map {M N} f := m.twistedCochainComplexMap M.isDGRightModule N.isDGRightModule f
  map_id M := m.twistedCochainComplexMap_id M.isDGRightModule
  map_comp f g := m.twistedCochainComplexMap_comp _ _ _ f g

@[simp]
theorem twistedCochainComplexFunctor_obj (M : DGRightModuleCat.{uR, uA, uM} h) :
    (m.twistedCochainComplexFunctor h).obj M =
      m.twistedCochainComplex M.differential M.isDGRightModule :=
  (rfl)

@[simp]
theorem twistedCochainComplexFunctor_map (f : M ⟶ N) :
    (m.twistedCochainComplexFunctor h).map f =
      m.twistedCochainComplexMap M.isDGRightModule N.isDGRightModule f :=
  (rfl)

/-- The isomorphism of twisted complexes induced by an isomorphism of coefficient modules, the image
of `e` under `twistedCochainComplexFunctor`, between the twisted complexes themselves. -/
noncomputable def twistedCochainComplexMapIso (e : M ≅ N) :
    m.twistedCochainComplex M.differential M.isDGRightModule ≅
      m.twistedCochainComplex N.differential N.isDGRightModule :=
  (m.twistedCochainComplexFunctor h).mapIso e

@[simp]
theorem twistedCochainComplexMapIso_hom (e : M ≅ N) :
    (m.twistedCochainComplexMapIso e).hom =
      m.twistedCochainComplexMap M.isDGRightModule N.isDGRightModule e.hom :=
  (rfl)

@[simp]
theorem twistedCochainComplexMapIso_inv (e : M ≅ N) :
    (m.twistedCochainComplexMapIso e).inv =
      m.twistedCochainComplexMap N.isDGRightModule M.isDGRightModule e.inv :=
  (rfl)

end TwistingCocycle

end TauCeti
