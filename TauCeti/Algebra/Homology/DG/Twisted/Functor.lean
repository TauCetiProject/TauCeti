/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.Category
public import TauCeti.Algebra.Homology.DG.Twisted.Complex
-- The induced map is `gradedCochainComplexHom`, so this file needs the definition of the twisted
-- complex as a graded cochain complex, not only its API.
import all TauCeti.Algebra.Homology.DG.Twisted.Complex

/-!
# The twisted complex as a functor of the coefficient module

Let `m` be a twisting cocycle on a finite set `P` of generators graded by `ind`, with values in a
differential graded algebra `A`. The twisted complex `M ⊗ ⟨P⟩`
(`TauCeti.TwistingCocycle.twistedCochainComplex`) is functorial in the DG right module `M`: a
morphism `f : M ⟶ N` acts on `M ⊗ ⟨P⟩ = P → M` coefficientwise. Applied coefficientwise, `f`
preserves the total degree (`TauCeti.comp_mem_twistedTotalGrading`) and commutes with the twisted
differential of any matrix (`TauCeti.twistedDifferential_comp`), so it induces a cochain map
through `TauCeti.gradedCochainComplexHom`.

## Main definitions

* `TauCeti.TwistingCocycle.twistedCochainComplexMap`: the map of twisted complexes induced by a
  morphism of coefficient modules.
* `TauCeti.TwistingCocycle.twistedCochainComplexFunctor`: the twisted complex as a functor of the
  coefficient module.
* `TauCeti.TwistingCocycle.twistedCochainComplexMapIso`: the isomorphism of twisted complexes
  induced by an isomorphism of coefficient modules.

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

section Coefficients

variable {M N : DGRightModuleCat.{uR, uA, uM} h}

/-- A morphism of coefficient modules, applied coefficientwise, preserves the total degree. -/
theorem comp_mem_twistedTotalGrading (f : M ⟶ N) {k : ℤ} {g : P → M}
    (hg : g ∈ twistedTotalGrading M.grading ind k) :
    (fun x ↦ f (g x)) ∈ twistedTotalGrading N.grading ind k :=
  mem_twistedTotalGrading_iff.2 fun x ↦ f.map_mem' (mem_twistedTotalGrading_iff.1 hg x)

/-- A morphism of coefficient modules, applied coefficientwise, commutes with the twisted
differentials of any matrix. -/
theorem twistedDifferential_comp [Fintype P] (m : P → P → A) (f : M ⟶ N) (g : P → M) :
    twistedDifferential m N.grading N.differential (fun x ↦ f (g x)) =
      fun y ↦ f (twistedDifferential m M.grading M.differential g y) := by
  funext y
  simp only [twistedDifferential_apply, map_add, map_sum, DGRightModuleCat.map_d]
  congr 1
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← DGRightModuleHom.map_koszulTwist f, map_smul]

end Coefficients

namespace TwistingCocycle

variable [Fintype P] (m : TwistingCocycle 𝒜 d P ind) {M N Q : DGRightModuleCat.{uR, uA, uM} h}

/-- **The map of twisted complexes induced by a morphism of coefficient modules** `f : M ⟶ N`:
on `M ⊗ ⟨P⟩ = P → M` it applies `f` to the coefficient of each generator. -/
noncomputable def twistedCochainComplexMap (f : M ⟶ N) :
    m.twistedCochainComplex M.differential M.isDGRightModule ⟶
      m.twistedCochainComplex N.differential N.isDGRightModule :=
  gradedCochainComplexHom (LinearMap.compLeft (f.toLinearMap.restrictScalars R) P)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hg ↦ by
      rw [add_zero]
      exact comp_mem_twistedTotalGrading f hg)
    fun _ g ↦ twistedDifferential_comp m.m f g

/-- The map induced by `f` applies `f` to the coefficient of each generator. -/
@[simp]
theorem twistedCochainComplexXEquiv_twistedCochainComplexMap_f_apply (f : M ⟶ N) (k : ℤ)
    (g : (m.twistedCochainComplex M.differential M.isDGRightModule).X k) (x : P) :
    (twistedCochainComplexXEquiv m.mem_graded m.twisting N.isDGRightModule k
        (((m.twistedCochainComplexMap f).f k).hom g) : P → N) x =
      f ((twistedCochainComplexXEquiv m.mem_graded m.twisting M.isDGRightModule k g : P → M) x) :=
  congrFun (gradedCochainComplexXEquiv_gradedCochainComplexHom_f_apply _ _ _ k g) x

/-- The identity of the coefficient module induces the identity of the twisted complex. -/
@[simp]
theorem twistedCochainComplexMap_id :
    m.twistedCochainComplexMap (𝟙 M) = 𝟙 _ := by
  refine Eq.trans ?_ gradedCochainComplexHom_id
  unfold twistedCochainComplexMap
  congr 1
  ext
  exact DGRightModuleCat.id_apply M _

/-- The map induced by a composite is the composite of the induced maps. -/
@[simp]
theorem twistedCochainComplexMap_comp (f : M ⟶ N) (g : N ⟶ Q) :
    m.twistedCochainComplexMap (f ≫ g) =
      m.twistedCochainComplexMap f ≫ m.twistedCochainComplexMap g := by
  unfold twistedCochainComplexMap
  refine Eq.trans ?_ (gradedCochainComplexHom_comp _ _ _ _ _ _)
  congr 1
  ext
  exact DGRightModuleCat.comp_apply f g _

variable (h) in
/-- **The twisted complex as a functor of the coefficient module**: `M ↦ M ⊗ ⟨P⟩`. Its body is
exposed so that its objects are the twisted complexes. -/
@[expose] noncomputable def twistedCochainComplexFunctor :
    DGRightModuleCat.{uR, uA, uM} h ⥤ CochainComplex (ModuleCat.{max uP uM} R) ℤ where
  obj M := m.twistedCochainComplex M.differential M.isDGRightModule
  map f := m.twistedCochainComplexMap f

@[simp]
theorem twistedCochainComplexFunctor_obj (M : DGRightModuleCat.{uR, uA, uM} h) :
    (m.twistedCochainComplexFunctor h).obj M =
      m.twistedCochainComplex M.differential M.isDGRightModule :=
  (rfl)

@[simp]
theorem twistedCochainComplexFunctor_map (f : M ⟶ N) :
    (m.twistedCochainComplexFunctor h).map f = m.twistedCochainComplexMap f :=
  (rfl)

/-- The isomorphism of twisted complexes induced by an isomorphism of coefficient modules, the image
of `e` under `twistedCochainComplexFunctor`, between the twisted complexes themselves. -/
noncomputable def twistedCochainComplexMapIso (e : M ≅ N) :
    m.twistedCochainComplex M.differential M.isDGRightModule ≅
      m.twistedCochainComplex N.differential N.isDGRightModule :=
  (m.twistedCochainComplexFunctor h).mapIso e

@[simp]
theorem twistedCochainComplexMapIso_hom (e : M ≅ N) :
    (m.twistedCochainComplexMapIso e).hom = m.twistedCochainComplexMap e.hom :=
  (rfl)

@[simp]
theorem twistedCochainComplexMapIso_inv (e : M ≅ N) :
    (m.twistedCochainComplexMapIso e).inv = m.twistedCochainComplexMap e.inv :=
  (rfl)

end TwistingCocycle

end TauCeti
