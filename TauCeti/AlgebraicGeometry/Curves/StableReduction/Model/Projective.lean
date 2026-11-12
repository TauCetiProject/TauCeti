/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Closure
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.LinearAction
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricBaseChange

/-!
# Projective models by closure in projective space

Let `R` be a discrete valuation ring with fraction field `K`, let `M` be a finite `R`-module, and
let `C` be a closed subscheme of the projective space `ℙ(K ⊗[R] M) = Proj (Sym_K (K ⊗[R] M))`
over `K`. Since `ℙ(K ⊗[R] M)` is the generic fibre of `ℙ(M) = Proj (Sym_R M)` over `R`, the
scheme-theoretic closure of `C` in `ℙ(M)` is a model of `C` over `R`; it is proper because
`ℙ(M)` is proper over `R`. The convention is that of `TauCeti.SymmetricAlgebra.projToSpec`:
`M` is the module of linear homogeneous coordinates, so `M = R^{N+1}` gives `ℙᴺ_R`.

Every finite-dimensional `K`-vector space of coordinates is `K ⊗[R] R^n` for `n` its dimension.
Consequently a scheme `C` over `K` with a closed immersion into some projective space over `K`,
for instance a projective curve, has a proper model over `R`, embedded as a closed subscheme of
`ℙ^{n-1}_R`. This model is the starting point for regular and minimal models.

## Main definitions

* `TauCeti.Model.projectiveClosure`: the closure of `C ⊆ ℙ(K ⊗[R] M)` in `ℙ(M)`, as a model.
* `TauCeti.Model.projectiveClosureι`: its closed immersion into `ℙ(M)`.

## Main results

* `TauCeti.Model.genericι_projectiveClosureι`: on generic fibres, the closure restricts to the
  given embedding of `C`.
* `TauCeti.Model.isProper_projectiveClosure`: the closure is a proper model.
* `TauCeti.Model.exists_isClosedImmersion_isProper`: a closed subscheme of a projective space
  over `K` has a proper model over `R` which is a closed subscheme of a projective space over `R`.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002,
  Section 10.1: models of curves, in particular those obtained by closure in `ℙᴺ_R`.
-/

public section

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry TauCeti.SymmetricAlgebra
open scoped TensorProduct

namespace TauCeti

universe u

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}
variable (M : Type u) [AddCommMonoid M] [Module R M] [Module.Finite R M]
variable (j : C ⟶ Proj (homogeneousSubmodule K (K ⊗[R] M))) [IsClosedImmersion j]
  (hj : j ≫ projToSpec K (K ⊗[R] M) = toK)

/-- The scheme-theoretic closure in `ℙ(M) = Proj (Sym_R M)` of a closed subscheme `C` of its
generic fibre `ℙ(K ⊗[R] M)`, as a model of `C` over `R`. -/
def projectiveClosure : Model R K C toK :=
  closure (toR := projToSpec R M)
    (j ≫ (Proj.isPullback_symmetricAlgebra_baseChange R K M).isoPullback.hom) (by
      rw [genericFiber_hom, Category.assoc, IsPullback.isoPullback_hom_snd]
      exact hj)

/-- The closed immersion of the closure model of `C` into `ℙ(M)`. -/
def projectiveClosureι : (projectiveClosure M j hj).total ⟶ Proj (homogeneousSubmodule R M) :=
  closureι _ _

instance : IsClosedImmersion (projectiveClosureι M j hj) :=
  inferInstanceAs (IsClosedImmersion (closureι _ _))

/-- The structure morphism of the closure model is the restriction of that of `ℙ(M)`. -/
@[reassoc (attr := simp)]
lemma projectiveClosureι_projToSpec :
    projectiveClosureι M j hj ≫ projToSpec R M = (projectiveClosure M j hj).toBase :=
  closureι_toBase _ _

/-- On generic fibres, the inclusion of the closure model into `ℙ(M)` restricts to the given
embedding of `C` into `ℙ(K ⊗[R] M)`, followed by the projection `ℙ(K ⊗[R] M) ⟶ ℙ(M)`. -/
@[reassoc (attr := simp)]
lemma genericι_projectiveClosureι :
    (projectiveClosure M j hj).genericι ≫ projectiveClosureι M j hj =
      j ≫ (Proj.symmetricAlgebraScalarTensorIso R K M).hom ≫
        Proj.baseChangeProjection (homogeneousSubmodule R M) K := by
  refine (genericι_closureι (toR := projToSpec R M) _ _).trans ?_
  rw [Category.assoc, IsPullback.isoPullback_hom_fst]

/-- The closure model is the scheme-theoretic image of `C` in `ℙ(M)`: its ideal sheaf is the
kernel of `C ⟶ ℙ(K ⊗[R] M) ⟶ ℙ(M)`. -/
@[simp]
lemma ker_projectiveClosureι :
    (projectiveClosureι M j hj).ker =
      (j ≫ (Proj.symmetricAlgebraScalarTensorIso R K M).hom ≫
        Proj.baseChangeProjection (homogeneousSubmodule R M) K).ker := by
  refine (ker_closureι (toR := projToSpec R M) _ _).trans ?_
  rw [Category.assoc, IsPullback.isoPullback_hom_fst]

/-- The closure of `C` in `ℙ(M)` is a proper model of `C`. -/
lemma isProper_projectiveClosure : (projectiveClosure M j hj).IsProper :=
  isProper_closure (toR := projToSpec R M) _ _

/-- A closed subscheme `C` of a projective space `ℙ(V)` over `K`, with `V` a finite-dimensional
`K`-vector space of linear coordinates, has a proper model over `R` which is a closed subscheme of
the projective space `ℙ(R^n)` over `R`, with `n = dim V`. -/
theorem exists_isClosedImmersion_isProper (V : Type u) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (j : C ⟶ Proj (homogeneousSubmodule K V)) [IsClosedImmersion j]
    (hj : j ≫ projToSpec K V = toK) :
    ∃ (X : Model R K C toK)
      (ι : X.total ⟶ Proj (homogeneousSubmodule R (Fin (Module.finrank K V) → R))),
      IsClosedImmersion ι ∧ ι ≫ projToSpec R _ = X.toBase ∧ X.IsProper := by
  let e : (K ⊗[R] (Fin (Module.finrank K V) → R)) ≃ₗ[K] V :=
    TensorProduct.piScalarRight R K K _ ≪≫ₗ (Module.finBasis K V).equivFun.symm
  let j' := j ≫ (Proj.symmetricAlgebraMapIso K e).hom
  have hj' : j' ≫ projToSpec K _ = toK := by
    rw [Category.assoc, Proj.symmetricAlgebraMapIso_hom_projToSpec, hj]
  exact ⟨projectiveClosure _ j' hj', projectiveClosureι _ j' hj', inferInstance,
    projectiveClosureι_projToSpec _ j' hj', isProper_projectiveClosure _ j' hj'⟩

end Model

end TauCeti
