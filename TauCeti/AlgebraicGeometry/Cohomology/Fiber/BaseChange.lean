/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.FlatBaseChange
public import TauCeti.AlgebraicGeometry.Fibers.BaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Cohomology of fibres under arbitrary base change

The residue-field fibre of a base-changed family is the extension of the original fibre
along the induced map of residue fields. Thus its quasi-coherent cohomology is the scalar
extension of the original fibre cohomology, in every degree. The base change of the family
need not be flat. Quasi-compactness and quasi-separatedness suffice for the family.

The comparison uses the existing scheme-module cohomology and its canonical residue-field
actions. It does not assert the higher-direct-image sheaf base-change theorem.

## References

* The Stacks Project, Lemma 30.5.2 (tag 02KH).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Scheme.Modules TensorProduct
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
  {g : S' ⟶ S} {g' : X' ⟶ X}

namespace AlgebraicGeometry.Scheme.Modules

/-- The natural-valued finrank of cohomology on a scheme-theoretic fibre. It is zero for
cohomology that is not finite-dimensional, and agrees with its usual dimension when it is
finite-dimensional. -/
def fiberCohomologyFinrank (M : X.Modules) (f : X ⟶ S) (n : ℕ) (s : S) : ℕ :=
  letI := f.fiberOverSpecResidueField s
  Module.finrank (S.residueField s)
    (Cohomology ((Scheme.Modules.pullback (f.fiberι s)).obj M) n)

/-- The fibre cohomology finrank uses the canonical residue-field action on the pulled-back
sheaf. -/
theorem fiberCohomologyFinrank_def (M : X.Modules) (f : X ⟶ S) (n : ℕ) (s : S) :
    fiberCohomologyFinrank M f n s =
      letI := f.fiberOverSpecResidueField s
      Module.finrank (S.residueField s)
        (Cohomology ((Scheme.Modules.pullback (f.fiberι s)).obj M) n) := by rfl

end AlgebraicGeometry.Scheme.Modules

namespace CategoryTheory.CommSq

/-- Pulling the coefficient sheaf to the new fibre in either order gives the same sheaf. -/
def fiberBaseChangeCoefficientIso (H : CommSq g' f' f g) (M : X.Modules) (s' : S') :
    (Scheme.Modules.pullback (fiberBaseChangeMap H s')).obj
        ((Scheme.Modules.pullback (f.fiberι (g s'))).obj M) ≅
      (Scheme.Modules.pullback (f'.fiberι s')).obj ((Scheme.Modules.pullback g').obj M) :=
  (pullbackComp _ _).app M ≪≫
    (pullbackCongr (fiberBaseChangeMap_comp_fiberι H s')).app M ≪≫
    ((pullbackComp _ _).app M).symm

/-- The coefficient comparison is the composite of pullback composition and congruence maps. -/
theorem fiberBaseChangeCoefficientIso_hom (H : CommSq g' f' f g) (M : X.Modules) (s' : S') :
    (fiberBaseChangeCoefficientIso H M s').hom =
      ((pullbackComp (fiberBaseChangeMap H s') (f.fiberι (g s'))).app M).hom ≫
        ((pullbackCongr (fiberBaseChangeMap_comp_fiberι H s')).app M).hom ≫
        ((pullbackComp (f'.fiberι s') g').app M).inv := by rfl

end CategoryTheory.CommSq

namespace CategoryTheory.IsPullback

/-- **Fibre cohomology under arbitrary base change.** The canonical scalar extension of
`Hⁿ(X_s, M_s)` is `Hⁿ(X'_{s'}, (g'^* M)_{s'})`. The base map `g` need not be flat. -/
def fiberCohomologyBaseChangeLinearEquiv (H : IsPullback g' f' f g)
    (M : X.Modules) (n : ℕ) (s' : S')
    [CompactSpace (f.fiber (g s'))] [QuasiSeparatedSpace (f.fiber (g s'))]
    [((Scheme.Modules.pullback (f.fiberι (g s'))).obj M).IsQuasicoherent] :
    letI := f.fiberOverSpecResidueField (g s')
    letI := f'.fiberOverSpecResidueField s'
    letI : Algebra (S.residueField (g s')) (S'.residueField s') :=
      (g.residueFieldMap s').hom.toAlgebra
    S'.residueField s' ⊗[S.residueField (g s')]
        Cohomology ((Scheme.Modules.pullback (f.fiberι (g s'))).obj M) n ≃ₗ[S'.residueField s']
      Cohomology ((Scheme.Modules.pullback (f'.fiberι s')).obj
        ((Scheme.Modules.pullback g').obj M)) n := by
  letI := f.fiberOverSpecResidueField (g s')
  letI := f'.fiberOverSpecResidueField s'
  letI : Algebra (S.residueField (g s')) (S'.residueField s') :=
    (g.residueFieldMap s').hom.toAlgebra
  exact (cohomologyBaseChangeLinearEquiv
    (R := S.residueField (g s')) (R' := S'.residueField s')
    (by rw [CategoryTheory.CommSq.fiberBaseChangeMap_def];
        exact isPullback_fiberToSpecResidueField_of_isPullback H s')
    ((Scheme.Modules.pullback (f.fiberι (g s'))).obj M) n).trans
      (cohomologyBaseLinearEquivOfIso (S'.residueField s')
        (CategoryTheory.CommSq.fiberBaseChangeCoefficientIso H.toCommSq M s') n)

/-- The fibre cohomology comparison sends a pure tensor to the scalar multiple of pullback,
transported through the canonical identification of the two coefficient pullbacks. -/
@[simp]
lemma fiberCohomologyBaseChangeLinearEquiv_tmul (H : IsPullback g' f' f g)
    (M : X.Modules) (n : ℕ) (s' : S')
    [CompactSpace (f.fiber (g s'))] [QuasiSeparatedSpace (f.fiber (g s'))]
    [((Scheme.Modules.pullback (f.fiberι (g s'))).obj M).IsQuasicoherent] :
    letI := f.fiberOverSpecResidueField (g s')
    letI := f'.fiberOverSpecResidueField s'
    letI : Algebra (S.residueField (g s')) (S'.residueField s') :=
      (g.residueFieldMap s').hom.toAlgebra
    ∀ (r' : S'.residueField s')
      (x : Cohomology ((Scheme.Modules.pullback (f.fiberι (g s'))).obj M) n),
      fiberCohomologyBaseChangeLinearEquiv H M n s' (r' ⊗ₜ x) =
        r' • cohomologyMapBaseLinear (S'.residueField s') (f'.fiber s')
          (CategoryTheory.CommSq.fiberBaseChangeCoefficientIso H.toCommSq M s').hom n
            ((CategoryTheory.CommSq.fiberBaseChangeMap H.toCommSq s').cohomologyPullback
              ((Scheme.Modules.pullback (f.fiberι (g s'))).obj M) n x) := by
  let := f.fiberOverSpecResidueField (g s')
  let := f'.fiberOverSpecResidueField s'
  let : Algebra (S.residueField (g s')) (S'.residueField s') :=
    (g.residueFieldMap s').hom.toAlgebra
  intro r' x
  simp only [fiberCohomologyBaseChangeLinearEquiv, LinearEquiv.trans_apply,
    cohomologyBaseChangeLinearEquiv_tmul, cohomologyBaseLinearEquivOfIso_apply]
  exact (cohomologyMapBaseLinear _ _ _ n).map_smul r' _

/-- Fibre cohomology finranks are invariant under arbitrary base change. When the two cohomology
modules are finite-dimensional, this is the corresponding equality of dimensions; otherwise
`Module.finrank` uses its zero convention. -/
theorem fiberCohomologyFinrank_baseChange (H : IsPullback g' f' f g)
    (M : X.Modules) (n : ℕ) (s' : S')
    [CompactSpace (f.fiber (g s'))] [QuasiSeparatedSpace (f.fiber (g s'))]
    [((Scheme.Modules.pullback (f.fiberι (g s'))).obj M).IsQuasicoherent] :
    fiberCohomologyFinrank ((Scheme.Modules.pullback g').obj M) f' n s' =
      fiberCohomologyFinrank M f n (g s') := by
  let := f.fiberOverSpecResidueField (g s')
  let := f'.fiberOverSpecResidueField s'
  let : Algebra (S.residueField (g s')) (S'.residueField s') :=
    (g.residueFieldMap s').hom.toAlgebra
  rw [AlgebraicGeometry.Scheme.Modules.fiberCohomologyFinrank_def,
    AlgebraicGeometry.Scheme.Modules.fiberCohomologyFinrank_def,
    ← (fiberCohomologyBaseChangeLinearEquiv H M n s').finrank_eq,
    Module.finrank_baseChange]

/-- Vanishing of fibre cohomology can be checked after any extension of the base point.
In particular, passing from a residue-field fibre to a geometric fibre detects vanishing. This
statement is independent of the finrank zero convention for infinite-dimensional modules. -/
theorem subsingleton_cohomology_fiber_baseChange_iff (H : IsPullback g' f' f g)
    (M : X.Modules) (n : ℕ) (s' : S')
    [CompactSpace (f.fiber (g s'))] [QuasiSeparatedSpace (f.fiber (g s'))]
    [((Scheme.Modules.pullback (f.fiberι (g s'))).obj M).IsQuasicoherent] :
    Subsingleton (Cohomology ((Scheme.Modules.pullback (f'.fiberι s')).obj
        ((Scheme.Modules.pullback g').obj M)) n) ↔
      Subsingleton (Cohomology ((Scheme.Modules.pullback (f.fiberι (g s'))).obj M) n) := by
  let := f.fiberOverSpecResidueField (g s')
  let := f'.fiberOverSpecResidueField s'
  let : Algebra (S.residueField (g s')) (S'.residueField s') :=
    (g.residueFieldMap s').hom.toAlgebra
  rw [← (fiberCohomologyBaseChangeLinearEquiv H M n s').toEquiv.subsingleton_congr]
  exact Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right _ _

end CategoryTheory.IsPullback
