/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
public import TauCeti.Topology.Sheaves.Leray

/-!
# Čech cohomology of quasi-coherent sheaves for affine covers

Let `X` be a locally Noetherian scheme with affine diagonal, for instance a separated Noetherian
scheme, and let `M` be a quasi-coherent sheaf of modules on `X`. Finite intersections of affine
opens of `X` are then affine, and `M` has no cohomology in positive degrees on them. So every
finite affine open cover `U` of `X` is a Leray cover for `M`, and by Leray's theorem
(`TauCeti.Topology.homologyCechComplexIsoH`) the Čech cohomology `Hⁿ(U, M)` of the underlying
abelian sheaf of `M` is isomorphic to the cohomology `Hⁿ(X, M)`, so that `Hⁿ(X, M)` can be
computed from the Čech complex of any finite affine open cover.

The isomorphism is natural in the quasi-coherent sheaf `M`. In particular it intertwines the map
on Čech cohomology induced by multiplication by a global function `r` on `M` with the action of
`r` on `Hⁿ(X, M)` (`Scheme.Modules.cohomologyModule`), so it is compatible with the module
structures of both sides over the ring of global functions, and hence over any base ring.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.homologyCechComplexIsoCohomology`: for a finite affine open
  cover `U` of `X`, `Hⁿ(U, M) ≅ Hⁿ(X, M)` for every `n`;
* `AlgebraicGeometry.Scheme.Modules.homologyMap_comp_homologyCechComplexIsoCohomology_hom`: its
  naturality in `M`;
* `AlgebraicGeometry.Scheme.Modules.homologyCechComplexIsoCohomology_hom_globalSectionsSmul`: its
  compatibility with the action of global functions.

## References

* R. Hartshorne, *Algebraic Geometry*, Theorem III.4.5.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  [IsAffineHom (pullback.diagonal (terminal.from X))] {ι : Type u} (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i))

include hU in
/-- On a locally Noetherian scheme with affine diagonal, a quasi-coherent sheaf has no cohomology
in positive degrees on a nonempty finite intersection of affine opens. -/
private lemma subsingleton_cohomologyOn_inf_succ (M : X.Modules) [M.IsQuasicoherent]
    (s : Finset ι) (hs : s.Nonempty) (k : ℕ) : Subsingleton (cohomologyOn M (k + 1) (s.inf U)) := by
  -- a nonempty finite intersection of affine opens is affine, with Noetherian ring of sections
  have hW : IsAffineOpen (s.inf U) := by
    rw [Finset.inf_eq_iInf]
    exact IsAffineOpen.biInf _ s.finite_toSet hs fun j _ ↦ hU j
  have : IsNoetherianRing Γ(X, s.inf U) := IsLocallyNoetherian.component_noetherian ⟨_, hW⟩
  exact subsingleton_cohomologyOn_succ_of_isAffineOpen M hW k

variable [Finite ι] (hcover : ⨆ i, U i = ⊤)

/-- **Čech cohomology computes the cohomology of a quasi-coherent sheaf.** Let `X` be a locally
Noetherian scheme with affine diagonal (for instance a separated one), `M` a quasi-coherent sheaf
of modules on `X`, and `U` a finite family of affine opens covering `X`. Then the Čech cohomology
`Hⁿ(U, M)` of the underlying abelian sheaf of `M` is isomorphic to `Hⁿ(X, M)`, for every `n`,
naturally in `M` (`homologyMap_comp_homologyCechComplexIsoCohomology_hom`). -/
def homologyCechComplexIsoCohomology (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    ((cechComplexFunctor U).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj).homology n ≅
      AddCommGrpCat.of (Cohomology M n) :=
  TauCeti.Topology.homologyCechComplexIsoH U hcover _
    (subsingleton_cohomologyOn_inf_succ U hU M) n

/-- The comparison of Čech cohomology for a finite affine cover with the cohomology of a
quasi-coherent sheaf is natural in the sheaf. -/
@[reassoc]
theorem homologyMap_comp_homologyCechComplexIsoCohomology_hom {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map ((SheafOfModules.toSheaf X.ringCatSheaf).map f).hom) n ≫
        (homologyCechComplexIsoCohomology U hU hcover N n).hom =
      (homologyCechComplexIsoCohomology U hU hcover M n).hom ≫ (cohomologyFunctor X n).map f :=
  TauCeti.Topology.homologyMap_comp_homologyCechComplexIsoH_hom U hcover _ _ _ n

/-- The comparison of Čech cohomology for a finite affine cover with the cohomology of a
quasi-coherent sheaf `M` is linear over the global functions: it carries the map on Čech
cohomology induced by multiplication by `r` on `M` to scalar multiplication by `r` on
`Hⁿ(X, M)`. -/
theorem homologyCechComplexIsoCohomology_hom_globalSectionsSmul (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) (r : Γ(X, ⊤))
    (x : ((cechComplexFunctor U).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj).homology n) :
    (homologyCechComplexIsoCohomology U hU hcover M n).hom
        (HomologicalComplex.homologyMap ((cechComplexFunctor U).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map (M.globalSectionsSmul r)).hom) n x) =
      r • (homologyCechComplexIsoCohomology U hU hcover M n).hom x := by
  rw [cohomology_smul]
  exact ConcreteCategory.congr_hom
    (homologyMap_comp_homologyCechComplexIsoCohomology_hom U hU hcover (M.globalSectionsSmul r) n) x

end AlgebraicGeometry.Scheme.Modules
