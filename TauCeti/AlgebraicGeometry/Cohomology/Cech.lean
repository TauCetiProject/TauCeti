/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
public import TauCeti.Topology.Sheaves.Leray

/-!
# Čech cohomology of quasi-coherent sheaves for affine covers

Let `X` be a locally Noetherian scheme with affine diagonal, for instance a separated Noetherian
scheme, and let `M` be a quasi-coherent sheaf of modules on `X`. Finite intersections of affine
opens of `X` are then affine, and `M` has no cohomology in positive degrees on them. So every
finite affine open cover `U` of `X` is a Leray cover for `M`, and by Leray's theorem
(`TauCeti.Topology.nonempty_homology_cechComplex_iso_H`) the Čech cohomology `Hⁿ(U, M)` of the
underlying abelian sheaf of `M` is isomorphic to the cohomology `Hⁿ(X, M)`, so that `Hⁿ(X, M)` can
be computed, as an abelian group, from the Čech complex of any finite affine open cover. The
isomorphism is one of abelian groups, and is not claimed to be natural in `M`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.nonempty_homology_cechComplex_iso_cohomology`: for a finite
  affine open cover `U` of `X`, `Hⁿ(U, M) ≅ Hⁿ(X, M)` for every `n`.

## References

* R. Hartshorne, *Algebraic Geometry*, Theorem III.4.5.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

/-- **Čech cohomology computes the cohomology of a quasi-coherent sheaf.** Let `X` be a locally
Noetherian scheme with affine diagonal (for instance a separated one), `M` a quasi-coherent sheaf
of modules on `X`, and `U` a finite family of affine opens covering `X`. Then the Čech cohomology
`Hⁿ(U, M)` of the underlying abelian sheaf of `M` is isomorphic to `Hⁿ(X, M)`, for every `n`. -/
theorem nonempty_homology_cechComplex_iso_cohomology [IsLocallyNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] [M.IsQuasicoherent] {ι : Type u}
    [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcover : ⨆ i, U i = ⊤)
    (n : ℕ) :
    Nonempty (((cechComplexFunctor U).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj).homology n ≅
      AddCommGrpCat.of (Cohomology M n)) := by
  refine TauCeti.Topology.nonempty_homology_cechComplex_iso_H U hcover _ (fun s hs k ↦ ?_) n
  -- a nonempty finite intersection of affine opens is affine, with Noetherian ring of sections
  have hW : IsAffineOpen (s.inf U) := by
    rw [Finset.inf_eq_iInf]
    exact IsAffineOpen.biInf _ s.finite_toSet hs fun j _ ↦ hU j
  have : IsNoetherianRing Γ(X, s.inf U) := IsLocallyNoetherian.component_noetherian ⟨_, hW⟩
  exact subsingleton_cohomologyOn_succ_of_isAffineOpen M hW k

end AlgebraicGeometry.Scheme.Modules
