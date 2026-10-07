/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.LinearAlgebra.SymmetricAlgebra.FiniteType
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading

/-!
# The projective spectrum of a finite module

The coefficient morphism `Proj(Sym M) ⟶ Spec R` is proper when `M` is a finite
`R`-module, even when `M` is not free or projective. Over a Noetherian coefficient ring,
its source is a Noetherian scheme. These are the finiteness properties needed to apply
Chevalley's theorem to projective orbit morphisms.

The convention is that `M` consists of homogeneous linear coordinates. For the space of
lines in a finite locally free representation `V`, use `M = V∨`.

`SymmetricAlgebra.projToSpec` is the structural morphism over `R`. Its properness and
quasi-compactness instances require only `Module.Finite R M`; its Noetherianity instance
also requires `IsNoetherianRing R`. The chart formula describes this morphism on the
standard affine charts. Its source is Jacobson whenever `Spec R` is Jacobson.

## References

* Stacks Project, §27.8, the projective spectrum of a graded ring.
* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f, projective orbits.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.SymmetricAlgebra

universe u

variable (R : Type u) (M : Type u) [CommRing R] [AddCommMonoid M] [Module R M]

/-- The structural morphism from the projective spectrum of a symmetric algebra to the
spectrum of its coefficient ring. -/
noncomputable def projToSpec : Proj (homogeneousSubmodule R M) ⟶ Spec (.of R) :=
  Proj.toSpecZero (homogeneousSubmodule R M) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (homogeneousSubmodule R M 0)))

/-- The coefficient morphism is `Proj.toSpecZero` followed by the scalar identification. -/
theorem projToSpec_def :
    projToSpec R M = Proj.toSpecZero (homogeneousSubmodule R M) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (homogeneousSubmodule R M 0))) :=
  (rfl)

private theorem isIso_scalarSpecMap :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap R (homogeneousSubmodule R M 0)))) := by
  have h : Function.Bijective (algebraMap R (homogeneousSubmodule R M 0)) := by
    have h_eq : ⇑(homogeneousSubmoduleZeroEquiv R M).symm =
        algebraMap R (homogeneousSubmodule R M 0) := by
      funext r
      apply Subtype.ext
      simpa only [SetLike.GradeZero.coe_algebraMap] using
        coe_homogeneousSubmoduleZeroEquiv_symm_apply R M r
    rw [← h_eq]
    exact (homogeneousSubmoduleZeroEquiv R M).symm.bijective
  have : IsIso (CommRingCat.ofHom (algebraMap R (homogeneousSubmodule R M 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h
  infer_instance

/-- On a standard affine chart, the coefficient morphism comes from the inclusion of
scalars into the homogeneous localization. -/
@[reassoc (attr := simp)]
theorem awayι_projToSpec {f : SymmetricAlgebra R M} {n : ℕ}
    (hf : f ∈ homogeneousSubmodule R M n) (hn : 0 < n) :
    Proj.awayι (homogeneousSubmodule R M) f hf hn ≫ projToSpec R M =
      Spec.map (CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule R M)
          (Submonoid.powers f)).comp (algebraMap R (homogeneousSubmodule R M 0)))) := by
  rw [projToSpec_def, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rw [← CommRingCat.ofHom_comp]

/-- The projective spectrum of a finite module is proper over the coefficient ring.
Freeness and projectivity are not required. -/
instance instIsProperProjToSpec [Module.Finite R M] : IsProper (projToSpec R M) := by
  -- Use Mathlib's properness theorem for `Proj.toSpecZero` and the degree-zero equivalence.
  have := isIso_scalarSpecMap R M
  rw [projToSpec_def]
  infer_instance

/-- The projective spectrum of a finite module is quasi-compact, over any coefficient ring. -/
instance instCompactSpaceProj [Module.Finite R M] :
    CompactSpace (Proj (homogeneousSubmodule R M)) :=
  QuasiCompact.compactSpace_of_compactSpace (projToSpec R M)

/-- Over a Noetherian ring, the projective spectrum of a finite module is Noetherian. -/
instance instIsNoetherianProj [Module.Finite R M] [IsNoetherianRing R] :
    IsNoetherian (Proj (homogeneousSubmodule R M)) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (projToSpec R M)
  toCompactSpace := inferInstance

/-- The projective spectrum of a finite module over a Jacobson spectrum is Jacobson. -/
instance instJacobsonSpaceProj [Module.Finite R M] [JacobsonSpace (Spec (.of R))] :
    JacobsonSpace (Proj (homogeneousSubmodule R M)) :=
  LocallyOfFiniteType.jacobsonSpace (projToSpec R M)

end TauCeti.SymmetricAlgebra
