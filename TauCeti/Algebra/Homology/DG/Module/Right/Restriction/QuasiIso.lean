/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.QuasiIso
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.Cohomology
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.Functor

/-!
# Restriction of scalars preserves and reflects quasi-isomorphisms

Restriction along a DG algebra morphism changes the action, but not the underlying differential.
Consequently a restricted map is a quasi-isomorphism exactly when the original map is. This
allows restriction of scalars to descend to the localizations defining derived module categories.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.
-/

public section

open CategoryTheory

namespace TauCeti

universe uR uA uB uM uN

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

namespace DGRightModuleHom

variable {M : Type uM} {N : Type uN}
  [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M] [IsScalarTower R Bᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Bᵐᵒᵖ N] [IsScalarTower R Bᵐᵒᵖ N]
  {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece 𝒩]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N}
  {hM : IsDGRightModule hB ℳ dM} {hN : IsDGRightModule hB 𝒩 dN}

/-- Restriction of scalars preserves and reflects quasi-isomorphisms of DG right modules. -/
@[simp]
theorem isQuasiIso_restrictScalars_iff (f : DGAlgHom hA hB) (g : DGRightModuleHom hM hN) :
    (g.restrictScalars f).IsQuasiIso ↔ g.IsQuasiIso := by
  have he : (hN.restrictScalarsCohomologyEquiv f) ∘ (g.restrictScalars f).cohomologyMap =
      g.cohomologyMap ∘ (hM.restrictScalarsCohomologyEquiv f) :=
    funext (restrictScalarsCohomologyEquiv_cohomologyMap f hM g)
  rw [isQuasiIso_iff, isQuasiIso_iff,
    ← Function.Bijective.of_comp_iff' (hN.restrictScalarsCohomologyEquiv f).bijective, he,
    Function.Bijective.of_comp_iff _ (hM.restrictScalarsCohomologyEquiv f).bijective]

end DGRightModuleHom

namespace DGRightModuleCat

/-- The restriction functor preserves and reflects quasi-isomorphisms. -/
@[simp]
theorem isQuasiIso_restrictScalars_map_iff (f : DGAlgHom hA hB)
    {M N : DGRightModuleCat.{uR, uB, uM} hB} (g : M ⟶ N) :
    IsQuasiIso ((restrictScalars f).map g) ↔ IsQuasiIso g := by
  let g' : of (M.isDGRightModule.restrictScalars f) ⟶
      of (N.isDGRightModule.restrictScalars f) := g.restrictScalars f
  have e : Arrow.mk ((restrictScalars f).map g) ≅ Arrow.mk g' :=
    Arrow.isoMk (g := Arrow.mk g') (restrictScalarsObjIso f M) (restrictScalarsObjIso f N)
      (restrictScalarsObjIso_hom_naturality f g).symm
  rw [← quasiIsos_iff, (quasiIsos hA).arrow_mk_iso_iff e, quasiIsos_iff]
  exact DGRightModuleHom.isQuasiIso_restrictScalars_iff f g

end DGRightModuleCat

end TauCeti
