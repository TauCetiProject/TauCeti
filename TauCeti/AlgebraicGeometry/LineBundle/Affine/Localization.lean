/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import TauCeti.RingTheory.PicardGroup.Localization

/-!
# Spreading a generator of an affine line bundle

Let `M` be an invertible module over `R`. If its localization at a submonoid `S` is free,
an element `m` of `M` is a basis of the associated sheaf on some principal open `D(s)`,
with `s ∈ S`. The same section is a basis on `D(t)` for every multiple `t` of `s`.
The localization where freeness is known may be any ring and module model.

The conclusion gives the actual scalar-to-section isomorphism on each principal open;
it does not require an affine Picard-group equivalence or a choice of a global trivialization.

## References

* The Stacks Project, Tags 01IB (modules on affine schemes) and 0AFW (invertible modules).
-/

public noncomputable section

open AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- A generator of a localized invertible module spreads to a basis section on a principal
open, and on every smaller principal open obtained by multiplying its defining equation. -/
theorem exists_mem_bijective_smul_tilde {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    [Module.Invertible R M] (S : Submonoid R)
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
    {N : Type*} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (g : M →ₗ[R] N) [IsLocalizedModule S g] [Module.Free A N] :
    ∃ s ∈ S, ∃ m : M, ∀ t, s ∣ t →
      let _ : Module Γ(Spec R, PrimeSpectrum.basicOpen t) Γ(tilde M, PrimeSpectrum.basicOpen t) :=
        ((tilde M).val.obj (.op (PrimeSpectrum.basicOpen t))).isModule
      Function.Bijective (LinearMap.toSpanSingleton Γ(Spec R, PrimeSpectrum.basicOpen t)
        Γ(tilde M, PrimeSpectrum.basicOpen t) (tilde.toOpen M (PrimeSpectrum.basicOpen t) m)) := by
  obtain ⟨s, hs, m, hm⟩ := Module.Invertible.exists_mem_bijective_smul M S A g
  refine ⟨s, hs, m, fun t ht ↦ ?_⟩
  let : Algebra R Γ(Spec R, PrimeSpectrum.basicOpen t) :=
    StructureSheaf.openAlgebra R (.op (PrimeSpectrum.basicOpen t))
  let mR : Module R Γ(tilde M, PrimeSpectrum.basicOpen t) :=
    ((modulesSpecToSheaf.obj (tilde M)).obj.obj (.op (PrimeSpectrum.basicOpen t))).isModule
  let mS : Module Γ(Spec R, PrimeSpectrum.basicOpen t) Γ(tilde M, PrimeSpectrum.basicOpen t) :=
    ((tilde M).val.obj (.op (PrimeSpectrum.basicOpen t))).isModule
  have : IsLocalization.Away t Γ(Spec R, PrimeSpectrum.basicOpen t) :=
    StructureSheaf.IsLocalization.to_basicOpen R t
  have : IsScalarTower R Γ(Spec R, PrimeSpectrum.basicOpen t)
      Γ(tilde M, PrimeSpectrum.basicOpen t) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have hloc : IsLocalizedModule.Away t (tilde.toOpen M (PrimeSpectrum.basicOpen t)).hom :=
    .of_linearEquiv (.powers t) (StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen t))
      ((tilde.modulesSpecToSheafIso M).app _).toLinearEquiv.symm
  exact (@LocalizedModule.bijective_map_toSpanSingleton_iff R M _ _ _ (.powers t)
    Γ(Spec R, PrimeSpectrum.basicOpen t) _ _ _ Γ(tilde M, PrimeSpectrum.basicOpen t) _ mR mS _
    (tilde.toOpen M (PrimeSpectrum.basicOpen t)).hom hloc m).mp
      (hm t ht)

end TauCeti.AlgebraicGeometry
