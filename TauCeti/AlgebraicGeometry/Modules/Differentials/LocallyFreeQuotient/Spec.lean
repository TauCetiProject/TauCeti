/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.LocallyFreeQuotient
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Spec
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic

/-!
# Locally free quotients of the differentials of an affine scheme

Let `A` be an algebra over a commutative ring `R`. Under `Ω_{Spec A/R} ≅ Ω[A⁄R]~`, an `A`-linear
map `g : Ω[A⁄R] → M` to an `A`-module `M` induces a morphism of sheaves `Ω_{Spec A/R} ⟶ M~`,
which is an epimorphism if `g` is surjective. For `M = A^d` this is an epimorphism onto a finite
locally free sheaf of constant rank `d`, so `Ω_{Spec A/R}` admits a locally free quotient of rank
`d`. This is the affine global case of
the stalk criterion for `HasLocallyFreeQuotientOfDifferentials`.

Since `M ↦ M~` is fully faithful, a morphism `M~ ⟶ N~` carrying the morphism induced by `g` to
the one induced by `h` comes from an `A`-linear map, so the kernel of `g` lies in the kernel of
`h`.

## Main declarations

* `TauCeti.AlgebraicGeometry.differentialsSpecToTilde`: the morphism `Ω_{Spec A/R} ⟶ M~`
  induced by an `A`-linear map `Ω[A⁄R] → M`;
* `TauCeti.AlgebraicGeometry.hasLocallyFreeQuotientOfDifferentials_Spec_of_surjective`: a
  surjective `A`-linear map `Ω[A⁄R] → A^d` gives a locally free quotient of rank `d` of
  `Ω_{Spec A/R}`;
* `TauCeti.AlgebraicGeometry.ker_le_ker_of_differentialsSpecToTilde_comp_eq`: if the morphism
  induced by `g` factors the one induced by `h`, then `ker g ≤ ker h`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (R : Type u) [CommRing R] (A : CommRingCat.{u}) [Algebra R A]
  {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- The morphism `Ω_{Spec A/R} ⟶ M~` induced by an `A`-linear map `g : Ω[A⁄R] → M` through
`Ω_{Spec A/R} ≅ Ω[A⁄R]~`. -/
def differentialsSpecToTilde (g : Ω[A⁄R] →ₗ[A] M) :
    (Spec A).relativeDifferentials R ⟶ tilde (.of A M) :=
  (relativeDifferentialsSpecIso R A).hom ≫ (tilde.functor A).map (ModuleCat.ofHom g)

/-- `differentialsSpecToTilde R A g` is `Ω_{Spec A/R} ≅ Ω[A⁄R]~` followed by `g~`. -/
lemma differentialsSpecToTilde_def (g : Ω[A⁄R] →ₗ[A] M) :
    differentialsSpecToTilde R A g =
      (relativeDifferentialsSpecIso R A).hom ≫ (tilde.functor A).map (ModuleCat.ofHom g) :=
  (rfl)

/-- The morphism induced by `g` sends the differential `d a` of `a ∈ A` to the section `g (D a)`
of `M~`. -/
lemma differentialsSpecToTilde_app_d (g : Ω[A⁄R] →ₗ[A] M)
    (U : (Spec A).Opens) (a : A) :
    (differentialsSpecToTilde R A g).val.app (.op U)
        (((Spec A).universalDerivation R).d
          (((Spec A).presheaf.map (homOfLE le_top).op).hom ((Scheme.ΓSpecIso A).inv.hom a))) =
      tilde.toOpen (ModuleCat.of A M) U (g (KaehlerDifferential.D R A a)) := by
  rw [differentialsSpecToTilde_def]
  -- `(Spec A).Modules` is a type synonym for sheaves of modules on `Spec A`, so `rw` cannot use
  -- `SheafOfModules.comp_val`; the sections of a composite are the composite by definition.
  change (tilde.map (ModuleCat.ofHom g)).val.app (.op U)
    ((relativeDifferentialsSpecIso R A).hom.val.app (.op U) _) = _
  rw [relativeDifferentialsSpecIso_hom_app_d, tilde_map_val_app_toOpen, ModuleCat.ofHom_apply]

/-- The morphism induced by `ψ ∘ g` is the morphism induced by `g` followed by `ψ~`. -/
@[reassoc]
lemma differentialsSpecToTilde_comp (g : Ω[A⁄R] →ₗ[A] M) (ψ : M →ₗ[A] N) :
    differentialsSpecToTilde R A (ψ ∘ₗ g) =
      differentialsSpecToTilde R A g ≫ (tilde.functor A).map (ModuleCat.ofHom ψ) := by
  rw [differentialsSpecToTilde_def, ModuleCat.ofHom_comp, Functor.map_comp]
  exact (Category.assoc _ _ _).symm

/-- If `g` is surjective, the morphism `Ω_{Spec A/R} ⟶ M~` it induces is an epimorphism, since
`M ↦ M~` is a left adjoint. -/
theorem epi_differentialsSpecToTilde {g : Ω[A⁄R] →ₗ[A] M}
    (hg : Function.Surjective g) : Epi (differentialsSpecToTilde R A g) :=
  have : Epi (ModuleCat.ofHom g) := (ModuleCat.epi_iff_surjective _).mpr hg
  epi_comp' inferInstance (Functor.map_epi _ _)

/-- **A surjection of the Kähler differentials onto a free module gives a locally free quotient.**
For an `R`-algebra `A`, a surjective `A`-linear map `Ω[A⁄R] → A^d` induces an epimorphism
`Ω_{Spec A/R} ⟶ (A^d)~` onto the free sheaf of rank `d`. -/
theorem hasLocallyFreeQuotientOfDifferentials_Spec_of_surjective {d : ℕ}
    (g : Ω[A⁄R] →ₗ[A] (Fin d → A)) (hg : Function.Surjective g) :
    HasLocallyFreeQuotientOfDifferentials R (Spec A) d := by
  refine (hasLocallyFreeQuotientOfDifferentials_iff R _ d).mpr
    ⟨FiniteLocallyFreeSheaf.FixedRank.free _ d, ?_⟩
  rw [FiniteLocallyFreeSheaf.FixedRank.free_obj]
  exact ⟨differentialsSpecToTilde R A g ≫ (FiniteLocallyFreeSheaf.tildePiIsoFree A d).hom,
    epi_comp' (epi_differentialsSpecToTilde R A hg) inferInstance⟩

/-- If the morphism induced by `g` followed by a morphism `φ : M~ ⟶ N~` is the morphism induced
by `h`, then the kernel of `g` lies in the kernel of `h`: as `M ↦ M~` is fully faithful, `φ` comes
from an `A`-linear map `ψ` with `ψ ∘ g = h`. -/
theorem ker_le_ker_of_differentialsSpecToTilde_comp_eq
    (g : Ω[A⁄R] →ₗ[A] M) (h : Ω[A⁄R] →ₗ[A] N) (φ : tilde (.of A M) ⟶ tilde (.of A N))
    (hφ : differentialsSpecToTilde R A g ≫ φ = differentialsSpecToTilde R A h) :
    LinearMap.ker g ≤ LinearMap.ker h := by
  obtain ⟨ψ, rfl⟩ := (tilde.functor A).map_surjective φ
  have hψ : ModuleCat.ofHom (ψ.hom ∘ₗ g) = ModuleCat.ofHom h := by
    refine (tilde.functor A).map_injective
      ((cancel_epi (relativeDifferentialsSpecIso R A).hom).mp ?_)
    rw [← differentialsSpecToTilde_def, ← differentialsSpecToTilde_def,
      differentialsSpecToTilde_comp, ModuleCat.ofHom_hom]
    exact hφ
  have : ψ.hom ∘ₗ g = h := by simpa using congrArg ModuleCat.Hom.hom hψ
  exact this ▸ LinearMap.ker_le_ker_comp g ψ.hom

end

end TauCeti.AlgebraicGeometry
