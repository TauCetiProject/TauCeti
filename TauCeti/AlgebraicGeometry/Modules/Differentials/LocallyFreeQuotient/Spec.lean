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
map `g : Ω[A⁄R] → A^d` induces a morphism of sheaves `Ω_{Spec A/R} ⟶ (A^d)~`. If `g` is
surjective this morphism is an epimorphism onto a finite locally free sheaf of constant rank `d`,
so `Ω_{Spec A/R}` admits a locally free quotient of rank `d`. This is the affine global case of
the stalk criterion for `HasLocallyFreeQuotientOfDifferentials`.

Since `M ↦ M~` is fully faithful, a morphism `(A^d)~ ⟶ (A^e)~` carrying the quotient induced by
`g` to the one induced by `h` comes from an `A`-linear map, so the kernel of `g` lies in the
kernel of `h`.

## Main declarations

* `TauCeti.AlgebraicGeometry.differentialsSpecToTilde`: the morphism `Ω_{Spec A/R} ⟶ (A^d)~`
  induced by an `A`-linear map `Ω[A⁄R] → A^d`;
* `TauCeti.AlgebraicGeometry.hasLocallyFreeQuotientOfDifferentials_Spec_of_surjective`: a
  surjective `A`-linear map `Ω[A⁄R] → A^d` gives a locally free quotient of rank `d` of
  `Ω_{Spec A/R}`;
* `TauCeti.AlgebraicGeometry.ker_le_ker_of_differentialsSpecToTilde_comp_eq`: if the quotient
  induced by `g` factors the one induced by `h`, then `ker g ≤ ker h`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable (R : Type u) [CommRing R] (A : CommRingCat.{u}) [Algebra R A]

/-- The morphism `Ω_{Spec A/R} ⟶ (A^d)~` induced by an `A`-linear map `g : Ω[A⁄R] → A^d`
through `Ω_{Spec A/R} ≅ Ω[A⁄R]~`. -/
def differentialsSpecToTilde {d : ℕ} (g : Ω[A⁄R] →ₗ[A] (Fin d → A)) :
    (Spec A).relativeDifferentials R ⟶ tilde (.of A (Fin d → A)) :=
  (relativeDifferentialsSpecIso R A).hom ≫ (tilde.functor A).map (ModuleCat.ofHom g)

/-- `differentialsSpecToTilde R A g` is `Ω_{Spec A/R} ≅ Ω[A⁄R]~` followed by `g~`. -/
lemma differentialsSpecToTilde_def {d : ℕ} (g : Ω[A⁄R] →ₗ[A] (Fin d → A)) :
    differentialsSpecToTilde R A g =
      (relativeDifferentialsSpecIso R A).hom ≫ (tilde.functor A).map (ModuleCat.ofHom g) :=
  (rfl)

/-- The morphism induced by `g` sends the differential `d a` of `a ∈ A` to the section `g (D a)`
of `(A^d)~`. -/
lemma differentialsSpecToTilde_app_d {d : ℕ} (g : Ω[A⁄R] →ₗ[A] (Fin d → A))
    (U : (Spec A).Opens) (a : A) :
    (differentialsSpecToTilde R A g).val.app (.op U)
        (((Spec A).universalDerivation R).d
          (((Spec A).presheaf.map (homOfLE le_top).op).hom ((Scheme.ΓSpecIso A).inv.hom a))) =
      tilde.toOpen (ModuleCat.of A (Fin d → A)) U (g (KaehlerDifferential.D R A a)) := by
  rw [differentialsSpecToTilde_def]
  exact (congrArg ((tilde.map (ModuleCat.ofHom g)).val.app (.op U))
    (relativeDifferentialsSpecIso_hom_app_d R A U a)).trans
      (tilde_map_val_app_toOpen (ModuleCat.ofHom g) U _)

/-- If `g` is surjective, the morphism `Ω_{Spec A/R} ⟶ (A^d)~` it induces is an epimorphism, since
`M ↦ M~` is a left adjoint. -/
theorem epi_differentialsSpecToTilde {d : ℕ} {g : Ω[A⁄R] →ₗ[A] (Fin d → A)}
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

/-- If the morphism induced by `g` followed by a morphism `φ : (A^d)~ ⟶ (A^e)~` is the morphism
induced by `h`, then the kernel of `g` lies in the kernel of `h`: as `M ↦ M~` is fully faithful,
`φ` comes from an `A`-linear map `ψ` with `ψ ∘ g = h`. -/
theorem ker_le_ker_of_differentialsSpecToTilde_comp_eq {d e : ℕ}
    (g : Ω[A⁄R] →ₗ[A] (Fin d → A)) (h : Ω[A⁄R] →ₗ[A] (Fin e → A))
    (φ : tilde (.of A (Fin d → A)) ⟶ tilde (.of A (Fin e → A)))
    (hφ : differentialsSpecToTilde R A g ≫ φ = differentialsSpecToTilde R A h) :
    LinearMap.ker g ≤ LinearMap.ker h := by
  obtain ⟨ψ, rfl⟩ := (tilde.functor A).map_surjective φ
  have hψ : ModuleCat.ofHom g ≫ ψ = ModuleCat.ofHom h := by
    refine (tilde.functor A).map_injective ?_
    rw [Functor.map_comp]
    exact (cancel_epi (relativeDifferentialsSpecIso R A).hom).mp
      ((Category.assoc _ _ _).symm.trans hφ)
  have : ψ.hom ∘ₗ g = h := by simpa using congrArg ModuleCat.Hom.hom hψ
  exact this ▸ LinearMap.ker_le_ker_comp g ψ.hom

end

end TauCeti.AlgebraicGeometry
