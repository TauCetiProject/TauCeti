/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Projective
public import TauCeti.Algebra.Module.Generator
public import TauCeti.CategoryTheory.Preadditive.Progenerator

/-!
# Progenerators in `FGModuleCat`

A finitely generated `R`-module `P`, viewed as an object of `FGModuleCat R`, is a categorical
progenerator (`TauCeti.IsProgenerator P`) if and only if it is projective (`Module.Projective R P`)
and a module-theoretic generator (`TauCeti.Module.IsGenerator R P`). This bridges the categorical
progenerator API of `TauCeti.CategoryTheory.Preadditive.Progenerator` and
`TauCeti.CategoryTheory.Abelian.Progenerator` with the module-theoretic progenerator and Morita API
of `TauCeti.Algebra.Module.Generator` and `TauCeti.RingTheory.Morita.Progenerator`.

In particular, over any ring `R`, the regular module `R`, any positive finite free module
`Fin n → R`, and `R × R` are progenerators of `FGModuleCat R`.

## Main results

* `FGModuleCat.isProgenerator_of_projective_of_isGenerator`: every finitely generated projective
  generator is a progenerator of `FGModuleCat R`.
* `FGModuleCat.isGenerator_of_isProgenerator` and `FGModuleCat.isProgenerator_iff`: the equivalence
  between `TauCeti.IsProgenerator P` in `FGModuleCat R` and
  `Module.Projective R P ∧ TauCeti.Module.IsGenerator R P` (under `[Small.{v} R]`, which is
  automatic for `FGModuleCat.{u} R`).
* `FGModuleCat.isProgenerator_self`, `FGModuleCat.isProgenerator_pi`, and
  `FGModuleCat.isProgenerator_prod_self`: the regular module `R`, `Fin n → R` (`[NeZero n]`), and
  `R × R` are progenerators of `FGModuleCat R`.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, Graduate Texts in Mathematics 189, Springer (1999),
  §18.
-/

public section

namespace FGModuleCat

open CategoryTheory CategoryTheory.Limits TauCeti

universe u v

variable {R : Type u} [Ring R]

/-- A finitely generated projective `R`-module that is a generator is a progenerator of
`FGModuleCat R`. -/
theorem isProgenerator_of_projective_of_isGenerator (P : FGModuleCat.{v} R)
    [Module.Projective R P] [TauCeti.Module.IsGenerator R P] : IsProgenerator P where
  projective := FGModuleCat.projective_of_moduleProjective R P
  exists_epi_biproduct X := by
    obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' R X
    obtain ⟨k, p, hp⟩ := (TauCeti.Module.isGenerator_iff_exists_surjective (R := R) (M := P)).mp
      inferInstance
    let eFin : (Fin (m * k) → P) ≃ₗ[R] (Fin m → Fin k → P) :=
      (LinearEquiv.funCongrLeft R P finProdFinEquiv).trans (LinearEquiv.curry R P (Fin m) (Fin k))
    let pMap : (Fin m → Fin k → P) →ₗ[R] (Fin m → R) := LinearMap.pi fun i ↦ p ∘ₗ LinearMap.proj i
    have hpMap : Function.Surjective pMap := fun f ↦ by
      choose g hg using fun i ↦ hp (f i)
      exact ⟨g, funext hg⟩
    let φ : (Fin (m * k) → P) →ₗ[R] X := q ∘ₗ pMap ∘ₗ eFin.toLinearMap
    have hφ : Function.Surjective φ := hq.comp (hpMap.comp eFin.surjective)
    let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
    have : PreservesBiproduct (fun _ : Fin (m * k) ↦ P) F :=
      preservesBiproduct_of_preservesCoproduct F
    let eB : (F.obj (⨁ fun _ : Fin (m * k) ↦ P)) ≅ ModuleCat.of R (Fin (m * k) → P) :=
      F.mapBiproduct (fun _ : Fin (m * k) ↦ P) ≪≫
        ModuleCat.biproductIsoPi (fun _ : Fin (m * k) ↦ P.obj)
    have : Epi (ModuleCat.ofHom φ : ModuleCat.of R (Fin (m * k) → P) ⟶ X.obj) :=
      (ModuleCat.epi_iff_surjective _).mpr hφ
    have : Epi (eB.hom ≫ ModuleCat.ofHom φ) := epi_comp _ _
    refine ⟨m * k, ObjectProperty.homMk (eB.hom ≫ ModuleCat.ofHom φ), ?_⟩
    exact F.epi_of_epi_map ‹_›

/-- A progenerator of `FGModuleCat R` is a generator as an `R`-module (when `R` is `v`-small, which
holds automatically for `FGModuleCat.{u} R`). -/
theorem isGenerator_of_isProgenerator [Small.{v} R] {P : FGModuleCat.{v} R}
    (hP : IsProgenerator P) : TauCeti.Module.IsGenerator R P := by
  let eR : Shrink.{v} R ≃ₗ[R] R := Shrink.linearEquiv.{v} R R
  have : Module.Finite R (Shrink.{v} R) := Module.Finite.equiv eR.symm
  obtain ⟨n, π, hπ⟩ := hP.exists_epi_biproduct (FGModuleCat.of R (Shrink.{v} R))
  let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  have : PreservesBiproduct (fun _ : Fin n ↦ P) F := preservesBiproduct_of_preservesCoproduct F
  let eB : ModuleCat.of R (Fin n → P) ≅ F.obj (⨁ fun _ : Fin n ↦ P) :=
    (ModuleCat.biproductIsoPi (fun _ : Fin n ↦ P.obj)).symm ≪≫
      (F.mapBiproduct (fun _ : Fin n ↦ P)).symm
  have : Epi (F.map π) := inferInstance
  have hepi : Epi (eB.hom ≫ F.map π) := epi_comp _ _
  have hsurj : Function.Surjective (eB.hom ≫ F.map π).hom :=
    (ModuleCat.epi_iff_surjective _).mp hepi
  exact (TauCeti.Module.isGenerator_iff_exists_surjective (R := R) (M := P)).mpr
    ⟨n, eR.toLinearMap ∘ₗ (eB.hom ≫ F.map π).hom, eR.surjective.comp hsurj⟩

/-- **Characterization of progenerators in `FGModuleCat R`.** An object `P` of `FGModuleCat R` is a
categorical progenerator if and only if it is projective and a generator as an `R`-module. -/
theorem isProgenerator_iff [Small.{v} R] (P : FGModuleCat.{v} R) :
    IsProgenerator P ↔ Module.Projective R P ∧ TauCeti.Module.IsGenerator R P :=
  ⟨fun hP ↦
    have := hP.projective
    ⟨FGModuleCat.moduleProjective_of_projective P, isGenerator_of_isProgenerator hP⟩,
   fun ⟨_, _⟩ ↦ isProgenerator_of_projective_of_isGenerator P⟩

variable (R)

/-- The regular module `R` is a progenerator of `FGModuleCat R`. -/
theorem isProgenerator_self : IsProgenerator (FGModuleCat.of R R) :=
  isProgenerator_of_projective_of_isGenerator (FGModuleCat.of R R)

/-- Any positive finite free module `Fin n → R` (`n ≠ 0`) is a progenerator of `FGModuleCat R`. -/
theorem isProgenerator_pi (n : ℕ) [NeZero n] :
    IsProgenerator (FGModuleCat.of R (Fin n → R)) := by
  have : TauCeti.Module.IsGenerator R (Fin n → R) := by
    rcases subsingleton_or_nontrivial R with _ | _
    · exact ⟨0, Fin.elim0, Fin.elim0, Subsingleton.elim _ _⟩
    · have : Nontrivial (Fin n → R) := Function.nontrivial
      infer_instance
  exact isProgenerator_of_projective_of_isGenerator (FGModuleCat.of R (Fin n → R))

/-- The rank-two free module `R × R` is a progenerator of `FGModuleCat R`. -/
theorem isProgenerator_prod_self : IsProgenerator (FGModuleCat.of R (R × R)) :=
  isProgenerator_of_projective_of_isGenerator (FGModuleCat.of R (R × R))

end FGModuleCat
