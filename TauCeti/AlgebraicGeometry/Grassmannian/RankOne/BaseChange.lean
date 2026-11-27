/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.BaseChange
public import TauCeti.AlgebraicGeometry.Grassmannian.RankOne
import TauCeti.AlgebraicGeometry.Cover.Open
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
import TauCeti.RingTheory.Grassmannian.Chart.Locus
import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic

/-!
# The rank-one identification `G(1, M) ≅ Proj (Sym M)` commutes with base change

Let `R → R'` be a map of commutative rings and `f : M →ₗ[R] M'` a linear map exhibiting `M'` as
the base change of `M` to `R'` (`hf : IsBaseChange R' f`). The Grassmannian side of base change is
the morphism `hf.grassmannianSchemeHom 1 : G(1, M') ⟶ G(1, M)`; on the projective side, a graded
ring map `φ : Sym_R M → Sym_{R'} M'` extending `f` on generators induces
`Proj.map φ : Proj (Sym M') ⟶ Proj (Sym M)`. This file proves that the identifications
`Module.Grassmannian.toProj` of the rank-one Grassmannians with the projective spectra of the
symmetric algebras intertwine the two (`IsBaseChange.grassmannianSchemeHom_comp_toProj`).

The proof is on points over `R'`-algebras `A`. For a point `N` of `G(1, M')` over `A`, its image
`N'` in `G(1, A ⊗[R] M; A)` lies, over each basic open `D(a)` of a cover of `Spec A`, in the chart
at `1 ⊗ m` for some `m ∈ M`. The isomorphism `A ⊗[R'] M' ≃ A ⊗[R] M` carries `1 ⊗ f m` to `1 ⊗ m`
and transports charts and their linear forms
(`Module.Grassmannian.grassmannianCongr_mem_chart`,
`Module.Grassmannian.chartEquiv_grassmannianCongr_apply`), so over `D(a)` the point `N` lies in the
chart at `1 ⊗ f m`. On these charts both composites are points of `Proj (Sym M)` on the standard
open `D₊(m)` (`Module.Grassmannian.SpecMap_chartToProj`,
`AlgebraicGeometry.Proj.SpecMap_awayLift_awayι_comp_map`), whose homogeneous coordinates are the
linear forms of the two charts, and these agree.

## Main results

* `IsBaseChange.grassmannianSchemeHom_comp_toProj`: **the rank-one identification commutes with
  base change.**
* `IsBaseChange.isPullback_proj_map`: hence `Proj (Sym M')` is the base change of `Proj (Sym M)`
  to `Spec R'`, for any presentation of `M'` as a base change of `M`.

## References

* [The Stacks Project, Section 27.21, Projective bundles](https://stacks.math.columbia.edu/tag/01OA)
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct TauCeti.SymmetricAlgebra HomogeneousLocalization

namespace IsBaseChange

open Module.Grassmannian ChartAlgebra

section BaseChange

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {M M' : Type u}
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] [Module R M']
  [IsScalarTower R R' M'] {f : M →ₗ[R] M'} (hf : IsBaseChange R' f)
  (φ : homogeneousSubmodule R M →+*ᵍ homogeneousSubmodule R' M')
  (hφι : ∀ m : M, φ (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R' M' (f m))
  (hφ : HomogeneousIdeal.irrelevant (homogeneousSubmodule R' M') ≤
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule R M)).map φ)

include hφι in
/-- On the charts at `1 ⊗ m` and `1 ⊗ f m`, the homogeneous coordinates `Sym M → B` of a point of
`G(1, M')` and of its image in `G(1, M)` agree, the former composed with `φ`. -/
private theorem comp_evalUniversal_eq (B : Type u) [CommRing B] [Algebra R' B] [Algebra R B]
    [IsScalarTower R R' B] (m : M) (N : G(1, B ⊗[R'] M'; B))
    (hN' : hf.grassmannianEquiv B N ∈ chart B (fun _ : Fin 1 ↦ (1 : B) ⊗ₜ[R] m))
    (hN : N ∈ chart B (fun _ : Fin 1 ↦ (1 : B) ⊗ₜ[R'] f m)) :
    (((chartHomEquiv R (fun _ : Fin 1 ↦ m) B).symm ⟨_, hN'⟩ : _ →+* B)).comp
        (evalUniversal R m).toRingHom =
      ((((chartHomEquiv R' (fun _ : Fin 1 ↦ f m) B).symm ⟨N, hN⟩ : _ →+* B)).comp
        (evalUniversal R' (f m)).toRingHom).comp φ.toRingHom := by
  set g := (chartHomEquiv R (fun _ : Fin 1 ↦ m) B).symm ⟨_, hN'⟩
  set g' := (chartHomEquiv R' (fun _ : Fin 1 ↦ f m) B).symm ⟨N, hN⟩
  have hge := hf.grassmannianEquiv_apply N
  refine RingHom.ext fun p ↦ ?_
  induction p using SymmetricAlgebra.induction with
  | algebraMap r =>
    -- `φ` is determined on scalars by `φ (r • ι m) = r • ι (f m)`, evaluated where `ι (f m) = 1`
    set ψ' := ((g' : _ →+* B).comp (evalUniversal R' (f m)).toRingHom)
    have h1 : ψ' (SymmetricAlgebra.ι R' M' (f m)) = 1 := by simp [ψ']
    have h2 : φ (algebraMap R _ r) * SymmetricAlgebra.ι R' M' (f m) =
        algebraMap R' _ (algebraMap R R' r) * SymmetricAlgebra.ι R' M' (f m) := by
      calc φ (algebraMap R _ r) * SymmetricAlgebra.ι R' M' (f m)
          = φ (algebraMap R _ r * SymmetricAlgebra.ι R M m) := by rw [map_mul, hφι]
        _ = φ (SymmetricAlgebra.ι R M (r • m)) := by rw [map_smul, Algebra.smul_def]
        _ = SymmetricAlgebra.ι R' M' (f (r • m)) := hφι _
        _ = algebraMap R' _ (algebraMap R R' r) * SymmetricAlgebra.ι R' M' (f m) := by
          rw [map_smul, ← algebraMap_smul R' r (f m), map_smul, Algebra.smul_def]
    have h3 := congrArg ψ' h2
    rw [map_mul, map_mul, h1, mul_one, mul_one] at h3
    rw [RingHom.comp_apply, RingHom.comp_apply, GradedRingHom.coe_toRingHom, h3]
    simp [ψ', ← IsScalarTower.algebraMap_apply]
  | ι n =>
    have hy : (hf.cancelBaseChange B ∘ fun _ : Fin 1 ↦ (1 : B) ⊗ₜ[R'] f m) =
        fun _ ↦ (1 : B) ⊗ₜ[R] m :=
      funext fun _ ↦ hf.cancelBaseChange_tmul B 1 m
    have := chartEquiv_apply_eq_of_grassmannianCongr (hf.cancelBaseChange B) hy hge.symm hN hN'
      ((1 : B) ⊗ₜ[R'] f n)
    rw [hf.cancelBaseChange_tmul] at this
    have h0 := congrFun this 0
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, evalUniversal_ι, GradedRingHom.coe_toRingHom, hφι, g, g',
      chartHomEquiv_symm_apply_universalLinearMap]
    exact h0
  | mul p q hp hq => simp only [map_mul, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]

include hφι in
/-- The naturality of `toProj` on a point `N` of `G(1, M')` over an `R'`-algebra `B` whose image
in `G(1, B ⊗[R] M; B)` lies in the chart at `1 ⊗ m`. -/
private theorem toSchemeHom_grassmannianEquiv_comp_toProj (B : Type u) [CommRing B]
    [Algebra R' B] [Algebra R B] [IsScalarTower R R' B] (m : M) (N : G(1, B ⊗[R'] M'; B))
    (hN' : hf.grassmannianEquiv B N ∈ chart B (fun _ : Fin 1 ↦ (1 : B) ⊗ₜ[R] m)) :
    toSchemeHom (hf.grassmannianEquiv B N) ≫ toProj R = toSchemeHom N ≫ toProj R' ≫ Proj.map φ hφ
      := by
  have hge := hf.grassmannianEquiv_apply N
  have he : (hf.cancelBaseChange B).symm.grassmannianCongr (hf.grassmannianEquiv B N) = N := by
    rw [hge, ← LinearEquiv.grassmannianCongr_symm, Equiv.symm_apply_apply]
  have hx : ((hf.cancelBaseChange B).symm ∘ fun _ : Fin 1 ↦ (1 : B) ⊗ₜ[R] m) =
      fun _ ↦ (1 : B) ⊗ₜ[R'] f m :=
    funext fun _ ↦ hf.cancelBaseChange_symm_tmul B 1 m
  have hN : N ∈ chart B (fun _ : Fin 1 ↦ (1 : B) ⊗ₜ[R'] f m) := by
    simpa only [he, hx] using grassmannianCongr_mem_chart (hf.cancelBaseChange B).symm hN'
  set g := (chartHomEquiv R (fun _ : Fin 1 ↦ m) B).symm ⟨_, hN'⟩
  set g' := (chartHomEquiv R' (fun _ : Fin 1 ↦ f m) B).symm ⟨N, hN⟩
  have hL : toSchemeHom (hf.grassmannianEquiv B N) =
      Spec.map (CommRingCat.ofHom (g : _ →+* B)) ≫ chartι R (fun _ : Fin 1 ↦ m) := by
    rw [← toSchemeHom_chartHomEquiv, Equiv.apply_symm_apply]
  have hR : toSchemeHom N =
      Spec.map (CommRingCat.ofHom (g' : _ →+* B)) ≫ chartι R' (fun _ : Fin 1 ↦ f m) := by
    rw [← toSchemeHom_chartHomEquiv, Equiv.apply_symm_apply]
  have hring := comp_evalUniversal_eq hf φ hφι B m N hN' hN
  simp only [hL, hR, Category.assoc, chartι_toProj, chartι_toProj_assoc, SpecMap_chartToProj,
    reassoc_of% (SpecMap_chartToProj R' (f m) (g' : _ →+* B))]
  rw [Proj.SpecMap_awayLift_awayι_comp_map φ hφ (ι_mem_homogeneousSubmodule R M m) one_pos _
    (hφι m) _ _ (by rw [← hring]; simp)]
  -- the two points of `D₊(m)` have the homogeneous coordinates identified by `hring`
  simp only [g, g', hring]

include hφι in
/-- **The rank-one identification commutes with base change.** For a base change `f : M → M'`
along `R → R'` and a graded ring map `φ : Sym_R M → Sym_{R'} M'` restricting to `f` on generators,
the identifications `toProj` of the rank-one Grassmannians
`G(1, M)` and `G(1, M')` with `Proj (Sym M)` and `Proj (Sym M')` intertwine the base change morphism
`G(1, M') ⟶ G(1, M)` and `Proj.map φ`. -/
theorem grassmannianSchemeHom_comp_toProj :
    hf.grassmannianSchemeHom 1 ≫ toProj R = toProj R' ≫ Proj.map φ hφ := by
  refine scheme_hom_ext fun A _ _ N ↦ ?_
  let _ : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' A := .of_algebraMap_eq' rfl
  rw [IsBaseChange.toSchemeHom_comp_grassmannianSchemeHom_assoc]
  refine TauCeti.AlgebraicGeometry.Spec.hom_ext_of_span_eq_top
    {a | ∃ x : Fin 1 → M, a ∈ chartLocus (hf.grassmannianEquiv A N) (fun i ↦ (1 : A) ⊗ₜ[R] x i)}
    (eq_top_iff.mpr <| (iSup_chartLocus_tmul_eq_top _).ge.trans <|
      iSup_le fun x _ hb ↦ Ideal.subset_span ⟨x, hb⟩) fun ⟨a, x, ha⟩ ↦ ?_
  obtain ⟨m, rfl⟩ : ∃ m, x = fun _ ↦ m := ⟨_, eq_const_of_unique x⟩
  let ρ : A →ₐ[R'] Localization.Away a := IsScalarTower.toAlgHom R' A _
  have hB : hf.grassmannianEquiv (Localization.Away a) (map ρ N) ∈
      chart (Localization.Away a) (fun _ : Fin 1 ↦ (1 : Localization.Away a) ⊗ₜ[R] m) := by
    rw [hf.grassmannianEquiv_map]
    exact (map_mem_chart_iff (ρ.restrictScalars R) _ _).2 (Ideal.eq_top_of_isUnit_mem _
      (Ideal.mem_map_of_mem _ ha) (IsLocalization.Away.algebraMap_isUnit a))
  have h := toSchemeHom_grassmannianEquiv_comp_toProj hf φ hφι hφ _ m (map ρ N) hB
  rw [toSchemeHom_map, hf.grassmannianEquiv_map, toSchemeHom_map, Category.assoc] at h
  exact h

include hf hφι in
/-- **`Proj (Sym M)` commutes with base change along any presentation of a base change.** For a
base change `f : M → M'` along `R → R'` and a graded ring map `φ : Sym_R M → Sym_{R'} M'` extending
`f`, the square formed by `Proj.map φ` and the structure morphisms to
`Spec R'` and `Spec R` is cartesian. It is the base change square of the rank-one Grassmannians
(`IsBaseChange.isPullback_grassmannianSchemeHom`), transported along `toProjIso`. -/
theorem isPullback_proj_map :
    IsPullback (Proj.map φ hφ) (projToSpec R' M') (projToSpec R M)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
  (hf.isPullback_grassmannianSchemeHom 1).of_iso (toProjIso R') (toProjIso R) (Iso.refl _)
    (Iso.refl _) (by simpa using grassmannianSchemeHom_comp_toProj hf φ hφι hφ)
    (by simp) (by simp) (by simp)

end BaseChange

end IsBaseChange
