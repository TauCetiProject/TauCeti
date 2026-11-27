/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.BaseChange
public import TauCeti.AlgebraicGeometry.Grassmannian.RankOne
import TauCeti.AlgebraicGeometry.Cover.Open
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
symmetric algebras intertwine the two
(`Module.Grassmannian.grassmannianSchemeHom_comp_toProj`).

The proof is on points over `R'`-algebras `A`. For a point `N` of `G(1, M')` over `A`, its image
`N'` in `G(1, A ⊗[R] M; A)` lies, over each basic open `D(a)` of a cover of `Spec A`, in the chart
at `1 ⊗ m` for some `m ∈ M`. The isomorphism `A ⊗[R'] M' ≃ A ⊗[R] M` carries `1 ⊗ f m` to `1 ⊗ m`
and transports charts and their linear forms
(`Module.Grassmannian.grassmannianCongr_mem_chart`,
`Module.Grassmannian.chartEquiv_grassmannianCongr_apply`), so over `D(a)` the point `N` lies in the
chart at `1 ⊗ f m`. On these charts both composites are points of `Proj (Sym M)` on the standard
open `D₊(m)` (`Module.Grassmannian.SpecMap_chartToProj`, `Proj.awayι_comp_map`), whose homogeneous
coordinates are the linear forms of the two charts, and these agree.

## Main results

* `Module.Grassmannian.grassmannianCongr_mem_chart` and
  `Module.Grassmannian.chartEquiv_grassmannianCongr_apply`: transport of charts along a linear
  equivalence.
* `Module.Grassmannian.grassmannianSchemeHom_comp_toProj`: **the rank-one identification commutes
  with base change.**
* `Module.Grassmannian.isPullback_proj_map_of_isBaseChange`: hence `Proj (Sym M')` is the base
  change of `Proj (Sym M)` to `Spec R'`, for any presentation of `M'` as a base change of `M`.

## References

* [The Stacks Project, Section 27.21, Projective bundles](https://stacks.math.columbia.edu/tag/01OA)
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct TauCeti.SymmetricAlgebra HomogeneousLocalization

namespace Module.Grassmannian

section Chart

variable {A : Type*} [CommRing A] {P P' : Type*} [AddCommGroup P] [Module A P] [AddCommGroup P']
  [Module A P'] {k : ℕ}

/-- **Charts are transported along linear equivalences.** If `N` lies in the chart at `x`, then its
image under a linear equivalence `e` lies in the chart at `e ∘ x`. -/
theorem grassmannianCongr_mem_chart (e : P ≃ₗ[A] P') {x : Fin k → P} {N : G(k, P; A)}
    (hN : N ∈ chart A x) : e.grassmannianCongr N ∈ chart A (e ∘ x) := by
  rw [mem_chart_iff_sup_eq_top] at hN ⊢
  have h : (e.grassmannianCongr N).toSubmodule ⊔ Submodule.span A (Set.range (e ∘ x)) =
      (N.toSubmodule ⊔ Submodule.span A (Set.range x)).map (e : P →ₗ[A] P') := by
    rw [Submodule.map_sup, Submodule.map_span, ← Set.range_comp,
      LinearEquiv.toSubmodule_grassmannianCongr_apply]
    rfl
  rw [h, hN, Submodule.map_top, LinearEquiv.range]

/-- **Transport of the linear form of a chart.** The linear map `P' → A^k` of the chart at `e ∘ x`
attached to the image of `N` under a linear equivalence `e` is that of `N`, composed with
`e⁻¹`. -/
theorem chartEquiv_grassmannianCongr_apply (e : P ≃ₗ[A] P') {x : Fin k → P} (N : chart A x)
    (p : P) :
    (chartEquiv A (e ∘ x) ⟨e.grassmannianCongr N.val, grassmannianCongr_mem_chart e N.property⟩).val
      (e p) = (chartEquiv A x N).val p := by
  have h : (⟨e.grassmannianCongr N.val, grassmannianCongr_mem_chart e N.property⟩ :
      chart A (e ∘ x)) = (chartEquiv A (e ∘ x)).symm
        ⟨(chartEquiv A x N).val ∘ₗ e.symm.toLinearMap, fun i ↦ by simp⟩ := by
    refine Subtype.ext (Grassmannian.ext ?_)
    rw [toSubmodule_chartEquiv_symm_apply, LinearEquiv.toSubmodule_grassmannianCongr_apply,
      LinearMap.ker_comp, ker_chartEquiv_apply, Submodule.comap_equiv_eq_map_symm,
      LinearEquiv.symm_symm]
  rw [h, Equiv.apply_symm_apply]
  simp

/-- `Module.Grassmannian.chartEquiv_grassmannianCongr_apply` with the transported chart and point
given by equations. -/
theorem chartEquiv_apply_eq_of_grassmannianCongr (e : P ≃ₗ[A] P') {x : Fin k → P}
    {y : Fin k → P'} (hxy : e ∘ x = y) {N : G(k, P; A)} {N' : G(k, P'; A)}
    (hNN' : e.grassmannianCongr N = N') (hN : N ∈ chart A x) (hN' : N' ∈ chart A y) (p : P) :
    (chartEquiv A y ⟨N', hN'⟩).val (e p) = (chartEquiv A x ⟨N, hN⟩).val p := by
  subst hxy hNN'
  exact chartEquiv_grassmannianCongr_apply e ⟨N, hN⟩ p

end Chart

open ChartAlgebra

/-- A point of `Proj ℬ` on the standard open of `t = φ s`, followed by `Proj.map φ`, is the point on
the standard open of `s` with homogeneous coordinates composed with `φ`. -/
private theorem specMap_awayLift_awayι_comp_map {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B]
    [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (φ : 𝒜 →+*ᵍ ℬ)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    {s : A} (hs : s ∈ 𝒜 1) {t : B} (ht : t ∈ ℬ 1) (hst : φ s = t) (ψ : B →+* C)
    (hu : IsUnit (ψ t)) (hu' : IsUnit ((ψ.comp φ.toRingHom) s)) :
    Spec.map (CommRingCat.ofHom (Away.lift ℬ ψ hu)) ≫ Proj.awayι ℬ t ht one_pos ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom (Away.lift 𝒜 (ψ.comp φ.toRingHom) hu')) ≫
        Proj.awayι 𝒜 s hs one_pos := by
  subst hst
  rw [Proj.awayι_comp_map _ _ one_pos _ hs, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    Away.lift_comp_map]

section BaseChange

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {M M' : Type u}
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] [Module R M']
  [IsScalarTower R R' M'] {f : M →ₗ[R] M'} (hf : IsBaseChange R' f)
  (φ : homogeneousSubmodule R M →+*ᵍ homogeneousSubmodule R' M')
  (hφι : ∀ m : M, φ (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R' M' (f m))
  (hφ : HomogeneousIdeal.irrelevant (homogeneousSubmodule R' M') ≤
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule R M)).map φ)

/-- The point of `G(1, M)` attached to a point of `G(1, M')` along a base change is its transport
along `A ⊗[R'] M' ≃ A ⊗[R] M`. -/
private theorem grassmannianEquiv_eq_grassmannianCongr (B : Type u) [CommRing B] [Algebra R' B]
    [Algebra R B] [IsScalarTower R R' B] (N : G(1, B ⊗[R'] M'; B)) :
    hf.grassmannianEquiv B N = (hf.cancelBaseChange B).grassmannianCongr N :=
  Grassmannian.ext (by
    rw [IsBaseChange.toSubmodule_grassmannianEquiv,
      LinearEquiv.toSubmodule_grassmannianCongr_apply])

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
  have hge := grassmannianEquiv_eq_grassmannianCongr hf B N
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
    change (g : _ →+* B) ((evalUniversal R m) (algebraMap R _ r)) = ψ' (φ (algebraMap R _ r))
    rw [h3]
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
  have hge := grassmannianEquiv_eq_grassmannianCongr hf B N
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
  have hlift : ∀ (ψ₁ ψ₂ : SymmetricAlgebra R M →+* B) (_ : ψ₁ = ψ₂) h₁ h₂,
      Away.lift (homogeneousSubmodule R M) ψ₁ (f := SymmetricAlgebra.ι R M m) h₁ =
        Away.lift (homogeneousSubmodule R M) ψ₂ h₂ := by
    rintro _ _ rfl _ _
    rfl
  rw [hL, hR, Category.assoc, Category.assoc, chartι_toProj, chartι_toProj_assoc,
    SpecMap_chartToProj, reassoc_of% (SpecMap_chartToProj R' (f m) (g' : _ →+* B)),
    specMap_awayLift_awayι_comp_map φ hφ (ι_mem_homogeneousSubmodule R M m) _ (hφι m) _ _
      (by rw [← hring]; simp), hlift _ _ hring]

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
theorem isPullback_proj_map_of_isBaseChange :
    IsPullback (Proj.map φ hφ) (projToSpec R' M') (projToSpec R M)
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
  (hf.isPullback_grassmannianSchemeHom 1).of_iso (toProjIso R') (toProjIso R) (Iso.refl _)
    (Iso.refl _) (by simpa using grassmannianSchemeHom_comp_toProj hf φ hφι hφ)
    (by simp) (by simp) (by simp)

end BaseChange

end Module.Grassmannian
