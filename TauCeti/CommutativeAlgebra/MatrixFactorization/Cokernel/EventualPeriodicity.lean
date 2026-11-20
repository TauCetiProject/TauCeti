/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Minimal
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.MaximalCohenMacaulay
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Minimal
import Mathlib.RingTheory.KrullDimension.Regular
import TauCeti.CategoryTheory.Abelian.Projective.Resolution
import TauCeti.RingTheory.KrullDimension.Module
import TauCeti.RingTheory.LocalRing.Module

/-!
# Eventual two-periodicity of minimal free resolutions over local hypersurfaces

For a nonzero `w` in the maximal ideal of a regular local ring `S` with local hypersurface quotient
`R = S ⧸ (w)`, this file proves **Eisenbud's Theorem 6.1** (1980) for finite `R`-modules `M`:

* **Theorem 6.1(ii)** (`exists_isMinimal_quotientCokernel_iso_iff`, `hasPeriodicTail_two_zero_iff`,
  `exists_isMinimal_projectiveResolution_of_isMaximalCohenMacaulay`): `M` is maximal Cohen–Macaulay
  without nonzero projective `R`-retracts iff `M` is the reduced cokernel of a minimal matrix
  factorization of `w`, iff every minimal finite-term resolution of `M` has `HasPeriodicTail 2 0`.
* **Theorem 6.1(i)** (`exists_isMinimal_projectiveResolution_of_ringKrullDim_le_depth_add`,
  `hasPeriodicTail_two_of_isMinimal`, `exists_isMinimal_projectiveResolution`,
  `hasPeriodicTail_two_spanFinrank_of_isMinimal`): if `ringKrullDim R ≤ depth M + n`, minimal
  resolutions have `HasPeriodicTail 2 (n + 1)`, giving the uniform bound `(𝔪_S).spanFinrank`.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Theorem 6.1.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, AMS (2021), Section 4.
-/

public section
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace TauCeti.MatrixFactorization

section ResolutionHelpers

variable {R : Type u} [CommRing R]

private def projectiveResolutionOfIso {M N : ModuleCat.{u} R}
    (P : ProjectiveResolution M) (e : M ≅ N) : ProjectiveResolution N where
  complex := P.complex
  projective := P.projective
  π := P.π ≫ (ChainComplex.single₀ _).map e.hom
  quasiIso := by
    have : IsIso ((ChainComplex.single₀ (ModuleCat.{u} R)).map e.hom) :=
      inferInstanceAs (IsIso (((ChainComplex.single₀ _).mapIso e).hom))
    infer_instance

private abbrev augZero {K : ModuleCat.{u} R} (Q : ProjectiveResolution K) : Q.complex.X 0 ⟶ K :=
  Q.π.f 0 ≫ (HomologicalComplex.singleObjXSelf (.down ℕ) 0 K).hom

private theorem exact_consProjectiveResolution_zero {K F M : ModuleCat.{u} R}
    (Q : ProjectiveResolution K) {i : K ⟶ F} {p : F ⟶ M} (hip : Function.Exact i.hom p.hom) :
    Function.Exact (augZero Q ≫ i).hom p.hom := fun x ↦ by
  have hsurj : Function.Surjective (augZero Q).hom :=
    (ModuleCat.epi_iff_surjective (augZero Q)).1 inferInstance
  refine (hip x).trans ⟨fun ⟨y, hy⟩ ↦ ?_, fun ⟨z, hz⟩ ↦ ⟨(augZero Q).hom z, hz⟩⟩
  obtain ⟨z, rfl⟩ := hsurj y; exact ⟨z, hy⟩

private theorem exact_consProjectiveResolution_one {K F : ModuleCat.{u} R}
    (Q : ProjectiveResolution K) {i : K ⟶ F} (hi : Function.Injective i.hom) :
    Function.Exact (Q.complex.d 1 0).hom (augZero Q ≫ i).hom := fun y ↦ by
  have : Mono i := (ModuleCat.mono_iff_injective i).2 hi
  let i' := (HomologicalComplex.singleObjXSelf (.down ℕ) 0 K).hom ≫ i
  have hi' : Function.Injective i'.hom := (ModuleCat.mono_iff_injective i').1 inferInstance
  rw [show augZero Q ≫ i = Q.π.f 0 ≫ i' from Category.assoc _ _ _]
  change i'.hom ((Q.π.f 0).hom y) = 0 ↔ _
  rw [← map_zero i'.hom, hi'.eq_iff,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 Q.exact₀ y]

private theorem exists_consProjectiveResolution [IsLocalRing R]
    {K F M : ModuleCat.{u} R} [Projective F] [Module.Finite R F] [Module.Free R F]
    (Q : ProjectiveResolution K) {i : K ⟶ F} {p : F ⟶ M}
    (hi : Function.Injective i.hom) (hip : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) (hi_min : LinearMap.range i.hom ≤ maximalIdeal R • ⊤)
    (hQ_ff : ∀ k, Module.Finite R (Q.complex.X k) ∧ Module.Free R (Q.complex.X k))
    (hQ_min : Q.complex.IsMinimal) :
    ∃ P : ProjectiveResolution M,
      (∀ k, Module.Finite R (P.complex.X k) ∧ Module.Free R (P.complex.X k)) ∧
      P.complex.IsMinimal ∧ Nonempty (ChainComplex.truncate.obj P.complex ≅ Q.complex) := by
  let C := ChainComplex.augment Q.complex (augZero Q ≫ i) (by
    rw [← Category.assoc, augZero, ← Category.assoc, Q.complex_d_comp_π_f_zero, zero_comp,
      zero_comp])
  let p' : C.X 0 ⟶ M := p
  have : Epi p' := (ModuleCat.epi_iff_surjective p').2 hp
  have hp₀ : C.d 1 0 ≫ p' = 0 := by
    change (augZero Q ≫ i) ≫ p = 0
    rw [Category.assoc, show i ≫ p = 0 from
      ModuleCat.hom_ext (LinearMap.ext hip.apply_apply_eq_zero), comp_zero]
  let P : ProjectiveResolution M := C.toProjectiveResolution p' hp₀
    (fun | 0 => ‹Projective F› | k + 1 => Q.projective k)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
      (exact_consProjectiveResolution_zero Q hip))
    (fun
      | 0 => by
        rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
        exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
          (exact_consProjectiveResolution_one Q hi)
      | k + 1 => by
        rw [HomologicalComplex.exactAt_iff' _ (k + 3) (k + 2) (k + 1) (by simp) (by simp)]
        exact Q.exact_succ k)
  have hPC : P.complex = C := rfl
  refine ⟨P, fun k ↦ ?_, ?_, ⟨hPC ▸ ChainComplex.truncateAugment _ _ _⟩⟩
  · rw [hPC]
    rcases k with _ | k
    · change Module.Finite R F ∧ Module.Free R F; exact ⟨‹_›, ‹_›⟩
    · rw [ChainComplex.augment_X_succ]; exact hQ_ff k
  · rw [hPC, ChainComplex.isMinimal_iff_range_d_succ_le_maximalIdeal_smul]
    rw [ChainComplex.isMinimal_iff_range_d_succ_le_maximalIdeal_smul] at hQ_min
    rintro (_ | k) _ ⟨y, rfl⟩
    · exact hi_min ⟨(augZero Q).hom y, rfl⟩
    · exact hQ_min k ⟨y, rfl⟩

private theorem finite_of_projectiveResolution {M : ModuleCat.{u} R}
    (P : ProjectiveResolution M) [Module.Finite R (P.complex.X 0)] : Module.Finite R M :=
  Module.Finite.of_surjective (augZero P).hom
    ((ModuleCat.epi_iff_surjective (augZero P)).1 inferInstance)

private theorem exists_surjective_fin_ker_le_maximalIdeal_smul [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ (μ : ℕ) (p₀ : (Fin μ → R) →ₗ[R] M),
      Function.Surjective p₀ ∧ LinearMap.ker p₀ ≤ maximalIdeal R • ⊤ :=
  ⟨_, TauCeti.IsLocalRing.exists_surjective_ker_le_maximalIdeal_smul R M⟩

private theorem exists_minimal_syzygy [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ (F K : ModuleCat.{u} R) (i : K ⟶ F) (p : F ⟶ M),
      Projective F ∧ Module.Finite R F ∧ Module.Free R F ∧ Module.Finite R K ∧
      Function.Injective i.hom ∧ Function.Exact i.hom p.hom ∧ Function.Surjective p.hom ∧
      LinearMap.range i.hom ≤ maximalIdeal R • ⊤ := by
  obtain ⟨μ, p₀, hp₀, hker⟩ := exists_surjective_fin_ker_le_maximalIdeal_smul M
  have : Module.Finite R (LinearMap.ker p₀) := Module.Finite.iff_fg.2 (IsNoetherian.noetherian _)
  exact ⟨.of R (Fin μ → R), .of R (LinearMap.ker p₀),
    ModuleCat.ofHom (LinearMap.ker p₀).subtype, ModuleCat.ofHom p₀,
    ModuleCat.projective_of_categoryTheory_projective _, inferInstance, inferInstance,
    inferInstance, Subtype.val_injective, LinearMap.exact_subtype_ker_map p₀, hp₀,
    (Submodule.range_subtype _).le.trans hker⟩

end ResolutionHelpers

section Hypersurface

variable {S : Type u} [CommRing S] [_root_.IsRegularLocalRing S] {w : S}
  [IsLocalRing (S ⧸ Ideal.span {w})]

private theorem exists_isMinimal_quotientCokernel_iso_of_isMaximalCohenMacaulay
    (hw : w ≠ 0) (M : ModuleCat.{u} (S ⧸ Ideal.span {w}))
    [Module.Finite (S ⧸ Ideal.span {w}) M]
    (hMCM : Module.IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M)
    (hproj : ∀ P : ModuleCat.{u} (S ⧸ Ideal.span {w}), Projective P →
      Nonempty (Retract P M) → IsZero P) :
    ∃ X : MatrixFactorization S w, X.IsMinimal ∧
      Nonempty ((cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj ≅ M) := by
  have hmem : w ∈ nonZeroDivisors S := mem_nonZeroDivisors_of_ne_zero hw
  let M' := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj M
  have : Module.Finite S M' := ((Ideal.Quotient.mk (Ideal.span {w})).finite_restrictScalars_iff
    Ideal.Quotient.mk_surjective M).2 ‹_›
  have hpd :=
    (TauCeti.IsRegularLocalRing.isMaximalCohenMacaulay_quotient_iff_hasProjectiveDimensionLE
      hw M).1 hMCM
  obtain ⟨μ, π, hπ, hker_le⟩ := exists_surjective_fin_ker_le_maximalIdeal_smul M'
  have : Module.Finite S (LinearMap.ker π) := Module.Finite.iff_fg.2 (IsNoetherian.noetherian _)
  have : Module.Projective S (LinearMap.ker π) := by
    rw [IsProjective.iff_projective, projective_iff_hasProjectiveDimensionLE_zero]
    exact (π.hasProjectiveDimensionLE_succ_iff_ker hπ 0).1 hpd
  let P_fg : FGModuleCat.{u} S := FGModuleCat.of S (LinearMap.ker π)
  let Q_fg : FGModuleCat.{u} S := FGModuleCat.of S (Fin μ → S)
  have : Module.Projective S P_fg := ‹_›
  have : Module.Projective S Q_fg := inferInstanceAs (Module.Projective S (Fin μ → S))
  let f : P_fg ⟶ Q_fg := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.ker π).subtype)
  let g : Q_fg.obj ⟶ M' := ModuleCat.ofHom (X := Fin μ → S) (Y := M') π
  have hf : Function.Injective f.hom.hom := Subtype.val_injective
  have hfg : Function.Exact f.hom.hom g.hom := LinearMap.exact_subtype_ker_map π
  have hf_min : LinearMap.range f.hom.hom ≤ maximalIdeal S • ⊤ :=
    (Submodule.range_subtype (LinearMap.ker π)).le.trans hker_le
  exact ⟨ofInjective f hf (hfg.smul_mem_range (Ideal.Quotient.mk_singleton_self w)),
    (isMinimal_ofInjective_iff hmem hf hfg hπ hf_min).2 hproj,
    ⟨quotientCokernelIsoOfExact hf hfg hπ⟩⟩

/-- **Minimal matrix factorization representation.** Over `R = S ⧸ (w)` (`w ≠ 0`), a finite
`R`-module `M` is isomorphic to the reduced cokernel of a minimal matrix factorization of `w` iff
`M` is maximal Cohen–Macaulay over `R` and has no nonzero projective `R`-retract. -/
theorem exists_isMinimal_quotientCokernel_iso_iff
    (hw : w ≠ 0) (M : ModuleCat.{u} (S ⧸ Ideal.span {w}))
    [Module.Finite (S ⧸ Ideal.span {w}) M] :
    (∃ X : MatrixFactorization S w, X.IsMinimal ∧
      Nonempty ((cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj ≅ M)) ↔
      Module.IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M ∧
        ∀ P : ModuleCat.{u} (S ⧸ Ideal.span {w}), Projective P →
          Nonempty (Retract P M) → IsZero P := by
  have hmem : w ∈ nonZeroDivisors S := mem_nonZeroDivisors_of_ne_zero hw
  refine ⟨?_, fun ⟨hMCM, hproj⟩ ↦
    exists_isMinimal_quotientCokernel_iso_of_isMaximalCohenMacaulay hw M hMCM hproj⟩
  rintro ⟨X, hX, ⟨e⟩⟩
  have hgp : IsGorensteinProjective (S ⧸ Ideal.span {w}) M := (IsGorensteinProjective _).prop_of_iso
    e (isGorensteinProjective_cokernelFunctor_obj_baseChangeFunctor_obj hmem X)
  have hMCM := ((isFiniteMaximalCohenMacaulay_iff _ M).1
    ((isGorensteinProjective_quotient_iff_isFiniteMaximalCohenMacaulay hw M).1 hgp)).2
  have hd₁ := ((isMinimal_iff_range_le_maximalIdeal_smul (X := X)).1 hX).2
  have hno := (range_d₁_le_maximalIdeal_smul_iff_forall_projective_retract_isZero hmem X).1 hd₁
  exact ⟨hMCM, fun P _ ⟨ret⟩ ↦ hno P inferInstance ⟨ret.trans e.symm.retract⟩⟩

/-- **Zero-preperiod minimal resolution.** Every finite maximal Cohen–Macaulay `S ⧸ (w)`-module `M`
with no nonzero projective retract admits a minimal finite-free projective resolution unfolded in
degree `0` from a minimal matrix factorization of `w`. -/
theorem exists_isMinimal_projectiveResolution_of_isMaximalCohenMacaulay
    (hw : w ≠ 0) (M : ModuleCat.{u} (S ⧸ Ideal.span {w}))
    [Module.Finite (S ⧸ Ideal.span {w}) M]
    (hMCM : Module.IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M)
    (hproj : ∀ P : ModuleCat.{u} (S ⧸ Ideal.span {w}), Projective P →
      Nonempty (Retract P M) → IsZero P) :
    ∃ (P : ProjectiveResolution M) (X : MatrixFactorization S w),
      (∀ i, Module.Finite (S ⧸ Ideal.span {w}) (P.complex.X i) ∧
        Module.Free (S ⧸ Ideal.span {w}) (P.complex.X i)) ∧
      P.complex.IsMinimal ∧ X.IsMinimal ∧
      P.complex = PeriodicComplex.resolutionComplex (quotientPeriodicComplex.obj X) 1 := by
  have hmem : w ∈ nonZeroDivisors S := mem_nonZeroDivisors_of_ne_zero hw
  obtain ⟨X, hX, ⟨e⟩⟩ :=
    exists_isMinimal_quotientCokernel_iso_of_isMaximalCohenMacaulay hw M hMCM hproj
  let P := projectiveResolutionOfIso (quotientCokernelProjectiveResolution hmem X) e
  refine ⟨P, X, fun i ↦ ?_,
    (quotientCokernelProjectiveResolution_complex_isMinimal_iff hmem X).2 hX, hX, rfl⟩
  let Q := quotientPeriodicComplex.obj X
  have hfinQ (z : ZMod 2) : Module.Finite (S ⧸ Ideal.span {w}) (Q.X z) := by
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) z with rfl | rfl
    · exact ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X).obj.X₀.property
    · exact ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X).obj.X₁.property
  have : Module.Finite (S ⧸ Ideal.span {w}) (P.complex.X i) := hfinQ ((1 - i : ℤ) : ZMod 2)
  have : Module.Projective (S ⧸ Ideal.span {w}) (P.complex.X i) :=
    (IsProjective.iff_projective (P.complex.X i)).2 (P.projective i)
  exact ⟨‹_›, Module.free_of_projective_of_isLocalRing⟩

private theorem isZero_projective_retract_minimal_syzygy_of_isMaximalCohenMacaulay
    (hw : w ≠ 0) {M F K : ModuleCat.{u} (S ⧸ Ideal.span {w})}
    [Module.Finite (S ⧸ Ideal.span {w}) M]
    [Module.Finite (S ⧸ Ideal.span {w}) F] [Module.Free (S ⧸ Ideal.span {w}) F]
    [Module.Finite (S ⧸ Ideal.span {w}) K] {i : K ⟶ F} {p : F ⟶ M}
    (hi : Function.Injective i.hom) (hip : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom)
    (hi_min : LinearMap.range i.hom ≤ maximalIdeal (S ⧸ Ideal.span {w}) • ⊤)
    (hM : Module.IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M)
    (hK : Module.IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) K)
    (P : ModuleCat.{u} (S ⧸ Ideal.span {w})) [Projective P] (ret : Retract P K) :
    IsZero P := by
  let R := S ⧸ Ideal.span {w}
  have : IsNoetherianRing R := isNoetherianRing_of_surjective S _ _ Ideal.Quotient.mk_surjective
  have hF := (TauCeti.IsRegularLocalRing.isCohenMacaulay_quotient_span_singleton
    hw).isMaximalCohenMacaulay_of_free F
  have hK_fin : IsFiniteMaximalCohenMacaulay.{u} R K := (isFiniteMaximalCohenMacaulay_iff R K).2
    ⟨‹_›, hK⟩
  have hP_mcm := IsFiniteMaximalCohenMacaulay.of_retract ret hK_fin
  have : Module.Finite R P := ((isFiniteMaximalCohenMacaulay_iff R P).1 hP_mcm).1
  let K' : MaximalCohenMacaulayModuleCat.{u} R := ⟨K, hK_fin⟩
  let F' : MaximalCohenMacaulayModuleCat.{u} R :=
    ⟨F, (isFiniteMaximalCohenMacaulay_iff R F).2 ⟨‹_›, hF⟩⟩
  let M' : MaximalCohenMacaulayModuleCat.{u} R :=
    ⟨M, (isFiniteMaximalCohenMacaulay_iff R M).2 ⟨‹_›, hM⟩⟩
  let P' : MaximalCohenMacaulayModuleCat.{u} R := ⟨P, hP_mcm⟩
  let T : ShortComplex (MaximalCohenMacaulayModuleCat.{u} R) :=
    ShortComplex.mk (X₁ := K') (X₂ := F') (X₃ := M') (ObjectProperty.homMk i)
      (ObjectProperty.homMk p)
      (ObjectProperty.hom_ext _ (ModuleCat.hom_ext (LinearMap.ext hip.apply_apply_eq_zero)))
  have hT : (MaximalCohenMacaulayModuleCat.exactStructure.{u} R).Conflation T :=
    (MaximalCohenMacaulayModuleCat.exactStructure_conflation_iff R T).2
      { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hip
        mono_f := (ModuleCat.mono_iff_injective i).2 hi
        epi_g := (ModuleCat.epi_iff_surjective p).2 hp }
  have hInj : (MaximalCohenMacaulayModuleCat.exactStructure.{u} R).isInjective P' :=
    (MaximalCohenMacaulayModuleCat.exactStructure_isInjective_iff hw P').2 inferInstance
  have hinfl := (MaximalCohenMacaulayModuleCat.exactStructure.{u} R).isInflation_f hT
  let r' : K' ⟶ P' := ObjectProperty.homMk ret.r
  let g := hInj.factorThru hinfl r'
  have hg : i ≫ g.hom = ret.r := congrArg InducedCategory.Hom.hom (hInj.comp_factorThru hinfl r')
  have htop : (⊤ : Submodule R P) ≤ maximalIdeal R • ⊤ := fun x _ ↦ by
    have hx : g.hom.hom (i.hom (ret.i.hom x)) = x := by
      change (ret.i ≫ i ≫ g.hom).hom x = x
      rw [hg, ret.retract, ModuleCat.hom_id, LinearMap.id_apply]
    exact hx ▸ Submodule.smul_top_le_comap_smul_top (maximalIdeal R) g.hom.hom
      (hi_min ⟨ret.i.hom x, rfl⟩)
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson _ _ (IsNoetherian.noetherian ⊤) htop
    (ringJacobson_eq_maximalIdeal (R := R)).ge
  have : Subsingleton P :=
    subsingleton_of_forall_eq 0 fun x ↦ (Submodule.mem_bot R).1 (hbot ▸ Submodule.mem_top)
  exact ModuleCat.isZero_of_subsingleton P

/-- **Eisenbud's Theorem 6.1(i), constructive depth-bound form.** If a finite `S ⧸ (w)`-module `M`
satisfies `ringKrullDim (S ⧸ (w)) ≤ depth M + n`, then `M` has a minimal finite-free projective
resolution whose `(n + 1)`-st truncation is isomorphic to the periodic resolution of a minimal
matrix factorization of `w`. -/
theorem exists_isMinimal_projectiveResolution_of_ringKrullDim_le_depth_add
    (hw : w ≠ 0) (n : ℕ) (M : ModuleCat.{u} (S ⧸ Ideal.span {w}))
    [Module.Finite (S ⧸ Ideal.span {w}) M]
    (hn : ringKrullDim (S ⧸ Ideal.span {w}) ≤
      (IsLocalRing.depth M : WithBot ℕ∞) + n) :
    ∃ (P : ProjectiveResolution M) (X : MatrixFactorization S w),
      (∀ i, Module.Finite (S ⧸ Ideal.span {w}) (P.complex.X i) ∧
        Module.Free (S ⧸ Ideal.span {w}) (P.complex.X i)) ∧
      P.complex.IsMinimal ∧ X.IsMinimal ∧
      Nonempty (ChainComplex.truncate.obj^[n + 1] P.complex ≅
        PeriodicComplex.resolutionComplex (quotientPeriodicComplex.obj X) 1) := by
  let R := S ⧸ Ideal.span {w}
  have : IsNoetherianRing R := isNoetherianRing_of_surjective S _ _ Ideal.Quotient.mk_surjective
  induction n generalizing M with
  | zero =>
    rw [Nat.cast_zero, add_zero] at hn
    have hM := Module.isMaximalCohenMacaulay_iff_ringKrullDim_le_depth.2 hn
    obtain ⟨F, K, i, p, _, _, _, _, hi, hip, hp, hi_min⟩ := exists_minimal_syzygy M
    have hF := (TauCeti.IsRegularLocalRing.isCohenMacaulay_quotient_span_singleton
      hw).isMaximalCohenMacaulay_of_free F
    have hK := Module.IsMaximalCohenMacaulay.of_exact_left hip hi hp hF
      (hM.ringKrullDim_le_depth.trans (le_add_of_nonneg_right zero_le_one))
    obtain ⟨Q, X, hQ_ff, hQ_min, hX_min, hQ_eq⟩ :=
      exists_isMinimal_projectiveResolution_of_isMaximalCohenMacaulay hw K hK fun P₀ _ ⟨r⟩ ↦
        isZero_projective_retract_minimal_syzygy_of_isMaximalCohenMacaulay hw hi hip hp
          hi_min hM hK P₀ r
    obtain ⟨P, hP_ff, hP_min, ⟨e_tr⟩⟩ :=
      exists_consProjectiveResolution Q hi hip hp hi_min hQ_ff hQ_min
    exact ⟨P, X, hP_ff, hP_min, hX_min,
      ⟨eqToIso (congrFun (Function.iterate_one _) _) ≪≫ e_tr ≪≫ eqToIso hQ_eq⟩⟩
  | succ n ih =>
    obtain ⟨F, K, i, p, _, _, _, _, hi, hip, hp, hi_min⟩ := exists_minimal_syzygy M
    have hF := (TauCeti.IsRegularLocalRing.isCohenMacaulay_quotient_span_singleton
      hw).isMaximalCohenMacaulay_of_free F
    have hmin₀ := IsLocalRing.depth_min_snd_trd_add_one_le_fst_of_exact i.hom p.hom hip hi hp
    have hdepK : ringKrullDim R ≤ (IsLocalRing.depth K : WithBot ℕ∞) + n := by
      rcases le_total (IsLocalRing.depth F) (IsLocalRing.depth M + 1) with hle | hle
      · have : (IsLocalRing.depth F : WithBot ℕ∞) ≤ IsLocalRing.depth K :=
          WithBot.coe_le_coe.2 ((inf_eq_left.2 hle).symm.le.trans hmin₀)
        exact (hF.ringKrullDim_le_depth.trans
          (le_add_of_nonneg_right (Nat.cast_nonneg n))).trans (by gcongr)
      · have : (IsLocalRing.depth M : WithBot ℕ∞) + 1 ≤ IsLocalRing.depth K := by
          simpa only [WithBot.coe_add, WithBot.coe_one] using
            WithBot.coe_le_coe.2 ((inf_eq_right.2 hle).symm.le.trans hmin₀)
        have hMn : ringKrullDim R ≤ ((IsLocalRing.depth M : WithBot ℕ∞) + 1) + n := by
          simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm (1 : WithBot ℕ∞)] using hn
        exact hMn.trans (by gcongr)
    obtain ⟨Q, X, hQ_ff, hQ_min, hX_min, ⟨eQ⟩⟩ := ih K hdepK
    obtain ⟨P, hP_ff, hP_min, ⟨e_tr⟩⟩ :=
      exists_consProjectiveResolution Q hi hip hp hi_min hQ_ff hQ_min
    exact ⟨P, X, hP_ff, hP_min, hX_min,
      ⟨eqToIso (Function.iterate_succ_apply _ (n + 1) _) ≪≫
        ChainComplex.truncateIterateMapIso e_tr (n + 1) ≪≫ eQ⟩⟩

/-- **Eisenbud's Theorem 6.1(i), depth-bound form.** Every minimal finite-term projective
resolution of `M` over `S ⧸ (w)` (`w ≠ 0`) with `ringKrullDim (S ⧸ (w)) ≤ depth M + n` becomes
periodic of period `2` after at most `n + 1` steps. -/
theorem hasPeriodicTail_two_of_isMinimal
    (hw : w ≠ 0) {n : ℕ} {M : ModuleCat.{u} (S ⧸ Ideal.span {w})}
    (hn : ringKrullDim (S ⧸ Ideal.span {w}) ≤ (IsLocalRing.depth M : WithBot ℕ∞) + n)
    (P : ProjectiveResolution M) [∀ i, Module.Finite (S ⧸ Ideal.span {w}) (P.complex.X i)]
    (hP : P.complex.IsMinimal) :
    P.complex.HasPeriodicTail 2 (n + 1) := by
  have : Module.Finite (S ⧸ Ideal.span {w}) M := finite_of_projectiveResolution P
  obtain ⟨Q, _, hQ_ff, hQ_min, -, ⟨eQ⟩⟩ :=
    exists_isMinimal_projectiveResolution_of_ringKrullDim_le_depth_add hw n M hn
  have (i : ℕ) : Module.Finite (S ⧸ Ideal.span {w}) (Q.complex.X i) := (hQ_ff i).1
  exact (P.hasPeriodicTail_iff_of_isMinimal Q hP hQ_min 2 (n + 1)).2
    (.of_iso_resolutionComplex (by decide) eQ)

/-- **Eisenbud's Theorem 6.1(i), uniform constructive form.** Every finitely generated module over
`R = S ⧸ (w)` (`w ≠ 0`) has a minimal finite-free projective resolution whose truncation after
`(maximalIdeal S).spanFinrank = dim R + 1` steps unfolds a minimal matrix factorization of `w`. -/
theorem exists_isMinimal_projectiveResolution
    (hw : w ≠ 0) (M : ModuleCat.{u} (S ⧸ Ideal.span {w}))
    [Module.Finite (S ⧸ Ideal.span {w}) M] :
    ∃ (P : ProjectiveResolution M) (X : MatrixFactorization S w),
      (∀ i, Module.Finite (S ⧸ Ideal.span {w}) (P.complex.X i) ∧
        Module.Free (S ⧸ Ideal.span {w}) (P.complex.X i)) ∧
      P.complex.IsMinimal ∧ X.IsMinimal ∧
      Nonempty (ChainComplex.truncate.obj^[(maximalIdeal S).spanFinrank] P.complex ≅
        PeriodicComplex.resolutionComplex (quotientPeriodicComplex.obj X) 1) := by
  have : IsNoetherianRing (S ⧸ Ideal.span {w}) :=
    isNoetherianRing_of_surjective S _ _ Ideal.Quotient.mk_surjective
  obtain ⟨r, hr⟩ := Module.exists_supportDim_eq_natCast
    (R := S ⧸ Ideal.span {w}) (M := S ⧸ Ideal.span {w})
  have hdimR : ringKrullDim (S ⧸ Ideal.span {w}) = r :=
    (Module.supportDim_self_eq_ringKrullDim (R := S ⧸ Ideal.span {w})).symm.trans hr
  have hsucc : ringKrullDim (S ⧸ Ideal.span {w}) + 1 = ringKrullDim S :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim (.of_ne_zero hw)
      TauCeti.IsLocalRing.mem_maximalIdeal_of_isLocalRing_quotient_span_singleton
  rw [hdimR, ← _root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)] at hsucc
  have hr1 : r + 1 = (maximalIdeal S).spanFinrank := by exact_mod_cast hsucc
  rw [← hr1]
  refine exists_isMinimal_projectiveResolution_of_ringKrullDim_le_depth_add hw r M ?_
  rw [hdimR]
  exact le_add_of_nonneg_left (WithBot.coe_le_coe.2 (zero_le : (0 : ℕ∞) ≤ IsLocalRing.depth M))

/-- **Eisenbud's Theorem 6.1(i), uniform bound.** Every minimal finite-term projective resolution
over `S ⧸ (w)` (`w ≠ 0`) becomes periodic of period `2` after at most `(maximalIdeal S).spanFinrank`
steps. -/
theorem hasPeriodicTail_two_spanFinrank_of_isMinimal
    (hw : w ≠ 0) {M : ModuleCat.{u} (S ⧸ Ideal.span {w})}
    (P : ProjectiveResolution M) [∀ i, Module.Finite (S ⧸ Ideal.span {w}) (P.complex.X i)]
    (hP : P.complex.IsMinimal) :
    P.complex.HasPeriodicTail 2 (maximalIdeal S).spanFinrank := by
  have : Module.Finite (S ⧸ Ideal.span {w}) M := finite_of_projectiveResolution P
  obtain ⟨Q, _, hQ_ff, hQ_min, -, ⟨eQ⟩⟩ := exists_isMinimal_projectiveResolution hw M
  have (i : ℕ) : Module.Finite (S ⧸ Ideal.span {w}) (Q.complex.X i) := (hQ_ff i).1
  exact (P.hasPeriodicTail_iff_of_isMinimal Q hP hQ_min 2 (maximalIdeal S).spanFinrank).2
    (.of_iso_resolutionComplex (by decide) eQ)

omit [_root_.IsRegularLocalRing S] [IsLocalRing (S ⧸ Ideal.span {w})] in
private theorem nonempty_truncate_two_mul_iso_of_hasPeriodicTail_zero
    {K : ChainComplex (ModuleCat.{u} (S ⧸ Ideal.span {w})) ℕ} (h : K.HasPeriodicTail 2 0) :
    ∀ m : ℕ, Nonempty (ChainComplex.truncate.obj^[2 * m] K ≅ K)
  | 0 => ⟨Iso.refl K⟩
  | m + 1 => by
    obtain ⟨e_step⟩ := h.nonempty_truncate_iterate_iso
    let e_step' : ChainComplex.truncate.obj^[2] K ≅ K := e_step
    obtain ⟨e_ih⟩ := nonempty_truncate_two_mul_iso_of_hasPeriodicTail_zero h m
    exact ⟨eqToIso (by rw [show 2 * (m + 1) = 2 * m + 2 by ring, Function.iterate_add_apply]) ≪≫
      ChainComplex.truncateIterateMapIso e_step' (2 * m) ≪≫ e_ih⟩

omit [_root_.IsRegularLocalRing S] [IsLocalRing (S ⧸ Ideal.span {w})] in
private theorem exists_isMinimal_quotientCokernel_iso_of_iso_resolutionComplex
    {M : ModuleCat.{u} (S ⧸ Ideal.span {w})} (P : ProjectiveResolution M)
    (X : MatrixFactorization S w) (hX : X.IsMinimal) (j : ℤ)
    (e : P.complex ≅ PeriodicComplex.resolutionComplex (quotientPeriodicComplex.obj X) j) :
    ∃ Y : MatrixFactorization S w, Y.IsMinimal ∧
      Nonempty ((cokernelFunctor.obj
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y)).obj ≅ M) := by
  let Q := quotientPeriodicComplex.obj X
  let e₁ := HomologicalComplex.Hom.isoApp e 1
  let e₀ := HomologicalComplex.Hom.isoApp e 0
  rcases (by decide : ∀ z : ZMod 2, z = 1 ∨ z = 0) (j : ZMod 2) with hj | hj
  · have hj1 : ((j - 1 : ℤ) : ZMod 2) = 0 := by push_cast; rw [hj, sub_self]
    let α : (PeriodicComplex.resolutionComplex Q j).X 1 ≅ Q.X 0 := Q.XIsoOfEq (by simpa using hj1)
    let β : (PeriodicComplex.resolutionComplex Q j).X 0 ≅ Q.X 1 := Q.XIsoOfEq (by simpa using hj)
    have hd : (PeriodicComplex.resolutionComplex Q j).d 1 0 ≫ β.hom = α.hom ≫ Q.d 0 1 := by
      rw [PeriodicComplex.resolutionComplex_d]
      exact (Q.d_comp_XIsoOfEq_hom _ _).trans (Q.XIsoOfEq_hom_comp_d _ _).symm
    let dX := ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X).obj.d₀.hom
    have hcomm : (e₁ ≪≫ α).hom ≫ dX = P.complex.d 1 0 ≫ (e₀ ≪≫ β).hom := by
      change (e.hom.f 1 ≫ α.hom) ≫ Q.d 0 1 = P.complex.d 1 0 ≫ e.hom.f 0 ≫ β.hom
      rw [Category.assoc, ← hd, ← Category.assoc, e.hom.comm 1 0, Category.assoc]
    exact ⟨X, hX, ⟨CokernelCofork.mapIsoOfIsColimit (isColimitCokernelπ _)
      P.isColimitCokernelCofork (Arrow.isoMk (e₁ ≪≫ α) (e₀ ≪≫ β) hcomm).symm⟩⟩
  · have hj1 : ((j - 1 : ℤ) : ZMod 2) = 1 := by push_cast; rw [hj]; decide
    let α : (PeriodicComplex.resolutionComplex Q j).X 1 ≅ Q.X 1 := Q.XIsoOfEq (by simpa using hj1)
    let β : (PeriodicComplex.resolutionComplex Q j).X 0 ≅ Q.X 0 := Q.XIsoOfEq (by simpa using hj)
    have hd : (PeriodicComplex.resolutionComplex Q j).d 1 0 ≫ β.hom = α.hom ≫ Q.d 1 0 := by
      rw [PeriodicComplex.resolutionComplex_d]
      exact (Q.d_comp_XIsoOfEq_hom _ _).trans (Q.XIsoOfEq_hom_comp_d _ _).symm
    let Y := parityShift.obj X
    let dY := ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y).obj.d₀.hom
    have hYd₀ : dY = -Q.d 1 0 :=
      (ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {w}))).map_neg
    let negIso : Q.X 1 ≅ Q.X 1 :=
      { hom := -𝟙 _, inv := -𝟙 _, hom_inv_id := by simp, inv_hom_id := by simp }
    have hcomm' : (e.hom.f 1 ≫ α.hom ≫ (-𝟙 (Q.X 1))) ≫ (-Q.d 1 0) =
        P.complex.d 1 0 ≫ e.hom.f 0 ≫ β.hom := by
      rw [Category.assoc, Category.assoc, Preadditive.neg_comp, Category.id_comp, neg_neg,
        ← hd, ← Category.assoc, e.hom.comm 1 0, Category.assoc]
    have hcomm : (e₁ ≪≫ α ≪≫ negIso).hom ≫ dY = P.complex.d 1 0 ≫ (e₀ ≪≫ β).hom :=
      (congrArg ((e.hom.f 1 ≫ α.hom ≫ (-𝟙 (Q.X 1))) ≫ ·) hYd₀).trans hcomm'
    exact ⟨Y, (isMinimal_parityShift_iff X).2 hX, ⟨CokernelCofork.mapIsoOfIsColimit
      (isColimitCokernelπ _) P.isColimitCokernelCofork
      (Arrow.isoMk (e₁ ≪≫ α ≪≫ negIso) (e₀ ≪≫ β) hcomm).symm⟩⟩

/-- **Eisenbud's Theorem 6.1(ii).** For a minimal finite-term projective resolution `P` of an
`S ⧸ (w)`-module `M` (`w ≠ 0`), `P.complex.HasPeriodicTail 2 0` iff `M` is maximal Cohen–Macaulay
over `S ⧸ (w)` and has no nonzero projective `S ⧸ (w)`-retract. -/
theorem hasPeriodicTail_two_zero_iff
    (hw : w ≠ 0) {M : ModuleCat.{u} (S ⧸ Ideal.span {w})}
    (P : ProjectiveResolution M) [∀ i, Module.Finite (S ⧸ Ideal.span {w}) (P.complex.X i)]
    (hP : P.complex.IsMinimal) :
    P.complex.HasPeriodicTail 2 0 ↔
      Module.IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M ∧
        ∀ R_proj : ModuleCat.{u} (S ⧸ Ideal.span {w}), Projective R_proj →
          Nonempty (Retract R_proj M) → IsZero R_proj := by
  have : Module.Finite (S ⧸ Ideal.span {w}) M := finite_of_projectiveResolution P
  refine ⟨fun h0 ↦ ?_, fun ⟨hMCM, hproj⟩ ↦ ?_⟩
  · let p := (maximalIdeal S).spanFinrank
    obtain ⟨Q_M, X, hQ_ff, hQ_min, _, ⟨e_tail⟩⟩ := exists_isMinimal_projectiveResolution hw M
    have (i : ℕ) : Module.Finite (S ⧸ Ideal.span {w}) (Q_M.complex.X i) := (hQ_ff i).1
    let e_min : P.complex ≅ Q_M.complex := P.isoOfMinimal Q_M hP hQ_min
    obtain ⟨e_per⟩ := nonempty_truncate_two_mul_iso_of_hasPeriodicTail_zero h0 p
    let e_res : P.complex ≅
      PeriodicComplex.resolutionComplex (quotientPeriodicComplex.obj X) (1 - p) :=
      e_per.symm ≪≫ eqToIso (by rw [two_mul p, Function.iterate_add_apply]) ≪≫
        ChainComplex.truncateIterateMapIso (ChainComplex.truncateIterateMapIso e_min p) p ≪≫
        ChainComplex.truncateIterateMapIso e_tail p ≪≫
        PeriodicComplex.truncateIterateResolutionComplexIso (quotientPeriodicComplex.obj X) 1 p
    have hX_min : X.IsMinimal :=
      (resolutionComplex_quotientPeriodicComplex_isMinimal_iff X (1 - p)).1 (hP.of_iso e_res)
    exact (exists_isMinimal_quotientCokernel_iso_iff hw M).1
      (exists_isMinimal_quotientCokernel_iso_of_iso_resolutionComplex P X hX_min (1 - p) e_res)
  · obtain ⟨Q, _, hQ_ff, hQ_min, -, hQ_eq⟩ :=
      exists_isMinimal_projectiveResolution_of_isMaximalCohenMacaulay hw M hMCM hproj
    have (i : ℕ) : Module.Finite (S ⧸ Ideal.span {w}) (Q.complex.X i) := (hQ_ff i).1
    exact (P.hasPeriodicTail_iff_of_isMinimal Q hP hQ_min 2 0).2
      (hQ_eq ▸ PeriodicComplex.resolutionComplex_hasPeriodicTail _ 1)

end Hypersurface
end TauCeti.MatrixFactorization
