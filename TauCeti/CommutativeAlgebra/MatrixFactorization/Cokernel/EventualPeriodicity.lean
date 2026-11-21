/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Minimal
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Buchweitz
public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Minimal
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.KrullDimension.Regular
import TauCeti.Algebra.Category.ModuleCat.Projective.FiniteResolution
import TauCeti.Algebra.Category.ModuleCat.Projective.MinimalResolution.ChainComplex
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.CategoryTheory.Abelian.Projective.Resolution
import TauCeti.RingTheory.KrullDimension.Module
import TauCeti.RingTheory.LocalRing.Module
import TauCeti.RingTheory.LocalRing.Quotient
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay

/-!
# Eventual two-periodicity of minimal free resolutions over local hypersurfaces

For a nonzero `w` in the maximal ideal of a regular local ring `S` with local hypersurface quotient
`R = S ⧸ (w)`, this file proves **Eisenbud's Theorem 6.1** (1980) for finite `R`-modules `M`:

* **Theorem 6.1(ii)** (`exists_isMinimal_quotientCokernel_iso_iff`,
  `CategoryTheory.ProjectiveResolution.hasPeriodicTail_two_zero_iff`, and
  `exists_isMinimal_projectiveResolution_with_matrixFactorizationTail_of_isMaximalCohenMacaulay`):
  `M` is maximal Cohen–Macaulay without nonzero projective `R`-retracts iff `M` is the reduced
  cokernel of a minimal matrix factorization of `w`, iff every minimal finite-term resolution of `M`
  has `HasPeriodicTail 2 0`.
* **Theorem 6.1(i)**: if `ringKrullDim R ≤ depth M + n`, minimal resolutions have
  `HasPeriodicTail 2 (n + 1)`
  (`exists_isMinimal_projectiveResolution_with_matrixFactorizationTail_of_ringKrullDim_le_depth_add`
  and `P.hasPeriodicTail_two_of_isMinimal_of_ringKrullDim_le_depth_add` in
  `CategoryTheory.ProjectiveResolution`), giving the uniform bound `(𝔪_S).spanFinrank`
  (`exists_isMinimal_projectiveResolution_with_matrixFactorizationTail_spanFinrank` and
  `CategoryTheory.ProjectiveResolution.hasPeriodicTail_two_spanFinrank_of_isMinimal`).

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
  obtain ⟨π, hπ, hker_le⟩ := TauCeti.IsLocalRing.exists_surjective_ker_le_maximalIdeal_smul S M'
  have : Module.Finite S (LinearMap.ker π) := Module.Finite.iff_fg.2 (IsNoetherian.noetherian _)
  have : Module.Projective S (LinearMap.ker π) := by
    rw [IsProjective.iff_projective, projective_iff_hasProjectiveDimensionLE_zero]
    exact (π.hasProjectiveDimensionLE_succ_iff_ker hπ 0).1 hpd
  let μ := Module.finrank (ResidueField S) (TensorProduct S (ResidueField S) M')
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
theorem exists_isMinimal_projectiveResolution_with_matrixFactorizationTail_of_isMaximalCohenMacaulay
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
  let P := (quotientCokernelProjectiveResolution hmem X).ofIso e
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
      have hcomp : ret.i ≫ i ≫ g.hom = 𝟙 P := by rw [hg, ret.retract]
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply] using congrArg (fun f : P ⟶ P ↦ f.hom x) hcomp
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
theorem
    exists_isMinimal_projectiveResolution_with_matrixFactorizationTail_of_ringKrullDim_le_depth_add
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
  induction n generalizing M with
  | zero =>
    rw [Nat.cast_zero, add_zero] at hn
    have hM := Module.isMaximalCohenMacaulay_iff_ringKrullDim_le_depth.2 hn
    obtain ⟨F, K, i, p, _, _, _, hi, hip, hp, hi_min⟩ := ModuleCat.exists_minimal_syzygy M
    have hF := (TauCeti.IsRegularLocalRing.isCohenMacaulay_quotient_span_singleton
      hw).isMaximalCohenMacaulay_of_free F
    have hK := Module.IsMaximalCohenMacaulay.of_exact_left hip hi hp hF
      (hM.ringKrullDim_le_depth.trans (le_add_of_nonneg_right zero_le_one))
    obtain ⟨Q, X, hQ_ff, hQ_min, hX_min, hQ_eq⟩ :=
      exists_isMinimal_projectiveResolution_with_matrixFactorizationTail_of_isMaximalCohenMacaulay
        hw K hK fun P₀ _ ⟨r⟩ ↦
          isZero_projective_retract_minimal_syzygy_of_isMaximalCohenMacaulay hw hi hip hp
            hi_min hM hK P₀ r
    obtain ⟨P, hP_ff, hP_min, ⟨e_tr⟩⟩ :=
      ModuleCat.exists_consProjectiveResolution Q hi hip hp hi_min hQ_ff hQ_min
    exact ⟨P, X, hP_ff, hP_min, hX_min,
      ⟨eqToIso (congrFun (Function.iterate_one _) _) ≪≫ e_tr ≪≫ eqToIso hQ_eq⟩⟩
  | succ n ih =>
    obtain ⟨F, K, i, p, _, _, _, hi, hip, hp, hi_min⟩ := ModuleCat.exists_minimal_syzygy M
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
      ModuleCat.exists_consProjectiveResolution Q hi hip hp hi_min hQ_ff hQ_min
    exact ⟨P, X, hP_ff, hP_min, hX_min,
      ⟨eqToIso (Function.iterate_succ_apply _ (n + 1) _) ≪≫
        ChainComplex.truncateIterateMapIso e_tr (n + 1) ≪≫ eQ⟩⟩

private theorem exists_ringKrullDim_quotient_add_one_eq_spanFinrank (hw : w ≠ 0) :
    ∃ r : ℕ, ringKrullDim (S ⧸ Ideal.span {w}) = r ∧ r + 1 = (maximalIdeal S).spanFinrank := by
  obtain ⟨r, hr⟩ := Module.exists_supportDim_eq_natCast
    (R := S ⧸ Ideal.span {w}) (M := S ⧸ Ideal.span {w})
  have hdimR : ringKrullDim (S ⧸ Ideal.span {w}) = r :=
    (Module.supportDim_self_eq_ringKrullDim (R := S ⧸ Ideal.span {w})).symm.trans hr
  have hmem : w ∈ maximalIdeal S := (Ideal.span_singleton_le_iff_mem _).1
    (le_maximalIdeal (TauCeti.IsLocalRing.isLocalRing_quotient_iff.1 inferInstance))
  have hsucc : ringKrullDim (S ⧸ Ideal.span {w}) + 1 = ringKrullDim S :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim (.of_ne_zero hw) hmem
  rw [hdimR, ← _root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)] at hsucc
  exact ⟨r, hdimR, by exact_mod_cast hsucc⟩

/-- **Eisenbud's Theorem 6.1(i), uniform constructive form.** Every finitely generated module over
`R = S ⧸ (w)` (`w ≠ 0`) has a minimal finite-free projective resolution whose truncation after
`(maximalIdeal S).spanFinrank = dim R + 1` steps unfolds a minimal matrix factorization of `w`. -/
theorem exists_isMinimal_projectiveResolution_with_matrixFactorizationTail_spanFinrank
    (hw : w ≠ 0) (M : ModuleCat.{u} (S ⧸ Ideal.span {w}))
    [Module.Finite (S ⧸ Ideal.span {w}) M] :
    ∃ (P : ProjectiveResolution M) (X : MatrixFactorization S w),
      (∀ i, Module.Finite (S ⧸ Ideal.span {w}) (P.complex.X i) ∧
        Module.Free (S ⧸ Ideal.span {w}) (P.complex.X i)) ∧
      P.complex.IsMinimal ∧ X.IsMinimal ∧
      Nonempty (ChainComplex.truncate.obj^[(maximalIdeal S).spanFinrank] P.complex ≅
        PeriodicComplex.resolutionComplex (quotientPeriodicComplex.obj X) 1) := by
  obtain ⟨r, hdimR, hr1⟩ := exists_ringKrullDim_quotient_add_one_eq_spanFinrank hw
  rw [← hr1]
  refine
    exists_isMinimal_projectiveResolution_with_matrixFactorizationTail_of_ringKrullDim_le_depth_add
      hw r M ?_
  rw [hdimR]
  exact le_add_of_nonneg_left (WithBot.coe_le_coe.2 (zero_le : (0 : ℕ∞) ≤ IsLocalRing.depth M))

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
  have mkIso {Y : MatrixFactorization S w} (hY : Y.IsMinimal)
      (α' : (PeriodicComplex.resolutionComplex Q j).X 1 ≅
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y).obj.X₀.obj)
      (β' : (PeriodicComplex.resolutionComplex Q j).X 0 ≅
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y).obj.X₁.obj)
      (hsq : (PeriodicComplex.resolutionComplex Q j).d 1 0 ≫ β'.hom =
        α'.hom ≫ ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y).obj.d₀.hom) :
      ∃ Y' : MatrixFactorization S w, Y'.IsMinimal ∧
        Nonempty ((cokernelFunctor.obj
          ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y')).obj ≅ M) :=
    ⟨Y, hY, ⟨CokernelCofork.mapIsoOfIsColimit (isColimitCokernelπ _) P.isColimitCokernelCofork
      (Arrow.isoMk (e₁ ≪≫ α') (e₀ ≪≫ β') (by
        dsimp only [Arrow.mk_hom]
        simp only [e₁, e₀, Iso.trans_hom, HomologicalComplex.Hom.isoApp_hom, Category.assoc]
        rw [← hsq, ← Category.assoc, e.hom.comm 1 0, Category.assoc])).symm⟩⟩
  have mkStep {a b : ZMod 2} (ha : ((j - 1 : ℤ) : ZMod 2) = a) (hb : (j : ZMod 2) = b) :
      {α : (PeriodicComplex.resolutionComplex Q j).X 1 ≅ Q.X a //
        ∃ β : (PeriodicComplex.resolutionComplex Q j).X 0 ≅ Q.X b,
          (PeriodicComplex.resolutionComplex Q j).d 1 0 ≫ β.hom = α.hom ≫ Q.d a b} := by
    let α : (PeriodicComplex.resolutionComplex Q j).X 1 ≅ Q.X a := Q.XIsoOfEq (by simpa using ha)
    let β : (PeriodicComplex.resolutionComplex Q j).X 0 ≅ Q.X b := Q.XIsoOfEq (by simpa using hb)
    exact ⟨α, β, by
      rw [PeriodicComplex.resolutionComplex_d]
      exact (Q.d_comp_XIsoOfEq_hom _ _).trans (Q.XIsoOfEq_hom_comp_d _ _).symm⟩
  rcases (by decide : ∀ z : ZMod 2, z = 1 ∨ z = 0) (j : ZMod 2) with hj | hj
  · have hj1 : ((j - 1 : ℤ) : ZMod 2) = 0 := by push_cast; rw [hj, sub_self]
    obtain ⟨α, β, hd⟩ := mkStep hj1 hj
    have hdX :
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X).obj.d₀.hom = Q.d 0 1 :=
      (baseChangeFunctor_obj_d₀ _ X).trans (quotientPeriodicComplex_obj_d_zero_one X).symm
    exact mkIso hX α β (hd.trans (congrArg (α.hom ≫ ·) hdX.symm))
  · have hj1 : ((j - 1 : ℤ) : ZMod 2) = 1 := by push_cast; rw [hj]; decide
    obtain ⟨α, β, hd⟩ := mkStep hj1 hj
    let Y := parityShift.obj X
    have hY₀ : Q.X 1 =
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y).obj.X₀.obj := by
      rw [quotientPeriodicComplex_obj_X_one, baseChangeFunctor_obj_X₀, parityShift_obj_X₀]
    have hY₁ : Q.X 0 =
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y).obj.X₁.obj := by
      rw [quotientPeriodicComplex_obj_X_zero, baseChangeFunctor_obj_X₁, parityShift_obj_X₁]
    have hYd₀ :
        ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y).obj.d₀.hom =
          -Q.d 1 0 := by
      rw [baseChangeFunctor_obj_d₀, parityShift_obj_d₀, Functor.map_neg, Functor.map_neg,
        quotientPeriodicComplex_obj_d_one_zero]
      rfl
    have hYd₀' :
        eqToHom hY₀ ≫ ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj Y).obj.d₀.hom =
          -Q.d 1 0 ≫ eqToHom hY₁ :=
      ((conj_eqToHom_iff_heq (-Q.d 1 0) _ hY₀ hY₁).2 (heq_of_eq hYd₀.symm)).symm
    let negIso : Q.X 1 ≅ Q.X 1 :=
      { hom := -𝟙 _, inv := -𝟙 _, hom_inv_id := by simp, inv_hom_id := by simp }
    exact mkIso (Y := Y) ((isMinimal_parityShift_iff X).2 hX)
      ((α ≪≫ negIso) ≪≫ eqToIso hY₀) (β ≪≫ eqToIso hY₁) (by
        simp only [Iso.trans_hom, eqToIso.hom, Category.assoc]
        rw [hYd₀']
        dsimp only [negIso]
        simp only [Preadditive.neg_comp, Category.id_comp, neg_neg]
        rw [← Category.assoc, hd, Category.assoc])

end Hypersurface

end TauCeti.MatrixFactorization

namespace CategoryTheory.ProjectiveResolution

section Hypersurface

open TauCeti TauCeti.MatrixFactorization

variable {S : Type u} [CommRing S] [_root_.IsRegularLocalRing S] {w : S}
  [IsLocalRing (S ⧸ Ideal.span {w})]

/-- **Eisenbud's Theorem 6.1(i), depth-bound form.** Every minimal finite-term projective
resolution `P` of `M` over `S ⧸ (w)` (`w ≠ 0`) with `ringKrullDim (S ⧸ (w)) ≤ depth M + n` becomes
periodic of period `2` after at most `n + 1` steps. -/
theorem hasPeriodicTail_two_of_isMinimal_of_ringKrullDim_le_depth_add
    {M : ModuleCat.{u} (S ⧸ Ideal.span {w})} (P : ProjectiveResolution M)
    [∀ i, Module.Finite (S ⧸ Ideal.span {w}) (P.complex.X i)] (hP : P.complex.IsMinimal)
    (hw : w ≠ 0) {n : ℕ}
    (hn : ringKrullDim (S ⧸ Ideal.span {w}) ≤ (IsLocalRing.depth M : WithBot ℕ∞) + n) :
    P.complex.HasPeriodicTail 2 (n + 1) := by
  have : Module.Finite (S ⧸ Ideal.span {w}) M := ModuleCat.finite_of_projectiveResolution P
  obtain ⟨Q, _, hQ_ff, hQ_min, -, ⟨eQ⟩⟩ :=
    exists_isMinimal_projectiveResolution_with_matrixFactorizationTail_of_ringKrullDim_le_depth_add
      hw n M hn
  have (i : ℕ) : Module.Finite (S ⧸ Ideal.span {w}) (Q.complex.X i) := (hQ_ff i).1
  exact (P.hasPeriodicTail_iff_of_isMinimal Q hP hQ_min 2 (n + 1)).2
    (.of_iso_resolutionComplex (by decide) eQ)

/-- **Eisenbud's Theorem 6.1(i), uniform bound.** Every minimal finite-term projective resolution
`P` over `S ⧸ (w)` (`w ≠ 0`) becomes periodic of period `2` after at most
`(maximalIdeal S).spanFinrank` steps. -/
theorem hasPeriodicTail_two_spanFinrank_of_isMinimal
    {M : ModuleCat.{u} (S ⧸ Ideal.span {w})} (P : ProjectiveResolution M)
    [∀ i, Module.Finite (S ⧸ Ideal.span {w}) (P.complex.X i)] (hP : P.complex.IsMinimal)
    (hw : w ≠ 0) :
    P.complex.HasPeriodicTail 2 (maximalIdeal S).spanFinrank := by
  have : Module.Finite (S ⧸ Ideal.span {w}) M := ModuleCat.finite_of_projectiveResolution P
  obtain ⟨r, hdimR, hr1⟩ := exists_ringKrullDim_quotient_add_one_eq_spanFinrank hw
  rw [← hr1]
  refine P.hasPeriodicTail_two_of_isMinimal_of_ringKrullDim_le_depth_add hP hw ?_
  rw [hdimR]
  exact le_add_of_nonneg_left (WithBot.coe_le_coe.2 (zero_le : (0 : ℕ∞) ≤ IsLocalRing.depth M))

/-- **Eisenbud's Theorem 6.1(ii).** For a minimal finite-term projective resolution `P` of an
`S ⧸ (w)`-module `M` (`w ≠ 0`), `P.complex.HasPeriodicTail 2 0` iff `M` is maximal Cohen–Macaulay
over `S ⧸ (w)` and has no nonzero projective `S ⧸ (w)`-retract. -/
theorem hasPeriodicTail_two_zero_iff
    {M : ModuleCat.{u} (S ⧸ Ideal.span {w})} (P : ProjectiveResolution M)
    [∀ i, Module.Finite (S ⧸ Ideal.span {w}) (P.complex.X i)] (hP : P.complex.IsMinimal)
    (hw : w ≠ 0) :
    P.complex.HasPeriodicTail 2 0 ↔
      Module.IsMaximalCohenMacaulay (S ⧸ Ideal.span {w}) M ∧
        ∀ R_proj : ModuleCat.{u} (S ⧸ Ideal.span {w}), Projective R_proj →
          Nonempty (Retract R_proj M) → IsZero R_proj := by
  have : Module.Finite (S ⧸ Ideal.span {w}) M := ModuleCat.finite_of_projectiveResolution P
  refine ⟨fun h0 ↦ ?_, fun ⟨hMCM, hproj⟩ ↦ ?_⟩
  · let p := (maximalIdeal S).spanFinrank
    obtain ⟨Q_M, X, hQ_ff, hQ_min, hX_min, ⟨e_tail⟩⟩ :=
      exists_isMinimal_projectiveResolution_with_matrixFactorizationTail_spanFinrank hw M
    have (i : ℕ) : Module.Finite (S ⧸ Ideal.span {w}) (Q_M.complex.X i) := (hQ_ff i).1
    let e_min : P.complex ≅ Q_M.complex := P.isoOfMinimal Q_M hP hQ_min
    obtain ⟨e_per⟩ := h0.nonempty_truncate_iterate_mul_iso p
    let e_res : P.complex ≅
      PeriodicComplex.resolutionComplex (quotientPeriodicComplex.obj X) (1 - p) :=
      e_per.symm ≪≫
        eqToIso (by rw [Function.iterate_zero_apply, two_mul p, Function.iterate_add_apply]) ≪≫
        ChainComplex.truncateIterateMapIso (ChainComplex.truncateIterateMapIso e_min p) p ≪≫
        ChainComplex.truncateIterateMapIso e_tail p ≪≫
        PeriodicComplex.truncateIterateResolutionComplexIso (quotientPeriodicComplex.obj X) 1 p
    exact (exists_isMinimal_quotientCokernel_iso_iff hw M).1
      (exists_isMinimal_quotientCokernel_iso_of_iso_resolutionComplex P X hX_min (1 - p) e_res)
  · obtain ⟨Q, _, hQ_ff, hQ_min, -, hQ_eq⟩ :=
      exists_isMinimal_projectiveResolution_with_matrixFactorizationTail_of_isMaximalCohenMacaulay
        hw M hMCM hproj
    have (i : ℕ) : Module.Finite (S ⧸ Ideal.span {w}) (Q.complex.X i) := (hQ_ff i).1
    exact (P.hasPeriodicTail_iff_of_isMinimal Q hP hQ_min 2 0).2
      (hQ_eq ▸ PeriodicComplex.resolutionComplex_hasPeriodicTail _ 1)

end Hypersurface

end CategoryTheory.ProjectiveResolution
