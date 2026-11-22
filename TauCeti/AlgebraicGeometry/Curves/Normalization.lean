/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.Curves.Resolution
public import TauCeti.AlgebraicGeometry.IdealSheaf.Conductor.Cohomology
public import TauCeti.AlgebraicGeometry.Normalization.Modification
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
import TauCeti.AlgebraicGeometry.Cohomology.Cech.Basic
import TauCeti.AlgebraicGeometry.Cohomology.Spec
import TauCeti.AlgebraicGeometry.Curves.Cohomology.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Finite
import TauCeti.AlgebraicGeometry.Morphisms.Separated

/-!
# The normalization exact sequence and genus comparison for curves

Let `X` be a proper integral curve over an arbitrary field `k` (`X.IsCurveOver k`), possibly
singular, and let `f : Y ⟶ X` be a finite modification over `k`, for instance the normalization
`ν : X^ν ⟶ X` of `X` in its function field along `Spec k(X) ⟶ X`. Because `X` is reduced and `f`
is dominant, pullback of regular functions fits into the short exact sequence of `𝒪_X`-modules

`0 ⟶ 𝒪_X ⟶ f_* 𝒪_Y ⟶ Q ⟶ 0`,

where `Q = coker(𝒪_X ⟶ f_* 𝒪_Y)` is pushed forward from the Artinian (hence affine) conductor
closed subscheme `V(f.conductor)`
(`AlgebraicGeometry.Scheme.Hom.cokernelUnitToPushforwardIsoPushforward`). The general cohomological
properties of `Q` and of this exact sequence for finite modifications in dimension at most one are
proved in `TauCeti.AlgebraicGeometry.IdealSheaf.Conductor.Cohomology`.

Combining those general results with Čech comparison along the affine morphism `f`, we deduce:

* **Resolution of curves over any field**: birational equivalence preserves Krull dimension over a
  field (`AlgebraicGeometry.Scheme.Birational.topologicalKrullDim_eq_of_locallyOfFiniteType`), so
  any reduced modification of a curve over `k` is again a curve over `k`
  (`AlgebraicGeometry.Scheme.IsCurveOver.of_isModification`). By Japanese finiteness over fields,
  the normalization of `X` in `k(X)` is finite over `X`, regular
  (`AlgebraicGeometry.Scheme.IsCurveOver.isRegular_normalization`), and a curve over `k`
  (`AlgebraicGeometry.Scheme.IsCurveOver.isCurveOver_normalization`).
* **Unconditional vanishing and finiteness of structure-sheaf cohomology on singular curves**:
  transferring Grothendieck vanishing and finiteness from the regular normalization `X^ν` along the
  long exact sequence shows that `Hⁿ(X, 𝒪_X) = 0` for `n ≥ 2` and `dim_k Hⁿ(X, 𝒪_X) < ∞` for all
  `n` on every proper integral curve `X` over `k` (with no smoothness, regularity, perfect-field,
  or rational-point assumption). Registering `FiniteDimensional k Hⁿ(X, 𝒪_X)` as an instance makes
  `X.genus k` available on every `X.IsCurveOver k`.
* **Genus comparison and the `δ`-invariant regularity criterion**: for any finite modification
  `f : Y ⟶ X` of curves over `k`, `H¹(X, 𝒪_X)` surjects onto `H¹(Y, 𝒪_Y)`, giving
  `Y.genus k ≤ X.genus k` (`AlgebraicGeometry.Scheme.genus_le_of_isModification`), and
  Euler-characteristic additivity gives the general genus-drop relation over any field `k`:
  `X.genus k + dim_k H⁰(Y, 𝒪_Y) = Y.genus k + dim_k H⁰(X, 𝒪_X) + dim_k Γ(Q, ⊤)`
  (`AlgebraicGeometry.Scheme.genus_add_finrank_cohomology_zero_of_isModification`).
  Over a non-algebraically closed field, pinching a closed point to a subfield can keep
  `X.genus k = Y.genus k` while enlarging `dim_k H⁰(Y, 𝒪_Y) - dim_k H⁰(X, 𝒪_X)`; when all global
  functions on `Y` are constants in `k`, the relation simplifies to
  `X.genus k = Y.genus k + dim_k Γ(Q, ⊤)`. Over every field `k`, the global `δ`-invariant
  `dim_k Γ(Q, ⊤)` vanishes if and only if `f` is an isomorphism, so `X` is regular (equivalently
  normal) if and only if `dim_k Γ(coker(𝒪_X ⟶ ν_* 𝒪_{X^ν}), ⊤) = 0`.

## References

* J.-P. Serre, *Algebraic Groups and Class Fields*, GTM 117, Chapter IV, §1, Proposition 1.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Chapter IV, Exercise 1.8.
* [Stacks Project, Lemma 33.41.1](https://stacks.math.columbia.edu/tag/0C45) and
  [Lemma 53.19.3](https://stacks.math.columbia.edu/tag/0CE4).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open Module (finrank)

universe u

namespace AlgebraicGeometry.Scheme

/-- Every curve `X` over a field `k` admits a finite, scheme-theoretically dominant `k`-modification
from a regular curve over `k`, namely its normalization in `k(X)`. -/
private theorem exists_isRegular_isModification_of_isCurveOver (k : Type u) [Field k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] [X.IsCurveOver k] :
    ∃ (Y : Scheme.{u}) (_ : Y.Over (Spec (.of k))) (_ : Y.IsCurveOver k) (_ : IsRegular Y)
      (ν : Y ⟶ X), ν.IsOver (Spec (.of k)) ∧ IsFinite ν ∧ IsModification ν ∧
        IsSchemeTheoreticallyDominant ν := by
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  have := isFinite_fromNormalization_fromSpecStalk_genericPoint_of_locallyOfFiniteType
    (X ↘ Spec (.of k))
  let _ : ((X.fromSpecStalk (genericPoint X)).normalization).Over (Spec (.of k)) :=
    ⟨ν ≫ X ↘ Spec (.of k)⟩
  have : ν.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsRegular (X.fromSpecStalk (genericPoint X)).normalization :=
    IsCurveOver.isRegular_normalization k
  exact ⟨_, inferInstance, inferInstance, inferInstance, ν, inferInstance, inferInstance,
    inferInstance, .of_isDominant ν⟩

namespace Modules

section CurveCohomology

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **Grothendieck vanishing for the structure sheaf on a singular curve.** On every proper integral
curve `X` over a field `k` (with no regularity or smoothness hypothesis), `Hⁿ(X, 𝒪_X) = 0` for all
`n ≥ 2`. -/
theorem subsingleton_cohomology_unit_of_two_le_of_isCurveOver [X.IsCurveOver k]
    (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (Cohomology (SheafOfModules.unit X.ringCatSheaf : X.Modules) n) := by
  obtain ⟨Y, _, _, _, ν, _, _, _, _⟩ := exists_isRegular_isModification_of_isCurveOver k (X := X)
  have := IsCurveOver.isNoetherian k X
  have : X.IsSeparated := Scheme.IsSeparated.of_isSeparated (X ↘ Spec (.of k))
  have : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    AlgebraicGeometry.isQuasicoherent_structureSheaf Y
  rw [subsingleton_cohomology_unit_iff_of_two_le_of_isModification
    (IsCurveOver.topologicalKrullDim_eq_one k).le ν n hn]
  exact subsingleton_cohomology_of_two_le_of_isCurveOver k _ n hn

/-- **Grothendieck vanishing for the trivial line bundle on a singular curve.** On every proper
integral curve `X` over a field `k`, `Hⁿ(X, 𝒪_X) = 0` for all `n ≥ 2`. -/
theorem subsingleton_cohomology_trivial_of_two_le_of_isCurveOver [X.IsCurveOver k]
    (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (Cohomology (InvertibleSheaf.trivial X).obj n) := by
  have := subsingleton_cohomology_unit_of_two_le_of_isCurveOver k (X := X) n hn
  exact (trivialCohomologyBaseLinearEquiv k X n).toEquiv.subsingleton

/-- **Finiteness of structure-sheaf cohomology on any curve over a field.** On every proper
integral curve `X` over a field `k` (possibly singular, over an arbitrary field `k`),
`Hⁿ(X, 𝒪_X)` is finite-dimensional over `k` in every degree `n`. Registering this as an instance
makes `X.genus k` available unconditionally on every proper integral curve `[X.IsCurveOver k]`. -/
instance finiteDimensional_cohomology_trivial_of_isCurveOver [X.IsCurveOver k] (n : ℕ) :
    FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj n) := by
  obtain ⟨Y, _, _, _, ν, _, _, _, _⟩ := exists_isRegular_isModification_of_isCurveOver k (X := X)
  have := IsCurveOver.isNoetherian k X
  have : X.IsSeparated := Scheme.IsSeparated.of_isSeparated (X ↘ Spec (.of k))
  have hdim := (IsCurveOver.topologicalKrullDim_eq_one (X := X) k).le
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let _ : ∀ d, Module k (Cohomology OX d) := cohomologyBaseModule k X OX
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  have : OY.IsQuasicoherent := AlgebraicGeometry.isQuasicoherent_structureSheaf Y
  have : OY.IsFiniteType := inferInstance
  have hpush (m : ℕ) : FiniteDimensional k (Cohomology ((pushforward ν).obj OY) m) := by
    let _ : Module k (Cohomology OY m) := cohomologyBaseModule k Y OY m
    have := finiteDimensional_cohomology_of_isCurveOver k OY m
    exact Module.Finite.equiv (ν.cohomologyPushforwardBaseLinearEquivOfIsAffineHom k OY m).symm
  let φ : OX ⟶ (pushforward ν).obj OY :=
    SheafOfModules.unitToPushforwardObjUnit ν.toRingCatSheafHom
  have : Mono φ := ν.mono_unitToPushforwardObjUnit
  have hOX : FiniteDimensional k (Cohomology OX n) := by
    cases n with
    | zero =>
      have := hpush 0
      exact finiteDimensional_cohomology_zero_of_mono k X φ
    | succ n =>
      cases n with
      | zero =>
        have hS := TauCeti.cokernelSequence_shortExact φ
        have : FiniteDimensional k (Cohomology (ShortComplex.cokernelSequence φ).X₃ 0) :=
          ν.moduleFinite_cohomology_cokernel_unitToPushforwardObjUnit k hdim 0
        have : FiniteDimensional k (Cohomology (ShortComplex.cokernelSequence φ).X₂ 1) := hpush 1
        exact finiteDimensional_cohomology_X₁ k X hS 0 1 rfl
      | succ m =>
        have := subsingleton_cohomology_unit_of_two_le_of_isCurveOver k (X := X) (m + 2) (by omega)
        infer_instance
  exact Module.Finite.equiv (trivialCohomologyBaseLinearEquiv k X n).symm

/-- On any proper integral scheme `X` over a field `k` of Krull dimension at most one (covering
both reduced points of finite residue degree and possibly-singular curves), `Hⁿ(X, 𝒪_X)` is
finite-dimensional over `k` in every degree `n`. -/
theorem finiteDimensional_cohomology_trivial_of_topologicalKrullDim_le_one
    [IsIntegral X] [IsProper (X ↘ Spec (.of k))] (hX : topologicalKrullDim X ≤ 1) (n : ℕ) :
    FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj n) := by
  have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim X :=
    (WithBot.coe_le_coe.mpr (zero_le : (0 : ℕ∞) ≤ _)).trans
      (coheight_le_topologicalKrullDim (Classical.arbitrary X))
  rcases hX.eq_or_lt with hdim1 | hlt
  · have : X.IsCurveOver k := isCurveOver_iff.mpr ⟨inferInstance, inferInstance, hdim1⟩
    infer_instance
  · have hdim0 : topologicalKrullDim X = 0 :=
      le_antisymm (ENat.WithBot.lt_add_one_iff (m := 0).mp (by simpa using hlt)) h0
    have hsub : Subsingleton X := topologicalKrullDim_eq_zero_iff_subsingleton.mp hdim0
    have : LocallyQuasiFinite (X ↘ Spec (.of k)) :=
      LocallyQuasiFinite.of_finite_preimage_singleton (X ↘ Spec (.of k)) fun _ ↦ Set.toFinite _
    have : IsFinite (X ↘ Spec (.of k)) := .of_locallyQuasiFinite _
    let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let _ : Module k (Cohomology OX n) := cohomologyBaseModule k X OX n
    have : OX.IsQuasicoherent := AlgebraicGeometry.isQuasicoherent_structureSheaf X
    have : OX.IsFiniteType := inferInstance
    have : FiniteDimensional k (Cohomology OX n) :=
      moduleFinite_cohomology_of_isFinite_over_spec k OX n
    exact Module.Finite.equiv (trivialCohomologyBaseLinearEquiv k X n).symm

end CurveCohomology

end Modules

section GenusComparison

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]

/-- **Euler-characteristic comparison along a finite modification of curves.** For a finite
modification `f : Y ⟶ X` over `k` of a curve `X` over `k` with reduced source `Y`,
`χ(Y, 𝒪_Y) = χ(X, 𝒪_X) + dim_k Γ(coker(𝒪_X ⟶ f_* 𝒪_Y), ⊤)`. -/
theorem eulerCharBelow_trivial_of_isModification [X.IsCurveOver k] [IsReduced Y]
    (f : Y ⟶ X) [IsFinite f] [IsModification f] [f.IsOver (Spec (.of k))] :
    eulerCharBelow k Y (InvertibleSheaf.trivial Y).obj 2 =
      eulerCharBelow k X (InvertibleSheaf.trivial X).obj 2 +
        (finrank k
          Γ((cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) : X.Modules),
            ⊤) : ℤ) := by
  have : Y.IsCurveOver k := IsCurveOver.of_isModification k f
  have := IsCurveOver.isNoetherian k X
  have : X.IsSeparated := Scheme.IsSeparated.of_isSeparated (X ↘ Spec (.of k))
  have hdim := (IsCurveOver.topologicalKrullDim_eq_one (X := X) k).le
  have : IsSchemeTheoreticallyDominant f := .of_isDominant f
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let _ : ∀ m, Module k (Cohomology OX m) := cohomologyBaseModule k X OX
  let _ : ∀ m, Module k (Cohomology OY m) := cohomologyBaseModule k Y OY
  have : OY.IsQuasicoherent := AlgebraicGeometry.isQuasicoherent_structureSheaf Y
  let φ : OX ⟶ (pushforward f).obj OY :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have : Mono φ := f.mono_unitToPushforwardObjUnit
  have hS := TauCeti.cokernelSequence_shortExact φ
  let ePush (m : ℕ) := f.cohomologyPushforwardBaseLinearEquivOfIsAffineHom k OY m
  have hY_eq : eulerCharBelow k Y (InvertibleSheaf.trivial Y).obj 2 =
      eulerCharBelow k X ((pushforward f).obj OY) 2 := by
    rw [eulerCharBelow_two, eulerCharBelow_two,
      (trivialCohomologyBaseLinearEquiv k Y 0).finrank_eq,
      (trivialCohomologyBaseLinearEquiv k Y 1).finrank_eq,
      ← (ePush 0).finrank_eq, ← (ePush 1).finrank_eq]
  have hX_eq : eulerCharBelow k X (InvertibleSheaf.trivial X).obj 2 =
      eulerCharBelow k X OX 2 := by
    rw [eulerCharBelow_two, eulerCharBelow_two,
      (trivialCohomologyBaseLinearEquiv k X 0).finrank_eq,
      (trivialCohomologyBaseLinearEquiv k X 1).finrank_eq]
  have hpush_fd (m : ℕ) : FiniteDimensional k (Cohomology ((pushforward f).obj OY) m) := by
    have : FiniteDimensional k (Cohomology OY m) :=
      Module.Finite.equiv (trivialCohomologyBaseLinearEquiv k Y m)
    exact Module.Finite.equiv (ePush m).symm
  have hadd := eulerCharBelow_eq_add k hS 2
    (fun i _ _ ↦ Module.Finite.equiv (trivialCohomologyBaseLinearEquiv k X i))
    (fun i _ ↦ hpush_fd i)
    (subsingleton_cohomology_unit_of_two_le_of_isCurveOver k (X := X) 2 le_rfl)
  exact hY_eq.trans (hadd.trans (congrArg₂ (· + ·) hX_eq.symm
    (f.eulerCharBelow_cokernel_unitToPushforwardObjUnit k hdim 1)))

/-- **Monotonicity of the arithmetic genus under a finite modification.** For any finite
modification `f : Y ⟶ X` of curves over `k`, the surjection `H¹(X, 𝒪_X) ↠ H¹(Y, 𝒪_Y)` gives
`Y.genus k ≤ X.genus k`, over any field `k`. -/
theorem genus_le_of_isModification [X.IsCurveOver k] [Y.IsCurveOver k]
    (f : Y ⟶ X) [IsFinite f] [IsModification f] [f.IsOver (Spec (.of k))] :
    Y.genus k ≤ X.genus k := by
  have := IsCurveOver.isNoetherian k X
  have : X.IsSeparated := Scheme.IsSeparated.of_isSeparated (X ↘ Spec (.of k))
  have hdim := (IsCurveOver.topologicalKrullDim_eq_one (X := X) k).le
  have : IsSchemeTheoreticallyDominant f := .of_isDominant f
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let _ : Module k (Cohomology OX 1) := cohomologyBaseModule k X OX 1
  let _ : Module k (Cohomology OY 1) := cohomologyBaseModule k Y OY 1
  have : FiniteDimensional k (Cohomology OX 1) :=
    Module.Finite.equiv (trivialCohomologyBaseLinearEquiv k X 1)
  have : OY.IsQuasicoherent := AlgebraicGeometry.isQuasicoherent_structureSheaf Y
  let ePush := f.cohomologyPushforwardBaseLinearEquivOfIsAffineHom k OY 1
  let φ : OX ⟶ (pushforward f).obj OY :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let ψ : Cohomology OX 1 →ₗ[k] Cohomology OY 1 :=
    ePush.toLinearMap.comp (cohomologyMapBaseLinear k X φ 1)
  have hsurj : Function.Surjective ψ := ePush.surjective.comp (by
    rw [coe_cohomologyMapBaseLinear]
    exact f.cohomologyMap_unitToPushforwardObjUnit_one_surjective hdim)
  rw [Scheme.genus_def, Scheme.genus_def, (trivialCohomologyBaseLinearEquiv k Y 1).finrank_eq,
    (trivialCohomologyBaseLinearEquiv k X 1).finrank_eq]
  exact LinearMap.finrank_le_finrank_of_surjective hsurj

/-- **Exact genus-drop formula along a finite modification over an arbitrary field.** For any
finite modification `f : Y ⟶ X` of curves over `k` (without assuming `k` algebraically closed or
the existence of a `k`-rational point),
`X.genus k + dim_k H⁰(Y, 𝒪_Y) = Y.genus k + dim_k H⁰(X, 𝒪_X) + dim_k Γ(coker(𝒪_X ⟶ f_* 𝒪_Y), ⊤)`. -/
theorem genus_add_finrank_cohomology_zero_of_isModification [X.IsCurveOver k] [Y.IsCurveOver k]
    (f : Y ⟶ X) [IsFinite f] [IsModification f] [f.IsOver (Spec (.of k))] :
    X.genus k + finrank k (Cohomology (InvertibleSheaf.trivial Y).obj 0) =
      Y.genus k + finrank k (Cohomology (InvertibleSheaf.trivial X).obj 0) +
        finrank k
          Γ((cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) : X.Modules),
            ⊤) := by
  have h := eulerCharBelow_trivial_of_isModification k f
  rw [eulerCharBelow_two, eulerCharBelow_two, ← Scheme.genus_def, ← Scheme.genus_def] at h
  omega

/-- **Genus-drop formula when all global functions on the source are constants.** If `f : Y ⟶ X` is
a finite modification of curves over `k` and every global function on `Y` comes from `k` (for
instance when `Y` has a `k`-rational point or `k` is algebraically closed), then the same holds on
`X` and `X.genus k = Y.genus k + dim_k Γ(coker(𝒪_X ⟶ f_* 𝒪_Y), ⊤)`. -/
theorem genus_eq_add_finrank_globalSections_cokernel_of_surjective
    [X.IsCurveOver k] [Y.IsCurveOver k]
    (f : Y ⟶ X) [IsFinite f] [IsModification f] [f.IsOver (Spec (.of k))]
    (hY : Function.Surjective (baseRingToGlobalSections k Y)) :
    X.genus k = Y.genus k +
      finrank k
        Γ((cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) : X.Modules),
          ⊤) := by
  have : IsSchemeTheoreticallyDominant f := .of_isDominant f
  have hX : Function.Surjective (baseRingToGlobalSections k X) := fun s ↦ by
    obtain ⟨c, hc⟩ := hY (f.appTop s)
    refine ⟨c, f.app_injective ⊤ ?_⟩
    have hover := ConcreteCategory.congr_hom
      (congrArg Scheme.Hom.appTop (HomIsOver.comp_over (f := f) (S := Spec (.of k))))
      ((Scheme.ΓSpecIso (.of k)).inv c)
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← baseRingToGlobalSections_apply k X,
      ← baseRingToGlobalSections_apply k Y, hc] at hover
    exact hover
  have hY1 := finrank_cohomology_zero_trivial_eq_one_of_surjective k hY
  have hX1 := finrank_cohomology_zero_trivial_eq_one_of_surjective k hX
  have h := genus_add_finrank_cohomology_zero_of_isModification k f
  omega

omit [Y.Over (Spec (.of k))] in
/-- **The `δ`-invariant vanishes if and only if the finite modification is an isomorphism.** Over
any field `k`, for a finite modification `f : Y ⟶ X` of a curve `X` over `k`,
`dim_k Γ(coker(𝒪_X ⟶ f_* 𝒪_Y), ⊤) = 0 ↔ IsIso f`. Because the target curve `X` is integral (hence
reduced) and modifications are dominant, `f` is automatically scheme-theoretically dominant. -/
theorem finrank_globalSections_cokernel_unitToPushforwardObjUnit_eq_zero_iff_isIso
    [X.IsCurveOver k] (f : Y ⟶ X) [IsFinite f] [IsModification f] :
    finrank k
        Γ((cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) : X.Modules),
          ⊤) =
      0 ↔ IsIso f := by
  have := IsCurveOver.isNoetherian k X
  have : IsSchemeTheoreticallyDominant f := .of_isDominant f
  have hdim := (IsCurveOver.topologicalKrullDim_eq_one (X := X) k).le
  have : FiniteDimensional k
      Γ((cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) : X.Modules), ⊤) :=
    f.moduleFinite_globalSections_cokernel_unitToPushforwardObjUnit k hdim
  exact (Module.finrank_eq_zero_iff_of_free k _).trans
    (f.subsingleton_globalSections_cokernel_unitToPushforwardObjUnit_iff_isIso hdim)

/-- **Regularity criterion via the normalization `δ`-invariant.** Over any field `k`, a curve `X`
over `k` is regular if and only if the global `δ`-invariant
`dim_k Γ(coker(𝒪_X ⟶ ν_* 𝒪_{X^ν}), ⊤)` of its normalization `ν : X^ν ⟶ X` vanishes (Serre,
Chapter IV, §1, Proposition 1; Hartshorne, Exercise IV.1.8(a)). -/
theorem IsCurveOver.isRegular_iff_finrank_globalSections_cokernel_fromNormalization_eq_zero
    [X.IsCurveOver k] :
    IsRegular X ↔
      finrank k
        Γ((cokernel (SheafOfModules.unitToPushforwardObjUnit
            (X.fromSpecStalk (genericPoint X)).fromNormalization.toRingCatSheafHom) :
          X.Modules), ⊤) = 0 := by
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  have := isFinite_fromNormalization_fromSpecStalk_genericPoint_of_locallyOfFiniteType
    (X ↘ Spec (.of k))
  have := IsCurveOver.isNoetherian k X
  refine Iff.trans ?_
    (finrank_globalSections_cokernel_unitToPushforwardObjUnit_eq_zero_iff_isIso k ν).symm
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have : IsNormalScheme X := IsRegular.isNormal
    exact IsModification.isIso_of_isFinite ν
  · have : IsRegular (X.fromSpecStalk (genericPoint X)).normalization :=
      IsCurveOver.isRegular_normalization k
    exact IsRegular.of_isOpenImmersion (inv ν)

/-- When all global functions on the normalization `Y` of a curve `X` over `k` are constants in
`k`, the curve `X` is regular if and only if its arithmetic genus equals the genus of its
normalization. -/
theorem IsCurveOver.isRegular_iff_genus_eq_genus_normalization [X.IsCurveOver k]
    [((X.fromSpecStalk (genericPoint X)).normalization).Over (Spec (.of k))]
    [((X.fromSpecStalk (genericPoint X)).fromNormalization).IsOver (Spec (.of k))]
    (hY : Function.Surjective
      (baseRingToGlobalSections k (X.fromSpecStalk (genericPoint X)).normalization)) :
    IsRegular X ↔
      X.genus k = ((X.fromSpecStalk (genericPoint X)).normalization).genus k := by
  have := isFinite_fromNormalization_fromSpecStalk_genericPoint_of_locallyOfFiniteType
    (X ↘ Spec (.of k))
  have hgen := genus_eq_add_finrank_globalSections_cokernel_of_surjective k
    (X.fromSpecStalk (genericPoint X)).fromNormalization hY
  rw [IsCurveOver.isRegular_iff_finrank_globalSections_cokernel_fromNormalization_eq_zero k]
  omega

end GenusComparison

end AlgebraicGeometry.Scheme

end
