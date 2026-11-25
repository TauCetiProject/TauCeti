/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Restriction
public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol.Section
public import TauCeti.Geometry.Manifold.DifferentialOperator.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Pow
import TauCeti.Geometry.Manifold.MFDeriv.Localized
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Restricting differential operators between sections to open subsets

Let `V` and `W` be smooth real vector bundles over a finite-dimensional Hausdorff smooth manifold
`M`, with `W` of finite rank, and let `U ⊆ M` be open. The restrictions `V|_U` and `W|_U` are the
pullbacks of `V` and `W` along the inclusion of `U`, whose fibres over `x ∈ U` are those of `V`
and `W` over `x`. A differential operator `P : Γ(V) → Γ(W)` of order at most `m`, in Grothendieck's
sense (`TauCeti.differentialOperators`), is local
(`TauCeti.differentialOperators_section_apply_eq_zero_of_eventuallyEq`), and every smooth section
`s` of `V|_U` agrees near each point `x ∈ U` with a global smooth section `t` of `V`
(`ContMDiffSection.exists_eventually_eq_of_opens`), so

`(P|_U s)(x) = (P t)(x)`

is well defined. This gives the restriction `P|_U : Γ(V|_U) → Γ(W|_U)`, a differential operator of
order at most `m` over `C^∞(U)` (`TopologicalSpace.Opens.restrictSectionDifferentialOperators`).
It is the unique operator on `U` with `P|_U (t|_U) = (P t)|_U` for every global section `t`
(`TopologicalSpace.Opens.eq_restrictSectionDifferentialOperators_iff`). No continuity of `P` is
assumed, and boundary points are allowed.

Restriction commutes with composition and with commutators by multiplication operators, and it
preserves the principal symbol: at an interior point `x ∈ U` the principal symbol of `P|_U` at
`ξ ∘ ι` is that of `P` at `ξ`, where `ι : T_x U ≃ T_x M` is the identification of the tangent
spaces (`TauCeti.Manifold.tangentSpaceOpenEquiv`). This is the bundle version of
`TopologicalSpace.Opens.restrictDifferentialOperators` for operators on smooth functions. It is
how properties of an operator defined by its principal symbol, such as ellipticity and being of
Laplace type, pass to open subsets, and how a global operator is compared with its expressions in
charts and local frames.

## Main definitions

* `TopologicalSpace.Opens.restrictSectionDifferentialOperators U m`: restriction `P ↦ P|_U` of the
  differential operators of order at most `m` between sections to the open subset `U`, as a linear
  map.

## Main results

* `TopologicalSpace.Opens.restrictSectionDifferentialOperators_apply_of_eventuallyEq`:
  `(P|_U s)(x) = (P t)(x)` for any global section `t` agreeing with `s` near `x`.
* `TopologicalSpace.Opens.restrictSectionDifferentialOperators_apply_restrict`:
  `P|_U (t|_U) = (P t)|_U`.
* `TopologicalSpace.Opens.eq_restrictSectionDifferentialOperators_iff`: uniqueness of the
  restriction.
* `TopologicalSpace.Opens.restrictSectionDifferentialOperators_comp`: restriction commutes with
  composition.
* `TauCeti.smulCommutator_restrictSectionDifferentialOperators`: restriction commutes with
  commutators.
* `TauCeti.sectionPrincipalSymbol_restrictSectionDifferentialOperators`: restriction preserves the
  principal symbol.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §19 (linear differential operators between vector bundles and their locality).
* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

open Bundle Filter TopologicalSpace
open ContMDiffSection (extendAt eventually_extendAt eventually_add_eq_of_opens
  eventually_smul_eq_of_opens eventually_smul_function_eq_of_opens)
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W]
  (U : Opens M)

/-! ### Values of the restriction -/

/-- The value at `x ∈ U` of the restriction of `P` to `U` on `s`: the value at `x` of `P` on a
global smooth section agreeing with `s` near `x`. -/
private def restrictValue (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯)
    (s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯) (x : U) : W x :=
  P (extendAt s x) x

variable {U} {m k : ℕ}

/-- Two global sections agreeing near `x ∈ U` with the same section of `V|_U` have the same value
under a differential operator at `x`. -/
private theorem apply_eq_of_eventuallyEq {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    {s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯} {x : U}
    {t t' : Cₛ^∞⟮I; F, V⟯} (ht : ∀ᶠ y : U in 𝓝 x, t y = s y)
    (ht' : ∀ᶠ y : U in 𝓝 x, t' y = s y) : P t x = P t' x := by
  rw [← sub_eq_zero, ← Pi.sub_apply, ← ContMDiffSection.coe_sub, ← map_sub]
  refine differentialOperators_section_apply_eq_zero_of_eventuallyEq hP ?_
  -- `𝓝 x` in `M` is the image of `𝓝 x` in `U`.
  rw [← U.isOpenEmbedding'.map_nhds_eq x, eventually_map]
  filter_upwards [ht, ht'] with y hy hy'
  rw [ContMDiffSection.coe_sub, Pi.sub_apply]
  -- The fibre of `V|_U` over `y` is the fibre of `V` over `y`.
  exact sub_eq_zero.2 (hy.trans hy'.symm)

private theorem restrictValue_eq {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    {s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯} {x : U}
    {t : Cₛ^∞⟮I; F, V⟯} (ht : ∀ᶠ y : U in 𝓝 x, t y = s y) :
    restrictValue U P s x = P t x :=
  apply_eq_of_eventuallyEq hP (eventually_extendAt s x) ht

/-- The restriction of `P` applied to `s`, as a smooth section of `W|_U`: near each point it is the
restriction of `P t` for a global section `t` agreeing with `s` there. -/
private def restrictSection {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯) :
    Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯ where
  toFun := restrictValue U P s
  contMDiff_toFun x := by
    refine (((P (extendAt s x)).restrict U).contMDiff x).congr_of_eventuallyEq ?_
    filter_upwards [eventually_eventually_nhds.2 (eventually_extendAt s x)] with y hy
    rw [restrictValue_eq hP hy, ContMDiffSection.restrict_apply]

private theorem restrictSection_apply {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯) (x : U) :
    restrictSection hP s x = restrictValue U P s x :=
  (rfl)

/-- The restriction of a differential operator as a linear map between the sections of `V|_U` and
`W|_U`. -/
private def restrictLinearMap {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) :
    Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯ where
  toFun := restrictSection hP
  map_add' s s' := ContMDiffSection.ext fun x ↦ by
    have hs := eventually_extendAt s x
    have hs' := eventually_extendAt s' x
    simp only [ContMDiffSection.coe_add, Pi.add_apply, restrictSection_apply,
      restrictValue_eq hP (eventually_add_eq_of_opens hs hs'), restrictValue_eq hP hs,
      restrictValue_eq hP hs', map_add]
    -- The sum in the fibre of `W` over `x` is the sum in the fibre of `W|_U`.
    rfl
  map_smul' c s := ContMDiffSection.ext fun x ↦ by
    have hs := eventually_extendAt s x
    simp only [ContMDiffSection.coe_smul, Pi.smul_apply, RingHom.id_apply,
      restrictSection_apply, restrictValue_eq hP (eventually_smul_eq_of_opens c hs),
      restrictValue_eq hP hs, map_smul]
    -- The scalar action on the fibre of `W` over `x` is that on the fibre of `W|_U`.
    rfl

private theorem restrictLinearMap_apply {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯) (x : U) :
    restrictLinearMap hP s x = restrictValue U P s x :=
  (rfl)

variable [FiniteDimensional ℝ F'] [ContMDiffVectorBundle ∞ F' W I]

/-- The restriction of a differential operator of order at most `m` has order at most `m`: a
section of `V|_U` in `I_x ^ (m + 1) Γ(V|_U)` agrees near `x` with a global section in
`I_x ^ (m + 1) Γ(V)`, which `P` sends to a section vanishing at `x`. -/
private theorem restrictLinearMap_mem {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) :
    restrictLinearMap (U := U) hP ∈
      differentialOperators ℝ C^∞⟮I, U; ℝ⟯
        Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯
        Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯ m := by
  rw [mem_differentialOperators_section_iff_forall_apply_eq_zero]
  intro x s hs
  -- Every element of `I_x ^ (m + 1) Γ(V|_U)` agrees near `x` with a global section in
  -- `I_x ^ (m + 1) Γ(V)`.
  obtain ⟨t, ht, hts⟩ : ∃ t ∈ smoothVanishingIdeal I (x : M) ^ (m + 1) •
      (⊤ : Submodule C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯), ∀ᶠ y : U in 𝓝 x, t y = s y := by
    refine Submodule.smul_induction_on hs (fun h hh s _ ↦ ?_) fun s₁ s₂ h₁ h₂ ↦ ?_
    · obtain ⟨g, hg, hgh⟩ := exists_mem_smoothVanishingIdeal_pow_eventuallyEq_comp_subtype_val hh
      exact ⟨g • extendAt s x, Submodule.smul_mem_smul hg Submodule.mem_top,
        eventually_smul_function_eq_of_opens hgh (eventually_extendAt s x)⟩
    · obtain ⟨t₁, ht₁, hts₁⟩ := h₁
      obtain ⟨t₂, ht₂, hts₂⟩ := h₂
      exact ⟨t₁ + t₂, add_mem ht₁ ht₂, eventually_add_eq_of_opens hts₁ hts₂⟩
  rw [restrictLinearMap_apply, restrictValue_eq hP hts]
  exact apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top
    (apply_mem_smul_top_of_mem_pow_smul_top hP _ ht)

/-! ### Restriction of differential operators -/

variable (U m) in
/-- **Restriction of differential operators between sections to an open subset.** For a
differential operator `P : Γ(V) → Γ(W)` of order at most `m` and an open subset `U`, the
restriction `P|_U : Γ(V|_U) → Γ(W|_U)` is the differential operator of order at most `m` over
`C^∞(U)` whose value on `s` at `x ∈ U` is `(P t)(x)` for any global smooth section `t` agreeing
with `s` near `x`
(`TopologicalSpace.Opens.restrictSectionDifferentialOperators_apply_of_eventuallyEq`). It is
characterized by `P|_U (t|_U) = (P t)|_U`
(`TopologicalSpace.Opens.eq_restrictSectionDifferentialOperators_iff`). -/
def _root_.TopologicalSpace.Opens.restrictSectionDifferentialOperators :
    differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m →ₗ[ℝ]
      differentialOperators ℝ C^∞⟮I, U; ℝ⟯
        Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯
        Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯ m where
  toFun P := ⟨restrictLinearMap P.property, restrictLinearMap_mem P.property⟩
  map_add' P₁ P₂ := by
    ext s x
    have hs := eventually_extendAt s x
    simp only [Submodule.coe_add, LinearMap.add_apply, ContMDiffSection.coe_add, Pi.add_apply,
      restrictLinearMap_apply, restrictValue_eq (add_mem P₁.property P₂.property) hs,
      restrictValue_eq P₁.property hs, restrictValue_eq P₂.property hs]
    -- The sum in the fibre of `W` over `x` is the sum in the fibre of `W|_U`.
    rfl
  map_smul' c P := by
    ext s x
    have hs := eventually_extendAt s x
    simp only [Submodule.coe_smul, LinearMap.smul_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
      RingHom.id_apply, restrictLinearMap_apply,
      restrictValue_eq (Submodule.smul_mem _ c P.property) hs, restrictValue_eq P.property hs]
    -- The scalar action on the fibre of `W` over `x` is that on the fibre of `W|_U`.
    rfl

/-- **The values of a restricted operator.** If a global section `t` agrees with the section `s`
of `V|_U` near `x`, then `(P|_U s)(x) = (P t)(x)`. -/
theorem _root_.TopologicalSpace.Opens.restrictSectionDifferentialOperators_apply_of_eventuallyEq
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    {s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯} {x : U}
    {t : Cₛ^∞⟮I; F, V⟯} (ht : ∀ᶠ y : U in 𝓝 x, t y = s y) :
    (U.restrictSectionDifferentialOperators m P :
        Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
          Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯) s x =
      (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) t x :=
  restrictValue_eq P.property ht

/-- The restriction of `P` sends the restriction of `t` to the restriction of `P t`, with the
inclusion of `U` left bundled in the pullback-bundle types. -/
private theorem restrict_apply_restrict
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (t : Cₛ^∞⟮I; F, V⟯) :
    (U.restrictSectionDifferentialOperators m P :
        Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
          Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯) (t.restrict U) =
      ((P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) t).restrict U :=
  ContMDiffSection.ext fun x ↦ by
    rw [ContMDiffSection.restrict_apply]
    exact Opens.restrictSectionDifferentialOperators_apply_of_eventuallyEq P
      (.of_forall fun y ↦ (ContMDiffSection.restrict_apply t U y).symm)

/-- The restriction of `P` sends the restriction of `t` to the restriction of `P t`. -/
-- As for `ContMDiffSection.restrict_apply`, normalize the inclusion in the implicit pullback-bundle
-- types for simplification.
@[simp]
theorem _root_.TopologicalSpace.Opens.restrictSectionDifferentialOperators_apply_restrict
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (t : Cₛ^∞⟮I; F, V⟯) :
    dsimp% only [ContinuousMap.coe_mk]
      ((U.restrictSectionDifferentialOperators m P :
          Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
            Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯) (t.restrict U) =
        ((P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) t).restrict U) :=
  restrict_apply_restrict P t

/-- **Uniqueness of the restriction.** A differential operator `Q : Γ(V|_U) → Γ(W|_U)` of any order
with `Q (t|_U) = (P t)|_U` for every global section `t` is the restriction of `P`. -/
theorem _root_.TopologicalSpace.Opens.eq_coe_restrictSectionDifferentialOperators
    {Q : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯}
    (hQ : Q ∈ differentialOperators ℝ C^∞⟮I, U; ℝ⟯
      Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯
      Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯ k)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (h : ∀ t : Cₛ^∞⟮I; F, V⟯, Q (t.restrict U) =
      ((P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) t).restrict U) :
    Q = U.restrictSectionDifferentialOperators m P := by
  ext s x
  have hs := eventually_extendAt s x
  rw [Opens.restrictSectionDifferentialOperators_apply_of_eventuallyEq P hs,
    ← ContMDiffSection.restrict_apply _ U x, ← h, ← sub_eq_zero, ← Pi.sub_apply,
    ← ContMDiffSection.coe_sub, ← map_sub]
  refine differentialOperators_section_apply_eq_zero_of_eventuallyEq hQ ?_
  filter_upwards [hs] with y hy
  rw [ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.restrict_apply]
  -- The fibre of `V|_U` over `y` is the fibre of `V` over `y`.
  exact sub_eq_zero.2 hy.symm

/-- A differential operator `Q : Γ(V|_U) → Γ(W|_U)` is the restriction of `P` exactly when it sends
the restriction of every global section `t` to the restriction of `P t`. -/
theorem _root_.TopologicalSpace.Opens.eq_restrictSectionDifferentialOperators_iff
    {Q : differentialOperators ℝ C^∞⟮I, U; ℝ⟯
      Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯
      Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯ m}
    {P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m} :
    Q = U.restrictSectionDifferentialOperators m P ↔
      ∀ t : Cₛ^∞⟮I; F, V⟯,
        (Q : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
            Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯) (t.restrict U) =
          ((P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) t).restrict U := by
  refine ⟨?_, fun h ↦ Subtype.ext (Opens.eq_coe_restrictSectionDifferentialOperators
    Q.property P h)⟩
  rintro rfl t
  exact restrict_apply_restrict P t

/-- **Restriction commutes with composition.** For differential operators `P : Γ(W) → Γ(X)` and
`Q : Γ(V) → Γ(W)` of orders at most `m` and `k`, the restriction of `P ∘ Q`, an operator of order
at most `m + k`, is the composition of the restrictions. -/
theorem _root_.TopologicalSpace.Opens.restrictSectionDifferentialOperators_comp
    {F'' : Type*} [NormedAddCommGroup F''] [NormedSpace ℝ F''] [FiniteDimensional ℝ F'']
    {X : M → Type*} [TopologicalSpace (TotalSpace F'' X)]
    [∀ x, AddCommGroup (X x)] [∀ x, Module ℝ (X x)] [∀ x, TopologicalSpace (X x)]
    [FiberBundle F'' X] [VectorBundle ℝ F'' X] [ContMDiffVectorBundle ∞ F'' X I]
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F'', X⟯ m)
    (Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ k) :
    (U.restrictSectionDifferentialOperators (m + k)
        ⟨(P : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F'', X⟯) ∘ₗ (Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯),
          comp_mem_differentialOperators P.property Q.property⟩ :
        Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
          Cₛ^∞⟮I; F'', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ X⟯) =
      (U.restrictSectionDifferentialOperators m P :
          Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯ →ₗ[ℝ]
            Cₛ^∞⟮I; F'', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ X⟯) ∘ₗ
        (U.restrictSectionDifferentialOperators k Q :
          Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
            Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯) :=
  (Opens.eq_coe_restrictSectionDifferentialOperators
    (comp_mem_differentialOperators (U.restrictSectionDifferentialOperators m P).property
      (U.restrictSectionDifferentialOperators k Q).property) _ fun t ↦ by simp).symm

/-! ### Commutators and the principal symbol -/

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [FiniteDimensional ℝ F']
  [ContMDiffVectorBundle ∞ F' W I] in
/-- If `Q'` on `U` sends restrictions of global sections to restrictions of their images under
`Q`, then so do the iterated commutators of `Q'` with the restriction of `f` and of `Q` with `f`. -/
private theorem smulCommutator_pow_apply_restrict {Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    {Q' : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯}
    (h : ∀ t, Q' (t.restrict U) = (Q t).restrict U) (f : C^∞⟮I, M; ℝ⟯) (j : ℕ)
    (t : Cₛ^∞⟮I; F, V⟯) :
    (smulCommutator ℝ (f.restrict U) ^ j) Q' (t.restrict U) =
      ((smulCommutator ℝ f ^ j) Q t).restrict U := by
  induction j generalizing Q Q' with
  | zero => exact h t
  | succ j ih =>
    rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp]
    refine ih (fun t ↦ ?_)
    -- `ContMDiffSection.restrict_smul_function` restricts `f` as a composition with the
    -- inclusion.
    rw [smulCommutator_apply_apply, smulCommutator_apply_apply, ContMDiffMap.restrict_eq_comp,
      ← ContMDiffSection.restrict_smul_function, h, h, ContMDiffSection.restrict_sub,
      ContMDiffSection.restrict_smul_function]

/-- **Restriction commutes with commutators.** The commutator of `P|_U` with multiplication by the
restriction of `f` is the restriction of the commutator `[P, f]`. -/
theorem smulCommutator_restrictSectionDifferentialOperators
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ (m + 1))
    (f : C^∞⟮I, M; ℝ⟯) :
    smulCommutator ℝ (f.restrict U)
        (U.restrictSectionDifferentialOperators (m + 1) P :
          Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
            Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯) =
      (U.restrictSectionDifferentialOperators m
        ⟨smulCommutator ℝ f (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯),
          smulCommutator_mem_differentialOperators P.property f⟩ :
          Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
            Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯) :=
  Opens.eq_coe_restrictSectionDifferentialOperators
    (smulCommutator_mem_differentialOperators
      (U.restrictSectionDifferentialOperators (m + 1) P).property _) _
    (smulCommutator_pow_apply_restrict
      (restrict_apply_restrict P) f 1)

variable [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]

/-- **Restriction preserves the principal symbol.** At an interior point `x ∈ U`, the principal
symbol of `P|_U` at `ξ ∘ ι` is the principal symbol of `P` at `ξ`, where `ι : T_x U ≃ T_x M` is the
identification of the tangent spaces; the fibres of `V|_U` and `W|_U` over `x` are those of `V`
and `W`. -/
theorem sectionPrincipalSymbol_restrictSectionDifferentialOperators {x : U}
    (hx : I.IsInteriorPoint (x : M))
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : TangentSpace I (x : M) →L[ℝ] ℝ) :
    sectionPrincipalSymbol I (I.isInteriorPoint_iff_isInteriorPoint_val.mpr hx)
        (U.restrictSectionDifferentialOperators m P)
        (ξ.comp (Manifold.tangentSpaceOpenEquiv (I := I) x).toContinuousLinearMap) =
      sectionPrincipalSymbol I hx P ξ := by
  obtain ⟨f, -, rfl⟩ := exists_contMDiffMap_mvfderiv_eq (I := I) (x : M) (0 : ℝ) ξ
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨t, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ (x : M) v
  -- Both sides are `(m!)⁻¹` times the value at `x` of the `m`-fold commutator of `P` with `f`,
  -- applied to `t`.
  have h := sectionPrincipalSymbol_mvfderiv (I.isInteriorPoint_iff_isInteriorPoint_val.mpr hx)
    (U.restrictSectionDifferentialOperators m P) (f.restrict U) (t.restrict U)
  rw [ContMDiffMap.mvfderiv_restrict (n := ∞) (by simp), smulCommutator_pow_apply_restrict
    (restrict_apply_restrict P) f m t,
    ContMDiffSection.restrict_apply, ContMDiffSection.restrict_apply] at h
  rw [ContMDiffSection.evalLinearMap_apply]
  exact h.trans (sectionPrincipalSymbol_mvfderiv hx P f t).symm

end TauCeti
