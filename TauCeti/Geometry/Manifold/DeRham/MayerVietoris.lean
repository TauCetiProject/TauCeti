/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Map
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Algebra.Homology.ModuleCat.Biprod
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The Mayer–Vietoris sequence of de Rham complexes

For open subsets `U` and `V` of a manifold, restriction of smooth forms gives the Mayer–Vietoris
short complex of de Rham complexes
`0 ⟶ Ω^•(U ⊔ V) ⟶ Ω^•(U) ⊞ Ω^•(V) ⟶ Ω^•(U ⊓ V) ⟶ 0`,
whose first map is `(res, res)` and whose second map is the difference `res - res` of the two
restrictions to `U ⊓ V`.

In each degree, the first map is injective and the sequence is exact in the middle on every
manifold: forms on `U` and `V` that agree on `U ⊓ V` glue to a form on `U ⊔ V`. The second map is
surjective on a Hausdorff σ-compact manifold modelled on a finite-dimensional space: a smooth
function on `U ⊔ V` vanishing near the points outside `V` and equal to one near the points outside
`U` splits a form on `U ⊓ V` into a difference of forms extended by zero. Hence the Mayer–Vietoris
short complex is short exact (`TauCeti.mayerVietorisShortComplex_shortExact`), and Mathlib's
`CategoryTheory.ShortComplex.ShortExact.homology_exact₁`, `homology_exact₂` and `homology_exact₃`
give the Mayer–Vietoris long exact sequence of de Rham cohomology.

Its connecting map `TauCeti.deRhamCohomology.mayerVietorisδ : H^k(U ⊓ V) → H^{k+1}(U ⊔ V)` sends the
class of a closed form `φ = α - β` on `U ⊓ V`, with `α` on `U` and `β` on `V`, to the class of the
form on `U ⊔ V` that restricts to `dα` on `U` and to `dβ` on `V`
(`TauCeti.deRhamCohomology.mayerVietorisδ_mk`). For a smooth function `ρ` on `U ⊔ V` supported in
`V` with `1 - ρ` supported in `U`, the cut-off choices `α = ρ φ` and `β = (ρ - 1) φ`, extended by
zero, make this form the extension by zero of `d(ρ φ)`, so that form also represents the class
(`TauCeti.deRhamCohomology.mayerVietorisδ_mk_eq_mk_extendByZero`).

The connecting map is natural: a smooth map `U ⊔ V → U' ⊔ V'` carrying `U` into `U'` and `V` into
`V'` intertwines, through pullback, the connecting maps of the covers `{U', V'}` and `{U, V}`
(`TauCeti.deRhamCohomology.mayerVietorisδ_naturality`). In particular the connecting map commutes
with restriction to a smaller cover (`TauCeti.deRhamCohomology.mayerVietorisδ_naturality_of_le`).

## Main definitions and results

* `TauCeti.SmoothForm.injective_mayerVietoris`, `TauCeti.SmoothForm.exact_mayerVietoris` and
  `TauCeti.SmoothForm.surjective_mayerVietoris`: exactness of the Mayer–Vietoris sequence of
  smooth forms in a fixed degree.
* `TauCeti.mayerVietorisShortComplex`: the Mayer–Vietoris short complex of de Rham complexes.
* `TauCeti.mayerVietorisShortComplex_shortExact`: it is short exact.
* `TauCeti.deRhamCohomology.mayerVietorisδ`: the connecting map of the long exact sequence, with
  its description on classes `TauCeti.deRhamCohomology.mayerVietorisδ_mk` and through a cut-off
  function, `TauCeti.deRhamCohomology.mayerVietorisδ_mk_eq_mk_extendByZero`.
* `TauCeti.exists_closedForms_mpullback_eq_mextDerivₗ`: the closed form on `U ⊔ V` restricting to
  `dα` and `dβ`, which `TauCeti.deRhamCohomology.mayerVietorisδ_mk` takes as input, exists.
* `TauCeti.deRhamCohomology.mayerVietorisδ_naturality` and
  `TauCeti.deRhamCohomology.mayerVietorisδ_naturality_of_le`: naturality of the connecting map.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, the Mayer–Vietoris
  theorem and Corollary 17.42 (the connecting map).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §2.
-/

public section

noncomputable section

open CategoryTheory Limits Set Filter TopologicalSpace
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

namespace SmoothForm

section Exactness

variable [IsManifold I 1 M]

/-- A smooth form on `U ⊔ V` whose restrictions to `U` and to `V` vanish is zero. -/
theorem injective_mayerVietoris (U V : Opens M) :
    Function.Injective
      ((mpullback (I := I) (I' := I) (F := F) (k := k)
          (Opens.inclusion (le_sup_left : U ≤ U ⊔ V)) (contMDiff_inclusion _)).prod
        (mpullback (I := I) (I' := I)
          (Opens.inclusion (le_sup_right : V ≤ U ⊔ V)) (contMDiff_inclusion _))) := by
  refine (injective_iff_map_eq_zero _).mpr fun φ hφ ↦ ?_
  rw [LinearMap.prod_apply, Function.prod_apply, Prod.mk_eq_zero] at hφ
  apply Subtype.ext
  funext x
  rcases Opens.mem_sup.mp x.2 with hx | hx
  · have h := congrFun (congrArg Subtype.val hφ.1) ⟨x, hx⟩
    rw [coe_mpullback, mpullback_inclusion_apply] at h
    exact h
  · have h := congrFun (congrArg Subtype.val hφ.2) ⟨x, hx⟩
    rw [coe_mpullback, mpullback_inclusion_apply] at h
    exact h

/-- Smooth forms on `U` and `V` with the same restriction to `U ⊓ V` are the restrictions of a
smooth form on `U ⊔ V`. -/
theorem exact_mayerVietoris (U V : Opens M) :
    Function.Exact
      ((mpullback (I := I) (I' := I) (F := F) (k := k)
          (Opens.inclusion (le_sup_left : U ≤ U ⊔ V)) (contMDiff_inclusion _)).prod
        (mpullback (I := I) (I' := I)
          (Opens.inclusion (le_sup_right : V ≤ U ⊔ V)) (contMDiff_inclusion _)))
      ((mpullback (I := I) (I' := I) (F := F) (k := k)
          (Opens.inclusion (inf_le_left : U ⊓ V ≤ U)) (contMDiff_inclusion _)).coprod
        (-mpullback (I := I) (I' := I)
          (Opens.inclusion (inf_le_right : U ⊓ V ≤ V)) (contMDiff_inclusion _))) := by
  classical
  rintro ⟨α, β⟩
  simp only [LinearMap.coprod_apply, LinearMap.neg_apply, ← sub_eq_add_neg, sub_eq_zero,
    Set.mem_range, LinearMap.prod_apply, Function.prod_apply, Prod.mk.injEq]
  refine ⟨fun hαβ ↦ ?_, ?_⟩
  · -- Pointwise, `α` and `β` agree on `U ⊓ V`.
    have hagree : ∀ (y : M) (hU : y ∈ U) (hV : y ∈ V),
        (α.1 ⟨y, hU⟩ : E [⋀^Fin k]→L[ℝ] F) = β.1 ⟨y, hV⟩ := fun y hU hV ↦ by
      have h := congrFun (congrArg Subtype.val hαβ) ⟨y, hU, hV⟩
      rw [coe_mpullback, coe_mpullback, mpullback_inclusion_apply,
        mpullback_inclusion_apply] at h
      exact h
    let γ : RoughForm I (U ⊔ V : Opens M) F k := fun x ↦
      if hx : (x : M) ∈ U then (α.1 ⟨x, hx⟩ : E [⋀^Fin k]→L[ℝ] F)
      else β.1 ⟨x, (Opens.mem_sup.mp x.2).resolve_left hx⟩
    have hγU : TauCeti.mpullback I I (Opens.inclusion (le_sup_left : U ≤ U ⊔ V)) γ = α.1 := by
      funext y
      rw [mpullback_inclusion_apply]
      exact dite_eq_left y.2
    have hγV : TauCeti.mpullback I I (Opens.inclusion (le_sup_right : V ≤ U ⊔ V)) γ = β.1 := by
      funext y
      rw [mpullback_inclusion_apply]
      by_cases hy : (y : M) ∈ U
      · exact (dite_eq_left hy).trans (hagree y hy y.2)
      · exact dite_eq_right hy
    have hγ : IsSmoothForm I ∞ γ :=
      IsSmoothForm.of_mpullback_inclusion_sup (hγU ▸ α.isSmoothForm) (hγV ▸ β.isSmoothForm)
    exact ⟨⟨γ, hγ.mem_smoothForms⟩, Subtype.ext ((coe_mpullback _ _ _).trans hγU),
      Subtype.ext ((coe_mpullback _ _ _).trans hγV)⟩
  · rintro ⟨φ, rfl, rfl⟩
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← mpullback_comp, ← mpullback_comp]
    -- Both composites of inclusions are, by definition, the inclusion of `U ⊓ V` in `U ⊔ V`.
    rfl

end Exactness

end SmoothForm

section Cutoff

/-! ### Cut-off functions for a cover by two open subsets

A smooth function `ρ` on `U ⊔ V` supported in `V`, with `1 - ρ` supported in `U`, splits a form `φ`
on `U ⊓ V` as `ρ φ - (ρ - 1) φ`, where `ρ φ` extends by zero to `U` and `(ρ - 1) φ` to `V`. -/

variable {U V : Opens M} {ρ : (U ⊔ V : Opens M) → ℝ}

/-- A function on `U ⊔ V` supported in `V` vanishes near every point of `U` outside `U ⊓ V`. -/
private theorem eventually_eq_zero_of_tsupport_subset (hρV : tsupport ρ ⊆ {x | (x : M) ∈ V})
    {x : U} (hx : (x : M) ∉ U ⊓ V) : ∀ᶠ y in 𝓝 x, ρ (Opens.inclusion le_sup_left y) = 0 :=
  (continuous_inclusion (le_sup_left : U ≤ U ⊔ V)).continuousAt.eventually
    (notMem_tsupport_iff_eventuallyEq.mp fun h ↦ hx ⟨x.2, hρV h⟩)

/-- If `1 - ρ` is supported in `U`, then `ρ - 1` vanishes near every point of `V` outside
`U ⊓ V`. -/
private theorem eventually_sub_one_eq_zero_of_tsupport_subset
    (hρU : tsupport (fun x ↦ 1 - ρ x) ⊆ {x | (x : M) ∈ U}) {x : V} (hx : (x : M) ∉ U ⊓ V) :
    ∀ᶠ y in 𝓝 x, ρ (Opens.inclusion le_sup_right y) - 1 = 0 :=
  ((continuous_inclusion (le_sup_right : V ≤ U ⊔ V)).continuousAt.eventually
    (notMem_tsupport_iff_eventuallyEq.mp fun h ↦ hx ⟨hρU h, x.2⟩)).mono fun _ hy ↦ by
      rw [Pi.zero_apply] at hy
      linarith

variable [IsManifold I ∞ M] (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (hρV : tsupport ρ ⊆ {x | (x : M) ∈ V})
  (hρU : tsupport (fun x ↦ 1 - ρ x) ⊆ {x | (x : M) ∈ U})

/-- The cut-off form `ρ φ` on `U ⊓ V`, extended by zero to a smooth form on `U`. -/
private def cutoffLeft (φ : SmoothForm I (U ⊓ V : Opens M) F k) : SmoothForm I U F k :=
  ⟨RoughForm.extendByZero U fun y : (U ⊓ V : Opens M) ↦ ρ (Opens.inclusion inf_le_sup y) • φ.1 y,
    (φ.isSmoothForm.extendByZero_smul inf_le_left (hρ.comp (contMDiff_inclusion le_sup_left))
      fun _ hx ↦ eventually_eq_zero_of_tsupport_subset hρV hx).mem_smoothForms⟩

/-- The cut-off form `(ρ - 1) φ` on `U ⊓ V`, extended by zero to a smooth form on `V`. -/
private def cutoffRight (φ : SmoothForm I (U ⊓ V : Opens M) F k) : SmoothForm I V F k :=
  ⟨RoughForm.extendByZero V
      fun y : (U ⊓ V : Opens M) ↦ (ρ (Opens.inclusion inf_le_sup y) - 1) • φ.1 y,
    (φ.isSmoothForm.extendByZero_smul inf_le_right
      ((hρ.comp (contMDiff_inclusion le_sup_right)).sub contMDiff_const)
      fun _ hx ↦ eventually_sub_one_eq_zero_of_tsupport_subset hρU hx).mem_smoothForms⟩

/-- A form `φ` on `U ⊓ V` is the difference `ρ φ - (ρ - 1) φ` of the restrictions of its two
cut-off forms. -/
private theorem mpullback_cutoffLeft_sub_mpullback_cutoffRight
    (φ : SmoothForm I (U ⊓ V : Opens M) F k) :
    SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _)
        (cutoffLeft hρ hρV φ) -
      SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _)
        (cutoffRight hρ hρU φ) = φ := by
  apply Subtype.ext
  rw [Submodule.coe_sub, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, cutoffLeft,
    cutoffRight, RoughForm.mpullback_inclusion_extendByZero,
    RoughForm.mpullback_inclusion_extendByZero]
  funext y
  simp only [Pi.sub_apply, sub_smul, one_smul]
  -- The two cut-off factors are the same function, read through the two inclusions of `U ⊓ V`.
  exact sub_sub_cancel _ _

/-- For a closed form `φ` on `U ⊓ V`, the restrictions to `U` and to `V` of the extension by zero
of `d(ρ φ)` to `U ⊔ V` are the exterior derivatives of the two cut-off forms of `φ`. -/
private theorem mpullback_extendByZero_mextDeriv_cutoff (φ : closedForms I (U ⊓ V : Opens M) k) :
    mpullback I I (Opens.inclusion le_sup_left) (RoughForm.extendByZero (U ⊔ V)
        (mextDeriv fun y : (U ⊓ V : Opens M) ↦ ρ (Opens.inclusion inf_le_sup y) • φ.1.1 y)) =
      (mextDerivₗ I k (cutoffLeft hρ hρV φ.1)).1 ∧
    mpullback I I (Opens.inclusion le_sup_right) (RoughForm.extendByZero (U ⊔ V)
        (mextDeriv fun y : (U ⊓ V : Opens M) ↦ ρ (Opens.inclusion inf_le_sup y) • φ.1.1 y)) =
      (mextDerivₗ I k (cutoffRight hρ hρU φ.1)).1 := by
  have hρφ : IsSmoothForm I ∞
      fun y : (U ⊓ V : Opens M) ↦ ρ (Opens.inclusion inf_le_sup y) • φ.1.1 y :=
    φ.1.isSmoothForm.fun_smul (hρ.comp (contMDiff_inclusion inf_le_sup))
  have hρφ' : IsSmoothForm I ∞
      fun y : (U ⊓ V : Opens M) ↦ (ρ (Opens.inclusion inf_le_sup y) - 1) • φ.1.1 y :=
    φ.1.isSmoothForm.fun_smul ((hρ.comp (contMDiff_inclusion inf_le_sup)).sub contMDiff_const)
  rw [mextDerivₗ_apply, mextDerivₗ_apply, cutoffLeft, cutoffRight,
    RoughForm.mpullback_inclusion_extendByZero_eq_extendByZero,
    RoughForm.mpullback_inclusion_extendByZero_eq_extendByZero,
    RoughForm.mextDeriv_extendByZero inf_le_left fun _ hx ↦
      RoughForm.eventually_extendByZero_smul_eq_zero inf_le_left _
        (eventually_eq_zero_of_tsupport_subset hρV hx),
    RoughForm.mextDeriv_extendByZero inf_le_right fun _ hx ↦
      RoughForm.eventually_extendByZero_smul_eq_zero inf_le_right _
        (eventually_sub_one_eq_zero_of_tsupport_subset hρU hx)]
  refine ⟨rfl, congrArg _ ?_⟩
  -- Since `φ` is closed, `d((ρ - 1) φ) = d(ρ φ) - dφ = d(ρ φ)`.
  let ρφ : SmoothForm I (U ⊓ V : Opens M) ℝ k := ⟨_, hρφ.mem_smoothForms⟩
  have hsub : (fun y : (U ⊓ V : Opens M) ↦ (ρ (Opens.inclusion inf_le_sup y) - 1) • φ.1.1 y) =
      (ρφ - φ.1).1 := by
    funext y
    simp [ρφ, sub_smul]
  rw [hsub, ← mextDerivₗ_apply, map_sub, (mem_closedForms_iff_mextDerivₗ_eq_zero I _).mp φ.2,
    sub_zero, mextDerivₗ_apply]

include hρ hρV hρU in
/-- Let `ρ` be a smooth function on `U ⊔ V` supported in `V` such that `1 - ρ` is supported in `U`.
For a closed form `φ` on `U ⊓ V`, the form `d(ρ φ)` on `U ⊓ V` extends by zero to a closed form on
`U ⊔ V`. -/
theorem exists_closedForms_coe_eq_extendByZero_mextDeriv (φ : closedForms I (U ⊓ V : Opens M) k) :
    ∃ σ : closedForms I (U ⊔ V : Opens M) (k + 1),
      (σ.1 : RoughForm I (U ⊔ V : Opens M) ℝ (k + 1)) = RoughForm.extendByZero (U ⊔ V)
        (mextDeriv fun y : (U ⊓ V : Opens M) ↦ ρ (Opens.inclusion inf_le_sup y) • φ.1.1 y) := by
  obtain ⟨hU, hV⟩ := mpullback_extendByZero_mextDeriv_cutoff hρ hρV hρU φ
  -- The extension is smooth, since its restrictions to `U` and to `V` are smooth.
  have hσ : IsSmoothForm I ∞ (RoughForm.extendByZero (U ⊔ V)
      (mextDeriv fun y : (U ⊓ V : Opens M) ↦ ρ (Opens.inclusion inf_le_sup y) • φ.1.1 y)) :=
    IsSmoothForm.of_mpullback_inclusion_sup
      (hU ▸ (mextDerivₗ I k (cutoffLeft hρ hρV φ.1)).isSmoothForm)
      (hV ▸ (mextDerivₗ I k (cutoffRight hρ hρU φ.1)).isSmoothForm)
  let σ : SmoothForm I (U ⊔ V : Opens M) ℝ (k + 1) := ⟨_, hσ.mem_smoothForms⟩
  -- It is closed, since its restrictions to `U` and to `V` are exact.
  refine ⟨⟨σ, (mem_closedForms_iff_mextDerivₗ_eq_zero I σ).mpr <|
    SmoothForm.injective_mayerVietoris U V ?_⟩, rfl⟩
  rw [map_zero, LinearMap.prod_apply, Function.prod_apply, ← SmoothForm.mextDerivₗ_mpullback,
    ← SmoothForm.mextDerivₗ_mpullback, Subtype.ext ((SmoothForm.coe_mpullback _ _ _).trans hU),
    Subtype.ext ((SmoothForm.coe_mpullback _ _ _).trans hV)]
  exact Prod.ext (LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I k) _)
    (LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I k) _)

end Cutoff

/-- On a Hausdorff σ-compact manifold modelled on a finite-dimensional space, every smooth form
on `U ⊓ V` is the difference of the restrictions of smooth forms on `U` and on `V`. -/
theorem SmoothForm.surjective_mayerVietoris [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] (U V : Opens M) :
    Function.Surjective
      ((mpullback (I := I) (I' := I) (F := F) (k := k)
          (Opens.inclusion (inf_le_left : U ⊓ V ≤ U)) (contMDiff_inclusion _)).coprod
        (-mpullback (I := I) (I' := I)
          (Opens.inclusion (inf_le_right : U ⊓ V ≤ V)) (contMDiff_inclusion _))) := by
  intro θ
  -- The open subset `U ⊔ V` is again a Hausdorff σ-compact manifold, hence normal.
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : SecondCountableTopology H := I.secondCountableTopology
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  have : LocallyCompactSpace (U ⊔ V : Opens M) := ChartedSpace.locallyCompactSpace H _
  have : NormalSpace (U ⊔ V : Opens M) :=
    have := Manifold.metrizableSpace I (U ⊔ V : Opens M)
    inferInstance
  -- A cut-off function vanishing near the points outside `V` and equal to one near the points
  -- outside `U`.
  have hA : IsClosed {x : (U ⊔ V : Opens M) | (x : M) ∉ V} :=
    (V.isOpen.preimage continuous_subtype_val).isClosed_compl
  have hB : IsClosed {x : (U ⊔ V : Opens M) | (x : M) ∉ U} :=
    (U.isOpen.preimage continuous_subtype_val).isClosed_compl
  have hAB : Disjoint {x : (U ⊔ V : Opens M) | (x : M) ∉ V} {x | (x : M) ∉ U} :=
    disjoint_left.mpr fun x hxV hxU ↦ (Opens.mem_sup.mp x.2).elim hxU hxV
  obtain ⟨ρ, hρ0, hρ1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed I (n := ⊤) hA hB hAB
  have hρV : tsupport ρ ⊆ {x | (x : M) ∈ V} := fun x hx ↦ not_not.mp fun hxV ↦
    notMem_tsupport_iff_eventuallyEq.mpr (hρ0.filter_mono (nhds_le_nhdsSet hxV)) hx
  have hρU : tsupport (fun x ↦ 1 - ρ x) ⊆ {x | (x : M) ∈ U} := fun x hx ↦ not_not.mp fun hxU ↦
    notMem_tsupport_iff_eventuallyEq.mpr
      ((hρ1.filter_mono (nhds_le_nhdsSet hxU)).mono fun _ hy ↦ sub_eq_zero.mpr hy.symm) hx
  -- `θ = ρ θ - (ρ - 1) θ`, where `ρ θ` extends by zero to `U` and `(ρ - 1) θ` to `V`.
  refine ⟨(cutoffLeft ρ.contMDiff hρV θ, cutoffRight ρ.contMDiff hρU θ), ?_⟩
  rw [LinearMap.coprod_apply, LinearMap.neg_apply, ← sub_eq_add_neg]
  exact mpullback_cutoffLeft_sub_mpullback_cutoffRight ρ.contMDiff hρV hρU θ

section Complex

variable [IsManifold I 2 M]

variable (I) in
/-- The Mayer–Vietoris short complex `Ω^•(U ⊔ V) ⟶ Ω^•(U) ⊞ Ω^•(V) ⟶ Ω^•(U ⊓ V)` of de Rham
complexes, with first map the pair of restrictions and second map the difference of the
restrictions. -/
@[expose] def mayerVietorisShortComplex (U V : Opens M) :
    ShortComplex (CochainComplex (ModuleCat ℝ) ℕ) :=
  ShortComplex.mk
    (biprod.lift
      (deRhamComplex.map (I := I) (I' := I)
        (Opens.inclusion (le_sup_left : U ≤ U ⊔ V)) (contMDiff_inclusion _))
      (deRhamComplex.map (I := I) (I' := I)
        (Opens.inclusion (le_sup_right : V ≤ U ⊔ V)) (contMDiff_inclusion _)))
    (biprod.desc
      (deRhamComplex.map (I := I) (I' := I)
        (Opens.inclusion (inf_le_left : U ⊓ V ≤ U)) (contMDiff_inclusion _))
      (-deRhamComplex.map (I := I) (I' := I)
        (Opens.inclusion (inf_le_right : U ⊓ V ≤ V)) (contMDiff_inclusion _)))
    (by
      rw [biprod.lift_desc, Preadditive.comp_neg, ← deRhamComplex.map_comp,
        ← deRhamComplex.map_comp]
      -- Both composites of inclusions are, by definition, the inclusion of `U ⊓ V` in `U ⊔ V`.
      exact add_neg_cancel _)

/-- The first term of the Mayer–Vietoris short complex is the de Rham complex of `U ⊔ V`. -/
theorem mayerVietorisShortComplex_X₁ (U V : Opens M) :
    (mayerVietorisShortComplex I U V).X₁ = deRhamComplex I (U ⊔ V : Opens M) := (rfl)

/-- The first map of the Mayer–Vietoris short complex is the pair of restrictions to `U` and
to `V`. -/
theorem mayerVietorisShortComplex_f (U V : Opens M) :
    (mayerVietorisShortComplex I U V).f =
      biprod.lift
        (deRhamComplex.map (I := I) (I' := I)
          (Opens.inclusion (le_sup_left : U ≤ U ⊔ V)) (contMDiff_inclusion _))
        (deRhamComplex.map (I := I) (I' := I)
          (Opens.inclusion (le_sup_right : V ≤ U ⊔ V)) (contMDiff_inclusion _)) := (rfl)

/-- The second map of the Mayer–Vietoris short complex is the difference of the restrictions to
`U ⊓ V` from `U` and from `V`. -/
theorem mayerVietorisShortComplex_g (U V : Opens M) :
    (mayerVietorisShortComplex I U V).g =
      biprod.desc
        (deRhamComplex.map (I := I) (I' := I)
          (Opens.inclusion (inf_le_left : U ⊓ V ≤ U)) (contMDiff_inclusion _))
        (-deRhamComplex.map (I := I) (I' := I)
          (Opens.inclusion (inf_le_right : U ⊓ V ≤ V)) (contMDiff_inclusion _)) := (rfl)

/-- The middle term of the Mayer–Vietoris short complex is the biproduct of the de Rham complexes
of `U` and `V`. -/
theorem mayerVietorisShortComplex_X₂ (U V : Opens M) :
    (mayerVietorisShortComplex I U V).X₂ = (deRhamComplex I U ⊞ deRhamComplex I V) := (rfl)

/-- The last term of the Mayer–Vietoris short complex is the de Rham complex of `U ⊓ V`. -/
theorem mayerVietorisShortComplex_X₃ (U V : Opens M) :
    (mayerVietorisShortComplex I U V).X₃ = deRhamComplex I (U ⊓ V : Opens M) := (rfl)

/-- **The Mayer–Vietoris short exact sequence of de Rham complexes.** On a Hausdorff σ-compact
manifold modelled on a finite-dimensional space, the Mayer–Vietoris short complex of two open
subsets is short exact. -/
theorem mayerVietorisShortComplex_shortExact [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] (U V : Opens M) :
    (mayerVietorisShortComplex I U V).ShortExact := by
  -- In each degree, transport the exactness of the restriction maps of smooth forms along the
  -- identification of `(Ω^•(U) ⊞ Ω^•(V))^k` with the product module `Ωᵏ(U) × Ωᵏ(V)`.
  unfold mayerVietorisShortComplex
  exact HomologicalComplex.moduleCat_shortExact_biprod _
    (fun k ↦ deRhamComplexXIso I k) (fun k ↦ deRhamComplexXIso I k)
    (fun k ↦ deRhamComplexXIso I k) (fun k ↦ deRhamComplexXIso I k) _ _ _
    (fun k ↦ -SmoothForm.mpullback (k := k) (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
      (contMDiff_inclusion _))
    (fun k ↦ deRhamComplex.map_f _ _ k) (fun k ↦ deRhamComplex.map_f _ _ k)
    (fun k ↦ deRhamComplex.map_f _ _ k)
    (fun k ↦ by
      rw [HomologicalComplex.neg_f_apply, Preadditive.neg_comp, deRhamComplex.map_f,
        ← Preadditive.comp_neg]
      ext x
      simp)
    (fun _ ↦ SmoothForm.exact_mayerVietoris U V) (fun _ ↦ SmoothForm.injective_mayerVietoris U V)
    fun _ ↦ SmoothForm.surjective_mayerVietoris U V

/-- Let `α` be a smooth form on `U` and `β` a smooth form on `V` whose restrictions to `U ⊓ V` have
closed difference. Then `dα` and `dβ` are the restrictions of a closed form on `U ⊔ V`. This is the
form that represents the image of the class of that difference under the Mayer–Vietoris connecting
map (`TauCeti.deRhamCohomology.mayerVietorisδ_mk`). -/
theorem exists_closedForms_mpullback_eq_mextDerivₗ {U V : Opens M} (α : SmoothForm I U ℝ k)
    (β : SmoothForm I V ℝ k)
    (hαβ : SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _) α -
      SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _) β ∈
        closedForms I (U ⊓ V : Opens M) k) :
    ∃ σ : closedForms I (U ⊔ V : Opens M) (k + 1),
      SmoothForm.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) σ.1 =
          mextDerivₗ I k α ∧
        SmoothForm.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) σ.1 =
          mextDerivₗ I k β := by
  -- `dα` and `dβ` agree on `U ⊓ V`, so they glue to a form `σ` on `U ⊔ V`.
  obtain ⟨σ, hσ⟩ := (SmoothForm.exact_mayerVietoris (I := I) (F := ℝ) (k := k + 1) U V
    (mextDerivₗ I k α, mextDerivₗ I k β)).mp (by
      rw [LinearMap.coprod_apply, LinearMap.neg_apply, ← sub_eq_add_neg,
        ← SmoothForm.mextDerivₗ_mpullback, ← SmoothForm.mextDerivₗ_mpullback, ← map_sub]
      exact (mem_closedForms_iff_mextDerivₗ_eq_zero I _).mp hαβ)
  rw [LinearMap.prod_apply, Function.prod_apply, Prod.mk.injEq] at hσ
  -- It is closed, since its restrictions to `U` and to `V` are exact.
  refine ⟨⟨σ, (mem_closedForms_iff_mextDerivₗ_eq_zero I σ).mpr <|
    SmoothForm.injective_mayerVietoris U V ?_⟩, hσ⟩
  rw [map_zero, LinearMap.prod_apply, Function.prod_apply, ← SmoothForm.mextDerivₗ_mpullback,
    ← SmoothForm.mextDerivₗ_mpullback, hσ.1, hσ.2]
  exact Prod.ext (LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I k) _)
    (LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I k) _)

end Complex

section Connecting

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

namespace deRhamCohomology

variable (I) in
/-- The **Mayer–Vietoris connecting map** `H^k(U ⊓ V) → H^{k+1}(U ⊔ V)` of de Rham cohomology: the
connecting map of the long exact cohomology sequence of the Mayer–Vietoris short exact sequence of
de Rham complexes. -/
def mayerVietorisδ (U V : Opens M) (k : ℕ) :
    deRhamCohomology I (U ⊓ V : Opens M) k →ₗ[ℝ] deRhamCohomology I (U ⊔ V : Opens M) (k + 1) :=
  ((mayerVietorisShortComplex_shortExact (I := I) U V).δ k (k + 1) rfl).hom

/-- The Mayer–Vietoris connecting map is the connecting morphism of the homology sequence of the
Mayer–Vietoris short exact sequence, so Mathlib's exactness results for that sequence apply. -/
theorem ofHom_mayerVietorisδ (U V : Opens M) (k : ℕ) :
    ModuleCat.ofHom (mayerVietorisδ I U V k) =
      (mayerVietorisShortComplex_shortExact (I := I) U V).δ k (k + 1) rfl :=
  (rfl)

/-- **The Mayer–Vietoris connecting map on classes.** Let `φ` be a closed form on `U ⊓ V`, written
as the difference `α - β` of the restrictions of forms `α` on `U` and `β` on `V`. If `σ` is a
closed form on `U ⊔ V` restricting to `dα` on `U` and to `dβ` on `V`, then the connecting map sends
the class of `φ` to the class of `σ`. -/
theorem mayerVietorisδ_mk (U V : Opens M) {k : ℕ} (φ : closedForms I (U ⊓ V : Opens M) k)
    (α : SmoothForm I U ℝ k) (β : SmoothForm I V ℝ k)
    (hαβ : SmoothForm.mpullback (Opens.inclusion inf_le_left) (contMDiff_inclusion _) α -
      SmoothForm.mpullback (Opens.inclusion inf_le_right) (contMDiff_inclusion _) β = φ.1)
    (σ : closedForms I (U ⊔ V : Opens M) (k + 1))
    (hσU : SmoothForm.mpullback (Opens.inclusion le_sup_left) (contMDiff_inclusion _) σ.1 =
      mextDerivₗ I k α)
    (hσV : SmoothForm.mpullback (Opens.inclusion le_sup_right) (contMDiff_inclusion _) σ.1 =
      mextDerivₗ I k β) :
    mayerVietorisδ I U V k (mk I k φ) = mk I (k + 1) σ := by
  -- The lift of `φ` to `Ω^•(U) ⊞ Ω^•(V)` is the pair `(α, β)`.
  let x₂ : (deRhamComplex I U ⊞ deRhamComplex I V).X k :=
    (biprod.inl : deRhamComplex I U ⟶ deRhamComplex I U ⊞ deRhamComplex I V).f k
        ((deRhamComplexXIso I k).inv α) +
      (biprod.inr : deRhamComplex I V ⟶ deRhamComplex I U ⊞ deRhamComplex I V).f k
        ((deRhamComplexXIso I k).inv β)
  have hx₂ : (biprod.desc
      (deRhamComplex.map (I := I) (I' := I) (Opens.inclusion (inf_le_left : U ⊓ V ≤ U))
        (contMDiff_inclusion _))
      (-deRhamComplex.map (I := I) (I' := I) (Opens.inclusion (inf_le_right : U ⊓ V ≤ V))
        (contMDiff_inclusion _))).f k x₂ = (deRhamComplexXIso I k).inv φ.1 := by
    rw [← hαβ, map_sub, ← deRhamComplex.map_f_inv_apply, ← deRhamComplex.map_f_inv_apply]
    simp [x₂, ← ModuleCat.comp_apply, sub_eq_add_neg]
  -- The image of `σ` in `Ω^•(U) ⊞ Ω^•(V)` is the differential of the lift.
  have hσ : (biprod.lift
      (deRhamComplex.map (I := I) (I' := I) (Opens.inclusion (le_sup_left : U ≤ U ⊔ V))
        (contMDiff_inclusion _))
      (deRhamComplex.map (I := I) (I' := I) (Opens.inclusion (le_sup_right : V ≤ U ⊔ V))
        (contMDiff_inclusion _))).f (k + 1) ((deRhamComplexXIso I (k + 1)).inv σ.1) =
      (deRhamComplex I U ⊞ deRhamComplex I V).d k (k + 1) x₂ := by
    simp [x₂, biprod.lift_eq, deRhamComplex.map_f_inv_apply _ _ (k + 1) σ.1, hσU, hσV,
      HomologicalComplex.Hom.comm_apply, deRhamComplex_d_apply]
  rw [mayerVietorisδ, mk_eq_moduleCatHomologyClass, mk_eq_moduleCatHomologyClass,
    HomologicalComplex.moduleCatHomologyClass_apply,
    HomologicalComplex.moduleCatHomologyClass_apply]
  -- The terms and maps of the Mayer–Vietoris short complex are, by definition, those above.
  refine (mayerVietorisShortComplex_shortExact (I := I) U V).moduleCat_δ_homologyπ k (k + 1) rfl
    _ x₂ (hx₂.trans (HomologicalComplex.iCycles_moduleCatCyclesMk _ _ _ _ _ _).symm) _
    ((congrArg _ (HomologicalComplex.iCycles_moduleCatCyclesMk _ _ _ _ _ _)).trans hσ)

section Cutoff

variable {U V : Opens M} {ρ : (U ⊔ V : Opens M) → ℝ} (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ)
  (hρV : tsupport ρ ⊆ {x | (x : M) ∈ V}) (hρU : tsupport (fun x ↦ 1 - ρ x) ⊆ {x | (x : M) ∈ U})

include hρ hρV hρU in
/-- **The Mayer–Vietoris connecting map through a cut-off function.** Let `ρ` be a smooth function
on `U ⊔ V` supported in `V` such that `1 - ρ` is supported in `U`, and let `φ` be a closed form on
`U ⊓ V`. If `σ` is the closed form on `U ⊔ V` extending `d(ρ φ)` by zero
(`TauCeti.exists_closedForms_coe_eq_extendByZero_mextDeriv`), then the connecting map sends the
class of `φ` to the class of `σ`. -/
theorem mayerVietorisδ_mk_eq_mk_extendByZero (φ : closedForms I (U ⊓ V : Opens M) k)
    (σ : closedForms I (U ⊔ V : Opens M) (k + 1))
    (hσ : (σ.1 : RoughForm I (U ⊔ V : Opens M) ℝ (k + 1)) = RoughForm.extendByZero (U ⊔ V)
      (mextDeriv fun y : (U ⊓ V : Opens M) ↦ ρ (Opens.inclusion inf_le_sup y) • φ.1.1 y)) :
    mayerVietorisδ I U V k (mk I k φ) = mk I (k + 1) σ := by
  obtain ⟨hU, hV⟩ := mpullback_extendByZero_mextDeriv_cutoff hρ hρV hρU φ
  exact mayerVietorisδ_mk U V φ (cutoffLeft hρ hρV φ.1) (cutoffRight hρ hρU φ.1)
    (mpullback_cutoffLeft_sub_mpullback_cutoffRight hρ hρV hρU φ.1) σ
    (Subtype.ext ((SmoothForm.coe_mpullback _ _ _).trans (hσ ▸ hU)))
    (Subtype.ext ((SmoothForm.coe_mpullback _ _ _).trans (hσ ▸ hV)))

end Cutoff

section Naturality

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] [T2Space M'] [SigmaCompactSpace M']

/-- **Naturality of the Mayer–Vietoris connecting map.** Let `f : U ⊔ V → U' ⊔ V'` be a smooth map
carrying `U` into `U'` and `V` into `V'`, and let `g : U ⊓ V → U' ⊓ V'` be its restriction. Then
pulling back along `g` and then applying the connecting map of the cover `{U, V}` agrees with
applying the connecting map of the cover `{U', V'}` and then pulling back along `f`. -/
theorem mayerVietorisδ_naturality {U V : Opens M} {U' V' : Opens M'}
    (f : (U ⊔ V : Opens M) → (U' ⊔ V' : Opens M')) (hf : ContMDiff I I' ∞ f)
    (hfU : ∀ x : (U ⊔ V : Opens M), (x : M) ∈ U → (f x : M') ∈ U')
    (hfV : ∀ x : (U ⊔ V : Opens M), (x : M) ∈ V → (f x : M') ∈ V')
    (g : (U ⊓ V : Opens M) → (U' ⊓ V' : Opens M')) (hg : ContMDiff I I' ∞ g)
    (hfg : ∀ x, (g x : M') = f (Opens.inclusion inf_le_sup x))
    (c : deRhamCohomology I' (U' ⊓ V' : Opens M') k) :
    mayerVietorisδ I U V k (map g hg k c) = map f hf (k + 1) (mayerVietorisδ I' U' V' k c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective I' k c
  -- Write `φ = α - β` with `α` on `U'` and `β` on `V'`, and choose the closed form `σ` on
  -- `U' ⊔ V'` restricting to `dα` and `dβ`, which represents the image of `[φ]`.
  obtain ⟨⟨α, β⟩, hαβ⟩ := SmoothForm.surjective_mayerVietoris U' V' φ.1
  rw [LinearMap.coprod_apply, LinearMap.neg_apply, ← sub_eq_add_neg] at hαβ
  obtain ⟨σ, hσU, hσV⟩ := exists_closedForms_mpullback_eq_mextDerivₗ α β (hαβ ▸ φ.2)
  rw [mayerVietorisδ_mk U' V' φ α β hαβ σ hσU hσV, map_mk, map_mk]
  -- The restrictions of `f` to `U → U'` and to `V → V'`.
  let fU : U → U' := fun x ↦ ⟨f (Opens.inclusion le_sup_left x), hfU _ x.2⟩
  let fV : V → V' := fun x ↦ ⟨f (Opens.inclusion le_sup_right x), hfV _ x.2⟩
  -- Read in `M'`, they are the composites of `f` with the inclusions of `U` and `V` in `U ⊔ V`.
  have hfU' : ContMDiff I I' ∞ fU := (ContMDiff.subtypeVal_comp_iff U' fU).mp
    (contMDiff_subtype_val.comp (hf.comp (contMDiff_inclusion le_sup_left)) :
      ContMDiff I I' ∞ (Subtype.val ∘ f ∘ Opens.inclusion le_sup_left))
  have hfV' : ContMDiff I I' ∞ fV := (ContMDiff.subtypeVal_comp_iff V' fV).mp
    (contMDiff_subtype_val.comp (hf.comp (contMDiff_inclusion le_sup_right)) :
      ContMDiff I I' ∞ (Subtype.val ∘ f ∘ Opens.inclusion le_sup_right))
  have hgU : Opens.inclusion inf_le_left ∘ g = fU ∘ Opens.inclusion inf_le_left :=
    funext fun x ↦ Subtype.ext (hfg x)
  have hgV : Opens.inclusion inf_le_right ∘ g = fV ∘ Opens.inclusion inf_le_right :=
    funext fun x ↦ Subtype.ext (hfg x)
  refine mayerVietorisδ_mk U V _ (SmoothForm.mpullback fU hfU' α)
    (SmoothForm.mpullback fV hfV' β) ?_ (closedForms.mpullback f hf (k + 1) σ) ?_ ?_
  · rw [closedForms.coe_mpullback, ← hαβ, map_sub]
    simp only [← LinearMap.comp_apply, ← SmoothForm.mpullback_comp, hgU, hgV]
  · -- The inclusion of `U'` composed with `fU` is, by definition, `f` composed with the inclusion
    -- of `U`.
    rw [closedForms.coe_mpullback, ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp,
      SmoothForm.mextDerivₗ_mpullback, ← hσU, ← LinearMap.comp_apply,
      ← SmoothForm.mpullback_comp]
    rfl
  · -- Likewise for `V'`, `fV` and `V`.
    rw [closedForms.coe_mpullback, ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp,
      SmoothForm.mextDerivₗ_mpullback, ← hσV, ← LinearMap.comp_apply,
      ← SmoothForm.mpullback_comp]
    rfl

/-- **Naturality of the Mayer–Vietoris connecting map under refinement.** For open subsets
`U ≤ U'` and `V ≤ V'` of `M`, restricting a class from `U' ⊓ V'` to `U ⊓ V` and then applying the
connecting map of `{U, V}` agrees with applying the connecting map of `{U', V'}` and then
restricting from `U' ⊔ V'` to `U ⊔ V`. -/
theorem mayerVietorisδ_naturality_of_le {U V U' V' : Opens M} (hU : U ≤ U') (hV : V ≤ V')
    (c : deRhamCohomology I (U' ⊓ V' : Opens M) k) :
    mayerVietorisδ I U V k
        (map (Opens.inclusion (inf_le_inf hU hV)) (contMDiff_inclusion _) k c) =
      map (Opens.inclusion (sup_le_sup hU hV)) (contMDiff_inclusion _) (k + 1)
        (mayerVietorisδ I U' V' k c) :=
  mayerVietorisδ_naturality _ _ (fun _ hx ↦ hU hx) (fun _ hx ↦ hV hx) _ _ (fun _ ↦ rfl) c

end Naturality

end deRhamCohomology

end Connecting

end TauCeti
