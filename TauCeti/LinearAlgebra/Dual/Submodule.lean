/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs

import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Algebra.Module.LocalizedModule.Submodule

/-!
# Linear-form separation criteria for finite submodules

Let `R` be a commutative ring, `K` a field that is a faithful `R`-algebra, and `V` a
finite-dimensional `K`-vector space with a compatible `R`-module structure. An `R`-submodule
`M ≤ V` embeds `R`-linearly into `Fin d → R` with `d ≤ finrank K V` whenever `K`-linear forms on `V`
sending `M` into `Set.range (algebraMap R K)` separate the nonzero elements of `M`. When `R` is
Noetherian, this implies that `M` is finitely generated over `R`.

When `K` is a localization of `R`, every `R`-linear functional on `M` extends to a `K`-linear
functional on `V`, and every finitely generated `M` admits separating `K`-linear forms carrying `M`
into `Set.range (algebraMap R K)`. Consequently, when `K` is the fraction field of a Noetherian ring
`R`, finite generation of `M` is equivalent to separation by `Module.Dual R M` and to separation by
`K`-linear forms on `V` carrying `M` into `Set.range (algebraMap R K)`.

## Main results

* `Submodule.exists_injective_linearMap_fin_of_forall_exists_dual_ne_zero`: if `K`-linear forms on a
  finite-dimensional `K`-space `V` sending `M` into `Set.range (algebraMap R K)` separate nonzero
  elements of `M`, then `M` embeds `R`-linearly into `Fin d → R` with `d ≤ Module.finrank K V`
  (without assuming `R` is Noetherian).
* `Submodule.fg_of_forall_exists_dual_mem_range_ne_zero`: over a Noetherian ring `R`, the same
  separation hypothesis implies `M.FG`.
* `Submodule.exists_dual_apply_eq_algebraMap`: if `K` is a localization of `R`, every `R`-linear
  functional `M →ₗ[R] R` extends to a `K`-linear functional `V →ₗ[K] K`.
* `Submodule.FG.exists_dual_ne_zero`: for a finitely generated `R`-submodule `M`, every nonzero
  vector in `V` is separated from `0` by a `K`-linear functional sending `M` into
  `Set.range (algebraMap R K)`.
* `Submodule.fg_iff_forall_exists_dual_ne_zero` and
  `Submodule.fg_iff_forall_exists_dual_submodule_ne_zero`: the three-way equivalence over a
  Noetherian ring `R` with fraction field `K`.

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §4.1, Lemma 3 and Proposition 4.
-/

public section

namespace Submodule

section Faithful

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K] [FaithfulSMul R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- If `K`-linear functionals on a finite-dimensional `K`-vector space `V` carrying an
`R`-submodule `M` into `Set.range (algebraMap R K)` separate the nonzero elements of `M`, then `M`
embeds `R`-linearly into `Fin d → R` for some `d ≤ Module.finrank K V`
(Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §4.1, Lemma 3). -/
theorem exists_injective_linearMap_fin_of_forall_exists_dual_ne_zero [FiniteDimensional K V]
    (M : Submodule R V)
    (h : ∀ x ∈ M, x ≠ 0 → ∃ φ : Module.Dual K V,
      (∀ y ∈ M, φ y ∈ Set.range (algebraMap R K)) ∧ φ x ≠ 0) :
    ∃ (d : ℕ) (ι : M →ₗ[R] Fin d → R), d ≤ Module.finrank K V ∧ Function.Injective ι := by
  let S : Set (Module.Dual K V) := {φ | ∀ y ∈ M, φ y ∈ Set.range (algebraMap R K)}
  obtain ⟨f, hf_mem, hf_span, _⟩ := exists_fun_fin_finrank_span_eq K S
  let ψ (i : Fin (Module.finrank K (span K S))) : M →ₗ[R] R :=
    LinearMap.restrictScalarsRange M.subtype (Algebra.linearMap R K)
      (FaithfulSMul.algebraMap_injective R K) (f i) fun y ↦ hf_mem i y.val y.property
  refine ⟨Module.finrank K (span K S), LinearMap.pi ψ, ?_, ?_⟩
  · calc Module.finrank K (span K S)
        ≤ Module.finrank K (Module.Dual K V) := Submodule.finrank_le _
      _ = Module.finrank K V := Subspace.dual_finrank_eq
  · rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨φ, hφM, hφx⟩ := h x.val x.property (Subtype.coe_ne_coe.mpr hx0)
    have hker : span K S ≤ LinearMap.ker (Module.Dual.eval K V x.val) := by
      rw [← hf_span, span_le]
      rintro _ ⟨i, rfl⟩
      exact (LinearMap.restrictScalarsRange_apply_eq_zero_iff M.subtype (Algebra.linearMap R K)
        (FaithfulSMul.algebraMap_injective R K) (f i) (fun y ↦ hf_mem i y.val y.property) x).mp
        (congrFun hx i)
    exact hφx (hker (subset_span hφM))

/-- Over a Noetherian ring `R`, an `R`-submodule `M` of a finite-dimensional `K`-vector space `V` is
finitely generated whenever `K`-linear functionals carrying `M` into `Set.range (algebraMap R K)`
separate the nonzero elements of `M`
(Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §4.1, Lemma 3). -/
theorem fg_of_forall_exists_dual_mem_range_ne_zero [IsNoetherianRing R] [FiniteDimensional K V]
    (M : Submodule R V)
    (h : ∀ x ∈ M, x ≠ 0 → ∃ φ : Module.Dual K V,
      (∀ y ∈ M, φ y ∈ Set.range (algebraMap R K)) ∧ φ x ≠ 0) :
    M.FG := by
  obtain ⟨d, ι, -, hι⟩ := M.exists_injective_linearMap_fin_of_forall_exists_dual_ne_zero h
  exact Module.Finite.iff_fg.mp (Module.Finite.of_injective ι hι)

end Faithful

section Localization

variable {R V : Type*} [CommRing R] (K : Type*) [Field K] [Algebra R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- If `K` is a localization of `R` at a submonoid `S`, every `R`-linear functional on an
`R`-submodule `M ≤ V` extends to a `K`-linear functional on `V`
(Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §4.1, Proposition 4, `(ii) ⇒ (iii)`). -/
theorem exists_dual_apply_eq_algebraMap (S : Submonoid R) [IsLocalization S K]
    (M : Submodule R V) (f : Module.Dual R M) :
    ∃ φ : Module.Dual K V, ∀ y : M, φ y.val = algebraMap R K (f y) := by
  have : IsLocalizedModule S (LinearMap.id : V →ₗ[R] V) := isLocalizedModule_id S V K
  let g : M.localized' K S (LinearMap.id : V →ₗ[R] V) →ₗ[K] K :=
    (IsLocalizedModule.map S (M.toLocalized' K S (LinearMap.id : V →ₗ[R] V))
      (Algebra.linearMap R K) f).extendScalarsOfIsLocalization S K
  obtain ⟨φ, hφ⟩ := g.exists_extend
  refine ⟨φ, fun y ↦ ?_⟩
  have hy := LinearMap.congr_fun hφ (M.toLocalized' K S (LinearMap.id : V →ₗ[R] V) y)
  simpa only [g, LinearMap.comp_apply, Submodule.subtype_apply, toLocalized'_apply_coe,
    LinearMap.id_apply, LinearMap.extendScalarsOfIsLocalization_apply',
    IsLocalizedModule.map_apply, Algebra.linearMap_apply] using hy

/-- For a finitely generated `R`-submodule `M` of a `K`-vector space `V` over a field `K` that is a
localization of `R` at `S`, every nonzero vector in `V` is separated from `0` by a `K`-linear
functional on `V` sending `M` into `Set.range (algebraMap R K)`
(Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §4.1, Proposition 4, `(i) ⇒ (iii)`). -/
theorem FG.exists_dual_ne_zero (S : Submonoid R) [IsLocalization S K]
    {M : Submodule R V} (hM : M.FG) {x : V} (hx : x ≠ 0) :
    ∃ φ : Module.Dual K V, (∀ y ∈ M, φ y ∈ Set.range (algebraMap R K)) ∧ φ x ≠ 0 := by
  obtain ⟨ψ, hψx⟩ := Module.Projective.exists_dual_ne_zero K hx
  have hspan : span K ((1 : Submodule R K) : Set K) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    rw [← mul_one c, ← smul_eq_mul]
    exact smul_mem _ c (subset_span (Submodule.mem_one.mpr ⟨1, map_one (algebraMap R K)⟩))
  obtain ⟨s, hs, hsM⟩ := (hM.map (ψ.restrictScalars R)).exists_smul_mem_of_le_span
    (F := K) S (M := (1 : Submodule R K))
    (by rw [hspan]; exact fun _ _ ↦ mem_top)
  refine ⟨algebraMap R K s • ψ, fun y hy ↦ ?_, ?_⟩
  · rw [LinearMap.smul_apply, algebraMap_smul K s (ψ y)]
    exact Submodule.mem_one.mp (hsM (ψ y) ⟨y, hy, rfl⟩)
  · rw [LinearMap.smul_apply, smul_eq_mul]
    exact mul_ne_zero (IsLocalization.map_units K ⟨s, hs⟩).ne_zero hψx

end Localization

section FractionRing

variable {R V : Type*} [CommRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- Over a Noetherian ring `R` with fraction field `K`, an `R`-submodule `M` of a
finite-dimensional `K`-vector space `V` is finitely generated if and only if `K`-linear functionals
carrying `M` into `Set.range (algebraMap R K)` separate the nonzero elements of `M`
(Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §4.1, Proposition 4). -/
theorem fg_iff_forall_exists_dual_ne_zero [IsNoetherianRing R] [FiniteDimensional K V]
    (M : Submodule R V) :
    M.FG ↔ ∀ x ∈ M, x ≠ 0 → ∃ φ : Module.Dual K V,
      (∀ y ∈ M, φ y ∈ Set.range (algebraMap R K)) ∧ φ x ≠ 0 :=
  ⟨fun hM _ _ hx ↦ hM.exists_dual_ne_zero K (nonZeroDivisors R) hx,
    M.fg_of_forall_exists_dual_mem_range_ne_zero⟩

/-- Over a Noetherian ring `R` with fraction field `K`, an `R`-submodule `M` of a
finite-dimensional `K`-vector space `V` is finitely generated if and only if `Module.Dual R M`
separates the nonzero elements of `M`
(Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, §4.1, Proposition 4). -/
theorem fg_iff_forall_exists_dual_submodule_ne_zero [IsNoetherianRing R] [FiniteDimensional K V]
    (M : Submodule R V) :
    M.FG ↔ ∀ x : M, x ≠ 0 → ∃ f : Module.Dual R M, f x ≠ 0 := by
  rw [M.fg_iff_forall_exists_dual_ne_zero K]
  constructor
  · intro h x hx
    obtain ⟨φ, hφM, hφx⟩ := h x.val x.property (Subtype.coe_ne_coe.mpr hx)
    let f : Module.Dual R M :=
      LinearMap.restrictScalarsRange M.subtype (Algebra.linearMap R K)
        (IsFractionRing.injective R K) φ fun y ↦ hφM y.val y.property
    refine ⟨f, fun hf0 ↦ hφx <| (LinearMap.restrictScalarsRange_apply_eq_zero_iff M.subtype
      (Algebra.linearMap R K) (IsFractionRing.injective R K) φ
      (fun y ↦ hφM y.val y.property) x).mp hf0⟩
  · intro h x hxM hx0
    obtain ⟨f, hf⟩ := h ⟨x, hxM⟩ (Subtype.coe_ne_coe.mp hx0)
    obtain ⟨φ, hφ⟩ := M.exists_dual_apply_eq_algebraMap K (nonZeroDivisors R) f
    exact ⟨φ, fun y hy ↦ ⟨f ⟨y, hy⟩, (hφ ⟨y, hy⟩).symm⟩,
      by rw [hφ ⟨x, hxM⟩]; exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hf⟩

end FractionRing

end Submodule
