/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Japanese

import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Algebra.Module.LocalizedModule.Submodule

/-!
# Linear-form separation criteria for finite submodules and integral closures

Let `R` be a commutative ring, `K` a field that is a faithful `R`-algebra, and `V` a
finite-dimensional `K`-vector space with a compatible `R`-module structure. An `R`-submodule
`M ≤ V` embeds `R`-linearly into `Fin d → R` with `d ≤ finrank K V` whenever `K`-linear forms on `V`
sending `M` into `Set.range (algebraMap R K)` separate the nonzero elements of `M`. When `R` is
Noetherian, this implies that `M` is finitely generated over `R`.

When `K` is the fraction field of a Noetherian domain `R`, this sufficient condition becomes a
three-way equivalence: `M` is finitely generated if and only if `Module.Dual R M` separates points
of `M`, if and only if `K`-linear forms on `V` carrying `M` into `R` separate points of `M`.

Applied to integral closures in finite purely inseparable extensions via
`TauCeti.Ring.IsJapanese.of_isPurelyInseparable`, this yields a linear-functional criterion for a
Noetherian domain to be Japanese (`TauCeti.Ring.IsJapanese.of_forall_exists_dual_ne_zero`).

## Main results

* `Submodule.exists_injective_linearMap_fin_of_forall_exists_dual_ne_zero`: if `K`-linear forms on a
  finite-dimensional `K`-space `V` sending `M` into `R` separate nonzero elements of `M`, then `M`
  embeds `R`-linearly into `Fin d → R` with `d ≤ Module.finrank K V` (without assuming `R` is
  Noetherian).
* `Submodule.fg_of_forall_exists_dual_ne_zero`: over a Noetherian ring `R`, the same separation
  hypothesis implies `M.FG`.
* `Submodule.exists_dual_apply_eq_algebraMap`: if `K` is a localization of `R`, every `R`-linear
  functional `M →ₗ[R] R` extends to a `K`-linear functional `V →ₗ[K] K`.
* `Submodule.fg_iff_forall_exists_dual_ne_zero` and
  `Submodule.fg_iff_forall_exists_dual_submodule_ne_zero`: the three-way equivalence over a
  Noetherian domain `R` with fraction field `K`.
* `TauCeti.IsIntegralClosure.finite_of_forall_exists_dual_ne_zero` and
  `TauCeti.IsIntegralClosure.finite_iff_forall_exists_dual_ne_zero`: specialization to an abstract
  integral closure `C` of `R` in `L`.
* `TauCeti.Ring.IsJapanese.of_forall_exists_dual_ne_zero`: linear-functional criterion for a
  Noetherian domain to be Japanese, testing only finite purely inseparable extensions.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §4.1, Lemma 3 and
  Proposition 4.
-/

public section

namespace Submodule

section Faithful

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K] [FaithfulSMul R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- If `K`-linear functionals on a finite-dimensional `K`-vector space `V` carrying an
`R`-submodule `M` into `Set.range (algebraMap R K)` separate the nonzero elements of `M`, then `M`
embeds `R`-linearly into `Fin d → R` for some `d ≤ Module.finrank K V`
([bosch-guntzer-remmert], §4.1, Lemma 3). -/
theorem exists_injective_linearMap_fin_of_forall_exists_dual_ne_zero [FiniteDimensional K V]
    (M : Submodule R V)
    (h : ∀ x ∈ M, x ≠ 0 → ∃ φ : Module.Dual K V,
      (∀ y ∈ M, φ y ∈ Set.range (algebraMap R K)) ∧ φ x ≠ 0) :
    ∃ (d : ℕ) (ι : M →ₗ[R] Fin d → R), d ≤ Module.finrank K V ∧ Function.Injective ι := by
  let S : Set (Module.Dual K V) := {φ | ∀ y ∈ M, φ y ∈ Set.range (algebraMap R K)}
  obtain ⟨f, hf_mem, hf_span, _⟩ := exists_fun_fin_finrank_span_eq K S
  have hinj_alg : Function.Injective (Algebra.linearMap R K) :=
    (faithfulSMul_iff_algebraMap_injective R K).mp inferInstance
  let eR : R ≃ₗ[R] LinearMap.range (Algebra.linearMap R K) :=
    LinearEquiv.ofInjective (Algebra.linearMap R K) hinj_alg
  let ψ (i : Fin (Module.finrank K (span K S))) : M →ₗ[R] R :=
    eR.symm.toLinearMap.comp <|
      ((f i).restrictScalars R ∘ₗ M.subtype).codRestrict
        (LinearMap.range (Algebra.linearMap R K)) fun y ↦ hf_mem i y.1 y.2
  refine ⟨Module.finrank K (span K S), LinearMap.pi ψ, ?_, ?_⟩
  · calc Module.finrank K (span K S)
        ≤ Module.finrank K (Module.Dual K V) := Submodule.finrank_le _
      _ = Module.finrank K V := Subspace.dual_finrank_eq
  · rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨φ, hφM, hφx⟩ := h x.1 x.2 (Subtype.coe_ne_coe.mpr hx0)
    have hker : span K S ≤ LinearMap.ker (Module.Dual.eval K V x.1) := by
      rw [← hf_span, span_le]
      rintro _ ⟨i, rfl⟩
      have hψ0 : ψ i x = 0 := congrFun hx i
      have heval : Algebra.linearMap R K (ψ i x) = f i x.1 :=
        congrArg Subtype.val (eR.apply_symm_apply _)
      rw [hψ0, map_zero] at heval
      exact heval.symm
    exact hφx (hker (subset_span hφM))

/-- Over a Noetherian ring `R`, an `R`-submodule `M` of a finite-dimensional `K`-vector space `V` is
finitely generated whenever `K`-linear functionals carrying `M` into `Set.range (algebraMap R K)`
separate the nonzero elements of `M` ([bosch-guntzer-remmert], §4.1, Lemma 3). -/
theorem fg_of_forall_exists_dual_ne_zero [IsNoetherianRing R] [FiniteDimensional K V]
    (M : Submodule R V)
    (h : ∀ x ∈ M, x ≠ 0 → ∃ φ : Module.Dual K V,
      (∀ y ∈ M, φ y ∈ Set.range (algebraMap R K)) ∧ φ x ≠ 0) :
    M.FG := by
  obtain ⟨d, ι, -, hι⟩ := M.exists_injective_linearMap_fin_of_forall_exists_dual_ne_zero h
  exact Module.Finite.iff_fg.mp (Module.Finite.of_injective ι hι)

end Faithful

section Localization

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- If `K` is a localization of `R` at a submonoid `S`, every `R`-linear functional on an
`R`-submodule `M ≤ V` extends to a `K`-linear functional on `V`
([bosch-guntzer-remmert], §4.1, Proposition 4, `(ii) ⇒ (iii)`). -/
theorem exists_dual_apply_eq_algebraMap (S : Submonoid R) [IsLocalization S K]
    (M : Submodule R V) (f : Module.Dual R M) :
    ∃ φ : Module.Dual K V, ∀ y : M, φ y.1 = algebraMap R K (f y) := by
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
([bosch-guntzer-remmert], §4.1, Proposition 4, `(i) ⇒ (iii)`). -/
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

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- Over a Noetherian ring `R` with fraction field `K`, an `R`-submodule `M` of a
finite-dimensional `K`-vector space `V` is finitely generated if and only if `K`-linear functionals
carrying `M` into `Set.range (algebraMap R K)` separate the nonzero elements of `M`
([bosch-guntzer-remmert], §4.1, Proposition 4). -/
theorem fg_iff_forall_exists_dual_ne_zero [IsNoetherianRing R] [FiniteDimensional K V]
    (M : Submodule R V) :
    M.FG ↔ ∀ x ∈ M, x ≠ 0 → ∃ φ : Module.Dual K V,
      (∀ y ∈ M, φ y ∈ Set.range (algebraMap R K)) ∧ φ x ≠ 0 :=
  ⟨fun hM _ _ hx ↦ hM.exists_dual_ne_zero (nonZeroDivisors R) hx,
    M.fg_of_forall_exists_dual_ne_zero⟩

end FractionRing

/-- Over a Noetherian ring `R` with fraction field `K`, an `R`-submodule `M` of a
finite-dimensional `K`-vector space `V` is finitely generated if and only if `Module.Dual R M`
separates the nonzero elements of `M` ([bosch-guntzer-remmert], §4.1, Proposition 4). -/
theorem fg_iff_forall_exists_dual_submodule_ne_zero {R V : Type*} [CommRing R]
    [IsNoetherianRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V] [FiniteDimensional K V]
    (M : Submodule R V) :
    M.FG ↔ ∀ x : M, x ≠ 0 → ∃ f : Module.Dual R M, f x ≠ 0 := by
  rw [M.fg_iff_forall_exists_dual_ne_zero (K := K)]
  constructor
  · intro h x hx
    obtain ⟨φ, hφM, hφx⟩ := h x.1 x.2 (Subtype.coe_ne_coe.mpr hx)
    let eR : R ≃ₗ[R] LinearMap.range (Algebra.linearMap R K) :=
      LinearEquiv.ofInjective (Algebra.linearMap R K) (IsFractionRing.injective R K)
    let f : Module.Dual R M := eR.symm.toLinearMap.comp <|
      (φ.restrictScalars R ∘ₗ M.subtype).codRestrict
        (LinearMap.range (Algebra.linearMap R K)) fun y ↦ hφM y.1 y.2
    refine ⟨f, fun hf0 ↦ hφx ?_⟩
    have heval : Algebra.linearMap R K (f x) = φ x.1 :=
      congrArg Subtype.val (eR.apply_symm_apply _)
    rw [hf0, map_zero] at heval
    exact heval.symm
  · intro h x hxM hx0
    obtain ⟨f, hf⟩ := h ⟨x, hxM⟩ (Subtype.coe_ne_coe.mp hx0)
    obtain ⟨φ, hφ⟩ := M.exists_dual_apply_eq_algebraMap (K := K) (nonZeroDivisors R) f
    exact ⟨φ, fun y hy ↦ ⟨f ⟨y, hy⟩, (hφ ⟨y, hy⟩).symm⟩,
      by rw [hφ ⟨x, hxM⟩]; exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hf⟩

end Submodule

namespace TauCeti

section IsIntegralClosure

variable {R L C : Type*} [CommRing R] [CommRing L] [Algebra R L]
  [CommRing C] [Algebra R C] [Algebra C L] [IsScalarTower R C L] [IsIntegralClosure C R L]

/-- Let `R` be a Noetherian commutative ring, `K` a field that is a faithful `R`-algebra, and `L` a
commutative `R`-algebra that is a finite-dimensional `K`-vector space compatibly with `R`. An
integral closure `C` of `R` in `L` is a finite `R`-module whenever every nonzero element of `L`
integral over `R` is separated from `0` by a `K`-linear form on `L` carrying integral elements into
`Set.range (algebraMap R K)`. -/
theorem IsIntegralClosure.finite_of_forall_exists_dual_ne_zero [IsNoetherianRing R]
    (K : Type*) [Field K] [Algebra R K]
    [FaithfulSMul R K] [Module K L] [IsScalarTower R K L] [FiniteDimensional K L]
    (h : ∀ x : L, IsIntegral R x → x ≠ 0 → ∃ φ : Module.Dual K L,
      (∀ y : L, IsIntegral R y → φ y ∈ Set.range (algebraMap R K)) ∧ φ x ≠ 0) :
    Module.Finite R C := by
  let ι : C →ₗ[R] L := (IsScalarTower.toAlgHom R C L).toLinearMap
  have hι : Function.Injective ι := IsIntegralClosure.algebraMap_injective C R L
  have hrange (z : L) : z ∈ LinearMap.range ι ↔ IsIntegral R z :=
    ⟨by
      rintro ⟨c, rfl⟩
      exact (IsIntegralClosure.isIntegral R L c).map (IsScalarTower.toAlgHom R C L),
     fun hz ↦ IsIntegralClosure.isIntegral_iff.mp hz⟩
  have hfg : (LinearMap.range ι).FG :=
    (LinearMap.range ι).fg_of_forall_exists_dual_ne_zero fun x hx hx0 ↦ by
      obtain ⟨φ, hφM, hφx⟩ := h x ((hrange x).mp hx) hx0
      exact ⟨φ, fun y hy ↦ hφM y ((hrange y).mp hy), hφx⟩
  have : Module.Finite R (LinearMap.range ι) := Module.Finite.iff_fg.mpr hfg
  exact Module.Finite.equiv (LinearEquiv.ofInjective ι hι).symm

/-- Over a Noetherian ring `R` with fraction field `K`, an integral closure `C` of `R` in `L` is a
finite `R`-module if and only if `K`-linear forms on `L` carrying integral elements into
`Set.range (algebraMap R K)` separate nonzero integral elements. -/
theorem IsIntegralClosure.finite_iff_forall_exists_dual_ne_zero [IsNoetherianRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    [Module K L] [IsScalarTower R K L] [FiniteDimensional K L] :
    Module.Finite R C ↔ ∀ x : L, IsIntegral R x → x ≠ 0 → ∃ φ : Module.Dual K L,
      (∀ y : L, IsIntegral R y → φ y ∈ Set.range (algebraMap R K)) ∧ φ x ≠ 0 := by
  let ι : C →ₗ[R] L := (IsScalarTower.toAlgHom R C L).toLinearMap
  have hι : Function.Injective ι := IsIntegralClosure.algebraMap_injective C R L
  have hrange (z : L) : z ∈ LinearMap.range ι ↔ IsIntegral R z :=
    ⟨by
      rintro ⟨c, rfl⟩
      exact (IsIntegralClosure.isIntegral R L c).map (IsScalarTower.toAlgHom R C L),
     fun hz ↦ IsIntegralClosure.isIntegral_iff.mp hz⟩
  constructor
  · intro _ x _ hx0
    have hfg : (LinearMap.range ι).FG :=
      Module.Finite.iff_fg.mp (Module.Finite.equiv (LinearEquiv.ofInjective ι hι))
    obtain ⟨φ, hφM, hφx⟩ := hfg.exists_dual_ne_zero (K := K) (nonZeroDivisors R) hx0
    exact ⟨φ, fun y hy ↦ hφM y ((hrange y).mpr hy), hφx⟩
  · exact IsIntegralClosure.finite_of_forall_exists_dual_ne_zero (C := C) K

end IsIntegralClosure

namespace Ring.IsJapanese

universe u v

/-- **Linear-functional criterion for Japanese domains.** A Noetherian domain `R` with fraction
field `K` is Japanese if, for every finite purely inseparable extension `M` of `K` (in the universe
of `R`) and every nonzero `x : M` integral over `R`, there exists a `K`-linear functional
`φ : Module.Dual K M` sending every element of `M` integral over `R` into
`Set.range (algebraMap R K)` with `φ x ≠ 0`
([bosch-guntzer-remmert], §4.1, Lemma 3, combined with Stacks, Lemma 10.161.12 (032N)). -/
theorem of_forall_exists_dual_ne_zero {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (h : ∀ (M : Type u) [Field M] [Algebra K M] [Algebra R M] [IsScalarTower R K M]
      [FiniteDimensional K M] [IsPurelyInseparable K M] (x : M), IsIntegral R x → x ≠ 0 →
      ∃ φ : Module.Dual K M,
        (∀ y : M, IsIntegral R y → φ y ∈ Set.range (algebraMap R K)) ∧ φ x ≠ 0) :
    IsJapanese R :=
  IsJapanese.of_isPurelyInseparable K fun M _ _ _ _ _ _ ↦
    IsIntegralClosure.finite_of_forall_exists_dual_ne_zero (C := integralClosure R M) K (h M)

end Ring.IsJapanese

end TauCeti
