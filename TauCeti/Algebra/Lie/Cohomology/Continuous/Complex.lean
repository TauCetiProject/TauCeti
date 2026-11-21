/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Algebra.Lie.Cohomology.Continuous.Cohomology

/-!
# The continuous Chevalley–Eilenberg cochain complex

Let `L` be a Lie algebra carrying a topology whose Lie bracket is continuous and `M` an `L`-module
regarded as discrete whose orbit maps `⁅·, m⁆ : L → M` are locally constant. Building on
`TauCeti.Algebra.Lie.Cohomology.Continuous.Cohomology`, this file restricts the Chevalley–Eilenberg
differential to `continuousD` on `continuousCochain R L M n`, assembles these differentials into a
cochain complex `continuousCochainComplex` in `ModuleCat R` together with its subcomplex inclusion
`continuousCochainComplexι` into `cochainComplex R L M` and functoriality
`continuousCochainComplexMap`, and establishes a natural linear equivalence
`continuousCohomologyHomologyEquiv` between `continuousCohomology R L M n` and
`(continuousCochainComplex R L M hL hM).homology n`.

## Main definitions

* `TauCeti.LieModule.Cohomology.continuousD`: the Chevalley–Eilenberg differential restricted to
  `continuousCochain R L M n`.
* `TauCeti.LieModule.Cohomology.continuousCochainComplex`,
  `TauCeti.LieModule.Cohomology.continuousCochainComplexXIso`: the continuous Chevalley–Eilenberg
  cochain complex in `ModuleCat R` and its degreewise object identifications.
* `TauCeti.LieModule.Cohomology.continuousCochainComplexι`,
  `TauCeti.LieModule.Cohomology.continuousCochainComplexMap`: the subcomplex inclusion into
  `cochainComplex R L M` and functorial chain maps.
* `TauCeti.LieModule.Cohomology.continuousCohomologyClass`,
  `TauCeti.LieModule.Cohomology.continuousCohomologyHomologyEquiv`: the homology class map from
  continuous cocycles and the linear equivalence between `continuousCohomology` and the categorical
  homology of `continuousCochainComplex`.

## Main results

* `TauCeti.LieModule.Cohomology.continuousCochainMap_comp_continuousD`: `continuousCochainMap`
  commutes with `continuousD`.
* `TauCeti.LieModule.Cohomology.continuousCochainComplexMap_comp_ι`: functoriality commutes with
  the subcomplex inclusion `continuousCochainComplexι`.
* `TauCeti.LieModule.Cohomology.homologyMap_continuousCohomologyHomologyEquiv`: naturality of
  `continuousCohomologyHomologyEquiv` with respect to `continuousCohomologyMap` and `homologyMap`.

## References

* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), 85–124.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  §7.7.
-/

public section

open CategoryTheory HomologicalComplex _root_.LieModule.Cohomology

namespace TauCeti.LieModule.Cohomology

universe u v w

section Differential

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [TopologicalSpace L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The Chevalley–Eilenberg differential restricted to continuous cochains, defined when the Lie
bracket of `L` is continuous and every orbit map `⁅·, m⁆ : L → M` is locally constant. -/
def continuousD (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ) :
    continuousCochain R L M n →ₗ[R] continuousCochain R L M (n + 1) :=
  (d R L M n).restrict fun _ hω ↦ d_mem_continuousCochain hL hM hω

variable {R L M}

@[simp]
theorem coe_continuousD (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) {n : ℕ}
    (ω : continuousCochain R L M n) :
    (continuousD R L M hL hM n ω : L [⋀^Fin (n + 1)]→ₗ[R] M) = d R L M n ω := (rfl)

@[simp]
theorem continuousD_continuousD (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ)
    (ω : continuousCochain R L M n) :
    continuousD R L M hL hM (n + 1) (continuousD R L M hL hM n ω) = 0 := Subtype.ext (d_d n ω.val)

theorem continuousD_comp_continuousD (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ) :
    continuousD R L M hL hM (n + 1) ∘ₗ continuousD R L M hL hM n = 0 :=
  LinearMap.ext (continuousD_continuousD hL hM n)

/-- `continuousCochainMap` commutes with `continuousD` when `e` intertwines the module actions
along `φ`. -/
theorem continuousCochainMap_comp_continuousD {L' M' : Type*}
    [LieRing L'] [LieAlgebra R L'] [TopologicalSpace L']
    [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']
    (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (hφ : Continuous φ)
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M))
    (hL' : Continuous fun p : L' × L' ↦ ⁅p.1, p.2⁆)
    (hM' : ∀ m' : M', IsLocallyConstant (⁅·, m'⁆ : L' → M')) (n : ℕ) :
    (continuousCochainMap e φ hφ (n + 1)).comp (continuousD R L M hL hM n) =
      (continuousD R L' M' hL' hM' n).comp (continuousCochainMap e φ hφ n) := by
  ext ω : 1
  apply Subtype.ext
  simp only [LinearMap.comp_apply, coe_continuousCochainMap, coe_continuousD,
    cochainMap_d e φ he n ω.val]

end Differential

section CategoricalComplex

variable (R : Type u) [CommRing R] (L : Type v) (M : Type w) [LieRing L] [LieAlgebra R L]
  [TopologicalSpace L] [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The continuous Chevalley–Eilenberg cochain complex of `L` with discrete coefficients in `M`,
whose degree-`n` term is `continuousCochain R L M n` and whose differential is `continuousD`. -/
noncomputable def continuousCochainComplex (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) :
    CochainComplex (ModuleCat.{max v w} R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (continuousCochain R L M n))
    (fun n ↦ ModuleCat.ofHom (continuousD R L M hL hM n))
    fun n ↦ ModuleCat.hom_ext (continuousD_comp_continuousD hL hM n)

/-- Canonical identification of the degree-`n` object of `continuousCochainComplex` with
`continuousCochain R L M n`. -/
noncomputable def continuousCochainComplexXIso (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ) :
    (continuousCochainComplex R L M hL hM).X n ≅ ModuleCat.of R (continuousCochain R L M n) :=
  Iso.refl _

/-- Under `continuousCochainComplexXIso`, the differential of `continuousCochainComplex` from
degree `n` to degree `n + 1` is `continuousD`. -/
@[reassoc, elementwise]
theorem continuousCochainComplex_d_succ (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ) :
    (continuousCochainComplex R L M hL hM).d n (n + 1) ≫
        (continuousCochainComplexXIso R L M hL hM (n + 1)).hom =
      (continuousCochainComplexXIso R L M hL hM n).hom ≫
        ModuleCat.ofHom (continuousD R L M hL hM n) := by
  simp [continuousCochainComplex, continuousCochainComplexXIso]

/-- The subcomplex inclusion of `continuousCochainComplex` into the algebraic Chevalley–Eilenberg
complex `cochainComplex R L M`. -/
noncomputable def continuousCochainComplexι (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) :
    continuousCochainComplex R L M hL hM ⟶ cochainComplex R L M :=
  CochainComplex.ofHom
    (fun n ↦ (continuousCochainComplexXIso R L M hL hM n).hom ≫
      ModuleCat.ofHom (continuousCochain R L M n).subtype)
    fun n ↦ by
      rw [cochainComplex_d_succ]
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
      have hx := congrArg Subtype.val
        (continuousCochainComplex_d_succ_apply R L M hL hM n x).symm
      rw [coe_continuousD] at hx
      exact hx

@[simp, reassoc]
theorem continuousCochainComplexι_f (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ) :
    (continuousCochainComplexι R L M hL hM).f n =
      (continuousCochainComplexXIso R L M hL hM n).hom ≫
        ModuleCat.ofHom (continuousCochain R L M n).subtype := (rfl)

variable {R L M} {L' L'' : Type v} {M' M'' : Type w}
  [LieRing L'] [LieAlgebra R L'] [TopologicalSpace L']
  [LieRing L''] [LieAlgebra R L''] [TopologicalSpace L'']
  [AddCommGroup M'] [Module R M'] [LieRingModule L' M'] [LieModule R L' M']
  [AddCommGroup M''] [Module R M''] [LieRingModule L'' M''] [LieModule R L'' M'']

/-- The chain map on continuous Chevalley–Eilenberg complexes induced by a continuous Lie algebra
morphism `φ : L' →ₗ⁅R⁆ L` and an intertwining linear map `e : M →ₗ[R] M'`. -/
noncomputable def continuousCochainComplexMap (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (hφ : Continuous φ)
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M))
    (hL' : Continuous fun p : L' × L' ↦ ⁅p.1, p.2⁆)
    (hM' : ∀ m' : M', IsLocallyConstant (⁅·, m'⁆ : L' → M')) :
    continuousCochainComplex R L M hL hM ⟶ continuousCochainComplex R L' M' hL' hM' :=
  CochainComplex.ofHom
    (fun n ↦ (continuousCochainComplexXIso R L M hL hM n).hom ≫
      ModuleCat.ofHom (continuousCochainMap e φ hφ n) ≫
        (continuousCochainComplexXIso R L' M' hL' hM' n).inv)
    fun n ↦ by
      have hcomm : ModuleCat.ofHom (continuousCochainMap e φ hφ n) ≫
          ModuleCat.ofHom (continuousD R L' M' hL' hM' n) =
        ModuleCat.ofHom (continuousD R L M hL hM n) ≫
          ModuleCat.ofHom (continuousCochainMap e φ hφ (n + 1)) :=
        ModuleCat.hom_ext
          (continuousCochainMap_comp_continuousD e φ he hφ hL hM hL' hM' n).symm
      rw [(Iso.eq_comp_inv _).mpr (continuousCochainComplex_d_succ R L M hL hM n),
        (Iso.eq_comp_inv _).mpr (continuousCochainComplex_d_succ R L' M' hL' hM' n)]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hcomm]

@[reassoc, elementwise]
theorem continuousCochainComplexMap_f (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (hφ : Continuous φ)
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M))
    (hL' : Continuous fun p : L' × L' ↦ ⁅p.1, p.2⁆)
    (hM' : ∀ m' : M', IsLocallyConstant (⁅·, m'⁆ : L' → M')) (n : ℕ) :
    (continuousCochainComplexMap e φ he hφ hL hM hL' hM').f n ≫
        (continuousCochainComplexXIso R L' M' hL' hM' n).hom =
      (continuousCochainComplexXIso R L M hL hM n).hom ≫
        ModuleCat.ofHom (continuousCochainMap e φ hφ n) := by
  simp [continuousCochainComplexMap]

@[simp]
theorem continuousCochainComplexMap_id
    {he : ∀ (x : L) (m : M),
      (LinearMap.id : M →ₗ[R] M) ⁅(LieHom.id : L →ₗ⁅R⁆ L) x, m⁆ = ⁅x, LinearMap.id m⁆}
    {hφ : Continuous (LieHom.id : L →ₗ⁅R⁆ L)}
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) :
    continuousCochainComplexMap (LinearMap.id : M →ₗ[R] M) (LieHom.id : L →ₗ⁅R⁆ L) he hφ
        hL hM hL hM = 𝟙 (continuousCochainComplex R L M hL hM) := by
  ext n : 2; simp [continuousCochainComplexMap]

theorem continuousCochainComplexMap_comp (e : M →ₗ[R] M') (e' : M' →ₗ[R] M'')
    (φ : L' →ₗ⁅R⁆ L) (ψ : L'' →ₗ⁅R⁆ L')
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆)
    (he' : ∀ (x : L'') (m' : M'), e' ⁅ψ x, m'⁆ = ⁅x, e' m'⁆)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M))
    (hL' : Continuous fun p : L' × L' ↦ ⁅p.1, p.2⁆)
    (hM' : ∀ m' : M', IsLocallyConstant (⁅·, m'⁆ : L' → M'))
    (hL'' : Continuous fun p : L'' × L'' ↦ ⁅p.1, p.2⁆)
    (hM'' : ∀ m'' : M'', IsLocallyConstant (⁅·, m''⁆ : L'' → M'')) :
    continuousCochainComplexMap e φ he hφ hL hM hL' hM' ≫
        continuousCochainComplexMap e' ψ he' hψ hL' hM' hL'' hM'' =
      continuousCochainComplexMap (e'.comp e) (φ.comp ψ)
        (fun x m ↦ by simp [he, he']) (hφ.comp hψ) hL hM hL'' hM'' := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  rw [HomologicalComplex.comp_f,
    (Iso.eq_comp_inv _).mpr (continuousCochainComplexMap_f e φ he hφ hL hM hL' hM' n),
    (Iso.eq_comp_inv _).mpr (continuousCochainComplexMap_f e' ψ he' hψ hL' hM' hL'' hM'' n),
    (Iso.eq_comp_inv _).mpr (continuousCochainComplexMap_f (e'.comp e) (φ.comp ψ)
      (fun x m ↦ by simp [he, he']) (hφ.comp hψ) hL hM hL'' hM'' n)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (ModuleCat.ofHom (continuousCochainMap e φ hφ n)),
    ← ModuleCat.ofHom_comp, continuousCochainMap_comp]

/-- The subcomplex inclusion `continuousCochainComplexι` commutes with functoriality. -/
@[reassoc]
theorem continuousCochainComplexMap_comp_ι (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (hφ : Continuous φ)
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M))
    (hL' : Continuous fun p : L' × L' ↦ ⁅p.1, p.2⁆)
    (hM' : ∀ m' : M', IsLocallyConstant (⁅·, m'⁆ : L' → M')) :
    continuousCochainComplexMap e φ he hφ hL hM hL' hM' ≫
        continuousCochainComplexι R L' M' hL' hM' =
      continuousCochainComplexι R L M hL hM ≫ cochainComplexMap e φ he := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, continuousCochainComplexι_f,
    continuousCochainComplexι_f, cochainComplexMap_f]
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  have hx := congrArg Subtype.val
    (continuousCochainComplexMap_f_apply e φ he hφ hL hM hL' hM' n x)
  rw [coe_continuousCochainMap] at hx; exact hx

variable (R L M)

/-- The homology class in `(continuousCochainComplex R L M hL hM).homology n` attached to a
continuous `n`-cocycle. -/
noncomputable def continuousCohomologyClass (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ) :
    continuousCocycle R L M n →ₗ[R] (continuousCochainComplex R L M hL hM).homology n :=
  (continuousCochainComplex R L M hL hM).moduleCatHomologyClass (CochainComplex.next ℕ n)
    ((continuousCochainComplexXIso R L M hL hM n).inv.hom ∘ₗ
      Submodule.inclusion (continuousCocycle_le_continuousCochain R L M n))
    fun z ↦ ((continuousCochainComplex R L M hL hM).moduleCat_d_inv_eq_zero_iff
      (continuousD R L M hL hM) (continuousCochainComplex_d_succ R L M hL hM)
      (Submodule.inclusion (continuousCocycle_le_continuousCochain R L M n) z)).mpr
        (Subtype.ext (mem_continuousCocycle_iff.mp z.property).2)

/-- The homology class of a continuous cocycle `z` is its `homologyπ` image via
`moduleCatCyclesMk`. -/
theorem continuousCohomologyClass_apply (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ)
    (z : continuousCocycle R L M n) :
    continuousCohomologyClass R L M hL hM n z =
      (continuousCochainComplex R L M hL hM).homologyπ n
        ((continuousCochainComplex R L M hL hM).moduleCatCyclesMk
          ((continuousCochainComplexXIso R L M hL hM n).inv
            (Submodule.inclusion (continuousCocycle_le_continuousCochain R L M n) z))
          (n + 1) (CochainComplex.next ℕ n)
          (((continuousCochainComplex R L M hL hM).moduleCat_d_inv_eq_zero_iff
            (continuousD R L M hL hM) (continuousCochainComplex_d_succ R L M hL hM)
            (Submodule.inclusion (continuousCocycle_le_continuousCochain R L M n) z)).mpr
              (Subtype.ext ((coe_continuousD hL hM _).trans
                (mem_continuousCocycle_iff.mp z.property).2)))) :=
  HomologicalComplex.moduleCatHomologyClass_apply _ _ _ _ _

/-- `continuousCohomologyClass` sends `z` to the `homologyπ` class of any cycle with underlying
cochain `z.1`. -/
theorem continuousCohomologyClass_eq_homologyπ (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) {n : ℕ}
    (z : continuousCocycle R L M n)
    (y : (continuousCochainComplex R L M hL hM).cycles n)
    (hy : ((continuousCochainComplexXIso R L M hL hM n).hom
      ((continuousCochainComplex R L M hL hM).iCycles n y) : L [⋀^Fin n]→ₗ[R] M) = z.val) :
    continuousCohomologyClass R L M hL hM n z =
      (continuousCochainComplex R L M hL hM).homologyπ n y := by
  rw [continuousCohomologyClass_apply]
  congr 1
  apply (continuousCochainComplex R L M hL hM).moduleCat_iCycles_injective n
  apply (ModuleCat.mono_iff_injective
    (continuousCochainComplexXIso R L M hL hM n).hom).mp inferInstance
  rw [HomologicalComplex.iCycles_moduleCatCyclesMk, Iso.inv_hom_id_apply]
  exact Subtype.ext hy.symm

/-- Pushing `continuousCohomologyClass` along `continuousCochainComplexι` gives the algebraic
Chevalley–Eilenberg homology class of `z.1`. -/
@[simp]
theorem homologyMap_continuousCochainComplexι_continuousCohomologyClass
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ)
    (z : continuousCocycle R L M n) :
    homologyMap (continuousCochainComplexι R L M hL hM) n
        (continuousCohomologyClass R L M hL hM n z) =
      (cochainComplex R L M).homologyπ n
        ((cochainComplex R L M).moduleCatCyclesMk (z.val : (cochainComplex R L M).X n)
          (n + 1) (CochainComplex.next ℕ n)
          (by rw [cochainComplex_d_succ]; exact (mem_continuousCocycle_iff.mp z.property).2)) := by
  rw [continuousCohomologyClass_apply, HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk]
  congr 1

/-- Every homology class of `continuousCochainComplex` is represented by a continuous cocycle. -/
theorem continuousCohomologyClass_surjective (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ) :
    Function.Surjective (continuousCohomologyClass R L M hL hM n) := by
  refine (continuousCochainComplex R L M hL hM).moduleCatHomologyClass_surjective _ _ _
    fun x hx ↦ ?_
  let ω := (continuousCochainComplexXIso R L M hL hM n).hom x
  have hdx : continuousD R L M hL hM n ω = 0 := by
    rw [← (continuousCochainComplex R L M hL hM).moduleCat_d_inv_eq_zero_iff
      (continuousD R L M hL hM) (continuousCochainComplex_d_succ R L M hL hM) ω]
    simpa [ω] using hx
  have hz : ω.val ∈ continuousCocycle R L M n :=
    mem_continuousCocycle_iff.mpr ⟨ω.property, by simpa using congrArg Subtype.val hdx⟩
  refine ⟨⟨ω.val, hz⟩, ?_⟩
  have hco : Submodule.inclusion (continuousCocycle_le_continuousCochain R L M n) ⟨ω.val, hz⟩ = ω :=
    Subtype.ext rfl
  simp [hco, ω]

/-- A continuous cocycle represents the zero homology class in `continuousCochainComplex` if and
only if it is a continuous coboundary. -/
@[simp]
theorem continuousCohomologyClass_eq_zero_iff (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ)
    (z : continuousCocycle R L M n) :
    continuousCohomologyClass R L M hL hM n z = 0 ↔
      z ∈ continuousCoboundary R L M n := by
  cases n with
  | zero =>
    rw [continuousCohomologyClass,
      (continuousCochainComplex R L M hL hM).moduleCatHomologyClass_eq_zero_iff _ _ _
        CochainComplex.prev_nat_zero,
      mem_continuousCoboundary_zero_iff,
      (continuousCochainComplex R L M hL hM).shape 0 0 (by simp)]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, exists_const, LinearMap.comp_apply]
    refine ⟨fun h ↦ Subtype.ext ?_, fun h ↦ by simp [h]⟩
    have h' := congrArg (continuousCochainComplexXIso R L M hL hM 0).hom h.symm
    simpa using congrArg Subtype.val h'
  | succ n =>
    rw [continuousCohomologyClass,
      (continuousCochainComplex R L M hL hM).moduleCatHomologyClass_eq_zero_iff _ _ _
        (CochainComplex.prev_nat_succ n),
      mem_continuousCoboundary_succ_iff]
    refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun ⟨ω, hω, hdω⟩ ↦ ?_⟩
    · let η := (continuousCochainComplexXIso R L M hL hM n).hom y
      refine ⟨η.val, η.property, ?_⟩
      have hy' := congrArg (continuousCochainComplexXIso R L M hL hM (n + 1)).hom hy
      rw [continuousCochainComplex_d_succ_apply, LinearMap.comp_apply,
        ModuleCat.Hom.hom, Iso.inv_hom_id_apply] at hy'
      simpa using congrArg Subtype.val hy'
    · refine ⟨(continuousCochainComplexXIso R L M hL hM n).inv ⟨ω, hω⟩, ?_⟩
      apply (ModuleCat.mono_iff_injective
        (continuousCochainComplexXIso R L M hL hM (n + 1)).hom).mp inferInstance
      rw [continuousCochainComplex_d_succ_apply]
      simp only [LinearMap.comp_apply, Iso.inv_hom_id_apply]
      exact Subtype.ext (by simpa using hdω)

/-- **Comparison with categorical homology.** When the Lie bracket of `L` is continuous and every
orbit map `⁅·, m⁆ : L → M` is locally constant, the concrete quotient
`continuousCohomology R L M n` is linearly equivalent to the degree-`n` homology of
`continuousCochainComplex R L M hL hM`. -/
noncomputable def continuousCohomologyHomologyEquiv (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) (n : ℕ) :
    continuousCohomology R L M n ≃ₗ[R] (continuousCochainComplex R L M hL hM).homology n :=
  (Submodule.quotEquivOfEq _ _
    (Submodule.ext fun z ↦ (continuousCohomologyClass_eq_zero_iff R L M hL hM n z).symm)).trans
    ((continuousCohomologyClass R L M hL hM n).quotKerEquivOfSurjective
      (continuousCohomologyClass_surjective R L M hL hM n))

variable {R L M}

@[simp]
theorem continuousCohomologyHomologyEquiv_mk (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) {n : ℕ}
    (z : continuousCocycle R L M n) :
    continuousCohomologyHomologyEquiv R L M hL hM n (continuousCohomologyMk R L M n z) =
      continuousCohomologyClass R L M hL hM n z := by
  rw [continuousCohomologyHomologyEquiv, continuousCohomologyMk_eq_mkQ]; rfl

@[simp]
theorem continuousCohomologyHomologyEquiv_symm_continuousCohomologyClass
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M)) {n : ℕ}
    (z : continuousCocycle R L M n) :
    (continuousCohomologyHomologyEquiv R L M hL hM n).symm
        (continuousCohomologyClass R L M hL hM n z) =
      continuousCohomologyMk R L M n z :=
  (continuousCohomologyHomologyEquiv R L M hL hM n).injective (by simp)

/-- `continuousCohomologyHomologyEquiv` intertwines `continuousCohomologyMap` with `homologyMap` on
`continuousCochainComplexMap`. -/
theorem homologyMap_continuousCohomologyHomologyEquiv (e : M →ₗ[R] M') (φ : L' →ₗ⁅R⁆ L)
    (he : ∀ (x : L') (m : M), e ⁅φ x, m⁆ = ⁅x, e m⁆) (hφ : Continuous φ)
    (hL : Continuous fun p : L × L ↦ ⁅p.1, p.2⁆)
    (hM : ∀ m : M, IsLocallyConstant (⁅·, m⁆ : L → M))
    (hL' : Continuous fun p : L' × L' ↦ ⁅p.1, p.2⁆)
    (hM' : ∀ m' : M', IsLocallyConstant (⁅·, m'⁆ : L' → M')) (n : ℕ)
    (q : continuousCohomology R L M n) :
    homologyMap (continuousCochainComplexMap e φ he hφ hL hM hL' hM') n
        (continuousCohomologyHomologyEquiv R L M hL hM n q) =
      continuousCohomologyHomologyEquiv R L' M' hL' hM' n
        (continuousCohomologyMap e φ he hφ n q) := by
  obtain ⟨z, rfl⟩ := continuousCohomologyMk_surjective R L M n q
  rw [continuousCohomologyMap_mk, continuousCohomologyHomologyEquiv_mk,
    continuousCohomologyHomologyEquiv_mk, continuousCohomologyClass, continuousCohomologyClass]
  refine HomologicalComplex.homologyMap_moduleCatHomologyClass (CochainComplex.next ℕ n) _ _
    (continuousCochainComplexMap e φ he hφ hL hM hL' hM') _ _
    (continuousCocycleMap e φ he hφ n) (fun w ↦ ?_) z
  apply (ModuleCat.mono_iff_injective
    (continuousCochainComplexXIso R L' M' hL' hM' n).hom).mp inferInstance
  rw [continuousCochainComplexMap_f_apply]
  simp only [LinearMap.comp_apply, ModuleCat.Hom.hom, Iso.inv_hom_id_apply]
  exact Subtype.ext (by simp)

end CategoricalComplex

end TauCeti.LieModule.Cohomology
