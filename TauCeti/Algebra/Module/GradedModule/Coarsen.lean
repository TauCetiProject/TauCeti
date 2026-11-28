/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.Algebra.Module.GradedModule.Trivial
import Mathlib.LinearAlgebra.DirectSum.Basis
import TauCeti.Algebra.DirectSum.Component
import TauCeti.Algebra.DirectSum.Internal

/-!
# Coarsening a grading along a map of index types

A family of submodules `ℳ : ι → Submodule R M` and a map `f : ι → κ` of index types give a
family indexed by `κ`: its degree-`k` piece is the sum of the pieces `ℳ i` with `f i = k`.  When
`ℳ` is an internal direct-sum decomposition, so is the coarsened family, over any semiring
(`DirectSum.IsInternal.iSup_fiber`).

The main example is the parity grading of an integer grading, obtained by reducing degrees
modulo two: its even piece is the sum of the pieces of degree `2 * k`, and its odd piece is the
sum of the pieces of degree `2 * k + 1`.  This is how an integer-graded object is regarded as a
super (parity-graded) object, for example when Koszul signs only depend on parities.

## Main definitions

* `TauCeti.coarsenGrading ℳ f`: the coarsening of a family of submodules along `f : ι → κ`.
* `TauCeti.coarsenGradingEquiv`: equivalence between the direct sum over the fibre `f i = k` and
  `coarsenGrading ℳ f k` (transferring `Module.Free` via `TauCeti.instModuleFreeCoarsenGrading`).
* `TauCeti.parityGrading ℳ`: the parity grading of an integer-indexed family of submodules.
* `TauCeti.InternalGrading.coarsen`, `TauCeti.InternalGrading.parity`, and
  `TauCeti.InternalGrading.ofParity`: coarsening, parity reduction, and the `{0, 1}`-supported
  integer lift for bundled internal gradings.

## Main results

* `TauCeti.coarsenGrading_le_iff`: the universal property of the coarsened pieces, and
  `TauCeti.coarsenGrading_induction`: the corresponding induction principle on elements.
* `TauCeti.coarsenGrading_apply_of_injective`: coarsening along an injective map keeps each piece.
* `TauCeti.decompose_coarsenGrading`: the coarsened homogeneous components are the sums of the
  original components in each fibre.
* `TauCeti.mem_coarsenGrading_iff`: an element lies in the coarsened piece of degree `k` exactly
  when its components outside the fibre over `k` vanish.
* `TauCeti.coarsenGrading_span_image_fiber`: coarsening the spans of the fibres of a degree
  function gives the spans of the fibres of the composite degree function.
* `LinearMap.IsHomogeneous.coarsenGrading` and
  `LinearMap.IsHomogeneous.coarsenGrading_zero`: homogeneity of linear maps under
  coarsened gradings, with the criterion `LinearMap.isHomogeneous_coarsenGrading_iff`, and its
  converse `LinearMap.IsHomogeneous.of_coarsenGrading` along an injective map, and
  `LinearMap.isHomogeneous_coarsenGrading_span_iff` for the coarsened spans of fibres.
* `TauCeti.smul_mem_coarsenGrading`: a scalar action shifting the degree by `r` shifts the
  coarsened degree by `f r`.
* `TauCeti.parityGrading_zero`, `TauCeti.parityGrading_one`, `TauCeti.parityGrading_one_eq_bot_iff`,
  `TauCeti.eq_bot_of_parityGrading_one_eq_bot_of_odd`, `TauCeti.parityGrading_trivialGrading_one`,
  and `TauCeti.parityGrading_one_eq_bot_iff_of_isHomogeneous_zero`: the even and odd pieces and
  even-support preservation.
* `TauCeti.mem_parityGrading_zero_of_odd_eq_bot`, `TauCeti.mem_parityGrading_one_of_even_eq_bot`,
  and `TauCeti.coe_decompose_zero_add_coe_decompose_one`: single-parity concentration and the
  two-term decomposition for `ZMod 2`-gradings.
* `TauCeti.InternalGrading.parity_ofParity`: reducing `G.ofParity` modulo two recovers `G`.
-/

public section

open DirectSum

namespace TauCeti

universe uR uM uι uκ

variable {R : Type uR} {M : Type uM} {ι : Type uι} {κ : Type uκ}
  [Semiring R] [AddCommMonoid M] [Module R M]

section Coarsen

/-- The coarsening of a family of submodules `ℳ : ι → Submodule R M` along a map `f : ι → κ` of
index types: the degree-`k` piece is the sum of the pieces `ℳ i` over the fibre `f i = k`. -/
def coarsenGrading (ℳ : ι → Submodule R M) (f : ι → κ) (k : κ) : Submodule R M :=
  ⨆ (i) (_ : f i = k), ℳ i

/-- The degree-`k` piece of the coarsened grading is the supremum of the pieces over `k`. -/
theorem coarsenGrading_apply (ℳ : ι → Submodule R M) (f : ι → κ) (k : κ) :
    coarsenGrading ℳ f k = ⨆ (i) (_ : f i = k), ℳ i := (rfl)

/-- The universal property of the coarsened pieces: the degree-`k` piece lies in a submodule
exactly when every piece in the fibre over `k` does. -/
theorem coarsenGrading_le_iff {ℳ : ι → Submodule R M} {f : ι → κ} {k : κ} {N : Submodule R M} :
    coarsenGrading ℳ f k ≤ N ↔ ∀ i, f i = k → ℳ i ≤ N :=
  iSup₂_le_iff

/-- Each piece is contained in the coarsened piece of the image degree. -/
theorem le_coarsenGrading (ℳ : ι → Submodule R M) (f : ι → κ) (i : ι) :
    ℳ i ≤ coarsenGrading ℳ f (f i) :=
  le_iSup₂_of_le i rfl le_rfl

/-- An element of degree `i` has degree `f i` in the coarsened grading. -/
theorem mem_coarsenGrading_of_mem {ℳ : ι → Submodule R M} (f : ι → κ) {i : ι} {x : M}
    (hx : x ∈ ℳ i) : x ∈ coarsenGrading ℳ f (f i) :=
  le_coarsenGrading ℳ f i hx

/-- Coarsening along an injective map of index types merges no pieces: the coarsened piece of
degree `f i` is `ℳ i`. -/
theorem coarsenGrading_apply_of_injective (ℳ : ι → Submodule R M) {f : ι → κ}
    (hf : Function.Injective f) (i : ι) : coarsenGrading ℳ f (f i) = ℳ i :=
  le_antisymm (coarsenGrading_le_iff.2 fun _ hj ↦ (congrArg ℳ (hf hj)).le) (le_coarsenGrading ℳ f i)

/-- Induction on membership in a coarsened piece: a property that holds on every piece of the
fibre over `k` and is closed under zero and addition holds on the coarsened piece of degree `k`. -/
@[elab_as_elim]
theorem coarsenGrading_induction {ℳ : ι → Submodule R M} {f : ι → κ} {k : κ}
    {motive : M → Prop} {x : M} (hx : x ∈ coarsenGrading ℳ f k)
    (mem : ∀ i, f i = k → ∀ y ∈ ℳ i, motive y) (zero : motive 0)
    (add : ∀ y z, motive y → motive z → motive (y + z)) : motive x :=
  Submodule.iSup_induction (motive := motive) _ hx
    (fun i _ hy ↦ Submodule.iSup_induction (motive := motive) _ hy (fun hi z hz ↦ mem i hi z hz)
      zero add) zero add

/-- Coarsening along the identity does nothing. -/
@[simp]
theorem coarsenGrading_id (ℳ : ι → Submodule R M) : coarsenGrading ℳ id = ℳ := by
  funext k
  exact le_antisymm (coarsenGrading_le_iff.2 fun _ h ↦ h ▸ le_rfl) (le_coarsenGrading ℳ id k)

/-- Coarsening twice is coarsening along the composite. -/
@[simp]
theorem coarsenGrading_coarsenGrading {ν : Type*} (ℳ : ι → Submodule R M) (f : ι → κ)
    (g : κ → ν) : coarsenGrading (coarsenGrading ℳ f) g = coarsenGrading ℳ (g ∘ f) := by
  funext n
  refine le_antisymm (coarsenGrading_le_iff.2 fun k hk ↦ coarsenGrading_le_iff.2 fun i hi ↦ ?_)
    (coarsenGrading_le_iff.2 fun i hi ↦ ?_)
  · exact le_coarsenGrading ℳ (g ∘ f) i |>.trans_eq (by rw [Function.comp_apply, hi, hk])
  · exact (le_coarsenGrading ℳ f i).trans
      (le_coarsenGrading (coarsenGrading ℳ f) g (f i) |>.trans_eq (by rw [← hi]; rfl))

section DecidableEq

variable [DecidableEq ι] [DecidableEq κ]

/-- The decomposition into coarsened pieces, chosen from the internality of the coarsened family
(`DirectSum.IsInternal.iSup_fiber`); any two decompositions of the same family agree. -/
noncomputable instance (ℳ : ι → Submodule R M) [Decomposition ℳ] (f : ι → κ) :
    Decomposition (coarsenGrading ℳ f) :=
  -- The internality proof is elaborated as a proof, where the body of `coarsenGrading` unfolds.
  IsInternal.chooseDecomposition _ (by exact IsInternal.iSup_fiber (Decomposition.isInternal ℳ) f)

variable (ℳ : ι → Submodule R M) [Decomposition ℳ] (f : ι → κ)

/-- The coarsened homogeneous component of degree `k` is the sum of the components whose degree
lies in the fibre over `k`. -/
theorem decompose_coarsenGrading [∀ (i) (x : ℳ i), Decidable (x ≠ 0)] (x : M) (k : κ) :
    (decompose (coarsenGrading ℳ f) x k : M) =
      ∑ i ∈ (decompose ℳ x).support with f i = k, (decompose ℳ x i : M) := by
  conv_lhs => rw [← sum_support_decompose ℳ x]
  rw [decompose_sum, DirectSum.sum_apply, Submodule.coe_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hx := mem_coarsenGrading_of_mem f (decompose ℳ x i).property
  split_ifs with hi
  · exact hi ▸ decompose_of_mem_same _ hx
  · exact decompose_of_mem_ne _ hx hi

end DecidableEq

variable [DecidableEq ι] (ℳ : ι → Submodule R M) [Decomposition ℳ] (f : ι → κ)

/-- An element lies in the coarsened piece of degree `k` exactly when its homogeneous components
of every degree outside the fibre over `k` vanish. -/
theorem mem_coarsenGrading_iff {x : M} {k : κ} :
    x ∈ coarsenGrading ℳ f k ↔ ∀ i, f i ≠ k → (decompose ℳ x i : M) = 0 := by
  classical
  refine ⟨fun hx i hi ↦ ?_, fun hx ↦ ?_⟩
  · -- The `i`-th component vanishes on every piece of the fibre over `k`.
    have hle : coarsenGrading ℳ f k ≤ LinearMap.ker (homogeneousProj ℳ i) :=
      coarsenGrading_le_iff.2 fun j hj y hy ↦
        LinearMap.mem_ker.2 (homogeneousProj_apply_of_mem_ne ℳ hy (by rintro rfl; exact hi hj))
    simpa only [LinearMap.mem_ker, homogeneousProj_apply, ← Subtype.coe_inj,
      Submodule.coe_zero] using hle hx
  · rw [← sum_support_decompose ℳ x]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    by_cases hi : f i = k
    · exact hi ▸ mem_coarsenGrading_of_mem f (decompose ℳ x i).property
    · rw [hx i hi]
      exact zero_mem _

omit [DecidableEq ι] [Decomposition ℳ] in
private def coarsenGradingToSubmodule (k : κ) :
    (⨁ i : {i : ι // f i = k}, ℳ i.val) →ₗ[R] coarsenGrading ℳ f k :=
  toModule R {i : ι // f i = k} (coarsenGrading ℳ f k) fun i ↦
    Submodule.inclusion ((le_coarsenGrading ℳ f i.val).trans_eq (congrArg
        (coarsenGrading ℳ f) i.property))

open Classical in
private noncomputable def coarsenGradingProj (k : κ) :
    M →ₗ[R] ⨁ i : {i : ι // f i = k}, ℳ i.val :=
  (toModule R ι (⨁ i : {i : ι // f i = k}, ℳ i.val) fun i ↦
    if h : f i = k then lof R {j : ι // f j = k} (fun j ↦ ℳ j.val) ⟨i, h⟩ else 0).comp
    (decomposeLinearEquiv ℳ).toLinearMap

private theorem coarsenGradingProj_apply (k : κ) (y : M) (i : {i : ι // f i = k}) :
    (coarsenGradingProj ℳ f k y i : M) = (decompose ℳ y i.val : M) := by
  classical
  induction y using Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous j y =>
    simp only [coarsenGradingProj, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [decomposeLinearEquiv_apply_coe ℳ j y, toModule_lof]
    by_cases hj : j = i.val
    · subst hj
      rw [dite_eq_left i.property, decompose_of_mem_same ℳ y.property]
      simp
    · by_cases hfk : f j = k
      · have hne : i ≠ ⟨j, hfk⟩ := fun heq ↦ hj (congrArg Subtype.val heq.symm)
        rw [dite_eq_left hfk, lof_eq_of, of_eq_of_ne _ _ _ hne, Submodule.coe_zero,
          decompose_of_mem_ne ℳ y.property hj]
      · rw [dite_eq_right hfk, LinearMap.zero_apply, DirectSum.zero_apply, Submodule.coe_zero,
          decompose_of_mem_ne ℳ y.property hj]
  | add y z hy hz => simp [hy, hz]

/-- Each coarsened piece is the direct sum of the original pieces in its fibre. -/
noncomputable def coarsenGradingEquiv (k : κ) :
    (⨁ i : {i : ι // f i = k}, ℳ i.val) ≃ₗ[R] coarsenGrading ℳ f k :=
  LinearEquiv.ofLinearMap
    (coarsenGradingToSubmodule ℳ f k)
    ((coarsenGradingProj ℳ f k).comp (coarsenGrading ℳ f k).subtype)
    (by
      classical
      have hleft : ∀ x ∈ coarsenGrading ℳ f k,
          (coarsenGradingToSubmodule ℳ f k (coarsenGradingProj ℳ f k x) : M) = x := fun x hx ↦
        coarsenGrading_induction hx
          (fun i hi y hy ↦ by
            simp only [coarsenGradingProj, coarsenGradingToSubmodule, LinearMap.comp_apply,
              LinearEquiv.coe_coe]
            rw [decomposeLinearEquiv_apply_coe ℳ i ⟨y, hy⟩, toModule_lof, dite_eq_left hi,
              toModule_lof]
            simp)
          (by simp)
          (fun y z hy hz ↦ by simp [hy, hz])
      exact LinearMap.ext fun ⟨x, hx⟩ ↦ Subtype.ext (hleft x hx))
    (by
      classical
      refine DirectSum.linearMap_ext R fun i ↦ LinearMap.ext fun x ↦ ?_
      simp only [coarsenGradingProj, coarsenGradingToSubmodule, LinearMap.comp_apply,
        LinearMap.id_apply, Submodule.coe_subtype, LinearEquiv.coe_coe, toModule_lof,
        Submodule.coe_inclusion]
      rw [decomposeLinearEquiv_apply_coe ℳ i.val x, toModule_lof, dite_eq_left i.property])

/-- On a single fibre summand, `coarsenGradingEquiv` is the submodule inclusion into `M`. -/
@[simp]
theorem coe_coarsenGradingEquiv_lof (k : κ) (i : {i : ι // f i = k}) (x : ℳ i.val) :
    (coarsenGradingEquiv ℳ f k (lof R {j : ι // f j = k} (fun j ↦ ℳ j.val) i x) : M) = x := by
  simp [coarsenGradingEquiv, coarsenGradingToSubmodule]

/-- On a single fibre summand written with `DirectSum.of`, `coarsenGradingEquiv` is the submodule
inclusion into `M`. -/
@[simp]
theorem coe_coarsenGradingEquiv_of (k : κ) (i : {i : ι // f i = k}) (x : ℳ i.val) :
    (coarsenGradingEquiv ℳ f k (of (fun j : {j : ι // f j = k} ↦ ℳ j.val) i x) : M) = x := by
  rw [← lof_eq_of R, coe_coarsenGradingEquiv_lof]

/-- The inverse of `coarsenGradingEquiv` extracts the `i`-th homogeneous component for each `i` in
the fibre over `k`. -/
@[simp]
theorem coarsenGradingEquiv_symm_apply (k : κ) (x : coarsenGrading ℳ f k)
    (i : {i : ι // f i = k}) :
    (coarsenGradingEquiv ℳ f k).symm x i = decompose ℳ (x : M) i.val := by
  refine Subtype.ext ?_
  simpa only [coarsenGradingEquiv, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    LinearMap.comp_apply, Submodule.coe_subtype] using coarsenGradingProj_apply ℳ f k x.val i

/-- A coarsened piece whose fibre pieces are all free `R`-modules is itself a free `R`-module. -/
instance instModuleFreeCoarsenGrading (k : κ) [∀ i : {i : ι // f i = k}, Module.Free R (ℳ i.val)] :
    Module.Free R (coarsenGrading ℳ f k) :=
  Module.Free.of_equiv (coarsenGradingEquiv ℳ f k)

omit [DecidableEq ι] [Decomposition ℳ] in
/-- Coarsening the spans of the fibres of a degree function `deg` on a family of vectors `v` along
`f` gives the spans of the fibres of `f ∘ deg`. This applies to the grading of a module with a
basis by degrees of the basis vectors (`Module.Basis.isInternal_span_image_fiber`). -/
theorem coarsenGrading_span_image_fiber {ι' : Type*} (v : ι' → M) (deg : ι' → ι) :
    coarsenGrading (fun i ↦ Submodule.span R (v '' {j | deg j = i})) f =
      fun k ↦ Submodule.span R (v '' {j | f (deg j) = k}) := by
  funext k
  refine le_antisymm (coarsenGrading_le_iff.2 fun i hi ↦ Submodule.span_mono ?_)
    (Submodule.span_le.2 ?_)
  · rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, (congrArg f hj).trans hi, rfl⟩
  · rintro _ ⟨j, hj, rfl⟩
    exact hj ▸ mem_coarsenGrading_of_mem f (Submodule.subset_span ⟨j, rfl, rfl⟩)

end Coarsen

section Homogeneous

variable {S N : Type*} [Semiring S] [Module S M] [AddCommMonoid N] [Module R N] [Module S N]
  [AddMonoid ι] [AddMonoid κ]

omit [AddMonoid ι] in
/-- A linear map is homogeneous of degree `d` for two coarsened gradings exactly when it maps each
piece `ℳ i` into the coarsened piece of degree `f i + d`. The map may be linear over another
semiring `S` than the pieces. -/
theorem _root_.LinearMap.isHomogeneous_coarsenGrading_iff {g : M →ₗ[S] N}
    {ℳ : ι → Submodule R M} {𝒩 : ι → Submodule R N} {f : ι → κ} {d : κ} :
    LinearMap.IsHomogeneous g (TauCeti.coarsenGrading ℳ f) (TauCeti.coarsenGrading 𝒩 f) d ↔
      ∀ i, ∀ x ∈ ℳ i, g x ∈ TauCeti.coarsenGrading 𝒩 f (f i + d) :=
  ⟨fun hg _ _ hx ↦ hg.map_mem (mem_coarsenGrading_of_mem f hx), fun h ↦
    LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ coarsenGrading_induction hx
      (fun i hi y hy ↦ hi ▸ h i y hy) (by simp) fun _ _ hy hz ↦ by
        simpa only [map_add] using add_mem hy hz⟩

/-- A linear map that is homogeneous of degree `q` for two gradings is homogeneous of degree
`f q` for the gradings coarsened along an additive homomorphism `f`. -/
theorem _root_.LinearMap.IsHomogeneous.coarsenGrading {F : Type*} [FunLike F ι κ]
    [AddHomClass F ι κ] {g : M →ₗ[S] N} {ℳ : ι → Submodule R M}
    {𝒩 : ι → Submodule R N} {q : ι} (hg : LinearMap.IsHomogeneous g ℳ 𝒩 q) (f : F) :
    LinearMap.IsHomogeneous g (TauCeti.coarsenGrading ℳ f) (TauCeti.coarsenGrading 𝒩 f) (f q) :=
  LinearMap.isHomogeneous_coarsenGrading_iff.2 fun _ _ hx ↦ by
    simpa only [map_add] using mem_coarsenGrading_of_mem f (hg.map_mem hx)

/-- A degree-zero homogeneous linear map remains homogeneous of degree zero after coarsening along
any map `f : ι → κ` of index types. -/
theorem _root_.LinearMap.IsHomogeneous.coarsenGrading_zero {g : M →ₗ[S] N}
    {ℳ : ι → Submodule R M} {𝒩 : ι → Submodule R N} (hg : LinearMap.IsHomogeneous g ℳ 𝒩 0)
    (f : ι → κ) :
    LinearMap.IsHomogeneous g (TauCeti.coarsenGrading ℳ f) (TauCeti.coarsenGrading 𝒩 f) 0 :=
  LinearMap.isHomogeneous_coarsenGrading_iff.2 fun _ _ hx ↦ by
    simpa only [add_zero] using
      mem_coarsenGrading_of_mem f (by simpa only [add_zero] using hg.map_mem hx)

/-- A linear map that is homogeneous of degree `f q` for gradings coarsened along an injective
additive homomorphism `f` is homogeneous of degree `q` for the original gradings, since coarsening
along `f` merges no pieces. -/
theorem _root_.LinearMap.IsHomogeneous.of_coarsenGrading {F : Type*} [FunLike F ι κ]
    [AddHomClass F ι κ] {g : M →ₗ[S] N} {ℳ : ι → Submodule R M} {𝒩 : ι → Submodule R N} {q : ι}
    {f : F} (hf : Function.Injective f)
    (hg : LinearMap.IsHomogeneous g (TauCeti.coarsenGrading ℳ f) (TauCeti.coarsenGrading 𝒩 f)
      (f q)) :
    LinearMap.IsHomogeneous g ℳ 𝒩 q :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    simpa only [← map_add, coarsenGrading_apply_of_injective 𝒩 hf] using
      hg.map_mem (mem_coarsenGrading_of_mem f hx)

omit [AddMonoid ι] in
/-- A linear map out of the coarsening along `f` of the spans of the fibres of a degree function
`deg` on vectors `v` is homogeneous of degree `d` exactly when it maps each `v j` into the piece
of degree `f (deg j) + d`. -/
theorem _root_.LinearMap.isHomogeneous_coarsenGrading_span_iff [LinearMap.CompatibleSMul M N R S]
    {ι' : Type*} {g : M →ₗ[S] N} {v : ι' → M} {deg : ι' → ι} {𝒩 : κ → Submodule R N}
    {f : ι → κ} {d : κ} :
    LinearMap.IsHomogeneous g
        (TauCeti.coarsenGrading (fun i ↦ Submodule.span R (v '' {j | deg j = i})) f) 𝒩 d ↔
      ∀ j, g (v j) ∈ 𝒩 (f (deg j) + d) := by
  rw [coarsenGrading_span_image_fiber, LinearMap.isHomogeneous_span_iff]
  exact ⟨fun h j ↦ h _ _ ⟨j, rfl, rfl⟩, by rintro h _ _ ⟨j, rfl, rfl⟩; exact h j⟩

/-- If the action of `a` maps each piece `ℳ i` into `ℳ (i + r)`, it maps the piece of degree `k`
of the coarsening along an additive homomorphism `f` into the piece of degree `k + f r`. -/
theorem smul_mem_coarsenGrading {A F : Type*} [Monoid A] [DistribMulAction A M]
    [SMulCommClass A R M] [FunLike F ι κ] [AddHomClass F ι κ] {ℳ : ι → Submodule R M} {a : A}
    {r : ι} (ha : ∀ i, ∀ x ∈ ℳ i, a • x ∈ ℳ (i + r)) (f : F) {k : κ} {x : M}
    (hx : x ∈ TauCeti.coarsenGrading ℳ f k) : a • x ∈ TauCeti.coarsenGrading ℳ f (k + f r) :=
  ((LinearMap.isHomogeneous_def (f := DistribSMul.toLinearMap R M a)).2 ha).coarsenGrading f
    |>.map_mem hx

end Homogeneous

section Parity

/-- The parity grading of an integer-indexed family of submodules, indexed by `ZMod 2`: its
even piece is the sum of the pieces of even degree and its odd piece is the sum of the pieces
of odd degree (`parityGrading_zero`, `parityGrading_one`).  It is reducible to the coarsening
along reduction modulo two, so the `coarsenGrading` API and instances apply to it directly. -/
abbrev parityGrading (ℳ : ℤ → Submodule R M) : ZMod 2 → Submodule R M :=
  coarsenGrading ℳ (Int.castAddHom (ZMod 2))

/-- Coarsening an integer-indexed family along `Int.cast : ℤ → ZMod 2` is its parity grading. -/
@[simp]
theorem coarsenGrading_intCast (ℳ : ℤ → Submodule R M) :
    coarsenGrading ℳ (fun n : ℤ ↦ (n : ZMod 2)) = parityGrading ℳ := by
  rw [parityGrading, Int.coe_castAddHom]

/-- An element of degree `n` has parity `n` modulo two. -/
theorem mem_parityGrading_of_mem {ℳ : ℤ → Submodule R M} {n : ℤ} {x : M} (hx : x ∈ ℳ n) :
    x ∈ parityGrading ℳ n :=
  mem_coarsenGrading_of_mem (Int.castAddHom (ZMod 2)) hx

/-- A degree-zero homogeneous linear map between integer-graded modules is also homogeneous of
degree zero for their parity gradings. -/
theorem _root_.LinearMap.IsHomogeneous.parityGrading_zero {N : Type*} [AddCommMonoid N] [Module R N]
    {g : M →ₗ[R] N} {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
    (hg : LinearMap.IsHomogeneous g ℳ 𝒩 0) :
    LinearMap.IsHomogeneous g (parityGrading ℳ) (parityGrading 𝒩) 0 :=
  hg.coarsenGrading_zero (Int.castAddHom (ZMod 2))

/-- The universal property of the parity pieces. -/
theorem parityGrading_le_iff {ℳ : ℤ → Submodule R M} {i : ZMod 2} {N : Submodule R M} :
    parityGrading ℳ i ≤ N ↔ ∀ n : ℤ, (n : ZMod 2) = i → ℳ n ≤ N :=
  coarsenGrading_le_iff

/-- The even piece of the parity grading is the sum of the pieces of degree `2 * k`. -/
theorem parityGrading_zero (ℳ : ℤ → Submodule R M) :
    parityGrading ℳ 0 = ⨆ k : ℤ, ℳ (2 * k) := by
  refine le_antisymm (parityGrading_le_iff.2 fun n hn ↦ ?_) (iSup_le fun k x hx ↦ ?_)
  · obtain ⟨k, rfl⟩ : 2 ∣ n := (ZMod.intCast_zmod_eq_zero_iff_dvd n 2).1 hn
    exact le_iSup (fun k ↦ ℳ (2 * k)) k
  · simpa [CharP.ofNat_eq_zero] using mem_parityGrading_of_mem hx

/-- The odd piece of the parity grading is the sum of the pieces of degree `2 * k + 1`. -/
theorem parityGrading_one (ℳ : ℤ → Submodule R M) :
    parityGrading ℳ 1 = ⨆ k : ℤ, ℳ (2 * k + 1) := by
  refine le_antisymm (parityGrading_le_iff.2 fun n hn ↦ ?_) (iSup_le fun k x hx ↦ ?_)
  · obtain ⟨k, hk⟩ : 2 ∣ n - 1 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 (by push_cast; rw [hn, sub_self])
    rw [eq_add_of_sub_eq hk]
    exact le_iSup (fun k ↦ ℳ (2 * k + 1)) k
  · simpa [CharP.ofNat_eq_zero] using mem_parityGrading_of_mem hx

/-- When all odd-degree pieces vanish, every element has even parity. -/
theorem mem_parityGrading_zero_of_odd_eq_bot {ℳ : ℤ → Submodule R M} [Decomposition ℳ]
    (hℳ : ∀ p, Odd p → ℳ p = ⊥) (x : M) : x ∈ parityGrading ℳ 0 :=
  TauCeti.DirectSum.mem_of_forall_ne_eq_bot (ℳ := parityGrading ℳ)
    (fun j hj ↦ by
      have hj1 : j = 1 := by revert j hj; decide
      rw [hj1, parityGrading_one]
      exact iSup_eq_bot.2 fun k ↦ hℳ (2 * k + 1) ⟨k, rfl⟩)
    x

/-- When all even-degree pieces vanish, every element has odd parity. -/
theorem mem_parityGrading_one_of_even_eq_bot {ℳ : ℤ → Submodule R M} [Decomposition ℳ]
    (hℳ : ∀ p, Even p → ℳ p = ⊥) (x : M) : x ∈ parityGrading ℳ 1 :=
  TauCeti.DirectSum.mem_of_forall_ne_eq_bot (ℳ := parityGrading ℳ)
    (fun j hj ↦ by
      have hj0 : j = 0 := by revert j hj; decide
      rw [hj0, parityGrading_zero]
      exact iSup_eq_bot.2 fun k ↦ hℳ (2 * k) ⟨k, two_mul k⟩)
    x

omit [Semiring R] [Module R M] in
/-- Every element of a `ZMod 2`-graded additive monoid is the sum of its degree-`0` and degree-`1`
components. -/
theorem coe_decompose_zero_add_coe_decompose_one {σ : Type*} [SetLike σ M] [AddSubmonoidClass σ M]
    (ℳ : ZMod 2 → σ) [Decomposition ℳ] (x : M) :
    (decompose ℳ x 0 : M) + (decompose ℳ x 1 : M) = x := by
  have h := Decomposition.left_inv (ℳ := ℳ) x
  rw [← sum_univ_of (Decomposition.decompose' x), map_sum] at h
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [huniv, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)] at h
  simpa using h

/-- An integer-indexed family of submodules is supported in even degrees (`parityGrading ℳ 1 = ⊥`)
if and only if every odd-degree piece `ℳ (2 * k + 1)` vanishes. -/
theorem parityGrading_one_eq_bot_iff {ℳ : ℤ → Submodule R M} :
    parityGrading ℳ 1 = ⊥ ↔ ∀ k : ℤ, ℳ (2 * k + 1) = ⊥ := by
  rw [parityGrading_one, iSup_eq_bot]

/-- In an even-supported family (`parityGrading ℳ 1 = ⊥`), every piece of odd degree vanishes. -/
theorem eq_bot_of_parityGrading_one_eq_bot_of_odd {ℳ : ℤ → Submodule R M}
    (h : parityGrading ℳ 1 = ⊥) {n : ℤ} (hn : Odd n) : ℳ n = ⊥ := by
  obtain ⟨k, rfl⟩ := hn
  exact parityGrading_one_eq_bot_iff.mp h k

variable (R M) in
/-- The trivial integer grading is concentrated in degree `0`, hence supported in even degrees. -/
@[simp] theorem parityGrading_trivialGrading_one : parityGrading (trivialGrading R M) 1 = ⊥ :=
  parityGrading_one_eq_bot_iff.mpr fun _ => trivialGrading_eq_bot R M (by omega)

/-- A degree-zero homogeneous linear equivalence transfers vanishing of the odd parity piece from
target to source. -/
theorem parityGrading_one_eq_bot_of_isHomogeneous_zero {S N : Type*} [Semiring S]
    [Module S M] [AddCommMonoid N] [Module R N] [Module S N]
    {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {e : M ≃ₗ[S] N}
    (he : LinearMap.IsHomogeneous e.toLinearMap ℳ 𝒩 0) (hN : parityGrading 𝒩 1 = ⊥) :
    parityGrading ℳ 1 = ⊥ := by
  rw [parityGrading_one_eq_bot_iff] at hN ⊢
  refine fun k => (Submodule.eq_bot_iff _).mpr fun x hx => e.injective ?_
  have hex : e x ∈ 𝒩 (2 * k + 1) := by simpa using he.map_mem hx
  simpa [hN k] using hex

/-- Even support (`parityGrading · 1 = ⊥`) is invariant under degree-zero homogeneous linear
equivalences of internally graded modules. -/
theorem parityGrading_one_eq_bot_iff_of_isHomogeneous_zero {S N : Type*} [Semiring S]
    [Module S M] [AddCommMonoid N] [Module R N] [Module S N]
    {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
    [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] {e : M ≃ₗ[S] N}
    (he : LinearMap.IsHomogeneous e.toLinearMap ℳ 𝒩 0) :
    parityGrading ℳ 1 = ⊥ ↔ parityGrading 𝒩 1 = ⊥ := by
  have he' : LinearMap.IsHomogeneous e.toLinearMap
      (InternalGrading.ofDecomposition ℳ).piece (InternalGrading.ofDecomposition 𝒩).piece 0 := by
    simpa using he
  have hsymm : LinearMap.IsHomogeneous e.symm.toLinearMap 𝒩 ℳ 0 := by
    simpa using he'.linearEquiv_symm
  exact ⟨parityGrading_one_eq_bot_of_isHomogeneous_zero hsymm,
    parityGrading_one_eq_bot_of_isHomogeneous_zero he⟩

end Parity

namespace InternalGrading

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- The coarsening of an internal grading along a map `f : ι → κ` of index types: the degree-`k`
piece is the sum of the pieces whose degree lies in the fibre over `k`. -/
noncomputable def coarsen (G : InternalGrading R M ι) (f : ι → κ) :
    InternalGrading R M κ where
  piece := coarsenGrading G.piece f
  isInternal := G.isInternal.iSup_fiber f

/-- The homogeneous pieces of `G.coarsen f` are given by `coarsenGrading G.piece f`. -/
@[simp]
theorem coarsen_piece (G : InternalGrading R M ι) (f : ι → κ) :
    (G.coarsen f).piece = coarsenGrading G.piece f := (rfl)

/-- An element of degree `i` in `G` has degree `f i` in `G.coarsen f`. -/
theorem mem_coarsen_of_mem (G : InternalGrading R M ι) (f : ι → κ) {i : ι} {x : M}
    (hx : x ∈ G.piece i) : x ∈ (G.coarsen f).piece (f i) :=
  mem_coarsenGrading_of_mem f hx

/-- The parity grading of an internal integer grading: the internal `ZMod 2`-grading whose even
piece is the sum of the pieces of degree `2 * k` and whose odd piece is the sum of the pieces of
degree `2 * k + 1`. It is reducible to `G.coarsen (Int.castAddHom (ZMod 2))`, matching
`TauCeti.parityGrading`, so the `InternalGrading.coarsen` API and dependent types indexed by
`G.parity` specialize `G.coarsen` directly. -/
noncomputable abbrev parity (G : InternalGrading R M ℤ) : InternalGrading R M (ZMod 2) :=
  G.coarsen (Int.castAddHom (ZMod 2))

/-- Coarsening an internal integer grading along `Int.cast : ℤ → ZMod 2` is its parity grading. -/
@[simp]
theorem coarsen_intCast (G : InternalGrading R M ℤ) :
    G.coarsen (fun n : ℤ ↦ (n : ZMod 2)) = G.parity := by
  rw [parity, Int.coe_castAddHom]

/-- The homogeneous pieces of `G.parity` are given by `parityGrading G.piece`. -/
theorem parity_piece (G : InternalGrading R M ℤ) : G.parity.piece = parityGrading G.piece := (rfl)

/-- The `{0, 1}`-supported integer grading associated to an internal parity grading, placing the
even piece in degree `0`, the odd piece in degree `1`, and `⊥` in every other degree. Its parity
reduction is the original grading (`parity_ofParity`). -/
noncomputable def ofParity (G : InternalGrading R M (ZMod 2)) : InternalGrading R M ℤ :=
  G.coarsen fun i ↦ (i.val : ℤ)

/-- The degree-`0` piece of `G.ofParity` is the even piece of `G`. -/
@[simp]
theorem ofParity_piece_zero (G : InternalGrading R M (ZMod 2)) :
    G.ofParity.piece 0 = G.piece 0 := by
  refine le_antisymm (coarsenGrading_le_iff.2 fun i hi ↦ ?_)
    (le_coarsenGrading G.piece (fun i : ZMod 2 ↦ (i.val : ℤ)) 0)
  rcases (by decide : ∀ j : ZMod 2, j = 0 ∨ j = 1) i with rfl | rfl
  · exact le_rfl
  · simp [ZMod.val_one] at hi

/-- The degree-`1` piece of `G.ofParity` is the odd piece of `G`. -/
@[simp]
theorem ofParity_piece_one (G : InternalGrading R M (ZMod 2)) :
    G.ofParity.piece 1 = G.piece 1 := by
  refine le_antisymm (coarsenGrading_le_iff.2 fun i hi ↦ ?_)
    (le_coarsenGrading G.piece (fun i : ZMod 2 ↦ (i.val : ℤ)) 1)
  rcases (by decide : ∀ j : ZMod 2, j = 0 ∨ j = 1) i with rfl | rfl
  · simp at hi
  · exact le_rfl

/-- Outside degrees `0` and `1`, the pieces of `G.ofParity` vanish. -/
theorem ofParity_piece_eq_bot {G : InternalGrading R M (ZMod 2)} {n : ℤ}
    (hn₀ : n ≠ 0) (hn₁ : n ≠ 1) : G.ofParity.piece n = ⊥ := by
  rw [eq_bot_iff]
  refine coarsenGrading_le_iff.2 fun i hi ↦ False.elim ?_
  rcases (by decide : ∀ j : ZMod 2, j = 0 ∨ j = 1) i with rfl | rfl
  · exact hn₀ (by simpa using hi.symm)
  · exact hn₁ (by simpa [ZMod.val_one] using hi.symm)

/-- Every degree-`n` piece of `G.ofParity` lies in the parity-`n` piece of `G`. -/
theorem ofParity_piece_le (G : InternalGrading R M (ZMod 2)) (n : ℤ) :
    G.ofParity.piece n ≤ G.piece n :=
  coarsenGrading_le_iff.2 fun i hi ↦ by
    subst hi
    simp

/-- Reducing `G.ofParity` modulo two recovers `G`. -/
@[simp]
theorem parity_ofParity (G : InternalGrading R M (ZMod 2)) : G.ofParity.parity = G := by
  have h : (Int.castAddHom (ZMod 2) ∘ fun j : ZMod 2 ↦ (j.val : ℤ)) = id :=
    funext fun j ↦ by simp
  ext i
  rw [parity_piece, ofParity, coarsen_piece, parityGrading, coarsenGrading_coarsenGrading, h,
    coarsenGrading_id]

end InternalGrading

section HomogeneousInternalGrading

variable {N : Type*} [AddCommMonoid N] [Module R N]

/-- A linear map that is homogeneous of degree `q` between internally graded modules is homogeneous
of degree `f q` between their coarsenings along an additive homomorphism `f`. -/
theorem _root_.LinearMap.IsHomogeneous.coarsen {F : Type*} [DecidableEq ι] [DecidableEq κ]
    [AddMonoid ι] [AddMonoid κ] [FunLike F ι κ] [AddHomClass F ι κ] {g : M →ₗ[R] N}
    {G : InternalGrading R M ι} {H : InternalGrading R N ι} {q : ι}
    (hg : LinearMap.IsHomogeneous g G.piece H.piece q) (f : F) :
    LinearMap.IsHomogeneous g (G.coarsen f).piece (H.coarsen f).piece (f q) := by
  simpa only [InternalGrading.coarsen_piece] using hg.coarsenGrading f

/-- A degree-zero homogeneous linear map between internally graded modules remains homogeneous of
degree zero after coarsening along any map `f : ι → κ` of index types. -/
theorem _root_.LinearMap.IsHomogeneous.coarsen_zero [DecidableEq ι] [DecidableEq κ]
    [AddMonoid ι] [AddMonoid κ] {g : M →ₗ[R] N}
    {G : InternalGrading R M ι} {H : InternalGrading R N ι}
    (hg : LinearMap.IsHomogeneous g G.piece H.piece 0) (f : ι → κ) :
    LinearMap.IsHomogeneous g (G.coarsen f).piece (H.coarsen f).piece 0 := by
  simpa only [InternalGrading.coarsen_piece] using hg.coarsenGrading_zero f

/-- A linear map that is homogeneous of integer degree `q` between internally graded modules is
homogeneous of parity `q mod 2` between their parity gradings. -/
theorem _root_.LinearMap.IsHomogeneous.parity {g : M →ₗ[R] N}
    {G : InternalGrading R M ℤ} {H : InternalGrading R N ℤ} {q : ℤ}
    (hg : LinearMap.IsHomogeneous g G.piece H.piece q) :
    LinearMap.IsHomogeneous g G.parity.piece H.parity.piece q :=
  hg.coarsen (Int.castAddHom (ZMod 2))

end HomogeneousInternalGrading

end TauCeti
