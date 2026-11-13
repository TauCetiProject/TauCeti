/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.IntUnitsPower
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import TauCeti.Algebra.Module.GradedModule.Internal
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
* `TauCeti.InternalGrading.coarsen` and `TauCeti.InternalGrading.parity`: the same constructions
  for bundled internal gradings.

## Main results

* `TauCeti.coarsenGrading_le_iff`: the universal property of the coarsened pieces, and
  `TauCeti.coarsenGrading_induction`: the corresponding induction principle on elements.
* `TauCeti.decompose_coarsenGrading`: the coarsened homogeneous components are the sums of the
  original components in each fibre.
* `TauCeti.mem_coarsenGrading_iff`: an element lies in the coarsened piece of degree `k` exactly
  when its components outside the fibre over `k` vanish.
* `TauCeti.LinearMap.IsHomogeneous.coarsenGrading` and
  `TauCeti.LinearMap.IsHomogeneous.coarsenGrading_zero`: homogeneity of linear maps under
  coarsened gradings.
* `TauCeti.parityGrading_zero`, `TauCeti.parityGrading_one`,
  `TauCeti.mem_parityGrading_zero_of_odd_eq_bot`, `TauCeti.mem_parityGrading_one_of_even_eq_bot`,
  and `TauCeti.coe_decompose_zero_add_coe_decompose_one`: the even and odd pieces, single-parity
  concentration, and the two-term decomposition for `ZMod 2`-gradings.
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
    (⨁ i : {i : ι // f i = k}, ℳ i.1) →ₗ[R] coarsenGrading ℳ f k :=
  toModule R {i : ι // f i = k} (coarsenGrading ℳ f k) fun i ↦
    Submodule.inclusion ((le_coarsenGrading ℳ f i.1).trans_eq (congrArg (coarsenGrading ℳ f) i.2))

open Classical in
private noncomputable def coarsenGradingProj (k : κ) :
    M →ₗ[R] ⨁ i : {i : ι // f i = k}, ℳ i.1 :=
  (toModule R ι (⨁ i : {i : ι // f i = k}, ℳ i.1) fun i ↦
    if h : f i = k then lof R {j : ι // f j = k} (fun j ↦ ℳ j.1) ⟨i, h⟩ else 0).comp
    (decomposeLinearEquiv ℳ).toLinearMap

private theorem coarsenGradingProj_apply (k : κ) (y : M) (i : {i : ι // f i = k}) :
    (coarsenGradingProj ℳ f k y i : M) = (decompose ℳ y i.1 : M) := by
  classical
  induction y using Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous j y =>
    simp only [coarsenGradingProj, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [decomposeLinearEquiv_apply_coe ℳ j y, toModule_lof]
    by_cases hj : j = i.1
    · subst hj
      rw [dite_eq_left i.2, decompose_of_mem_same ℳ y.2]
      simp
    · by_cases hfk : f j = k
      · have hne : i ≠ ⟨j, hfk⟩ := fun heq ↦ hj (congrArg Subtype.val heq.symm)
        rw [dite_eq_left hfk, lof_eq_of, of_eq_of_ne _ _ _ hne, Submodule.coe_zero,
          decompose_of_mem_ne ℳ y.2 hj]
      · rw [dite_eq_right hfk, LinearMap.zero_apply, DirectSum.zero_apply, Submodule.coe_zero,
          decompose_of_mem_ne ℳ y.2 hj]
  | add y z hy hz => simp [hy, hz]

/-- Each coarsened piece is the direct sum of the original pieces in its fibre. -/
noncomputable def coarsenGradingEquiv (k : κ) :
    (⨁ i : {i : ι // f i = k}, ℳ i.1) ≃ₗ[R] coarsenGrading ℳ f k :=
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
      rw [decomposeLinearEquiv_apply_coe ℳ i.1 x, toModule_lof, dite_eq_left i.2])

/-- On a single fibre summand, `coarsenGradingEquiv` is the submodule inclusion into `M`. -/
@[simp]
theorem coe_coarsenGradingEquiv_lof (k : κ) (i : {i : ι // f i = k}) (x : ℳ i.1) :
    (coarsenGradingEquiv ℳ f k (lof R {j : ι // f j = k} (fun j ↦ ℳ j.1) i x) : M) = x := by
  simp [coarsenGradingEquiv, coarsenGradingToSubmodule]

/-- On a single fibre summand written with `DirectSum.of`, `coarsenGradingEquiv` is the submodule
inclusion into `M`. -/
@[simp]
theorem coe_coarsenGradingEquiv_of (k : κ) (i : {i : ι // f i = k}) (x : ℳ i.1) :
    (coarsenGradingEquiv ℳ f k (of (fun j : {j : ι // f j = k} ↦ ℳ j.1) i x) : M) = x := by
  rw [← lof_eq_of R, coe_coarsenGradingEquiv_lof]

/-- The inverse of `coarsenGradingEquiv` extracts the `i`-th homogeneous component for each `i` in
the fibre over `k`. -/
@[simp]
theorem coarsenGradingEquiv_symm_apply (k : κ) (x : coarsenGrading ℳ f k)
    (i : {i : ι // f i = k}) :
    (coarsenGradingEquiv ℳ f k).symm x i = decompose ℳ (x : M) i.1 := by
  refine Subtype.ext ?_
  simpa only [coarsenGradingEquiv, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    LinearMap.comp_apply, Submodule.coe_subtype] using coarsenGradingProj_apply ℳ f k x.1 i

/-- A coarsened piece whose fibre pieces are all free `R`-modules is itself a free `R`-module. -/
instance instModuleFreeCoarsenGrading (k : κ) [∀ i : {i : ι // f i = k}, Module.Free R (ℳ i.1)] :
    Module.Free R (coarsenGrading ℳ f k) :=
  Module.Free.of_equiv (coarsenGradingEquiv ℳ f k)

end Coarsen

section Homogeneous

variable {N : Type*} [AddCommMonoid N] [Module R N] [AddMonoid ι] [AddMonoid κ]

/-- A linear map that is homogeneous of degree `q` for two gradings is homogeneous of degree
`f q` for the gradings coarsened along an additive homomorphism `f`. -/
theorem LinearMap.IsHomogeneous.coarsenGrading {g : M →ₗ[R] N} {ℳ : ι → Submodule R M}
    {𝒩 : ι → Submodule R N} {q : ι} (hg : LinearMap.IsHomogeneous g ℳ 𝒩 q) (f : ι →+ κ) :
    LinearMap.IsHomogeneous g (TauCeti.coarsenGrading ℳ f) (TauCeti.coarsenGrading 𝒩 f) (f q) :=
  LinearMap.isHomogeneous_def.2 fun k x hx ↦ by
    have hle : TauCeti.coarsenGrading ℳ f k ≤
        (TauCeti.coarsenGrading 𝒩 f (k + f q)).comap g :=
      coarsenGrading_le_iff.2 fun i hi y hy ↦ by
        simpa [hi] using mem_coarsenGrading_of_mem f (hg.map_mem hy)
    exact hle hx

/-- A degree-zero homogeneous linear map remains homogeneous of degree zero after coarsening along
any map `f : ι → κ` of index types. -/
theorem LinearMap.IsHomogeneous.coarsenGrading_zero {g : M →ₗ[R] N} {ℳ : ι → Submodule R M}
    {𝒩 : ι → Submodule R N} (hg : LinearMap.IsHomogeneous g ℳ 𝒩 0) (f : ι → κ) :
    LinearMap.IsHomogeneous g (TauCeti.coarsenGrading ℳ f) (TauCeti.coarsenGrading 𝒩 f) 0 :=
  LinearMap.isHomogeneous_def.2 fun k x hx ↦ by
    have hle : TauCeti.coarsenGrading ℳ f k ≤
        (TauCeti.coarsenGrading 𝒩 f (k + 0)).comap g :=
      coarsenGrading_le_iff.2 fun i hi y hy ↦ by
        simpa only [add_zero, Submodule.mem_comap, ← hi] using
          mem_coarsenGrading_of_mem f (by simpa only [add_zero] using hg.map_mem hy)
    exact hle hx

end Homogeneous

section Parity

/-- The parity grading of an integer-indexed family of submodules, indexed by `ZMod 2`: its
even piece is the sum of the pieces of even degree and its odd piece is the sum of the pieces
of odd degree (`parityGrading_zero`, `parityGrading_one`).  It is reducible to the coarsening
along reduction modulo two, so the `coarsenGrading` API and instances apply to it directly. -/
abbrev parityGrading (ℳ : ℤ → Submodule R M) : ZMod 2 → Submodule R M :=
  coarsenGrading ℳ (Int.castAddHom (ZMod 2))

/-- An element of degree `n` has parity `n` modulo two. -/
theorem mem_parityGrading_of_mem {ℳ : ℤ → Submodule R M} {n : ℤ} {x : M} (hx : x ∈ ℳ n) :
    x ∈ parityGrading ℳ n :=
  mem_coarsenGrading_of_mem (Int.castAddHom (ZMod 2)) hx

/-- A degree-zero homogeneous linear map between integer-graded modules is also homogeneous of
degree zero for their parity gradings. -/
theorem LinearMap.IsHomogeneous.parityGrading_zero {N : Type*} [AddCommMonoid N] [Module R N]
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

end Parity

namespace InternalGrading

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- The coarsening of an internal grading along a map `f : ι → κ` of index types: the degree-`k`
piece is the sum of the pieces whose degree lies in the fibre over `k`. -/
noncomputable def coarsen (G : InternalGrading R M ι) (f : ι → κ) : InternalGrading R M κ where
  piece := coarsenGrading G.piece f
  isInternal := G.isInternal.iSup_fiber f

@[simp]
theorem coarsen_piece (G : InternalGrading R M ι) (f : ι → κ) :
    (G.coarsen f).piece = coarsenGrading G.piece f := (rfl)

/-- The parity grading of an internal integer grading: the internal `ZMod 2`-grading whose even
piece is the sum of the pieces of degree `2 * k` and whose odd piece is the sum of the pieces of
degree `2 * k + 1`. -/
noncomputable def parity (G : InternalGrading R M ℤ) : InternalGrading R M (ZMod 2) :=
  G.coarsen (Int.castAddHom (ZMod 2))

@[simp]
theorem parity_piece (G : InternalGrading R M ℤ) : G.parity.piece = parityGrading G.piece := (rfl)

end InternalGrading

end TauCeti
