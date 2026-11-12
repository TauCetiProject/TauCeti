/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.IntUnitsPower
public import TauCeti.Algebra.Module.GradedModule.Internal
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
  `coarsenGrading ℳ f k`.
* `TauCeti.parityGrading ℳ`: the parity grading of an integer-indexed family of submodules.
* `TauCeti.LinearMap.IsHomogeneous.restrictParity`: restriction of a degree-zero homogeneous map
  to each parity piece.
* `TauCeti.InternalGrading.coarsen` and `TauCeti.InternalGrading.parity`: the same constructions
  for bundled internal gradings.

## Main results

* `TauCeti.coarsenGrading_le_iff`: the universal property of the coarsened pieces, and
  `TauCeti.coarsenGrading_induction`: the corresponding induction principle on elements.
* `TauCeti.decompose_coarsenGrading`: the coarsened homogeneous components are the sums of the
  original components in each fibre.
* `TauCeti.mem_coarsenGrading_iff`: an element lies in the coarsened piece of degree `k` exactly
  when its components outside the fibre over `k` vanish.
* `TauCeti.LinearMap.IsHomogeneous.coarsenGrading`: a homogeneous linear map of degree `q` is
  homogeneous of degree `f q` for gradings coarsened along an additive homomorphism `f`.
* `TauCeti.parityGrading_zero`, `TauCeti.parityGrading_one`, and
  `TauCeti.decompose_parityGrading_zero_add_one`: the even and odd pieces and the two-term parity
  decomposition of an element.
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

omit [DecidableEq κ] in
/-- An element lies in the coarsened piece of degree `k` exactly when its homogeneous components
of every degree outside the fibre over `k` vanish. -/
theorem mem_coarsenGrading_iff {x : M} {k : κ} :
    x ∈ coarsenGrading ℳ f k ↔ ∀ i, f i ≠ k → (decompose ℳ x i : M) = 0 := by
  classical
  refine ⟨fun hx i hi ↦ ?_, fun hx ↦ ?_⟩
  · -- The `i`-th component vanishes on every piece of the fibre over `k`.
    let π : M →ₗ[R] ℳ i := (component R ι (fun i ↦ ℳ i) i).comp
      (decomposeLinearEquiv ℳ).toLinearMap
    have hle : coarsenGrading ℳ f k ≤ LinearMap.ker π :=
      coarsenGrading_le_iff.2 fun j hj y hy ↦ by
        rw [LinearMap.mem_ker, ← Subtype.coe_inj]
        exact decompose_of_mem_ne ℳ hy (by rintro rfl; exact hi hj)
    exact congrArg Subtype.val (LinearMap.mem_ker.1 (hle hx))
  · rw [← sum_support_decompose ℳ x]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    by_cases hi : f i = k
    · exact hi ▸ mem_coarsenGrading_of_mem f (decompose ℳ x i).property
    · rw [hx i hi]
      exact zero_mem _

/-- Each coarsened piece is the direct sum of the original pieces in its fibre. -/
noncomputable def coarsenGradingEquiv (k : κ) :
    (⨁ i : {i : ι // f i = k}, ℳ i.1) ≃ₗ[R] coarsenGrading ℳ f k :=
  LinearEquiv.ofLinearMap
    (toModule R {i : ι // f i = k} (coarsenGrading ℳ f k) fun i ↦
      (ℳ i.1).subtype.codRestrict (coarsenGrading ℳ f k) fun x ↦ by
        rw [Submodule.coe_subtype]
        have hx : (x : M) ∈ coarsenGrading ℳ f (f i.1) := mem_coarsenGrading_of_mem f x.2
        rwa [i.2] at hx)
    (((toModule R ι (⨁ i : {i : ι // f i = k}, ℳ i.1) fun i ↦
        if h : f i = k then lof R {j : ι // f j = k} (fun j ↦ ℳ j.1) ⟨i, h⟩ else 0).comp
      (decomposeLinearEquiv ℳ).toLinearMap).comp (coarsenGrading ℳ f k).subtype)
    (by
      have hleft : ∀ x ∈ coarsenGrading ℳ f k,
          ((toModule R {i : ι // f i = k} (coarsenGrading ℳ f k) fun i ↦
              (ℳ i.1).subtype.codRestrict (coarsenGrading ℳ f k) fun y ↦ by
                rw [Submodule.coe_subtype]
                have hy : (y : M) ∈ coarsenGrading ℳ f (f i.1) := mem_coarsenGrading_of_mem f y.2
                rwa [i.2] at hy)
            ((toModule R ι (⨁ i : {i : ι // f i = k}, ℳ i.1) fun i ↦
              if h : f i = k then lof R {j : ι // f j = k} (fun j ↦ ℳ j.1) ⟨i, h⟩ else 0)
                (decomposeLinearEquiv ℳ x)) : M) = x := fun x hx ↦
        coarsenGrading_induction hx
          (fun i hi y hy ↦ by
            rw [decomposeLinearEquiv_apply_coe ℳ i ⟨y, hy⟩, toModule_lof, dite_eq_left hi,
              toModule_lof]
            rfl)
          (by simp)
          (fun y z hy hz ↦ by simp [hy, hz])
      exact LinearMap.ext fun ⟨x, hx⟩ ↦ Subtype.ext (hleft x hx))
    (by
      refine DirectSum.linearMap_ext R fun i ↦ LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.coe_subtype,
        LinearEquiv.coe_coe, toModule_lof, LinearMap.codRestrict_apply]
      rw [decomposeLinearEquiv_apply_coe ℳ i.1 x, toModule_lof, dite_eq_left i.2])

/-- On a single fibre summand, `coarsenGradingEquiv` is the submodule inclusion into `M`. -/
@[simp]
theorem coe_coarsenGradingEquiv_lof (k : κ) (i : {i : ι // f i = k}) (x : ℳ i.1) :
    (coarsenGradingEquiv ℳ f k (lof R {j : ι // f j = k} (fun j ↦ ℳ j.1) i x) : M) = x := by
  simp [coarsenGradingEquiv]

/-- The inverse of `coarsenGradingEquiv` extracts the `i`-th homogeneous component for each `i` in
the fibre over `k`. -/
@[simp]
theorem coarsenGradingEquiv_symm_apply (k : κ) (x : coarsenGrading ℳ f k)
    (i : {i : ι // f i = k}) :
    (coarsenGradingEquiv ℳ f k).symm x i = decompose ℳ (x : M) i.1 := by
  have h : ∀ y : M, (((toModule R ι (⨁ j : {j : ι // f j = k}, ℳ j.1) fun j ↦
      if h : f j = k then lof R {j : ι // f j = k} (fun j ↦ ℳ j.1) ⟨j, h⟩ else 0)
        (decomposeLinearEquiv ℳ y)) i : M) = (decompose ℳ y i.1 : M) := fun y ↦ by
    induction y using Decomposition.inductionOn ℳ with
    | zero => simp
    | @homogeneous j y =>
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
  refine Subtype.ext ?_
  simpa only [coarsenGradingEquiv, LinearEquiv.symm_ofLinearMap, LinearEquiv.coe_ofLinearMap,
    LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype] using h x.1

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

/-- Every element is the sum of its even and odd components in the parity grading. -/
theorem decompose_parityGrading_zero_add_one (ℳ : ℤ → Submodule R M) [Decomposition ℳ] (x : M) :
    (decompose (parityGrading ℳ) x 0 : M) + (decompose (parityGrading ℳ) x 1 : M) = x := by
  induction x using Decomposition.inductionOn (parityGrading ℳ) with
  | zero => simp
  | @homogeneous k y =>
    rcases (by decide : ∀ k : ZMod 2, k = 0 ∨ k = 1) k with rfl | rfl
    · rw [decompose_of_mem_same _ y.2, decompose_of_mem_ne _ y.2 (by decide), add_zero]
    · rw [decompose_of_mem_ne _ y.2 (by decide), decompose_of_mem_same _ y.2, zero_add]
  | add y z hy hz =>
    simp only [decompose_add, add_apply, Submodule.coe_add]
    calc
      ((decompose (parityGrading ℳ) y 0 : M) + (decompose (parityGrading ℳ) z 0 : M)) +
          ((decompose (parityGrading ℳ) y 1 : M) + (decompose (parityGrading ℳ) z 1 : M)) =
        ((decompose (parityGrading ℳ) y 0 : M) + (decompose (parityGrading ℳ) y 1 : M)) +
          ((decompose (parityGrading ℳ) z 0 : M) + (decompose (parityGrading ℳ) z 1 : M)) :=
        add_add_add_comm _ _ _ _
      _ = y + z := by rw [hy, hz]

/-- A degree-zero homogeneous linear map restricts to a linear map on each parity piece. -/
def LinearMap.IsHomogeneous.restrictParity {N : Type*} [AddCommMonoid N] [Module R N]
    {g : M →ₗ[R] N} {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
    (hg : LinearMap.IsHomogeneous g ℳ 𝒩 0) (k : ZMod 2) :
    parityGrading ℳ k →ₗ[R] parityGrading 𝒩 k :=
  g.restrict fun _ hx ↦ by
    have h := (hg.coarsenGrading (Int.castAddHom (ZMod 2))).map_mem hx
    rwa [map_zero, add_zero] at h

/-- Coercing `restrictParity` back to the ambient module applies the original map `g`. -/
@[simp]
theorem LinearMap.IsHomogeneous.coe_restrictParity_apply {N : Type*} [AddCommMonoid N] [Module R N]
    {g : M →ₗ[R] N} {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N}
    (hg : LinearMap.IsHomogeneous g ℳ 𝒩 0) (k : ZMod 2) (x : parityGrading ℳ k) :
    (hg.restrictParity k x : N) = g x :=
  (rfl)

/-- Restricting a degree-zero homogeneous map to a parity piece commutes with decomposition into
parity components. -/
@[simp]
theorem LinearMap.IsHomogeneous.restrictParity_decompose {N : Type*} [AddCommMonoid N] [Module R N]
    {g : M →ₗ[R] N} {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} [Decomposition ℳ]
    [Decomposition 𝒩] (hg : LinearMap.IsHomogeneous g ℳ 𝒩 0) (k : ZMod 2) (x : M) :
    hg.restrictParity k (decompose (parityGrading ℳ) x k) =
      decompose (parityGrading 𝒩) (g x) k := by
  apply Subtype.ext
  rw [hg.coe_restrictParity_apply]
  have h := (hg.coarsenGrading (Int.castAddHom (ZMod 2))).map_decompose k x
  rwa [map_zero, add_zero] at h

end Parity

namespace InternalGrading

variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]

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
noncomputable def parity (G : InternalGrading R M) : InternalGrading R M (ZMod 2) :=
  G.coarsen (Int.castAddHom (ZMod 2))

@[simp]
theorem parity_piece (G : InternalGrading R M) : G.parity.piece = parityGrading G.piece := (rfl)

end InternalGrading

end TauCeti
