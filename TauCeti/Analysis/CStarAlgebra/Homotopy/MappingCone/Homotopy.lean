/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Homotopy.MappingCone.Basic
import Mathlib.Topology.Order.ProjIcc

/-!
# Homotopy invariance of mapping cones

For a homotopy `Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁` between `⋆`-homomorphisms
`φ₀, φ₁ : A →⋆ₙₐ[ℂ] B`, `evalZeroMap Φ : MappingCone Φ.toHom →⋆ₙₐ[ℂ] MappingCone φ₀` and
`evalOneMap Φ : MappingCone Φ.toHom →⋆ₙₐ[ℂ] MappingCone φ₁` are `⋆`-homotopy equivalences,
yielding `MappingCone.homotopyEquiv Φ : StarHomotopyEquiv (MappingCone φ₀) (MappingCone φ₁)`.

## Main declarations

* `TauCeti.MappingCone.evalZeroMap`, `TauCeti.MappingCone.evalOneMap`, and
  `TauCeti.MappingCone.inclZeroMap`: endpoint evaluations and rescaling-and-concatenation inverse.
* `TauCeti.MappingCone.evalZeroHomotopyEquiv`, `TauCeti.MappingCone.symmEquiv`,
  `TauCeti.MappingCone.evalOneHomotopyEquiv`, and `TauCeti.MappingCone.homotopyEquiv`: homotopy
  invariance of mapping cones.
* `NonUnitalStarAlgHom.Homotopic.nonempty_mappingCone_starHomotopyEquiv`: homotopic
  `⋆`-homomorphisms have `⋆`-homotopy-equivalent mapping cones.
-/

public section

noncomputable section

open Filter Set Topology unitInterval
open scoped CStarAlgebra ZeroAtInfty

namespace TauCeti

namespace MappingCone

section HomotopyInvariance

/-- Clamped rescaling `(s, t) ↦ min (s * (1 + t)) 1` on `unitInterval × unitInterval`. -/
private def scaleClamp : C(I × I, I) where
  toFun p := Set.projIcc (0 : ℝ) 1 zero_le_one ((p.1 : ℝ) * (1 + (p.2 : ℝ)))
  continuous_toFun := continuous_projIcc.comp
    ((continuous_subtypeVal.comp _root_.continuous_fst).mul
      (continuous_const.add (continuous_subtypeVal.comp _root_.continuous_snd)))

/-- The real value of `scaleClamp p` is `min (p.1 * (1 + p.2)) 1`. -/
@[simp] private theorem coe_scaleClamp (p : I × I) :
    (scaleClamp p : ℝ) = min ((p.1 : ℝ) * (1 + (p.2 : ℝ))) 1 := by
  have h0 : 0 ≤ min 1 ((p.1 : ℝ) * (1 + (p.2 : ℝ))) :=
    le_min zero_le_one (mul_nonneg p.1.property.1 (by linarith [p.2.property.1]))
  simp [scaleClamp, Set.coe_projIcc, max_eq_right h0, min_comm]

private theorem scaleClamp_of_ge_one {p : I × I} (hp : 1 ≤ (p.1 : ℝ) * (1 + (p.2 : ℝ))) :
    scaleClamp p = 1 := Set.projIcc_of_right_le zero_le_one hp

@[simp]
private theorem scaleClamp_zero_left (t : I) : scaleClamp (0, t) = 0 := by simp [scaleClamp]

@[simp] private theorem scaleClamp_one_left (t : I) : scaleClamp (1, t) = 1 :=
  scaleClamp_of_ge_one (by simpa using le_add_of_nonneg_right (a := (1 : ℝ)) t.property.1)

@[simp]
private theorem scaleClamp_zero_right (s : I) : scaleClamp (s, 0) = s := by simp [scaleClamp]

/-- Clamped shift `(s, t) ↦ max (s * (1 + t) - 1) 0` on `unitInterval × unitInterval`. -/
private def shiftClamp : C(I × I, I) where
  toFun p := Set.projIcc (0 : ℝ) 1 zero_le_one ((p.1 : ℝ) * (1 + (p.2 : ℝ)) - 1)
  continuous_toFun := continuous_projIcc.comp
    (((continuous_subtypeVal.comp _root_.continuous_fst).mul
      (continuous_const.add (continuous_subtypeVal.comp _root_.continuous_snd))).sub
      continuous_const)

/-- The real value of `shiftClamp p` is `max (p.1 * (1 + p.2) - 1) 0`. -/
@[simp] private theorem coe_shiftClamp (p : I × I) :
    (shiftClamp p : ℝ) = max ((p.1 : ℝ) * (1 + (p.2 : ℝ)) - 1) 0 := by
  have hle : (p.1 : ℝ) * (1 + (p.2 : ℝ)) - 1 ≤ 1 := by
    nlinarith [p.1.property.1, p.1.property.2, p.2.property.1, p.2.property.2]
  simp [shiftClamp, Set.coe_projIcc, min_eq_right hle, max_comm]

private theorem shiftClamp_of_le_one {p : I × I} (hp : (p.1 : ℝ) * (1 + (p.2 : ℝ)) ≤ 1) :
    shiftClamp p = 0 := Set.projIcc_of_le_left zero_le_one (sub_nonpos.mpr hp)

@[simp] private theorem shiftClamp_zero_left (t : I) : shiftClamp (0, t) = 0 :=
  shiftClamp_of_le_one (by norm_num)

@[simp]
private theorem shiftClamp_one_left (t : I) : shiftClamp (1, t) = t := by simp [shiftClamp]

@[simp] private theorem shiftClamp_zero_right (s : I) : shiftClamp (s, 0) = 0 :=
  shiftClamp_of_le_one (by simpa using s.property.2)

/-- Linear homotopy `((r, s), t) ↦ (Set.Icc.convexComb (scaleClamp (s, t)) s r,
Set.Icc.convexComb (shiftClamp (s, t)) t r)` from `(scaleClamp (s, t), shiftClamp (s, t))` at
`r = 0` to `(s, t)` at `r = 1`. -/
private def warpHomotopy : C((I × I) × I, I × I) where
  toFun q :=
    (Set.Icc.convexComb (scaleClamp (q.1.2, q.2)) q.1.2 q.1.1,
     Set.Icc.convexComb (shiftClamp (q.1.2, q.2)) q.2 q.1.1)
  continuous_toFun := by refine Continuous.prodMk ?_ ?_ <;> fun_prop

private theorem warpHomotopy_apply (q : (I × I) × I) :
    warpHomotopy q =
      (Set.Icc.convexComb (scaleClamp (q.1.2, q.2)) q.1.2 q.1.1,
       Set.Icc.convexComb (shiftClamp (q.1.2, q.2)) q.2 q.1.1) := (rfl)

@[simp] private theorem warpHomotopy_zero_left (s t : I) :
    warpHomotopy ((0, s), t) = (scaleClamp (s, t), shiftClamp (s, t)) := by
  simp [warpHomotopy_apply]

@[simp] private theorem warpHomotopy_one_left (s t : I) : warpHomotopy ((1, s), t) = (s, t) := by
  simp [warpHomotopy_apply]

@[simp] private theorem warpHomotopy_fst_zero (r t : I) : (warpHomotopy ((r, 0), t)).1 = 0 := by
  simp [warpHomotopy_apply]

@[simp] private theorem warpHomotopy_one_mid (r t : I) : warpHomotopy ((r, 1), t) = (1, t) := by
  simp [warpHomotopy_apply]

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {φ₀ φ₁ : A →⋆ₙₐ[ℂ] B}

/-- Evaluation `MappingCone Φ.toHom →⋆ₙₐ[ℂ] MappingCone (Φ.eval t)` at `t : unitInterval`. -/
def evalMap (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (t : I) :
    MappingCone Φ.toHom →⋆ₙₐ[ℂ] MappingCone (Φ.eval t) :=
  map Φ.toHom (Φ.eval t) (.id ℂ A) (ContinuousMap.evalNonUnitalStarAlgHom ℂ B t) <| by
    ext a; simp

@[simp]
theorem fst_evalMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (t : I)
    (x : MappingCone Φ.toHom) : (evalMap Φ t x).fst = x.fst := by simp [evalMap]

@[simp]
theorem snd_evalMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (t : I)
    (x : MappingCone Φ.toHom) (s : Ioc (0 : ℝ) 1) : (evalMap Φ t x).snd s = x.snd s t := by
  simp [evalMap]

@[simp] theorem fstHom_comp_evalMap (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (t : I) :
    (fstHom (Φ.eval t)).comp (evalMap Φ t) = fstHom Φ.toHom :=
  (fstHom_comp_map _ _ _ _ _).trans (NonUnitalStarAlgHom.id_comp _)

theorem evalMap_comp_inr (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (t : I) :
    (evalMap Φ t).comp (inr Φ.toHom) =
      (inr (Φ.eval t)).comp (CStarSuspension.map (ContinuousMap.evalNonUnitalStarAlgHom ℂ B t)) :=
  map_comp_inr _

private def castCodomain {φ : A →⋆ₙₐ[ℂ] C(I, B)} {ψ₁ ψ₂ : A →⋆ₙₐ[ℂ] B} (h : ψ₁ = ψ₂)
    (f : MappingCone φ →⋆ₙₐ[ℂ] MappingCone ψ₁) :
    MappingCone φ →⋆ₙₐ[ℂ] MappingCone ψ₂ :=
  h ▸ f

private theorem fst_castCodomain_apply {φ : A →⋆ₙₐ[ℂ] C(I, B)} {ψ₁ ψ₂ : A →⋆ₙₐ[ℂ] B}
    (h : ψ₁ = ψ₂) (f : MappingCone φ →⋆ₙₐ[ℂ] MappingCone ψ₁) (x : MappingCone φ) :
    (castCodomain h f x).fst = (f x).fst := by cases h; rfl

private theorem snd_castCodomain_apply {φ : A →⋆ₙₐ[ℂ] C(I, B)} {ψ₁ ψ₂ : A →⋆ₙₐ[ℂ] B}
    (h : ψ₁ = ψ₂) (f : MappingCone φ →⋆ₙₐ[ℂ] MappingCone ψ₁) (x : MappingCone φ) :
    (castCodomain h f x).snd = (f x).snd := by cases h; rfl

private theorem fstHom_comp_castCodomain {φ : A →⋆ₙₐ[ℂ] C(I, B)} {ψ₁ ψ₂ : A →⋆ₙₐ[ℂ] B}
    (h : ψ₁ = ψ₂) (f : MappingCone φ →⋆ₙₐ[ℂ] MappingCone ψ₁) :
    (fstHom ψ₂).comp (castCodomain h f) = (fstHom ψ₁).comp f := by cases h; rfl

private theorem castCodomain_comp_inr {φ : A →⋆ₙₐ[ℂ] C(I, B)} {ψ₁ ψ₂ : A →⋆ₙₐ[ℂ] B}
    (h : ψ₁ = ψ₂) (f : MappingCone φ →⋆ₙₐ[ℂ] MappingCone ψ₁)
    {g : CStarSuspension C(I, B) →⋆ₙₐ[ℂ] CStarSuspension B}
    (hf : f.comp (inr φ) = (inr ψ₁).comp g) :
    (castCodomain h f).comp (inr φ) = (inr ψ₂).comp g := by cases h; exact hf

/-- Endpoint evaluation `MappingCone Φ.toHom →⋆ₙₐ[ℂ] MappingCone φ₀` at `t = 0`. -/
def evalZeroMap (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    MappingCone Φ.toHom →⋆ₙₐ[ℂ] MappingCone φ₀ :=
  castCodomain Φ.eval_zero (evalMap Φ 0)

@[simp]
theorem fst_evalZeroMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone Φ.toHom) :
    (evalZeroMap Φ x).fst = x.fst := by
  rw [evalZeroMap, fst_castCodomain_apply, fst_evalMap_apply]

@[simp]
theorem snd_evalZeroMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone Φ.toHom)
    (s : Ioc (0 : ℝ) 1) : (evalZeroMap Φ x).snd s = x.snd s 0 := by
  rw [evalZeroMap, snd_castCodomain_apply, snd_evalMap_apply]

@[simp] theorem fstHom_comp_evalZeroMap (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (fstHom φ₀).comp (evalZeroMap Φ) = fstHom Φ.toHom := by
  rw [evalZeroMap, fstHom_comp_castCodomain, fstHom_comp_evalMap]

theorem evalZeroMap_comp_inr (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (evalZeroMap Φ).comp (inr Φ.toHom) =
      (inr φ₀).comp (CStarSuspension.map (ContinuousMap.evalNonUnitalStarAlgHom ℂ B 0)) :=
  castCodomain_comp_inr Φ.eval_zero (evalMap Φ 0) (evalMap_comp_inr Φ 0)

/-- Endpoint evaluation `MappingCone Φ.toHom →⋆ₙₐ[ℂ] MappingCone φ₁` at `t = 1`. -/
def evalOneMap (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    MappingCone Φ.toHom →⋆ₙₐ[ℂ] MappingCone φ₁ :=
  castCodomain Φ.eval_one (evalMap Φ 1)

@[simp]
theorem fst_evalOneMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone Φ.toHom) :
    (evalOneMap Φ x).fst = x.fst := by
  rw [evalOneMap, fst_castCodomain_apply, fst_evalMap_apply]

@[simp]
theorem snd_evalOneMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone Φ.toHom)
    (s : Ioc (0 : ℝ) 1) : (evalOneMap Φ x).snd s = x.snd s 1 := by
  rw [evalOneMap, snd_castCodomain_apply, snd_evalMap_apply]

@[simp] theorem fstHom_comp_evalOneMap (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (fstHom φ₁).comp (evalOneMap Φ) = fstHom Φ.toHom := by
  rw [evalOneMap, fstHom_comp_castCodomain, fstHom_comp_evalMap]

theorem evalOneMap_comp_inr (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (evalOneMap Φ).comp (inr Φ.toHom) =
      (inr φ₁).comp (CStarSuspension.map (ContinuousMap.evalNonUnitalStarAlgHom ℂ B 1)) :=
  castCodomain_comp_inr Φ.eval_one (evalMap Φ 1) (evalMap_comp_inr Φ 1)

/-- Underlying continuous square `(s, t) ↦ f(s(1 + t))` for `s(1 + t) ≤ 1` and
`Φ_a(s(1 + t) - 1)` for `s(1 + t) ≥ 1`, defining `inclZeroSquare`. -/
private def inclZeroSquareFun (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone φ₀) :
    C(I × I, B) where
  toFun p :=
    if (p.1 : ℝ) * (1 + (p.2 : ℝ)) ≤ 1 then
      CStarCone.toUnitIntervalMap x.snd (scaleClamp p)
    else
      Φ.toHom x.fst (shiftClamp p)
  continuous_toFun := by
    refine Continuous.if_le
      ((CStarCone.toUnitIntervalMap x.snd).comp scaleClamp).continuous
      ((Φ.toHom x.fst).comp shiftClamp).continuous
      ((continuous_subtypeVal.comp _root_.continuous_fst).mul
        (continuous_const.add (continuous_subtypeVal.comp _root_.continuous_snd)))
      continuous_const fun p hp => ?_
    rw [scaleClamp_of_ge_one hp.ge, shiftClamp_of_le_one hp.le,
      CStarCone.toUnitIntervalMap_apply_one, ← x.eq_evalOne, Φ.toHom_apply_zero]

/-- Two-parameter continuous family `(s, t) ↦ f(s(1 + t))` for `s(1 + t) ≤ 1` and
`Φ_a(s(1 + t) - 1)` for `s(1 + t) ≥ 1`, defining the homotopy inverse to `evalZeroMap`. -/
private def inclZeroSquare (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    MappingCone φ₀ →⋆ₙₐ[ℂ] C(I × I, B) :=
  ContinuousMap.nonUnitalStarAlgHomOfPointwise (inclZeroSquareFun Φ) fun p => by
    by_cases hp : (p.1 : ℝ) * (1 + (p.2 : ℝ)) ≤ 1
    · refine ⟨((ContinuousMap.evalNonUnitalStarAlgHom ℂ B (scaleClamp p)).comp
          CStarCone.toUnitIntervalMap).comp (sndHom φ₀), fun x => ?_⟩
      simp [inclZeroSquareFun, hp]
    · refine ⟨((ContinuousMap.evalNonUnitalStarAlgHom ℂ B (shiftClamp p)).comp
          Φ.toHom).comp (fstHom φ₀), fun x => ?_⟩
      simp [inclZeroSquareFun, hp]

private theorem inclZeroSquare_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁)
    (x : MappingCone φ₀) (p : I × I) :
    inclZeroSquare Φ x p =
      if (p.1 : ℝ) * (1 + (p.2 : ℝ)) ≤ 1 then
        CStarCone.toUnitIntervalMap x.snd (scaleClamp p)
      else
        Φ.toHom x.fst (shiftClamp p) := by simp [inclZeroSquare, inclZeroSquareFun]

private theorem inclZeroSquare_zero_left (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁)
    (x : MappingCone φ₀) : (inclZeroSquare Φ x).curry 0 = 0 := by
  ext t
  rw [ContinuousMap.curry_apply, ContinuousMap.zero_apply]
  simp [inclZeroSquare_apply]

private theorem inclZeroSquare_one_left (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁)
    (x : MappingCone φ₀) : (inclZeroSquare Φ x).curry 1 = Φ.toHom x.fst := by
  ext t
  rw [ContinuousMap.curry_apply, inclZeroSquare_apply, Set.Icc.coe_one, one_mul]
  split_ifs with ht
  · have ht_le : (t : ℝ) ≤ 0 := by linarith
    have ht0 : t = 0 := Subtype.ext (le_antisymm ht_le t.property.1)
    subst ht0
    rw [scaleClamp_one_left, CStarCone.toUnitIntervalMap_apply_one, ← x.eq_evalOne,
      Φ.toHom_apply_zero]
  · rw [shiftClamp_one_left]

private def inclZeroConeHom (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    MappingCone φ₀ →⋆ₙₐ[ℂ] CStarCone C(I, B) where
  toFun x :=
    CStarCone.ofUnitIntervalMapEqZero ((inclZeroSquare Φ x).curry) (inclZeroSquare_zero_left Φ x)
  map_smul' c x := by ext s t; simp [map_smul]
  map_zero' := by ext s t; simp
  map_add' x y := by ext s t; simp [map_add]
  map_mul' x y := by ext s t; simp [map_mul]
  map_star' x := by ext s t; simp [map_star]

private theorem inclZeroConeHom_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁)
    (x : MappingCone φ₀) :
    inclZeroConeHom Φ x =
      CStarCone.ofUnitIntervalMapEqZero ((inclZeroSquare Φ x).curry)
        (inclZeroSquare_zero_left Φ x) :=
  rfl

/-- Rescaling-and-concatenation `⋆`-homomorphism `MappingCone φ₀ →⋆ₙₐ[ℂ] MappingCone Φ.toHom`
forming a `⋆`-homotopy inverse to `evalZeroMap Φ`. -/
def inclZeroMap (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    MappingCone φ₀ →⋆ₙₐ[ℂ] MappingCone Φ.toHom :=
  lift Φ.toHom (fstHom φ₀) (inclZeroConeHom Φ)
    (by
      ext x t
      simpa [inclZeroConeHom_apply] using
        DFunLike.congr_fun (inclZeroSquare_one_left Φ x).symm t)

@[simp]
theorem fst_inclZeroMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone φ₀) :
    (inclZeroMap Φ x).fst = x.fst := by simp [inclZeroMap]

theorem snd_inclZeroMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone φ₀)
    (s : Ioc (0 : ℝ) 1) (t : I) :
    (inclZeroMap Φ x).snd s t =
      if h : (s : ℝ) * (1 + (t : ℝ)) ≤ 1 then
        CStarCone.toUnitIntervalMap x.snd ⟨(s : ℝ) * (1 + (t : ℝ)),
          mul_nonneg s.property.1.le (by linarith [t.property.1]), h⟩
      else
        Φ.toHom x.fst ⟨(s : ℝ) * (1 + (t : ℝ)) - 1,
          by linarith, by nlinarith [s.property.1, s.property.2, t.property.1, t.property.2]⟩ := by
  rw [inclZeroMap, snd_lift_apply, inclZeroConeHom_apply]
  simp only [CStarCone.ofUnitIntervalMapEqZero_apply, ContinuousMap.curry_apply,
    inclZeroSquare_apply]
  split_ifs with h
  · congr 1; ext; simp [h]
  · congr 1; ext; simp [(not_le.mp h).le]

@[simp] theorem evalZeroMap_comp_inclZeroMap (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (evalZeroMap Φ).comp (inclZeroMap Φ) = .id ℂ (MappingCone φ₀) := by
  ext x : 1
  refine ext (by simp) ?_
  ext s
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_id, id_eq,
    snd_evalZeroMap_apply]
  rw [snd_inclZeroMap_apply, dite_eq_left (by simpa using s.property.2)]
  have hsub :
      (⟨(s : ℝ) * (1 + ((0 : I) : ℝ)),
        mul_nonneg s.property.1.le (by linarith [(0 : I).property.1]),
        by simpa using s.property.2⟩ : I) = Set.inclusion Ioc_subset_Icc_self s := by
    ext; simp
  rw [hsub, CStarCone.toUnitIntervalMap_apply_inclusion]

/-- Continuous family `r ↦ G_r` in `CStarCone C(I, B)` deforming
`(s, t) ↦ F(scaleClamp, shiftClamp)` to `G`. -/
private def warpConeMap (G : CStarCone C(I, B)) : C(I, CStarCone C(I, B)) where
  toFun r := CStarCone.ofUnitIntervalMapEqZero
    (((((CStarCone.toUnitIntervalMap G).uncurry.comp warpHomotopy).curry).curry) r)
    (by ext t; simp [ContinuousMap.curry_apply, Function.uncurry])
  continuous_toFun := by
    exact CStarCone.continuous_ofUnitIntervalMapEqZero
      ((((CStarCone.toUnitIntervalMap G).uncurry.comp warpHomotopy).curry).curry).continuous _

@[simp] private theorem warpConeMap_apply (G : CStarCone C(I, B)) (r : I) (s : Ioc (0 : ℝ) 1)
    (t : I) :
    warpConeMap G r s t =
      CStarCone.toUnitIntervalMap G
        (warpHomotopy ((r, Set.inclusion Ioc_subset_Icc_self s), t)).1
        (warpHomotopy ((r, Set.inclusion Ioc_subset_Icc_self s), t)).2 := by
  simp [warpConeMap, Function.uncurry]

private theorem evalOne_warpConeMap (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁)
    (y : MappingCone Φ.toHom) (r : I) :
    CStarCone.evalOne (warpConeMap y.snd r) = Φ.toHom y.fst := by
  ext t
  simp [← y.eq_evalOne]

private theorem snd_inclZeroMap_evalZeroMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁)
    (y : MappingCone Φ.toHom) (s : Ioc (0 : ℝ) 1) (t : I) :
    (inclZeroMap Φ (evalZeroMap Φ y)).snd s t =
      CStarCone.toUnitIntervalMap y.snd (scaleClamp (Set.inclusion Ioc_subset_Icc_self s, t))
        (shiftClamp (Set.inclusion Ioc_subset_Icc_self s, t)) := by
  have hpath0 := congrFun
    (eq_of_zero_of_inclusion_Ioc_Icc
      (g₁ := fun u => CStarCone.toUnitIntervalMap (evalZeroMap Φ y).snd u)
      (g₂ := fun u => CStarCone.toUnitIntervalMap y.snd u 0)
      (by simp) (by simp))
  rw [snd_inclZeroMap_apply]
  split_ifs with hs
  · rw [shiftClamp_of_le_one hs, hpath0]
    congr 2; ext; simp [hs]
  · rw [scaleClamp_of_ge_one (not_le.mp hs).le, fst_evalZeroMap_apply,
      CStarCone.toUnitIntervalMap_apply_one, ← y.eq_evalOne]
    congr 1; ext; simp [(not_le.mp hs).le]

/-- Homotopy from `(inclZeroMap Φ).comp (evalZeroMap Φ)` to `.id ℂ (MappingCone Φ.toHom)`. -/
private def inclZeroCompEvalZeroHomotopy (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    NonUnitalStarAlgHom.Homotopy ((inclZeroMap Φ).comp (evalZeroMap Φ))
      (.id ℂ (MappingCone Φ.toHom)) where
  toHom :=
    { toFun y :=
        { toFun r := mk Φ.toHom y.fst (warpConeMap y.snd r) (evalOne_warpConeMap Φ y r).symm
          continuous_toFun := continuous_iff.mpr
            ⟨by simp_rw [fst_mk]; exact continuous_const,
             by simp_rw [snd_mk]; exact (warpConeMap y.snd).continuous⟩ }
      map_smul' c y := by ext r : 1; refine ext (by simp) ?_; ext s t; simp [map_smul]
      map_zero' := by ext r : 1; refine ext (by simp) ?_; ext s t; simp
      map_add' x y := by ext r : 1; refine ext (by simp) ?_; ext s t; simp [map_add]
      map_mul' x y := by ext r : 1; refine ext (by simp) ?_; ext s t; simp [map_mul]
      map_star' y := by ext r : 1; refine ext (by simp) ?_; ext s t; simp [map_star] }
  toHom_apply_zero y := by
    refine ext (by simp) ?_; ext s t
    simp [snd_inclZeroMap_evalZeroMap_apply]
  toHom_apply_one y := by
    refine ext (by simp) ?_; ext s t
    simp

/-- Endpoint evaluation at `0` is a `⋆`-homotopy equivalence
`MappingCone Φ.toHom → MappingCone φ₀`. -/
def evalZeroHomotopyEquiv (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    StarHomotopyEquiv (MappingCone Φ.toHom) (MappingCone φ₀) where
  toFun := evalZeroMap Φ
  invFun := inclZeroMap Φ
  left_inv := ⟨inclZeroCompEvalZeroHomotopy Φ⟩
  right_inv := by rw [evalZeroMap_comp_inclZeroMap]; exact ⟨.refl _⟩

@[simp] theorem evalZeroHomotopyEquiv_toFun (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (evalZeroHomotopyEquiv Φ).toFun = evalZeroMap Φ := (rfl)

@[simp] theorem evalZeroHomotopyEquiv_invFun (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (evalZeroHomotopyEquiv Φ).invFun = inclZeroMap Φ := (rfl)

/-- Time-reversal `⋆`-isomorphism `MappingCone Φ.toHom ≃⋆ₐ[ℂ] MappingCone Φ.symm.toHom` intertwining
`evalOneMap Φ` with `evalZeroMap Φ.symm`. -/
def symmEquiv (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    MappingCone Φ.toHom ≃⋆ₐ[ℂ] MappingCone Φ.symm.toHom :=
  StarAlgEquiv.ofNonUnitalStarAlgHom
    (map Φ.toHom Φ.symm.toHom (.id ℂ A)
      (unitInterval.symmHomeomorph.compStarAlgEquivₙ' ℂ B).toNonUnitalStarAlgHom
      (by ext a t; simp))
    (map Φ.symm.toHom Φ.toHom (.id ℂ A)
      (unitInterval.symmHomeomorph.compStarAlgEquivₙ' ℂ B).toNonUnitalStarAlgHom
      (by ext a t; simp))
    (by ext x : 1; refine ext (by simp) ?_; ext s t; simp)
    (by ext x : 1; refine ext (by simp) ?_; ext s t; simp)

@[simp]
theorem fst_symmEquiv_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone Φ.toHom) :
    (symmEquiv Φ x).fst = x.fst := by simp [symmEquiv]

@[simp]
theorem snd_symmEquiv_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone Φ.toHom)
    (s : Ioc (0 : ℝ) 1) (t : I) : (symmEquiv Φ x).snd s t = x.snd s (σ t) := by simp [symmEquiv]

@[simp]
theorem fst_symmEquiv_symm_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁)
    (x : MappingCone Φ.symm.toHom) : ((symmEquiv Φ).symm x).fst = x.fst := by simp [symmEquiv]

@[simp]
theorem snd_symmEquiv_symm_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁)
    (x : MappingCone Φ.symm.toHom) (s : Ioc (0 : ℝ) 1) (t : I) :
    ((symmEquiv Φ).symm x).snd s t = x.snd s (σ t) := by simp [symmEquiv]

theorem evalOneMap_eq_evalZeroMap_comp_symmEquiv (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    evalOneMap Φ = (evalZeroMap Φ.symm).comp (symmEquiv Φ).toNonUnitalStarAlgHom := by
  ext x : 1; refine ext (by simp) ?_; ext s; simp [symmEquiv]

/-- Endpoint evaluation at `1` is a `⋆`-homotopy equivalence
`MappingCone Φ.toHom → MappingCone φ₁`. -/
def evalOneHomotopyEquiv (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    StarHomotopyEquiv (MappingCone Φ.toHom) (MappingCone φ₁) where
  toFun := evalOneMap Φ
  invFun := (symmEquiv Φ).symm.toNonUnitalStarAlgHom.comp (inclZeroMap Φ.symm)
  left_inv := by
    rw [evalOneMap_eq_evalZeroMap_comp_symmEquiv]
    simpa using ((StarHomotopyEquiv.ofStarAlgEquiv (symmEquiv Φ)).trans
      (evalZeroHomotopyEquiv Φ.symm)).left_inv
  right_inv := by
    rw [evalOneMap_eq_evalZeroMap_comp_symmEquiv]
    simpa using ((StarHomotopyEquiv.ofStarAlgEquiv (symmEquiv Φ)).trans
      (evalZeroHomotopyEquiv Φ.symm)).right_inv

@[simp] theorem evalOneHomotopyEquiv_toFun (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (evalOneHomotopyEquiv Φ).toFun = evalOneMap Φ := (rfl)

@[simp] theorem evalOneHomotopyEquiv_invFun (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (evalOneHomotopyEquiv Φ).invFun =
      (symmEquiv Φ).symm.toNonUnitalStarAlgHom.comp (inclZeroMap Φ.symm) := (rfl)

/-- A homotopy `Φ` between `φ₀` and `φ₁` induces a `⋆`-homotopy equivalence between `MappingCone φ₀`
and `MappingCone φ₁`. -/
def homotopyEquiv (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    StarHomotopyEquiv (MappingCone φ₀) (MappingCone φ₁) :=
  (evalZeroHomotopyEquiv Φ).symm.trans (evalOneHomotopyEquiv Φ)

@[simp] theorem homotopyEquiv_toFun (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (homotopyEquiv Φ).toFun = (evalOneMap Φ).comp (inclZeroMap Φ) := by simp [homotopyEquiv]

@[simp] theorem homotopyEquiv_invFun (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (homotopyEquiv Φ).invFun =
      (evalZeroMap Φ).comp ((symmEquiv Φ).symm.toNonUnitalStarAlgHom.comp (inclZeroMap Φ.symm)) :=
  by simp [homotopyEquiv]

end HomotopyInvariance

end MappingCone

end TauCeti

namespace NonUnitalStarAlgHom.Homotopic

/-- Homotopic `⋆`-homomorphisms between C⋆-algebras have `⋆`-homotopy-equivalent mapping cones. -/
theorem nonempty_mappingCone_starHomotopyEquiv {A B : Type*} [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] {φ₀ φ₁ : A →⋆ₙₐ[ℂ] B} (h : φ₀.Homotopic φ₁) :
    Nonempty (TauCeti.StarHomotopyEquiv (TauCeti.MappingCone φ₀) (TauCeti.MappingCone φ₁)) :=
  h.elim fun Φ => ⟨TauCeti.MappingCone.homotopyEquiv Φ⟩

end NonUnitalStarAlgHom.Homotopic

end
