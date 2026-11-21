/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Homotopy.MappingCone

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

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {φ₀ φ₁ : A →⋆ₙₐ[ℂ] B}

/-- Endpoint evaluation `MappingCone Φ.toHom →⋆ₙₐ[ℂ] MappingCone φ₀` at `t = 0`. -/
def evalZeroMap (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    MappingCone Φ.toHom →⋆ₙₐ[ℂ] MappingCone φ₀ :=
  map Φ.toHom φ₀ (.id ℂ A) (ContinuousMap.evalNonUnitalStarAlgHom ℂ B 0) <| by ext a; simp

@[simp]
theorem fst_evalZeroMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone Φ.toHom) :
    (evalZeroMap Φ x).fst = x.fst := by simp [evalZeroMap]

@[simp]
theorem snd_evalZeroMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone Φ.toHom)
    (s : Ioc (0 : ℝ) 1) : (evalZeroMap Φ x).snd s = x.snd s 0 := by simp [evalZeroMap]

/-- Endpoint evaluation `MappingCone Φ.toHom →⋆ₙₐ[ℂ] MappingCone φ₁` at `t = 1`. -/
def evalOneMap (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    MappingCone Φ.toHom →⋆ₙₐ[ℂ] MappingCone φ₁ :=
  map Φ.toHom φ₁ (.id ℂ A) (ContinuousMap.evalNonUnitalStarAlgHom ℂ B 1) <| by ext a; simp

@[simp]
theorem fst_evalOneMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone Φ.toHom) :
    (evalOneMap Φ x).fst = x.fst := by simp [evalOneMap]

@[simp]
theorem snd_evalOneMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone Φ.toHom)
    (s : Ioc (0 : ℝ) 1) : (evalOneMap Φ x).snd s = x.snd s 1 := by simp [evalOneMap]

/-- Clamped rescaling `(s, t) ↦ min(s(1 + t), 1)` on `unitInterval × unitInterval`. -/
private def scaleClamp : C(I × I, I) where
  toFun p := ⟨min ((p.1 : ℝ) * (1 + (p.2 : ℝ))) 1,
    le_min (mul_nonneg p.1.property.1 (by linarith [p.2.property.1])) zero_le_one, min_le_right _ _⟩
  continuous_toFun := Continuous.subtype_mk
    (((continuous_subtypeVal.comp _root_.continuous_fst).mul
      (continuous_const.add (continuous_subtypeVal.comp _root_.continuous_snd))).min
        continuous_const) _

/-- Clamped shift `(s, t) ↦ max(s(1 + t) - 1, 0)` on `unitInterval × unitInterval`. -/
private def shiftClamp : C(I × I, I) where
  toFun p := ⟨max ((p.1 : ℝ) * (1 + (p.2 : ℝ)) - 1) 0,
    le_max_right _ _,
    max_le (by nlinarith [p.1.property.1, p.1.property.2, p.2.property.1, p.2.property.2])
      zero_le_one⟩
  continuous_toFun := Continuous.subtype_mk
    ((((continuous_subtypeVal.comp _root_.continuous_fst).mul
      (continuous_const.add (continuous_subtypeVal.comp _root_.continuous_snd))).sub
        continuous_const).max continuous_const) _

private theorem scaleClamp_zero_left (t : I) : scaleClamp (0, t) = 0 := by
  ext; simp [scaleClamp]

private theorem scaleClamp_one_left (t : I) : scaleClamp (1, t) = 1 := by
  ext; simp [scaleClamp, min_eq_right (le_add_of_nonneg_right t.property.1)]

private theorem shiftClamp_one_left (t : I) : shiftClamp (1, t) = t := by
  ext; simp [shiftClamp, t.property.1]

private theorem scaleClamp_zero_right (s : I) : scaleClamp (s, 0) = s := by
  ext; simp [scaleClamp, min_eq_left s.property.2]

private theorem shiftClamp_of_le_one {p : I × I} (hp : (p.1 : ℝ) * (1 + (p.2 : ℝ)) ≤ 1) :
    shiftClamp p = 0 := by
  ext; simp [shiftClamp, max_eq_right (sub_nonpos.mpr hp)]

private theorem scaleClamp_of_ge_one {p : I × I} (hp : 1 ≤ (p.1 : ℝ) * (1 + (p.2 : ℝ))) :
    scaleClamp p = 1 := by
  ext; simp [scaleClamp, min_eq_right hp]

/-- Two-parameter continuous family `(s, t) ↦ f(s(1 + t))` for `s(1 + t) ≤ 1` and
`Φ_a(s(1 + t) - 1)` for `s(1 + t) ≥ 1`, defining the homotopy inverse to `evalZeroMap`. -/
private def inclZeroSquare (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    MappingCone φ₀ →⋆ₙₐ[ℂ] C(I × I, B) where
  toFun x :=
    { toFun p :=
        if (p.1 : ℝ) * (1 + (p.2 : ℝ)) ≤ 1 then
          CStarCone.toPath x.snd (scaleClamp p)
        else
          Φ.toHom x.fst (shiftClamp p)
      continuous_toFun := by
        refine Continuous.if_le
          ((CStarCone.toPath x.snd).comp scaleClamp).continuous
          ((Φ.toHom x.fst).comp shiftClamp).continuous
          ((continuous_subtypeVal.comp _root_.continuous_fst).mul
            (continuous_const.add (continuous_subtypeVal.comp _root_.continuous_snd)))
          continuous_const fun p hp => ?_
        have hs1 : scaleClamp p = 1 := by ext; simp [scaleClamp, hp]
        have hs0 : shiftClamp p = 0 := by ext; simp [shiftClamp, hp]
        rw [hs1, hs0, CStarCone.toPath_apply_one, ← x.eq_evalOne, Φ.eval_zero] }
  map_smul' c x := by
    ext p; simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply]
    split_ifs <;> simp [map_smul]
  map_zero' := by
    ext p; simp only [ContinuousMap.coe_mk, ContinuousMap.zero_apply]; split_ifs <;> simp
  map_add' x y := by
    ext p; simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply]
    split_ifs <;> simp [map_add]
  map_mul' x y := by
    ext p; simp only [ContinuousMap.coe_mk, ContinuousMap.mul_apply]
    split_ifs <;> simp [map_mul]
  map_star' x := by
    ext p; simp only [ContinuousMap.coe_mk, ContinuousMap.star_apply]
    split_ifs <;> simp [map_star]

private theorem inclZeroSquare_zero_left (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁)
    (x : MappingCone φ₀) : (inclZeroSquare Φ x).curry 0 = 0 := by
  ext t
  rw [ContinuousMap.curry_apply, ContinuousMap.zero_apply]
  simp [inclZeroSquare, scaleClamp_zero_left]

private theorem inclZeroSquare_one_left (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁)
    (x : MappingCone φ₀) : (inclZeroSquare Φ x).curry 1 = Φ.toHom x.fst := by
  ext t
  rw [ContinuousMap.curry_apply]
  have h1 : ((1 : I) : ℝ) = 1 := rfl
  simp only [inclZeroSquare, NonUnitalStarAlgHom.coe_mk',
    NonUnitalAlgHom.coe_mk, ContinuousMap.coe_mk, h1, one_mul]
  split_ifs with ht
  · have ht_le : (t : ℝ) ≤ 0 := by linarith
    have ht0 : t = 0 := Subtype.ext (le_antisymm ht_le t.property.1)
    subst ht0
    rw [scaleClamp_one_left, CStarCone.toPath_apply_one, ← x.eq_evalOne, Φ.eval_zero]
  · rw [shiftClamp_one_left]

/-- Rescaling-and-concatenation `⋆`-homomorphism `MappingCone φ₀ →⋆ₙₐ[ℂ] MappingCone Φ.toHom`
forming a `⋆`-homotopy inverse to `evalZeroMap Φ`. -/
def inclZeroMap (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    MappingCone φ₀ →⋆ₙₐ[ℂ] MappingCone Φ.toHom :=
  lift Φ.toHom (fstHom φ₀)
    { toFun x := CStarCone.ofPathEqZero ((inclZeroSquare Φ x).curry) (inclZeroSquare_zero_left Φ x)
      map_smul' c x := by ext s t; simp [map_smul]
      map_zero' := by ext s t; simp
      map_add' x y := by ext s t; simp [map_add]
      map_mul' x y := by ext s t; simp [map_mul]
      map_star' x := by ext s t; simp [map_star] }
    (by ext x t; simpa using DFunLike.congr_fun (inclZeroSquare_one_left Φ x).symm t)

@[simp]
theorem fst_inclZeroMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone φ₀) :
    (inclZeroMap Φ x).fst = x.fst := by simp [inclZeroMap]

theorem snd_inclZeroMap_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone φ₀)
    (s : Ioc (0 : ℝ) 1) (t : I) :
    (inclZeroMap Φ x).snd s t =
      if h : (s : ℝ) * (1 + (t : ℝ)) ≤ 1 then
        CStarCone.toPath x.snd ⟨(s : ℝ) * (1 + (t : ℝ)),
          mul_nonneg s.property.1.le (by linarith [t.property.1]), h⟩
      else
        Φ.toHom x.fst ⟨(s : ℝ) * (1 + (t : ℝ)) - 1,
          by linarith, by nlinarith [s.property.1, s.property.2, t.property.1, t.property.2]⟩ := by
  simp only [inclZeroMap, snd_lift_apply, NonUnitalStarAlgHom.coe_mk', NonUnitalAlgHom.coe_mk,
    CStarCone.ofPathEqZero_apply, ContinuousMap.curry_apply, inclZeroSquare,
    ContinuousMap.coe_mk, coe_iocToUnitInterval]
  split_ifs with h
  · congr 1; ext; simp [scaleClamp, h]
  · congr 1; ext; simp [shiftClamp, (not_le.mp h).le]

@[simp]
theorem evalZeroMap_comp_inclZeroMap (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (evalZeroMap Φ).comp (inclZeroMap Φ) = .id ℂ (MappingCone φ₀) := by
  ext x : 1
  refine ext (by simp) ?_
  ext s
  have h0 : ((0 : I) : ℝ) = 0 := rfl
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_id, id_eq,
    snd_evalZeroMap_apply, inclZeroMap, snd_lift_apply, NonUnitalStarAlgHom.coe_mk',
    NonUnitalAlgHom.coe_mk, CStarCone.ofPathEqZero_apply, ContinuousMap.curry_apply,
    inclZeroSquare, ContinuousMap.coe_mk, coe_iocToUnitInterval, h0, add_zero, mul_one]
  split_ifs with hs
  · rw [scaleClamp_zero_right, CStarCone.toPath_apply_ioc]
  · exact False.elim (hs s.property.2)

/-- Linear homotopy `((r, s), t) ↦ ((1 - r) * scaleClamp (s, t) + r * s, ...)` from
`(scaleClamp (s, t), shiftClamp (s, t))` at `r = 0` to `(s, t)` at `r = 1`. -/
private def warpHomotopy : C((I × I) × I, I × I) where
  toFun q :=
    let p : I × I := (q.1.2, q.2)
    (⟨(1 - (q.1.1 : ℝ)) * (scaleClamp p : ℝ) + (q.1.1 : ℝ) * (p.1 : ℝ),
        add_nonneg (mul_nonneg (sub_nonneg.mpr q.1.1.property.2) (scaleClamp p).property.1)
          (mul_nonneg q.1.1.property.1 p.1.property.1),
        by nlinarith
          [q.1.1.property.1, q.1.1.property.2, (scaleClamp p).property.2, p.1.property.2]⟩,
     ⟨(1 - (q.1.1 : ℝ)) * (shiftClamp p : ℝ) + (q.1.1 : ℝ) * (p.2 : ℝ),
        add_nonneg (mul_nonneg (sub_nonneg.mpr q.1.1.property.2) (shiftClamp p).property.1)
          (mul_nonneg q.1.1.property.1 p.2.property.1),
        by nlinarith
          [q.1.1.property.1, q.1.1.property.2, (shiftClamp p).property.2, p.2.property.2]⟩)
  continuous_toFun := by
    have hr : Continuous fun q : (I × I) × I => (q.1.1 : ℝ) :=
      continuous_subtypeVal.comp (_root_.continuous_fst.comp _root_.continuous_fst)
    have hp : Continuous fun q : (I × I) × I => ((q.1.2, q.2) : I × I) :=
      (_root_.continuous_snd.comp _root_.continuous_fst).prodMk _root_.continuous_snd
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.subtype_mk ?_ _)
    · exact ((continuous_const.sub hr).mul
        (continuous_subtypeVal.comp (scaleClamp.continuous.comp hp))).add
        (hr.mul (continuous_subtypeVal.comp (_root_.continuous_fst.comp hp)))
    · exact ((continuous_const.sub hr).mul
        (continuous_subtypeVal.comp (shiftClamp.continuous.comp hp))).add
        (hr.mul (continuous_subtypeVal.comp (_root_.continuous_snd.comp hp)))

private theorem warpHomotopy_zero_left (s t : I) :
    warpHomotopy ((0, s), t) = (scaleClamp (s, t), shiftClamp (s, t)) := by
  ext <;> simp [warpHomotopy]

private theorem warpHomotopy_one_left (s t : I) : warpHomotopy ((1, s), t) = (s, t) := by
  ext <;> simp [warpHomotopy]

private theorem warpHomotopy_fst_zero (r t : I) : (warpHomotopy ((r, 0), t)).1 = 0 := by
  ext; simp [warpHomotopy, scaleClamp_zero_left]

private theorem warpHomotopy_one_mid (r t : I) : warpHomotopy ((r, 1), t) = (1, t) := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · simp [warpHomotopy, scaleClamp_one_left]
  · simp [warpHomotopy, shiftClamp_one_left]; ring

/-- Continuous path `r ↦ G_r` in `CStarCone C(I, B)` deforming `(s, t) ↦ F(scaleClamp, shiftClamp)`
to `G`. -/
private def warpConePath (G : CStarCone C(I, B)) : C(I, CStarCone C(I, B)) where
  toFun r := CStarCone.ofPathEqZero
    (((((CStarCone.toPath G).uncurry.comp warpHomotopy).curry).curry) r)
    (by ext t; simp [ContinuousMap.curry_apply, Function.uncurry, warpHomotopy_fst_zero])
  continuous_toFun := by
    rw [(CStarCone.isometry_toPath (A := C(I, B))).isUniformInducing.isInducing.continuous_iff]
    have hcomp : (CStarCone.toPath (A := C(I, B)) ∘ fun r => CStarCone.ofPathEqZero
        (((((CStarCone.toPath G).uncurry.comp warpHomotopy).curry).curry) r)
        (by ext t; simp [ContinuousMap.curry_apply, Function.uncurry, warpHomotopy_fst_zero])) =
        (((CStarCone.toPath G).uncurry.comp warpHomotopy).curry).curry := by
      ext r s t; simp
    rw [hcomp]
    exact ((((CStarCone.toPath G).uncurry.comp warpHomotopy).curry).curry).continuous

private theorem evalOne_warpConePath (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁)
    (y : MappingCone Φ.toHom) (r : I) :
    CStarCone.evalOne (warpConePath y.snd r) = Φ.toHom y.fst := by
  ext t; simp [warpConePath, Function.uncurry, warpHomotopy_one_mid, ← y.eq_evalOne]

private theorem inclZeroSquare_evalZeroMap_eq (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁)
    (y : MappingCone Φ.toHom) (p : I × I) :
    inclZeroSquare Φ (evalZeroMap Φ y) p =
      (CStarCone.toPath y.snd).uncurry (scaleClamp p, shiftClamp p) := by
  have hpath0 (u : I) : CStarCone.toPath (evalZeroMap Φ y).snd u = CStarCone.toPath y.snd u 0 := by
    by_cases hu0 : u = 0
    · subst hu0; simp
    · obtain ⟨w, rfl⟩ := notMem_compl_iff.mp fun hw =>
        hu0 ((notMem_range_iocToUnitInterval_iff u).mp hw)
      simp
  simp only [inclZeroSquare, NonUnitalStarAlgHom.coe_mk', NonUnitalAlgHom.coe_mk,
    ContinuousMap.coe_mk, ContinuousMap.uncurry_apply, Function.uncurry_apply_pair]
  split_ifs with hp
  · rw [shiftClamp_of_le_one hp, hpath0]
  · rw [scaleClamp_of_ge_one (not_le.mp hp).le, fst_evalZeroMap_apply, CStarCone.toPath_apply_one,
      ← y.eq_evalOne]

/-- Homotopy from `(inclZeroMap Φ).comp (evalZeroMap Φ)` to `.id ℂ (MappingCone Φ.toHom)`. -/
private def inclZeroCompEvalZeroHomotopy (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    NonUnitalStarAlgHom.Homotopy ((inclZeroMap Φ).comp (evalZeroMap Φ))
      (.id ℂ (MappingCone Φ.toHom)) where
  toHom :=
    { toFun y :=
        { toFun r := mk Φ.toHom y.fst (warpConePath y.snd r) (evalOne_warpConePath Φ y r).symm
          continuous_toFun := continuous_iff.mpr
            ⟨by simp_rw [fst_mk]; exact continuous_const,
             by simp_rw [snd_mk]; exact (warpConePath y.snd).continuous⟩ }
      map_smul' c y := by
        ext r : 1; refine ext (by simp) ?_; ext s t
        simp [warpConePath, Function.uncurry, map_smul]
      map_zero' := by
        ext r : 1; refine ext (by simp) ?_; ext s t; simp [warpConePath, Function.uncurry]
      map_add' x y := by
        ext r : 1; refine ext (by simp) ?_; ext s t
        simp [warpConePath, Function.uncurry, map_add]
      map_mul' x y := by
        ext r : 1; refine ext (by simp) ?_; ext s t
        simp [warpConePath, Function.uncurry, map_mul]
      map_star' y := by
        ext r : 1; refine ext (by simp) ?_; ext s t
        simp [warpConePath, Function.uncurry, map_star] }
  eval_zero y := by
    refine ext (by simp) ?_; ext s t
    have heq := inclZeroSquare_evalZeroMap_eq Φ y (iocToUnitInterval s, t)
    simp only [ContinuousMap.uncurry_apply, Function.uncurry_apply_pair] at heq
    simp [warpConePath, Function.uncurry, warpHomotopy_zero_left, inclZeroMap, heq]
  eval_one y := by
    refine ext (by simp) ?_; ext s t
    simp [warpConePath, Function.uncurry, warpHomotopy_one_left]

/-- Endpoint evaluation at `0` is a `⋆`-homotopy equivalence
`MappingCone Φ.toHom → MappingCone φ₀`. -/
def evalZeroHomotopyEquiv (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    StarHomotopyEquiv (MappingCone Φ.toHom) (MappingCone φ₀) where
  toFun := evalZeroMap Φ
  invFun := inclZeroMap Φ
  left_inv := ⟨inclZeroCompEvalZeroHomotopy Φ⟩
  right_inv := by rw [evalZeroMap_comp_inclZeroMap]; exact ⟨.refl _⟩

@[simp]
theorem evalZeroHomotopyEquiv_toFun (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (evalZeroHomotopyEquiv Φ).toFun = evalZeroMap Φ := (rfl)

@[simp]
theorem evalZeroHomotopyEquiv_invFun (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (evalZeroHomotopyEquiv Φ).invFun = inclZeroMap Φ := (rfl)

/-- Time-reversal `⋆`-isomorphism `MappingCone Φ.toHom ≃⋆ₐ[ℂ] MappingCone Φ.symm.toHom` intertwining
`evalOneMap Φ` with `evalZeroMap Φ.symm`. -/
def symmEquiv (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    MappingCone Φ.toHom ≃⋆ₐ[ℂ] MappingCone Φ.symm.toHom :=
  StarAlgEquiv.ofNonUnitalStarAlgHom
    (map Φ.toHom Φ.symm.toHom (.id ℂ A)
      (unitInterval.symmHomeomorph.compNonUnitalStarAlgEquiv' ℂ B).toNonUnitalStarAlgHom
      (by ext a t; simp))
    (map Φ.symm.toHom Φ.toHom (.id ℂ A)
      (unitInterval.symmHomeomorph.compNonUnitalStarAlgEquiv' ℂ B).toNonUnitalStarAlgHom
      (by ext a t; simp))
    (by ext x : 1; refine ext (by simp) ?_; ext s t; simp)
    (by ext x : 1; refine ext (by simp) ?_; ext s t; simp)

@[simp]
theorem fst_symmEquiv_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone Φ.toHom) :
    (symmEquiv Φ x).fst = x.fst := by simp [symmEquiv]

@[simp]
theorem snd_symmEquiv_apply (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) (x : MappingCone Φ.toHom)
    (s : Ioc (0 : ℝ) 1) (t : I) : (symmEquiv Φ x).snd s t = x.snd s (σ t) := by
  simp [symmEquiv]

theorem evalOneMap_eq_evalZeroMap_comp_symmEquiv (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    evalOneMap Φ = (evalZeroMap Φ.symm).comp (symmEquiv Φ).toNonUnitalStarAlgHom := by
  ext x : 1; refine ext (by simp) ?_; ext s; simp [symmEquiv]

/-- Endpoint evaluation at `1` is a `⋆`-homotopy equivalence
`MappingCone Φ.toHom → MappingCone φ₁`. -/
def evalOneHomotopyEquiv (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    StarHomotopyEquiv (MappingCone Φ.toHom) (MappingCone φ₁) := by
  let e := (StarHomotopyEquiv.ofStarAlgEquiv (symmEquiv Φ)).trans (evalZeroHomotopyEquiv Φ.symm)
  have htoFun : e.toFun = evalOneMap Φ := by
    simpa [e] using (evalOneMap_eq_evalZeroMap_comp_symmEquiv Φ).symm
  exact
    { toFun := evalOneMap Φ
      invFun := e.invFun
      left_inv := by rw [← htoFun]; exact e.left_inv
      right_inv := by rw [← htoFun]; exact e.right_inv }

@[simp]
theorem evalOneHomotopyEquiv_toFun (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    (evalOneHomotopyEquiv Φ).toFun = evalOneMap Φ := (rfl)

/-- A homotopy `Φ` between `φ₀` and `φ₁` induces a `⋆`-homotopy equivalence between `MappingCone φ₀`
and `MappingCone φ₁`. -/
def homotopyEquiv (Φ : NonUnitalStarAlgHom.Homotopy φ₀ φ₁) :
    StarHomotopyEquiv (MappingCone φ₀) (MappingCone φ₁) :=
  (evalZeroHomotopyEquiv Φ).symm.trans (evalOneHomotopyEquiv Φ)

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
