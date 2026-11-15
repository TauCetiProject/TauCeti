/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.AsymptoticUnitaryEquivalence.Multiplier
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FreeLoop
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# Separation of asymptotic and strong asymptotic unitary equivalence

On `B = C(S¹, M₂(ℂ))`, let `windingUnitary` be the unitary loop `ζ ↦ diag(ζ, 1)` of winding number
`1`, and let `windingConjHom = Ad(windingUnitary) : B →⋆ₙₐ[ℂ] B`. The identity endomorphism of `B`
and `windingConjHom` are asymptotically unitarily equivalent via the constant path at
`windingUnitary`, yet they are *not* strongly asymptotically unitarily equivalent (and hence neither
strongly unitization nor strongly multiplier asymptotically unitarily equivalent).

Indeed, if a path `u : C(ℝ≥0, unitary B)` with `u 0 = 1` implemented strong asymptotic unitary
equivalence even after precomposing with the constant-matrix inclusion `constHom : M₂(ℂ) →⋆ₙₐ[ℂ] B`,
then `w t := star windingUnitary * u t` would asymptotically commute with `M₂(ℂ)` while keeping
winding number `-1` in determinant. At large `t`, `w t` is close to a scalar loop `ζ ↦ a(ζ) • 1`,
forcing its determinant loop to have even degree `2 * deg(a / ‖a‖)`, contradicting `-1`.
-/

public section

noncomputable section

open Filter Topology
open scoped ComplexOrder CStarAlgebra MultiplierAlgebra NNReal unitInterval

namespace TauCeti.AsymptoticUnitaryEquivalenceExample

/-- `2 × 2` complex matrices equipped with the C⋆-algebra norm. -/
abbrev Mat₂ := CStarMatrix (Fin 2) (Fin 2) ℂ

/-- Continuous loops `S¹ → M₂(ℂ)` as a unital C⋆-algebra. -/
abbrev CircleMat₂ := C(Circle, Mat₂)

private def evalUnitary (u : unitary CircleMat₂) (ζ : Circle) : unitary Mat₂ :=
  ⟨(u : CircleMat₂) ζ, Unitary.mem_iff.mpr
    ⟨congrArg (fun f : CircleMat₂ ↦ f ζ) u.2.1, congrArg (fun f : CircleMat₂ ↦ f ζ) u.2.2⟩⟩

private theorem continuous_ofMatrix_symm :
    Continuous (CStarMatrix.ofMatrix.symm : Mat₂ → Matrix (Fin 2) (Fin 2) ℂ) := by
  have heq : (CStarMatrix.ofMatrix.symm : Mat₂ → Matrix (Fin 2) (Fin 2) ℂ) =
      CStarMatrix.ofMatrixL.symm :=
    funext fun M ↦ CStarMatrix.ofMatrix.symm_apply_eq.mpr <| by
      rw [congrFun CStarMatrix.ofMatrix_eq_ofMatrixL]
      exact (CStarMatrix.ofMatrixL.apply_symm_apply M).symm
  rw [heq]
  exact CStarMatrix.ofMatrixL.symm.continuous

private theorem norm_det_unitary (u : unitary CircleMat₂) (ζ : Circle) :
    ‖(CStarMatrix.ofMatrix.symm ((u : CircleMat₂) ζ)).det‖ = 1 := by
  let e := (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin 2) (A := ℂ)).symm
  have he (M : Mat₂) : CStarMatrix.ofMatrix.symm M = e M :=
    CStarMatrix.ofMatrix.symm_apply_eq.mpr <| by
      rw [congrFun CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv]
      exact (CStarMatrix.ofMatrixStarAlgEquiv.apply_symm_apply M).symm
  rw [he]
  have hmul : (u : CircleMat₂) ζ * star ((u : CircleMat₂) ζ) = 1 :=
    congrArg (fun f : CircleMat₂ ↦ f ζ) u.2.2
  have hdet : (e ((u : CircleMat₂) ζ)).det * star (e ((u : CircleMat₂) ζ)).det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.star_eq_conjTranspose, ← map_star,
      ← Matrix.det_mul, ← map_mul, hmul, map_one, Matrix.det_one]
  have hsq : ‖(e ((u : CircleMat₂) ζ)).det‖ * ‖(e ((u : CircleMat₂) ζ)).det‖ = 1 := by
    rw [← CStarRing.norm_self_mul_star, hdet, norm_one]
  nlinarith [norm_nonneg (e ((u : CircleMat₂) ζ)).det]

/-- Pointwise `2 × 2` determinant as a free loop `S¹ → S¹` for any `u : unitary C(S¹, M₂(ℂ))`. -/
private def detLoop (u : unitary CircleMat₂) : C(Circle, Circle) where
  toFun ζ := ⟨(CStarMatrix.ofMatrix.symm ((u : CircleMat₂) ζ)).det,
    mem_sphere_zero_iff_norm.2 (norm_det_unitary u ζ)⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_ofMatrix_symm.comp (u : CircleMat₂).continuous).matrix_det _

@[simp]
private theorem detLoop_coe_apply (u : unitary CircleMat₂) (ζ : Circle) :
    (detLoop u ζ : ℂ) = (CStarMatrix.ofMatrix.symm ((u : CircleMat₂) ζ)).det :=
  rfl

private theorem continuous_detLoop : Continuous detLoop := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  refine Continuous.subtype_mk ?_ _
  exact (continuous_ofMatrix_symm.comp
    (continuous_eval.comp (continuous_subtype_val.prodMap continuous_id))).matrix_det

private def windingMap : CircleMat₂ where
  toFun ζ := CStarMatrix.ofMatrix !![(ζ : ℂ), 0; 0, 1]
  continuous_toFun := by
    refine CStarMatrix.ofMatrixL.continuous.comp (continuous_matrix fun i j ↦ ?_)
    fin_cases i <;> fin_cases j <;> fun_prop

@[simp]
private theorem windingMap_apply (ζ : Circle) :
    windingMap ζ = CStarMatrix.ofMatrix !![(ζ : ℂ), 0; 0, 1] :=
  rfl

/-- The unitary loop `ζ ↦ diag(ζ, 1)` in `C(S¹, M₂(ℂ))` of determinant winding number `1`. -/
def windingUnitary : unitary CircleMat₂ :=
  ⟨windingMap, by
    rw [Unitary.mem_iff]
    have hz (ζ : Circle) : (starRingEnd ℂ) (ζ : ℂ) * (ζ : ℂ) = 1 := by
      rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
    have hz' (ζ : Circle) : (ζ : ℂ) * (starRingEnd ℂ) (ζ : ℂ) = 1 := by
      simpa [mul_comm] using hz ζ
    constructor <;>
      · ext ζ i j
        fin_cases i <;> fin_cases j <;>
          simp [CStarMatrix.mul_apply, CStarMatrix.star_apply, Fin.sum_univ_two, hz, hz']⟩

/-- Inner automorphism `f ↦ windingUnitary * f * star windingUnitary` of `C(S¹, M₂(ℂ))` as a
nonunital `⋆`-homomorphism. -/
def windingConjHom : CircleMat₂ →⋆ₙₐ[ℂ] CircleMat₂ where
  toFun f := (windingUnitary : CircleMat₂) * f * star (windingUnitary : CircleMat₂)
  map_smul' c f := by ext ζ; simp [mul_assoc]
  map_zero' := by ext ζ; simp
  map_add' f g := by ext ζ; simp [mul_add, add_mul]
  map_mul' f g := by
    refine ContinuousMap.ext fun ζ ↦ ?_
    have h : star ((windingUnitary : CircleMat₂) ζ) * (windingUnitary : CircleMat₂) ζ = 1 :=
      congrArg (fun x : CircleMat₂ ↦ x ζ) windingUnitary.2.1
    simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply]
    calc
      (windingUnitary : CircleMat₂) ζ * (f ζ * g ζ) * star ((windingUnitary : CircleMat₂) ζ)
        = (windingUnitary : CircleMat₂) ζ * f ζ *
            (star ((windingUnitary : CircleMat₂) ζ) * (windingUnitary : CircleMat₂) ζ) * g ζ *
            star ((windingUnitary : CircleMat₂) ζ) := by
          rw [h, mul_one]
          noncomm_ring
      _ = (windingUnitary : CircleMat₂) ζ * f ζ * star ((windingUnitary : CircleMat₂) ζ) *
            ((windingUnitary : CircleMat₂) ζ * g ζ * star ((windingUnitary : CircleMat₂) ζ)) := by
          noncomm_ring
  map_star' f := by ext ζ; simp [mul_assoc]

/-- Applying `windingConjHom` conjugates by `windingUnitary`. -/
@[simp]
theorem windingConjHom_apply (f : CircleMat₂) :
    windingConjHom f =
      (windingUnitary : CircleMat₂) * f * star (windingUnitary : CircleMat₂) := by
  rfl

/-- Inclusion of constant `2 × 2` matrices into `C(S¹, M₂(ℂ))`. -/
def constHom : Mat₂ →⋆ₙₐ[ℂ] CircleMat₂ where
  toFun M := ContinuousMap.const Circle M
  map_smul' _ _ := by ext; simp
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by ext; simp
  map_star' _ := by ext; simp

/-- `windingUnitary` does not lie in the identity path component of `unitary C(S¹, M₂(ℂ))`. -/
theorem not_joined_one_windingUnitary : ¬ Joined (1 : unitary CircleMat₂) windingUnitary := by
  intro h
  have hdeg := Circle.degree_toBasedLoop_eq_of_joined (h.map continuous_detLoop)
  have h1 : detLoop 1 = ⟨(· ^ (0 : ℤ)), continuous_zpow 0⟩ := by
    ext ζ
    dsimp
    simp [Matrix.det_fin_two]
  have hw : detLoop windingUnitary = ⟨(· ^ (1 : ℤ)), continuous_zpow 1⟩ := by
    ext ζ
    dsimp
    simp [windingUnitary, Matrix.det_fin_two]
  rw [h1, hw, Circle.degree_toBasedLoop_zpow, Circle.degree_toBasedLoop_zpow] at hdeg
  omega

/-- The identity on `C(S¹, M₂(ℂ))` and `windingConjHom` are asymptotically unitarily equivalent. -/
theorem asymptoticallyUnitarilyEquivalent_id_windingConjHom :
    AsymptoticallyUnitarilyEquivalent (A := CircleMat₂) (B := CircleMat₂)
      (NonUnitalStarAlgHom.id ℂ CircleMat₂) windingConjHom :=
  AsymptoticallyUnitarilyEquivalent.of_unitary windingUnitary fun f ↦ by simp

/-- The identity on `C(S¹, M₂(ℂ))` and `windingConjHom` are unitization asymptotically unitarily
equivalent. -/
theorem unitizationAsymptoticallyUnitarilyEquivalent_id_windingConjHom :
    UnitizationAsymptoticallyUnitarilyEquivalent (A := CircleMat₂) (B := CircleMat₂)
      (NonUnitalStarAlgHom.id ℂ CircleMat₂) windingConjHom :=
  UnitizationAsymptoticallyUnitarilyEquivalent.iff_asymptoticallyUnitarilyEquivalent.mpr
    asymptoticallyUnitarilyEquivalent_id_windingConjHom

/-- The identity on `C(S¹, M₂(ℂ))` and `windingConjHom` are multiplier asymptotically unitarily
equivalent. -/
theorem multiplierAsymptoticallyUnitarilyEquivalent_id_windingConjHom :
    MultiplierAsymptoticallyUnitarilyEquivalent (A := CircleMat₂) (B := CircleMat₂)
      (NonUnitalStarAlgHom.id ℂ CircleMat₂) windingConjHom :=
  MultiplierAsymptoticallyUnitarilyEquivalent.iff_asymptoticallyUnitarilyEquivalent.mpr
    asymptoticallyUnitarilyEquivalent_id_windingConjHom

private def p₀ : Mat₂ := CStarMatrix.ofMatrix !![1, 0; 0, 0]

private def e₀₁ : Mat₂ := CStarMatrix.ofMatrix !![0, 1; 0, 0]

private theorem norm_sq_entry_sub_det_lt_one {W : Mat₂} (hW : ‖W‖ ≤ 1)
    (hp : ‖W * p₀ - p₀ * W‖ < 1 / 4) (he : ‖W * e₀₁ - e₀₁ * W‖ < 1 / 4) :
    ‖W 0 0 ^ 2 - (CStarMatrix.ofMatrix.symm W).det‖ < 1 := by
  have hb : ‖W 0 1‖ < 1 / 4 := by
    have h01 : (W * p₀ - p₀ * W) 0 1 = -W 0 1 := by
      simp [p₀, CStarMatrix.mul_apply, Fin.sum_univ_two]
    calc ‖W 0 1‖ = ‖-W 0 1‖ := (norm_neg _).symm
      _ = ‖(W * p₀ - p₀ * W) 0 1‖ := by rw [h01]
      _ ≤ ‖W * p₀ - p₀ * W‖ := CStarMatrix.norm_entry_le_norm
      _ < 1 / 4 := hp
  have hc : ‖W 1 0‖ < 1 / 4 := by
    have h10 : (W * p₀ - p₀ * W) 1 0 = W 1 0 := by
      simp [p₀, CStarMatrix.mul_apply, Fin.sum_univ_two]
    calc ‖W 1 0‖ = ‖(W * p₀ - p₀ * W) 1 0‖ := by rw [h10]
      _ ≤ ‖W * p₀ - p₀ * W‖ := CStarMatrix.norm_entry_le_norm
      _ < 1 / 4 := hp
  have had : ‖W 0 0 - W 1 1‖ < 1 / 4 := by
    have h01 : (W * e₀₁ - e₀₁ * W) 0 1 = W 0 0 - W 1 1 := by
      simp [e₀₁, CStarMatrix.mul_apply, Fin.sum_univ_two]
    calc ‖W 0 0 - W 1 1‖ = ‖(W * e₀₁ - e₀₁ * W) 0 1‖ := by rw [h01]
      _ ≤ ‖W * e₀₁ - e₀₁ * W‖ := CStarMatrix.norm_entry_le_norm
      _ < 1 / 4 := he
  have ha : ‖W 0 0‖ ≤ 1 := CStarMatrix.norm_entry_le_norm.trans hW
  have hid : W 0 0 ^ 2 - (CStarMatrix.ofMatrix.symm W).det =
      W 0 0 * (W 0 0 - W 1 1) + W 0 1 * W 1 0 := by
    simp only [Matrix.det_fin_two, CStarMatrix.ofMatrix_symm_apply]
    ring
  rw [hid]
  calc
    ‖W 0 0 * (W 0 0 - W 1 1) + W 0 1 * W 1 0‖
      ≤ ‖W 0 0 * (W 0 0 - W 1 1)‖ + ‖W 0 1 * W 1 0‖ := norm_add_le _ _
    _ = ‖W 0 0‖ * ‖W 0 0 - W 1 1‖ + ‖W 0 1‖ * ‖W 1 0‖ := by rw [norm_mul, norm_mul]
    _ < 1 * (1 / 4) + (1 / 4) * (1 / 4) := by
        nlinarith [norm_nonneg (W 0 0), norm_nonneg (W 0 0 - W 1 1),
          norm_nonneg (W 0 1), norm_nonneg (W 1 0)]
    _ < 1 := by norm_num

private theorem even_degree_detLoop_of_close (w : unitary CircleMat₂)
    (h : ∀ ζ : Circle,
      ‖((w : CircleMat₂) ζ) 0 0 ^ 2 - (CStarMatrix.ofMatrix.symm ((w : CircleMat₂) ζ)).det‖ < 1) :
    ∃ k : ℤ, Circle.degree (detLoop w).toBasedLoop = 2 * k := by
  let a : Circle → ℂ := fun ζ ↦ ((w : CircleMat₂) ζ) 0 0
  have ha_cont : Continuous a := (continuous_apply 0).comp ((continuous_apply 0).comp
    (w : CircleMat₂).continuous)
  have ha_pos (ζ : Circle) : 0 < ‖a ζ‖ := by
    by_contra hle
    have ha0 : a ζ = 0 := norm_eq_zero.mp (le_antisymm (not_lt.mp hle) (norm_nonneg _))
    have hlt := h ζ
    simp only [a] at ha0
    rw [ha0, zero_pow two_ne_zero, zero_sub, norm_neg, norm_det_unitary] at hlt
    exact lt_irrefl 1 hlt
  let α : C(Circle, Circle) :=
    { toFun ζ := ⟨a ζ / ‖a ζ‖, mem_sphere_zero_iff_norm.2 <| by
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
          div_self (ha_pos ζ).ne']⟩
      continuous_toFun := Continuous.subtype_mk (ha_cont.div
        (Complex.continuous_ofReal.comp ha_cont.norm) fun ζ ↦
          Complex.ofReal_ne_zero.2 (ha_pos ζ).ne') _ }
  have hα (ζ : Circle) : (α ζ : ℂ) = a ζ / ‖a ζ‖ := rfl
  refine ⟨Circle.degree α.toBasedLoop, ?_⟩
  have hdeg : Circle.degree (α.toBasedLoop.map (continuous_pow 2)) =
      Circle.degree (detLoop w).toBasedLoop := by
    refine Circle.degree_eq_of_norm_sub_lt (α.toBasedLoop.map (continuous_pow 2))
      (detLoop w).toBasedLoop (z := fun s ↦ a (TauCeti.unitToCircle s) ^ 2)
      (w := fun s ↦ (detLoop w (TauCeti.unitToCircle s) : ℂ))
      (fun s ↦ ?_) (fun s ↦ ?_) (fun s ↦ ?_)
    · simp [hα, div_pow, Complex.ofReal_pow]
    · simp [norm_det_unitary]
    · simpa [a, norm_det_unitary] using h (TauCeti.unitToCircle s)
  rw [Circle.degree_map_pow] at hdeg
  exact_mod_cast hdeg.symm

private theorem eventually_commutator_lt {u : C(ℝ≥0, unitary CircleMat₂)}
    (hu : ∀ M : Mat₂, Tendsto (fun t ↦ (u t : CircleMat₂) * constHom M * star (u t : CircleMat₂))
      atTop (𝓝 ((windingConjHom.comp constHom) M)))
    (M : Mat₂) :
    ∀ᶠ t : ℝ≥0 in atTop, ∀ ζ : Circle,
      ‖((star windingUnitary * u t : unitary CircleMat₂) : CircleMat₂) ζ * M -
        M * ((star windingUnitary * u t : unitary CircleMat₂) : CircleMat₂) ζ‖ < 1 / 4 := by
  have hb := (ContinuousMap.isUniformEmbedding_equivBoundedOfCompact Circle Mat₂
    ).isInducing.tendsto_nhds_iff.mp (hu M)
  filter_upwards [Metric.tendsto_nhds.mp hb (1 / 4) (by norm_num)] with t ht ζ
  set V : Mat₂ := (windingUnitary : CircleMat₂) ζ
  set U : Mat₂ := (u t : CircleMat₂) ζ
  have hpt : ‖U * M * star U - V * M * star V‖ < 1 / 4 := by
    have hd := (BoundedContinuousFunction.dist_coe_le_dist ζ).trans_lt ht
    simpa only [Function.comp_def, ContinuousMap.equivBoundedOfCompact_apply,
      BoundedContinuousFunction.mkOfCompact_apply, NonUnitalStarAlgHom.comp_apply,
      windingConjHom_apply, constHom, ContinuousMap.mul_apply, ContinuousMap.star_apply,
      NonUnitalStarAlgHom.coe_mk', NonUnitalAlgHom.coe_mk, ContinuousMap.const_apply,
      dist_eq_norm] using hd
  have hV : star V * V = 1 := congrArg (fun f : CircleMat₂ ↦ f ζ) windingUnitary.2.1
  have hU : star U * U = 1 := congrArg (fun f : CircleMat₂ ↦ f ζ) (u t).2.1
  have hid : ((star windingUnitary * u t : unitary CircleMat₂) : CircleMat₂) ζ * M -
      M * ((star windingUnitary * u t : unitary CircleMat₂) : CircleMat₂) ζ =
      star V * (U * M * star U - V * M * star V) * U := by
    simp only [Submonoid.coe_mul, Unitary.coe_star, ContinuousMap.mul_apply,
      ContinuousMap.star_apply]
    have h1 : star V * U * M = star V * (U * M * star U) * U := by
      calc star V * U * M = star V * U * M * (star U * U) := by rw [hU, mul_one]
        _ = star V * (U * M * star U) * U := by noncomm_ring
    have h2 : M * (star V * U) = star V * (V * M * star V) * U := by
      calc M * (star V * U) = (star V * V) * M * (star V * U) := by rw [hV, one_mul]
        _ = star V * (V * M * star V) * U := by noncomm_ring
    rw [h1, h2]
    noncomm_ring
  rw [hid]
  have hnorm : ‖star V * (U * M * star U - V * M * star V) * U‖ =
      ‖U * M * star U - V * M * star V‖ :=
    (CStarRing.norm_mul_coe_unitary _ (evalUnitary (u t) ζ)).trans
      (CStarRing.norm_coe_unitary_mul (star (evalUnitary windingUnitary ζ)) _)
  exact hnorm.trans_lt hpt

/-- Even on the constant subalgebra `constHom : M₂(ℂ) →⋆ₙₐ[ℂ] C(S¹, M₂(ℂ))`, `constHom` and
`windingConjHom.comp constHom` are not strongly asymptotically unitarily equivalent. -/
theorem not_stronglyAsymptoticallyUnitarilyEquivalent_constHom :
    ¬ StronglyAsymptoticallyUnitarilyEquivalent (A := Mat₂) (B := CircleMat₂)
        constHom (windingConjHom.comp constHom) := by
  rw [stronglyAsymptoticallyUnitarilyEquivalent_def]
  rintro ⟨u, hu0, hu⟩
  obtain ⟨t, hpt, het⟩ :=
    ((eventually_commutator_lt hu p₀).and (eventually_commutator_lt hu e₀₁)).exists
  let w : C(ℝ≥0, unitary CircleMat₂) :=
    ⟨fun s ↦ star windingUnitary * u s, continuous_const.mul u.continuous⟩
  have hjoined : Joined (w 0) (w t) :=
    ⟨{ toFun s := w ⟨(s : ℝ) * (t : ℝ), mul_nonneg s.2.1 t.2⟩
       continuous_toFun := w.continuous.comp (Continuous.subtype_mk
         (continuous_subtype_val.mul continuous_const) _)
       source' := congrArg w (Subtype.ext (zero_mul (t : ℝ)))
       target' := congrArg w (Subtype.ext (one_mul (t : ℝ))) }⟩
  have hdeg_wt : Circle.degree (detLoop (w t)).toBasedLoop = -1 := by
    rw [← Circle.degree_toBasedLoop_eq_of_joined (hjoined.map continuous_detLoop)]
    have hw0 : detLoop (w 0) = ⟨(· ^ (-1 : ℤ)), continuous_zpow (-1)⟩ := by
      ext ζ
      dsimp
      simp [w, hu0, windingUnitary, Matrix.det_fin_two, CStarMatrix.star_apply,
        ← Circle.coe_inv, Circle.coe_inv_eq_conj]
    rw [hw0, Circle.degree_toBasedLoop_zpow]
  have hnorm_wt (ζ : Circle) : ‖((w t : unitary CircleMat₂) : CircleMat₂) ζ‖ ≤ 1 :=
    (CStarRing.norm_coe_unitary (evalUnitary (w t) ζ)).le
  obtain ⟨k, hk⟩ := even_degree_detLoop_of_close (w t) fun ζ ↦
    norm_sq_entry_sub_det_lt_one (hnorm_wt ζ) (hpt ζ) (het ζ)
  omega

/-- The identity on `C(S¹, M₂(ℂ))` and `windingConjHom` are not strongly asymptotically unitarily
equivalent, separating asymptotic from strong asymptotic unitary equivalence. -/
theorem not_stronglyAsymptoticallyUnitarilyEquivalent_id_windingConjHom :
    ¬ StronglyAsymptoticallyUnitarilyEquivalent (A := CircleMat₂) (B := CircleMat₂)
      (NonUnitalStarAlgHom.id ℂ CircleMat₂) windingConjHom := by
  intro h
  exact not_stronglyAsymptoticallyUnitarilyEquivalent_constHom <| by
    simpa only [NonUnitalStarAlgHom.id_comp] using h.precomp constHom

/-- The identity on `C(S¹, M₂(ℂ))` and `windingConjHom` are not strongly unitization asymptotically
unitarily equivalent. -/
theorem not_unitizationStronglyAsymptoticallyUnitarilyEquivalent_id_windingConjHom :
    ¬ UnitizationStronglyAsymptoticallyUnitarilyEquivalent (A := CircleMat₂) (B := CircleMat₂)
      (NonUnitalStarAlgHom.id ℂ CircleMat₂) windingConjHom := by
  open UnitizationStronglyAsymptoticallyUnitarilyEquivalent in
  exact fun h ↦ not_stronglyAsymptoticallyUnitarilyEquivalent_id_windingConjHom
    ((iff_stronglyAsymptoticallyUnitarilyEquivalent (A := CircleMat₂) (B := CircleMat₂)).mp h)

/-- The identity on `C(S¹, M₂(ℂ))` and `windingConjHom` are not strongly multiplier asymptotically
unitarily equivalent. -/
theorem not_multiplierStronglyAsymptoticallyUnitarilyEquivalent_id_windingConjHom :
    ¬ MultiplierStronglyAsymptoticallyUnitarilyEquivalent (A := CircleMat₂) (B := CircleMat₂)
      (NonUnitalStarAlgHom.id ℂ CircleMat₂) windingConjHom := by
  open MultiplierStronglyAsymptoticallyUnitarilyEquivalent in
  exact fun h ↦ not_stronglyAsymptoticallyUnitarilyEquivalent_id_windingConjHom
    ((iff_stronglyAsymptoticallyUnitarilyEquivalent (A := CircleMat₂) (B := CircleMat₂)).mp h)

end TauCeti.AsymptoticUnitaryEquivalenceExample
