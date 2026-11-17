/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ContractionAlongMap.Family
public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Homotopy operator along a moving family of maps

For a family of maps `P : M × ℝ → N` between manifolds (possibly with boundary or corners), or a
family `P : M × ↥J → N` indexed by an open parameter interval `J : TopologicalSpace.Opens ℝ`
containing `[0, 1]`, integrating the family contraction `TauCeti.mfamilyContraction` over
`t ∈ [0, 1]` yields the moving-pullback homotopy operator

`(K_P ω)_x = ∫ t in (0 : ℝ)..1, C_(p_t, V_t) ω_x`

(`TauCeti.mfamilyHomotopyOperator`, `TauCeti.mfamilyHomotopyOperatorOpens`).

Wherever `P` is differentiable on `M × (0, 1)`, `K_P ω` coincides with the cylinder homotopy
operator `TauCeti.homotopyOperator` applied to the pullback of `ω` along the cylinder map
`M × [0, 1] → N` (`TauCeti.mfamilyHomotopyOperator_eq_homotopyOperator_mpullback`). When `M` and
`N` are `C²`, `P` is `C²` on `M × [0, 1]`, the coefficient space `F` is complete, and `ω` is a `C¹`
form on `N`, this gives the cochain-homotopy identity

`d(K_P ω) + K_P(dω) = p₁^* ω - p₀^* ω`

without requiring invertibility of the slices `p_t`.

## Main declarations

* `TauCeti.mfamilyHomotopyOperator`: homotopy operator of a family `P : M × ℝ → N`.
* `TauCeti.mfamilyHomotopyOperator_apply_eq_zero`, `TauCeti.mfamilyHomotopyOperator_comp_fst`:
  vanishing at time-stationary points and for time-independent families.
* `TauCeti.mpullback_subtype_val_mfamilyHomotopyOperator`,
  `TauCeti.mpullback_inclusion_mfamilyHomotopyOperator`,
  `TauCeti.mfamilyHomotopyOperator_mpullback_subtype_val`,
  `TauCeti.mfamilyHomotopyOperator_mpullback_inclusion`: open-subset restrictions on `M` and `N`.
* `TauCeti.mfamilyHomotopyOperator_comp_prodMap_id`,
  `TauCeti.mfamilyHomotopyOperator_comp_prodMap_id_of_isSmoothForm`,
  `TauCeti.mfamilyHomotopyOperator_mpullback`: source and target naturality.
* `TauCeti.mfamilyHomotopyOperator_eq_homotopyOperator_mpullback_at`,
  `TauCeti.mfamilyHomotopyOperator_eq_homotopyOperator_mpullback`: identification with
  `TauCeti.homotopyOperator` of the cylinder pullback.
* `TauCeti.IsSmoothForm.mfamilyHomotopyOperator`,
  `TauCeti.mextDeriv_mfamilyHomotopyOperator_add_mfamilyHomotopyOperator_mextDeriv`,
  `TauCeti.mextDeriv_mfamilyHomotopyOperator`: regularity and cochain-homotopy identity.
* `TauCeti.mfamilyHomotopyOperatorOpens` and its matching stationarity, open-restriction,
  naturality, cylinder-identification, regularity, and cochain-homotopy theorems for
  `P : M × ↥J → N` with `Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapters 14 and 17.
-/

public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace ContinuousAlternatingMap
open scoped Manifold Topology

namespace TauCeti

variable {E H M E' H' N E'' H'' L F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace N] [ChartedSpace H' N] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  [TopologicalSpace L] [ChartedSpace H'' L] {I'' : ModelWithCorners ℝ E'' H''}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ}

/-! ### Homotopy operator of a family of maps `P : M × ℝ → N` -/

section Homotopy

private def mfamilyIntegrand (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (P : M × ℝ → N) (ω : RoughForm I' N F (k + 1)) (x : M) (t : ℝ) : E [⋀^Fin k]→L[ℝ] F :=
  mfamilyContraction I I' P t ω x

/-- **Homotopy operator of a moving map `P : M × ℝ → N`.** Integrates
`mfamilyContraction I I' P t ω` over `t ∈ [0, 1]`. When `M, N` are `C²` manifolds, `P` is `C²` on
`M × [0, 1]`, `F` is complete, and `ω` is `C¹`, this satisfies
`d(K_P ω) + K_P(dω) = p₁^* ω - p₀^* ω` without invertibility of `p_t`. -/
def mfamilyHomotopyOperator (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (P : M × ℝ → N) (ω : RoughForm I' N F (k + 1)) : RoughForm I M F k :=
  fun x ↦ intervalIntegral (E := E [⋀^Fin k]→L[ℝ] F) (mfamilyIntegrand I I' P ω x) 0 1 volume

/-- Pointwise evaluation of `mfamilyHomotopyOperator` as an integral over `[0, 1]`. -/
theorem mfamilyHomotopyOperator_apply (P : M × ℝ → N) (ω : RoughForm I' N F (k + 1)) (x : M) :
    mfamilyHomotopyOperator I I' P ω x =
      intervalIntegral (E := E [⋀^Fin k]→L[ℝ] F)
        (fun t ↦ (mfamilyContraction I I' P t ω x : E [⋀^Fin k]→L[ℝ] F)) 0 1 volume := (rfl)

/-- `mfamilyHomotopyOperator` sends the zero form to zero. -/
@[simp]
theorem mfamilyHomotopyOperator_zero (P : M × ℝ → N) :
    mfamilyHomotopyOperator I I' P (0 : RoughForm I' N F (k + 1)) = 0 := by
  funext x
  rw [mfamilyHomotopyOperator_apply]
  have hfun : (fun t : ℝ ↦ (mfamilyContraction I I' P t (0 : RoughForm I' N F (k + 1)) x :
      E [⋀^Fin k]→L[ℝ] F)) = fun _ ↦ (0 : E [⋀^Fin k]→L[ℝ] F) :=
    funext fun t ↦ by rw [mfamilyContraction_zero]; rfl
  rw [hfun, intervalIntegral.integral_zero]
  rfl

/-- `mfamilyHomotopyOperator` commutes with real scalar multiplication. -/
@[simp]
theorem mfamilyHomotopyOperator_smul (P : M × ℝ → N) (c : ℝ) (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperator I I' P (c • ω) = c • mfamilyHomotopyOperator I I' P ω := by
  funext x
  let f : ℝ → E [⋀^Fin k]→L[ℝ] F := fun t ↦ mfamilyContraction I I' P t (c • ω) x
  let g : ℝ → E [⋀^Fin k]→L[ℝ] F := fun t ↦ mfamilyContraction I I' P t ω x
  have hfun : f = fun t ↦ c • g t :=
    funext fun t ↦ by dsimp only [f, g]; rw [mfamilyContraction_smul]; rfl
  have hint : intervalIntegral f 0 1 volume = c • intervalIntegral g 0 1 volume := by
    rw [hfun, intervalIntegral.integral_smul]
  exact (mfamilyHomotopyOperator_apply P (c • ω) x).trans hint

/-- `mfamilyHomotopyOperator` commutes with negation. -/
@[simp]
theorem mfamilyHomotopyOperator_neg (P : M × ℝ → N) (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperator I I' P (-ω) = -mfamilyHomotopyOperator I I' P ω := by
  rw [← neg_one_smul ℝ ω, mfamilyHomotopyOperator_smul, neg_one_smul]

/-- **Stationarity vanishing for `mfamilyHomotopyOperator`.** If `t ↦ P (x, t)` is constant on
`(0, 1)`, then `mfamilyHomotopyOperator I I' P ω x = 0`, with no differentiability hypothesis on
`P`. -/
theorem mfamilyHomotopyOperator_apply_eq_zero {P : M × ℝ → N} {x : M} {y : N}
    (hx : ∀ t ∈ Ioo (0 : ℝ) 1, P (x, t) = y) (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperator I I' P ω x = 0 := by
  rw [mfamilyHomotopyOperator_apply]
  have hzero : intervalIntegral (E := E [⋀^Fin k]→L[ℝ] F)
      (fun t ↦ (mfamilyContraction I I' P t ω x : E [⋀^Fin k]→L[ℝ] F)) 0 1 volume =
      intervalIntegral (E := E [⋀^Fin k]→L[ℝ] F) (fun _ ↦ 0) 0 1 volume := by
    refine intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun t ht ↦ ?_
    have hvel : mfamilyVelocity I I' P t x = 0 :=
      mfamilyVelocity_eq_zero_of_eventuallyEq_const
        (Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) hx)
    ext v
    rw [mfamilyContraction_def, mcontractionAlongMap_apply, hvel]
    exact (ω (P (x, t))).map_coord_zero 0 rfl
  rw [hzero, intervalIntegral.integral_zero]
  rfl

/-- `mfamilyHomotopyOperator` vanishes identically for a time-independent family `p ∘ Prod.fst`. -/
@[simp]
theorem mfamilyHomotopyOperator_comp_fst (p : M → N) (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperator I I' (p ∘ (Prod.fst : M × ℝ → M)) ω = 0 :=
  funext fun x ↦ mfamilyHomotopyOperator_apply_eq_zero (y := p x) (fun _ _ ↦ rfl) ω

/-- **Open source restriction of `mfamilyHomotopyOperator`.** Restricting to `U : Opens M` commutes
with `mfamilyHomotopyOperator`, with no regularity or completeness hypothesis. -/
@[simp]
theorem mpullback_subtype_val_mfamilyHomotopyOperator (U : Opens M) (P : M × ℝ → N)
    (ω : RoughForm I' N F (k + 1)) :
    mpullback I I (Subtype.val : U → M) (mfamilyHomotopyOperator I I' P ω) =
      mfamilyHomotopyOperator I I' (P ∘ Prod.map (Subtype.val : U → M) id) ω := by
  funext x
  have h1 : mpullback I I (Subtype.val : U → M) (mfamilyHomotopyOperator I I' P ω) x =
      mfamilyHomotopyOperator I I' P ω (x : M) := by
    ext v
    rw [mpullback_apply]
    simp only [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
      Manifold.tangentSpaceOpenEquiv_apply]
    rfl
  rw [h1, mfamilyHomotopyOperator_apply, mfamilyHomotopyOperator_apply]
  refine intervalIntegral.integral_congr (E := E [⋀^Fin k]→L[ℝ] F) fun t _ ↦ ?_
  have h2 := congrFun (mpullback_subtype_val_mfamilyContraction (I := I) (I' := I') U P t ω) x
  have h3 : mpullback I I (Subtype.val : U → M) (mfamilyContraction I I' P t ω) x =
      mfamilyContraction I I' P t ω (x : M) := by
    ext v
    rw [mpullback_apply]
    simp only [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
      Manifold.tangentSpaceOpenEquiv_apply]
    rfl
  exact h3.symm.trans h2

/-- **Nested open source restriction of `mfamilyHomotopyOperator`.** Restricting along `U ≤ W` in
`Opens M` commutes with `mfamilyHomotopyOperator`, with no regularity or completeness hypothesis. -/
@[simp]
theorem mpullback_inclusion_mfamilyHomotopyOperator {U W : Opens M} (h : U ≤ W) (P : W × ℝ → N)
    (ω : RoughForm I' N F (k + 1)) :
    mpullback I I (Opens.inclusion h) (mfamilyHomotopyOperator I I' P ω) =
      mfamilyHomotopyOperator I I' (P ∘ Prod.map (Opens.inclusion h) id) ω := by
  funext x
  rw [mpullback_inclusion_apply, mfamilyHomotopyOperator_apply, mfamilyHomotopyOperator_apply]
  refine intervalIntegral.integral_congr (E := E [⋀^Fin k]→L[ℝ] F) fun t _ ↦ ?_
  rw [← mpullback_inclusion_apply h (mfamilyContraction I I' P t ω) x,
    mpullback_inclusion_mfamilyContraction (I := I) (I' := I') h P t ω]

/-- **Open target restriction of `mfamilyHomotopyOperator`.** Pulling back along
`Subtype.val : U' → N` agrees with composing `P : M × ℝ → U'` with `Subtype.val`, with no
regularity hypothesis. -/
@[simp]
theorem mfamilyHomotopyOperator_mpullback_subtype_val (U' : Opens N) (P : M × ℝ → U')
    (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperator I I' P (mpullback I' I' (Subtype.val : U' → N) ω) =
      mfamilyHomotopyOperator I I' ((Subtype.val : U' → N) ∘ P) ω := by
  funext x
  rw [mfamilyHomotopyOperator_apply, mfamilyHomotopyOperator_apply]
  refine intervalIntegral.integral_congr (E := E [⋀^Fin k]→L[ℝ] F) fun t _ ↦ ?_
  exact congrFun (mfamilyContraction_mpullback_subtype_val U' P t ω) x

/-- **Nested open target restriction of `mfamilyHomotopyOperator`.** Pulling back along
`Opens.inclusion h` (`U' ≤ W'`) agrees with composing `P : M × ℝ → U'` with `Opens.inclusion h`,
with no regularity hypothesis. -/
@[simp]
theorem mfamilyHomotopyOperator_mpullback_inclusion {U' W' : Opens N} (h : U' ≤ W')
    (P : M × ℝ → U') (ω : RoughForm I' W' F (k + 1)) :
    mfamilyHomotopyOperator I I' P (mpullback I' I' (Opens.inclusion h) ω) =
      mfamilyHomotopyOperator I I' (Opens.inclusion h ∘ P) ω := by
  funext x
  rw [mfamilyHomotopyOperator_apply, mfamilyHomotopyOperator_apply]
  refine intervalIntegral.integral_congr (E := E [⋀^Fin k]→L[ℝ] F) fun t _ ↦ ?_
  exact congrFun (mfamilyContraction_mpullback_inclusion h P t ω) x

section HomotopyTargetNaturality

variable {E''' H''' Q : Type*} [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H'''] [TopologicalSpace Q] [ChartedSpace H''' Q]
  {I''' : ModelWithCorners ℝ E''' H'''}

/-- **Pointwise target naturality of `mfamilyHomotopyOperator`.** When `P` is differentiable at
`(x, t)` and `q : N → Q` is differentiable at `P (x, t)` for all `t ∈ (0, 1)`, applying
`mfamilyHomotopyOperator` to `q^* η` along `P` equals applying it to `η` along `q ∘ P`. -/
theorem mfamilyHomotopyOperator_mpullback_at {P : M × ℝ → N} {q : N → Q} {x : M}
    (hP : ∀ t ∈ Ioo (0 : ℝ) 1, MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (x, t))
    (hq : ∀ t ∈ Ioo (0 : ℝ) 1, MDifferentiableAt I' I''' q (P (x, t)))
    (η : RoughForm I''' Q F (k + 1)) :
    mfamilyHomotopyOperator I I' P (mpullback I' I''' q η) x =
      mfamilyHomotopyOperator I I''' (q ∘ P) η x := by
  rw [mfamilyHomotopyOperator_apply, mfamilyHomotopyOperator_apply]
  exact intervalIntegral.integral_congr_Ioo_of_le (E := E [⋀^Fin k]→L[ℝ] F) zero_le_one
    fun t ht ↦ mfamilyContraction_mpullback_at (hP t ht) (hq t ht)

/-- **Global target naturality of `mfamilyHomotopyOperator`.** For `P` differentiable on
`M × (0, 1)` and differentiable `q : N → Q`, `K_P (q^* η) = K_(q ∘ P) η`. -/
theorem mfamilyHomotopyOperator_mpullback {P : M × ℝ → N} {q : N → Q}
    (hP : MDifferentiableOn (I.prod 𝓘(ℝ, ℝ)) I' P (univ ×ˢ Ioo (0 : ℝ) 1))
    (hq : MDifferentiable I' I''' q) (η : RoughForm I''' Q F (k + 1)) :
    mfamilyHomotopyOperator I I' P (mpullback I' I''' q η) =
      mfamilyHomotopyOperator I I''' (q ∘ P) η :=
  funext fun x ↦ mfamilyHomotopyOperator_mpullback_at
    (fun t ht ↦ (hP (x, t) ⟨trivial, ht⟩).mdifferentiableAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨trivial, ht⟩))
    (fun t _ ↦ hq (P (x, t))) η

end HomotopyTargetNaturality

/-- **Cylinder-pullback identification at a point.** Whenever `P : M × ℝ → N` is differentiable at
`(x, t)` for all `t ∈ (0, 1)`, `mfamilyHomotopyOperator I I' P ω x` agrees with
`TauCeti.homotopyOperator` applied to the cylinder pullback `(P ∘ (id × Subtype.val))^* ω` on
`M × [0, 1]`. -/
theorem mfamilyHomotopyOperator_eq_homotopyOperator_mpullback_at
    {P : M × ℝ → N} {x : M}
    (hP : ∀ t ∈ Ioo (0 : ℝ) 1, MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (x, t))
    (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperator I I' P ω x =
      homotopyOperator
        (mpullback (I.prod (𝓡∂ 1)) I' (P ∘ Prod.map id (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) ω) x := by
  rw [mfamilyHomotopyOperator_apply, homotopyOperator_apply]
  refine intervalIntegral.integral_congr_Ioo_of_le zero_le_one (E := E [⋀^Fin k]→L[ℝ] F)
    fun t ht ↦ ?_
  have ht_icc : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
  let t' : Icc (0 : ℝ) 1 := ⟨t, ht_icc⟩
  have hproj : projIcc 0 1 zero_le_one t = t' := projIcc_of_mem zero_le_one ht_icc
  have hsub_d : MDifferentiableAt (I.prod (𝓡∂ 1)) (I.prod 𝓘(ℝ, ℝ))
      (Prod.map (id : M → M) (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) (x, t') :=
    mdifferentiableAt_id.prodMap ((contMDiff_subtypeVal_Icc t').mdifferentiableAt one_ne_zero)
  ext v
  rw [mfamilyContraction_apply]
  -- `curryLeft_apply_apply` does not fire because the tangent spaces of the cylinder `M × [0, 1]`
  -- agree with the model spaces only by definition; state the evaluation on `∂ₜ` and `(v i, 0)`
  -- explicitly (as in `TauCeti.homotopyOperator_apply_eq_zero`).
  change _ = mpullback (I.prod (𝓡∂ 1)) I' (P ∘ Prod.map id (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) ω
    (x, projIcc 0 1 zero_le_one t)
    (Matrix.vecCons ((0 : E), (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one t)))
      fun i ↦ ((v i : E), (0 : EuclideanSpace ℝ (Fin 1))))
  rw [hproj, mpullback_apply]
  refine congrArg (ω (P (x, t))) (funext fun i ↦ ?_)
  cases i using Fin.cases with
  | zero =>
    simp only [Matrix.cons_val_zero]
    let u0 : TangentSpace (I.prod (𝓡∂ 1)) (x, t') := ((0 : E), (1 : TangentSpace (𝓡∂ 1) t'))
    have h0 := mfderiv_comp_apply (x, t') (hP t ht) hsub_d u0
    have hpm0 : mfderiv (I.prod (𝓡∂ 1)) (I.prod 𝓘(ℝ, ℝ))
        (Prod.map (id : M → M) (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) (x, t') u0 =
        ((0 : E), (1 : ℝ)) := by
      rw [mfderiv_prodMap (p := (x, t')) mdifferentiableAt_id
        ((contMDiff_subtypeVal_Icc t').mdifferentiableAt one_ne_zero), mfderiv_id]
      exact Prod.ext rfl (mfderiv_subtypeVal_Icc_one t')
    exact (congrArg (mfderiv (I.prod 𝓘(ℝ, ℝ)) I' P (x, t)) hpm0.symm).trans h0.symm
  | succ i =>
    simp only [Matrix.cons_val_succ]
    rw [mfderiv_slice_left_apply (hP t ht) (v i)]
    let ui : TangentSpace (I.prod (𝓡∂ 1)) (x, t') :=
      ((v i : E), (0 : EuclideanSpace ℝ (Fin 1)))
    have hi := mfderiv_comp_apply (x, t') (hP t ht) hsub_d ui
    have hpmi : mfderiv (I.prod (𝓡∂ 1)) (I.prod 𝓘(ℝ, ℝ))
        (Prod.map (id : M → M) (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) (x, t') ui =
        (v i, (0 : ℝ)) := by
      rw [mfderiv_prodMap (p := (x, t')) mdifferentiableAt_id
        ((contMDiff_subtypeVal_Icc t').mdifferentiableAt one_ne_zero), mfderiv_id]
      refine Prod.ext rfl ?_
      exact _root_.map_zero (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Icc (0 : ℝ) 1 → ℝ) t')
    exact (congrArg (mfderiv (I.prod 𝓘(ℝ, ℝ)) I' P (x, t)) hpmi.symm).trans hi.symm

/-- **Global cylinder-pullback identification.** Whenever `P : M × ℝ → N` is differentiable on
`M × (0, 1)`, `mfamilyHomotopyOperator I I' P ω` equals `TauCeti.homotopyOperator` applied to the
cylinder pullback `(P ∘ (id × Subtype.val))^* ω` on `M × [0, 1]`. -/
theorem mfamilyHomotopyOperator_eq_homotopyOperator_mpullback
    {P : M × ℝ → N} (hP : MDifferentiableOn (I.prod 𝓘(ℝ, ℝ)) I' P (univ ×ˢ Ioo (0 : ℝ) 1))
    (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperator I I' P ω =
      homotopyOperator
        (mpullback (I.prod (𝓡∂ 1)) I' (P ∘ Prod.map id (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) ω) :=
  funext fun x ↦ mfamilyHomotopyOperator_eq_homotopyOperator_mpullback_at
    (fun t ht ↦ (hP (x, t) ⟨trivial, ht⟩).mdifferentiableAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨trivial, ht⟩))
    ω

private theorem contMDiff_comp_subtypeVal_Icc {r : WithTop ℕ∞} {P : M × ℝ → N}
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' r P (univ ×ˢ Icc (0 : ℝ) 1)) :
    ContMDiff (I.prod (𝓡∂ 1)) I' r (P ∘ Prod.map id (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) := fun q ↦
  (hP (q.1, q.2.1) ⟨trivial, q.2.2⟩).comp q
    (contMDiff_id.prodMap contMDiff_subtypeVal_Icc q).contMDiffWithinAt
    (fun p _ ↦ Set.mk_mem_prod (mem_univ _) p.2.2 :
      MapsTo (Prod.map id (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) univ (univ ×ˢ Icc (0 : ℝ) 1))

/-- **Source naturality of `mfamilyHomotopyOperator` for maps with invertible derivatives.**
Precomposing `P : M × ℝ → N` with `g × id : L × ℝ → M × ℝ`, where `g` is differentiable with
invertible derivatives everywhere, commutes with `mfamilyHomotopyOperator` whenever `P` is
differentiable on `M × (0, 1)`, with no regularity assumption on `ω` and no completeness assumption
on `F`. -/
theorem mfamilyHomotopyOperator_comp_prodMap_id {g : L → M} {P : M × ℝ → N}
    (hg : MDifferentiable I'' I g) (hdg : ∀ z, (mfderiv I'' I g z).IsInvertible)
    (hP : MDifferentiableOn (I.prod 𝓘(ℝ, ℝ)) I' P (univ ×ˢ Ioo (0 : ℝ) 1))
    (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperator I'' I' (P ∘ Prod.map g id) ω =
      mpullback I'' I g (mfamilyHomotopyOperator I I' P ω) := by
  funext z
  obtain ⟨D, hD⟩ := hdg z
  let Dm : E'' →L[ℝ] E := mfderiv I'' I g z
  let D' : E'' ≃L[ℝ] E := D
  have hD' : (D' : E'' →L[ℝ] E) = Dm := hD
  have hL (a : E [⋀^Fin k]→L[ℝ] F) :
      D'.symm.continuousAlternatingMapCongrLeft a = a.compContinuousLinearMap Dm := by
    rw [ContinuousLinearEquiv.continuousAlternatingMapCongrLeft_apply,
      ContinuousLinearEquiv.symm_symm, hD']
  have h1 : (mfamilyHomotopyOperator I'' I' (P ∘ Prod.map g id) ω z : E'' [⋀^Fin k]→L[ℝ] F) =
      intervalIntegral (E := E'' [⋀^Fin k]→L[ℝ] F)
        (fun t ↦ D'.symm.continuousAlternatingMapCongrLeft
          (mfamilyContraction I I' P t ω (g z) : E [⋀^Fin k]→L[ℝ] F))
        0 1 volume := by
    rw [mfamilyHomotopyOperator_apply]
    refine intervalIntegral.integral_congr_Ioo_of_le (E := E'' [⋀^Fin k]→L[ℝ] F) zero_le_one
      fun t ht ↦ ?_
    have hPt : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (g z, t) :=
      (hP (g z, t) ⟨trivial, ht⟩).mdifferentiableAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨trivial, ht⟩)
    have hm : (mpullback I'' I g (mfamilyContraction I I' P t ω) z : E'' [⋀^Fin k]→L[ℝ] F) =
        (mfamilyContraction I I' P t ω (g z) : E [⋀^Fin k]→L[ℝ] F).compContinuousLinearMap Dm := by
      ext v
      exact mpullback_apply g (mfamilyContraction I I' P t ω) z v
    exact ((mfamilyContraction_comp_prodMap_id_at (hg z) hPt).trans hm).trans
      (hL (mfamilyContraction I I' P t ω (g z))).symm
  have h2 : intervalIntegral (E := E'' [⋀^Fin k]→L[ℝ] F)
        (fun t ↦ D'.symm.continuousAlternatingMapCongrLeft
          (mfamilyContraction I I' P t ω (g z) : E [⋀^Fin k]→L[ℝ] F))
        0 1 volume =
      D'.symm.continuousAlternatingMapCongrLeft
        (mfamilyHomotopyOperator I I' P ω (g z) : E [⋀^Fin k]→L[ℝ] F) :=
    ContinuousLinearEquiv.intervalIntegral_comp_comm _ _
  have h3 : D'.symm.continuousAlternatingMapCongrLeft
        (mfamilyHomotopyOperator I I' P ω (g z) : E [⋀^Fin k]→L[ℝ] F) =
      (mpullback I'' I g (mfamilyHomotopyOperator I I' P ω) z : E'' [⋀^Fin k]→L[ℝ] F) := by
    refine (hL (mfamilyHomotopyOperator I I' P ω (g z))).trans ?_
    ext v
    exact (mpullback_apply g (mfamilyHomotopyOperator I I' P ω) z v).symm
  exact h1.trans (h2.trans h3)

/-- **Source naturality of `mfamilyHomotopyOperator` for continuous forms.** For `C¹` manifolds
`M, N`, a Banach space `F`, an arbitrary differentiable map `g : L → M`, a family `P : M × ℝ → N`
that is `C¹` on `M × [0, 1]`, and a continuous form `ω` on `N`,
`K_(P ∘ (g × id)) ω = g^* (K_P ω)`. -/
theorem mfamilyHomotopyOperator_comp_prodMap_id_of_isSmoothForm [IsManifold I 1 M]
    [IsManifold I' 1 N] [CompleteSpace F] {g : L → M} {P : M × ℝ → N}
    (hg : MDifferentiable I'' I g)
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' 1 P (univ ×ˢ Icc (0 : ℝ) 1))
    {ω : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' 0 ω) :
    mfamilyHomotopyOperator I'' I' (P ∘ Prod.map g id) ω =
      mpullback I'' I g (mfamilyHomotopyOperator I I' P ω) := by
  have hP_cyl : ContMDiff (I.prod (𝓡∂ 1)) I' ((0 : ℕ∞) + 1)
      (P ∘ Prod.map id (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) :=
    (contMDiff_comp_subtypeVal_Icc hP).of_le (by simp)
  have hP_mdiff : MDifferentiableOn (I.prod 𝓘(ℝ, ℝ)) I' P (univ ×ˢ Ioo (0 : ℝ) 1) :=
    (hP.mono (Set.prod_mono_right Ioo_subset_Icc_self)).mdifferentiableOn one_ne_zero
  have hPg_mdiff : MDifferentiableOn (I''.prod 𝓘(ℝ, ℝ)) I' (P ∘ Prod.map g id)
      (univ ×ˢ Ioo (0 : ℝ) 1) :=
    hP_mdiff.comp (hg.prodMap mdifferentiable_id).mdifferentiableOn fun _ hq ↦ ⟨trivial, hq.2⟩
  rw [mfamilyHomotopyOperator_eq_homotopyOperator_mpullback hPg_mdiff ω,
    mfamilyHomotopyOperator_eq_homotopyOperator_mpullback hP_mdiff ω]
  have hpull : mpullback (I''.prod (𝓡∂ 1)) I'
        ((P ∘ Prod.map g id) ∘ Prod.map id (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) ω =
      mpullback (I''.prod (𝓡∂ 1)) (I.prod (𝓡∂ 1)) (Prod.map g id)
        (mpullback (I.prod (𝓡∂ 1)) I' (P ∘ Prod.map id (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) ω) :=
    mpullback_comp (hg.prodMap mdifferentiable_id) (hP_cyl.mdifferentiable (by simp)) ω
  rw [hpull]
  exact homotopyOperator_mpullback_prodMap_id_of_isSmoothForm hg (hω.mpullback hP_cyl)

/-- `mfamilyHomotopyOperator` is additive on continuous forms when `P` is `C¹` on `M × [0, 1]`. -/
theorem mfamilyHomotopyOperator_add [IsManifold I 1 M] [IsManifold I' 1 N]
    {P : M × ℝ → N} (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' 1 P (univ ×ˢ Icc (0 : ℝ) 1))
    {ω η : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' 0 ω) (hη : IsSmoothForm I' 0 η) :
    mfamilyHomotopyOperator I I' P (ω + η) =
      mfamilyHomotopyOperator I I' P ω + mfamilyHomotopyOperator I I' P η := by
  have hP_cyl : ContMDiff (I.prod (𝓡∂ 1)) I' ((0 : ℕ∞) + 1)
      (P ∘ Prod.map id (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) :=
    (contMDiff_comp_subtypeVal_Icc hP).of_le (by simp)
  have hP_mdiff : MDifferentiableOn (I.prod 𝓘(ℝ, ℝ)) I' P (univ ×ˢ Ioo (0 : ℝ) 1) :=
    (hP.mono (Set.prod_mono_right Ioo_subset_Icc_self)).mdifferentiableOn one_ne_zero
  rw [mfamilyHomotopyOperator_eq_homotopyOperator_mpullback hP_mdiff (ω + η),
    mfamilyHomotopyOperator_eq_homotopyOperator_mpullback hP_mdiff ω,
    mfamilyHomotopyOperator_eq_homotopyOperator_mpullback hP_mdiff η,
    mpullback_add, homotopyOperator_add (hω.mpullback hP_cyl) (hη.mpullback hP_cyl)]

/-- `mfamilyHomotopyOperator` commutes with subtraction of continuous forms when `P` is `C¹` on
`M × [0, 1]`. -/
theorem mfamilyHomotopyOperator_sub [IsManifold I 1 M] [IsManifold I' 1 N]
    {P : M × ℝ → N} (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' 1 P (univ ×ˢ Icc (0 : ℝ) 1))
    {ω η : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' 0 ω) (hη : IsSmoothForm I' 0 η) :
    mfamilyHomotopyOperator I I' P (ω - η) =
      mfamilyHomotopyOperator I I' P ω - mfamilyHomotopyOperator I I' P η := by
  rw [sub_eq_add_neg, mfamilyHomotopyOperator_add hP hω hη.neg,
    ← neg_one_smul ℝ η, mfamilyHomotopyOperator_smul, neg_one_smul, sub_eq_add_neg]

/-- If `P` is `C^(r + 1)` on `M × [0, 1]`, `mfamilyHomotopyOperator` sends `C^r` forms on `N` to
`C^r` forms on `M`. -/
theorem IsSmoothForm.mfamilyHomotopyOperator {r : ℕ∞} [IsManifold I 1 M] [IsManifold I (r + 1) M]
    [IsManifold I' 1 N] {P : M × ℝ → N}
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' (r + 1) P (univ ×ˢ Icc (0 : ℝ) 1))
    {ω : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' r ω) :
    IsSmoothForm I r (TauCeti.mfamilyHomotopyOperator I I' P ω) := by
  have hP_mdiff : MDifferentiableOn (I.prod 𝓘(ℝ, ℝ)) I' P (univ ×ˢ Ioo (0 : ℝ) 1) :=
    (hP.mono (Set.prod_mono_right Ioo_subset_Icc_self)).mdifferentiableOn (by simp)
  rw [mfamilyHomotopyOperator_eq_homotopyOperator_mpullback hP_mdiff]
  exact (hω.mpullback (contMDiff_comp_subtypeVal_Icc hP)).homotopyOperator

/-- **The cochain-homotopy identity for a moving map `P : M × ℝ → N`.** When `M, N` are `C²`
manifolds (possibly with boundary or corners), `P` is `C²` on `M × [0, 1]`, `F` is a Banach space,
and `ω` is a `C¹` `(k + 1)`-form on `N`, `d(K_P ω) + K_P(dω) = p₁^* ω - p₀^* ω` without
invertibility of the slices `p_t`. -/
theorem mextDeriv_mfamilyHomotopyOperator_add_mfamilyHomotopyOperator_mextDeriv
    [IsManifold I 2 M] [IsManifold I' 2 N] [CompleteSpace F]
    {P : M × ℝ → N} (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' 2 P (univ ×ˢ Icc (0 : ℝ) 1))
    {ω : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' 1 ω) (x₀ : M) :
    mextDeriv (mfamilyHomotopyOperator I I' P ω) x₀ +
        mfamilyHomotopyOperator I I' P (mextDeriv ω) x₀ =
      mpullback I I' (fun x ↦ P (x, 1)) ω x₀ - mpullback I I' (fun x ↦ P (x, 0)) ω x₀ := by
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have : IsManifold I' 1 N := IsManifold.of_le one_le_two
  have hP_cyl := contMDiff_comp_subtypeVal_Icc hP
  have hP_mdiff : MDifferentiableOn (I.prod 𝓘(ℝ, ℝ)) I' P (univ ×ˢ Ioo (0 : ℝ) 1) :=
    (hP.mono (Set.prod_mono_right Ioo_subset_Icc_self)).mdifferentiableOn two_ne_zero
  have hφ := hω.mpullback (hP_cyl.of_le (m := (1 : ℕ∞) + 1) (by norm_num))
  have hd_pull := mpullback_mextDeriv hP_cyl ((isSmoothBundleForm_def 1 ω).mpr hω.contMDiff)
  rw [mfamilyHomotopyOperator_eq_homotopyOperator_mpullback hP_mdiff ω,
    mfamilyHomotopyOperator_eq_homotopyOperator_mpullback hP_mdiff (mextDeriv ω), hd_pull]
  refine (mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv hφ x₀).trans ?_
  have hend (c : Icc (0 : ℝ) 1) : mpullback I (I.prod (𝓡∂ 1)) (fun x ↦ (x, c))
      (mpullback (I.prod (𝓡∂ 1)) I' _ ω) x₀ = mpullback I I' (fun x ↦ P (x, (c : ℝ))) ω x₀ :=
    (mpullback_comp_at (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
      (hP_cyl.mdifferentiable two_ne_zero (x₀, c)) ω).symm
  rw [hend 1, hend 0]; rfl

/-- **Closed forms along a smooth homotopy.** When `M, N` are `C²` manifolds (possibly with boundary
or corners), `P` is `C²` on `M × [0, 1]`, `F` is a Banach space, and `ω` is a closed `C¹` form on
`N`, `d(K_P ω) = p₁^* ω - p₀^* ω`. -/
theorem mextDeriv_mfamilyHomotopyOperator [IsManifold I 2 M] [IsManifold I' 2 N] [CompleteSpace F]
    {P : M × ℝ → N} (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' 2 P (univ ×ˢ Icc (0 : ℝ) 1))
    {ω : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' 1 ω) (hclosed : mextDeriv ω = 0)
    (x₀ : M) :
    mextDeriv (mfamilyHomotopyOperator I I' P ω) x₀ =
      mpullback I I' (fun x ↦ P (x, 1)) ω x₀ - mpullback I I' (fun x ↦ P (x, 0)) ω x₀ := by
  rw [← mextDeriv_mfamilyHomotopyOperator_add_mfamilyHomotopyOperator_mextDeriv hP hω x₀,
    hclosed, mfamilyHomotopyOperator_zero, Pi.zero_apply, add_zero]

/-! ### Homotopy operator over an open parameter interval `J : Opens ℝ` -/

private def mfamilyIntegrandOpens (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    {J : Opens ℝ} (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) (P : M × ↥J → N)
    (ω : RoughForm I' N F (k + 1)) (x : M) (t : ℝ) : E [⋀^Fin k]→L[ℝ] F :=
  mfamilyContraction I I' P ⟨projIcc 0 1 zero_le_one t, hJ (projIcc 0 1 zero_le_one t).2⟩ ω x

/-- **Homotopy operator of a moving map `P : M × ↥J → N` over an open interval `J : Opens ℝ`
containing `[0, 1]`.** Integrates `mfamilyContraction I I' P ⟨t, hJ ht⟩ ω` over `t ∈ [0, 1]`. When
`M, N` are `C²` manifolds, `P` is `C²` on `M × [0, 1]`, `F` is complete, and `ω` is `C¹`, this
satisfies `d(K_P ω) + K_P(dω) = p₁^* ω - p₀^* ω` without invertibility of `p_t`. -/
def mfamilyHomotopyOperatorOpens (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    {J : Opens ℝ} (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) (P : M × ↥J → N)
    (ω : RoughForm I' N F (k + 1)) : RoughForm I M F k :=
  fun x ↦ intervalIntegral (E := E [⋀^Fin k]→L[ℝ] F)
    (mfamilyIntegrandOpens I I' hJ P ω x) 0 1 volume

/-- Pointwise evaluation of `mfamilyHomotopyOperatorOpens` as an integral over `[0, 1]`. -/
theorem mfamilyHomotopyOperatorOpens_apply {J : Opens ℝ} (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ))
    (P : M × ↥J → N) (ω : RoughForm I' N F (k + 1)) (x : M) :
    mfamilyHomotopyOperatorOpens I I' hJ P ω x = intervalIntegral (E := E [⋀^Fin k]→L[ℝ] F)
      (fun t ↦ (mfamilyContraction I I' P
        ⟨projIcc 0 1 zero_le_one t, hJ (projIcc 0 1 zero_le_one t).2⟩ ω x : E [⋀^Fin k]→L[ℝ] F))
      0 1 volume := (rfl)

/-- **Open parameter restriction of `mfamilyHomotopyOperator`.** Restricting `P : M × ℝ → N` to
`J : Opens ℝ` containing `[0, 1]` yields `mfamilyHomotopyOperator`, with no regularity
hypothesis. -/
@[simp]
theorem mfamilyHomotopyOperatorOpens_comp_prodMap_subtype_val {J : Opens ℝ}
    (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) (P : M × ℝ → N) (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperatorOpens I I' hJ (P ∘ Prod.map id (Subtype.val : J → ℝ)) ω =
      mfamilyHomotopyOperator I I' P ω := by
  funext x
  rw [mfamilyHomotopyOperatorOpens_apply, mfamilyHomotopyOperator_apply]
  refine intervalIntegral.integral_congr (E := E [⋀^Fin k]→L[ℝ] F) fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  rw [congrFun (mfamilyContraction_comp_prodMap_subtype_val J P
    ⟨projIcc 0 1 zero_le_one t, hJ (projIcc 0 1 zero_le_one t).2⟩ ω) x,
    projIcc_of_mem zero_le_one ht]

/-- **Nested open parameter restriction of `mfamilyHomotopyOperatorOpens`.** Restricting
`P : M × ↥J₂ → N` along `J₁ ≤ J₂` containing `[0, 1]` preserves `mfamilyHomotopyOperatorOpens`,
with no regularity hypothesis. -/
@[simp]
theorem mfamilyHomotopyOperatorOpens_comp_prodMap_inclusion {J₁ J₂ : Opens ℝ} (hJ : J₁ ≤ J₂)
    (hJ₁ : Icc (0 : ℝ) 1 ⊆ (J₁ : Set ℝ)) (P : M × ↥J₂ → N) (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperatorOpens I I' hJ₁ (P ∘ Prod.map id (Opens.inclusion hJ)) ω =
      mfamilyHomotopyOperatorOpens I I' (hJ₁.trans hJ) P ω := by
  funext x
  rw [mfamilyHomotopyOperatorOpens_apply, mfamilyHomotopyOperatorOpens_apply]
  refine intervalIntegral.integral_congr (E := E [⋀^Fin k]→L[ℝ] F) fun t _ ↦ ?_
  exact congrFun (mfamilyContraction_comp_prodMap_inclusion hJ P _ ω) x

/-- Retraction `ℝ → ↥J` extending the identity on `J : Opens ℝ` (used to lift families on `M × ↥J`
to `M × ℝ` while preserving regularity on `M × [0, 1]` and `M × (0, 1)`). -/
private def retractOpens {J : Opens ℝ} (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) : ℝ → ↥J :=
  Subtype.val.extend id (fun _ ↦ ⟨0, hJ (left_mem_Icc.mpr zero_le_one)⟩)

private theorem retractOpens_coe {J : Opens ℝ} (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) (u : J) :
    retractOpens hJ (u : ℝ) = u :=
  Subtype.val_injective.extend_apply id _ u

private theorem contMDiffAt_retractOpens {r : WithTop ℕ∞} {J : Opens ℝ}
    (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) (u : J) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) r (retractOpens hJ) (u : ℝ) :=
  contMDiffAt_id.extend_subtypeVal _

private theorem mfamilyHomotopyOperatorOpens_eq_retract {J : Opens ℝ}
    (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) (P : M × ↥J → N) (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperatorOpens I I' hJ P ω =
      mfamilyHomotopyOperator I I' (P ∘ Prod.map id (retractOpens hJ)) ω := by
  have heq : (P ∘ Prod.map id (retractOpens hJ)) ∘ Prod.map id (Subtype.val : J → ℝ) = P :=
    funext fun q ↦ congrArg P (Prod.ext rfl (retractOpens_coe hJ q.2))
  rw [← mfamilyHomotopyOperatorOpens_comp_prodMap_subtype_val hJ, heq]

private theorem mdifferentiableOn_comp_retractOpens {J : Opens ℝ}
    (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) {P : M × ↥J → N}
    (hP : MDifferentiableOn (I.prod 𝓘(ℝ, ℝ)) I' P
      (univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Ioo (0 : ℝ) 1))) :
    MDifferentiableOn (I.prod 𝓘(ℝ, ℝ)) I' (P ∘ Prod.map id (retractOpens hJ))
      (univ ×ˢ Ioo (0 : ℝ) 1) := by
  intro q hq
  have hu : q.2 ∈ J := hJ (Ioo_subset_Icc_self hq.2)
  let u : J := ⟨q.2, hu⟩
  have hret : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
      (Prod.map (id : M → M) (retractOpens hJ)) q :=
    mdifferentiableAt_id.prodMap
      ((contMDiffAt_retractOpens (r := 1) hJ u).mdifferentiableAt one_ne_zero)
  have hmaps : MapsTo (Prod.map (id : M → M) (retractOpens hJ))
      (univ ×ˢ Ioo (0 : ℝ) 1) (univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Ioo (0 : ℝ) 1)) := fun p hp ↦ by
    refine ⟨trivial, ?_⟩
    have hpJ : p.2 ∈ J := hJ (Ioo_subset_Icc_self hp.2)
    have hcoe : retractOpens hJ p.2 = ⟨p.2, hpJ⟩ := retractOpens_coe hJ ⟨p.2, hpJ⟩
    exact Set.mem_preimage.mpr (by rw [Prod.map_snd, hcoe]; exact hp.2)
  have hpt : Prod.map (id : M → M) (retractOpens hJ) q = (q.1, u) :=
    Prod.ext rfl (retractOpens_coe hJ u)
  exact MDifferentiableWithinAt.comp_of_eq q (hP (q.1, u) ⟨trivial, hq.2⟩)
    hret.mdifferentiableWithinAt hmaps hpt

private theorem contMDiffOn_comp_retractOpens {r : WithTop ℕ∞} {J : Opens ℝ}
    (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) {P : M × ↥J → N}
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' r P
      (univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Icc (0 : ℝ) 1))) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' r (P ∘ Prod.map id (retractOpens hJ))
      (univ ×ˢ Icc (0 : ℝ) 1) := by
  intro q hq
  let u : J := ⟨q.2, hJ hq.2⟩
  have hret : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) r
      (Prod.map (id : M → M) (retractOpens hJ)) q :=
    contMDiffAt_id.prodMap (contMDiffAt_retractOpens hJ u)
  have hmaps : MapsTo (Prod.map (id : M → M) (retractOpens hJ))
      (univ ×ˢ Icc (0 : ℝ) 1) (univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Icc (0 : ℝ) 1)) := fun p hp ↦ by
    refine ⟨trivial, ?_⟩
    have hcoe : retractOpens hJ p.2 = ⟨p.2, hJ hp.2⟩ := retractOpens_coe hJ ⟨p.2, hJ hp.2⟩
    exact Set.mem_preimage.mpr (by rw [Prod.map_snd, hcoe]; exact hp.2)
  have hpt : Prod.map (id : M → M) (retractOpens hJ) q = (q.1, u) :=
    Prod.ext rfl (retractOpens_coe hJ u)
  exact (hP (q.1, u) ⟨trivial, hq.2⟩).comp_of_eq hret.contMDiffWithinAt hmaps hpt

/-- `mfamilyHomotopyOperatorOpens` sends the zero form to zero. -/
@[simp]
theorem mfamilyHomotopyOperatorOpens_zero {J : Opens ℝ} (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ))
    (P : M × ↥J → N) :
    mfamilyHomotopyOperatorOpens I I' hJ P (0 : RoughForm I' N F (k + 1)) = 0 := by
  rw [mfamilyHomotopyOperatorOpens_eq_retract, mfamilyHomotopyOperator_zero]

/-- `mfamilyHomotopyOperatorOpens` commutes with real scalar multiplication. -/
@[simp]
theorem mfamilyHomotopyOperatorOpens_smul {J : Opens ℝ} (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ))
    (P : M × ↥J → N) (c : ℝ) (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperatorOpens I I' hJ P (c • ω) =
      c • mfamilyHomotopyOperatorOpens I I' hJ P ω := by
  rw [mfamilyHomotopyOperatorOpens_eq_retract, mfamilyHomotopyOperator_smul,
    ← mfamilyHomotopyOperatorOpens_eq_retract]

/-- `mfamilyHomotopyOperatorOpens` commutes with negation. -/
@[simp]
theorem mfamilyHomotopyOperatorOpens_neg {J : Opens ℝ} (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ))
    (P : M × ↥J → N) (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperatorOpens I I' hJ P (-ω) = -mfamilyHomotopyOperatorOpens I I' hJ P ω := by
  rw [mfamilyHomotopyOperatorOpens_eq_retract, mfamilyHomotopyOperator_neg,
    ← mfamilyHomotopyOperatorOpens_eq_retract]

/-- **Stationarity vanishing for `mfamilyHomotopyOperatorOpens`.** If `P (x, u) = y` for every
`u : J` with `(u : ℝ) ∈ (0, 1)`, then `mfamilyHomotopyOperatorOpens I I' hJ P ω x = 0`, with no
differentiability hypothesis on `P`. -/
theorem mfamilyHomotopyOperatorOpens_apply_eq_zero {J : Opens ℝ}
    (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) {P : M × ↥J → N} {x : M} {y : N}
    (hx : ∀ u : J, (u : ℝ) ∈ Ioo (0 : ℝ) 1 → P (x, u) = y) (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperatorOpens I I' hJ P ω x = 0 := by
  rw [mfamilyHomotopyOperatorOpens_eq_retract]
  refine mfamilyHomotopyOperator_apply_eq_zero (y := y) (fun t ht ↦ ?_) ω
  have hcoe : retractOpens hJ t = ⟨t, hJ (Ioo_subset_Icc_self ht)⟩ :=
    retractOpens_coe hJ ⟨t, hJ (Ioo_subset_Icc_self ht)⟩
  dsimp only [Function.comp_apply, Prod.map_apply, id_eq]
  rw [hcoe]
  exact hx ⟨t, hJ (Ioo_subset_Icc_self ht)⟩ ht

/-- `mfamilyHomotopyOperatorOpens` vanishes identically for a time-independent family
`p ∘ Prod.fst`. -/
@[simp]
theorem mfamilyHomotopyOperatorOpens_comp_fst {J : Opens ℝ} (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ))
    (p : M → N) (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperatorOpens I I' hJ (p ∘ (Prod.fst : M × ↥J → M)) ω = 0 :=
  funext fun x ↦ mfamilyHomotopyOperatorOpens_apply_eq_zero hJ (y := p x) (fun _ _ ↦ rfl) ω

/-- **Open source restriction of `mfamilyHomotopyOperatorOpens`.** -/
@[simp]
theorem mpullback_subtype_val_mfamilyHomotopyOperatorOpens {J : Opens ℝ}
    (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) (U : Opens M) (P : M × ↥J → N)
    (ω : RoughForm I' N F (k + 1)) :
    mpullback I I (Subtype.val : U → M) (mfamilyHomotopyOperatorOpens I I' hJ P ω) =
      mfamilyHomotopyOperatorOpens I I' hJ (P ∘ Prod.map (Subtype.val : U → M) id) ω := by
  rw [mfamilyHomotopyOperatorOpens_eq_retract, mpullback_subtype_val_mfamilyHomotopyOperator,
    mfamilyHomotopyOperatorOpens_eq_retract]
  rfl

/-- **Nested open source restriction of `mfamilyHomotopyOperatorOpens`.** -/
@[simp]
theorem mpullback_inclusion_mfamilyHomotopyOperatorOpens {J : Opens ℝ}
    (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) {U W : Opens M} (h : U ≤ W) (P : W × ↥J → N)
    (ω : RoughForm I' N F (k + 1)) :
    mpullback I I (Opens.inclusion h) (mfamilyHomotopyOperatorOpens I I' hJ P ω) =
      mfamilyHomotopyOperatorOpens I I' hJ (P ∘ Prod.map (Opens.inclusion h) id) ω := by
  rw [mfamilyHomotopyOperatorOpens_eq_retract, mpullback_inclusion_mfamilyHomotopyOperator,
    mfamilyHomotopyOperatorOpens_eq_retract]
  rfl

/-- **Open target restriction of `mfamilyHomotopyOperatorOpens`.** -/
@[simp]
theorem mfamilyHomotopyOperatorOpens_mpullback_subtype_val {J : Opens ℝ}
    (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) (U' : Opens N) (P : M × ↥J → U')
    (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperatorOpens I I' hJ P (mpullback I' I' (Subtype.val : U' → N) ω) =
      mfamilyHomotopyOperatorOpens I I' hJ ((Subtype.val : U' → N) ∘ P) ω := by
  rw [mfamilyHomotopyOperatorOpens_eq_retract, mfamilyHomotopyOperator_mpullback_subtype_val,
    mfamilyHomotopyOperatorOpens_eq_retract]
  rfl

/-- **Nested open target restriction of `mfamilyHomotopyOperatorOpens`.** -/
@[simp]
theorem mfamilyHomotopyOperatorOpens_mpullback_inclusion {J : Opens ℝ}
    (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) {U' W' : Opens N} (h : U' ≤ W') (P : M × ↥J → U')
    (ω : RoughForm I' W' F (k + 1)) :
    mfamilyHomotopyOperatorOpens I I' hJ P (mpullback I' I' (Opens.inclusion h) ω) =
      mfamilyHomotopyOperatorOpens I I' hJ (Opens.inclusion h ∘ P) ω := by
  rw [mfamilyHomotopyOperatorOpens_eq_retract, mfamilyHomotopyOperator_mpullback_inclusion,
    mfamilyHomotopyOperatorOpens_eq_retract]
  rfl

/-- **Source naturality of `mfamilyHomotopyOperatorOpens` for maps with invertible derivatives.** -/
theorem mfamilyHomotopyOperatorOpens_comp_prodMap_id {J : Opens ℝ}
    (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) {g : L → M} {P : M × ↥J → N}
    (hg : MDifferentiable I'' I g) (hdg : ∀ z, (mfderiv I'' I g z).IsInvertible)
    (hP : MDifferentiableOn (I.prod 𝓘(ℝ, ℝ)) I' P
      (univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Ioo (0 : ℝ) 1)))
    (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperatorOpens I'' I' hJ (P ∘ Prod.map g id) ω =
      mpullback I'' I g (mfamilyHomotopyOperatorOpens I I' hJ P ω) := by
  rw [mfamilyHomotopyOperatorOpens_eq_retract, mfamilyHomotopyOperatorOpens_eq_retract]
  exact mfamilyHomotopyOperator_comp_prodMap_id hg hdg (mdifferentiableOn_comp_retractOpens hJ hP) ω

/-- **Source naturality of `mfamilyHomotopyOperatorOpens` for continuous forms.** -/
theorem mfamilyHomotopyOperatorOpens_comp_prodMap_id_of_isSmoothForm [IsManifold I 1 M]
    [IsManifold I' 1 N] [CompleteSpace F] {J : Opens ℝ} (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ))
    {g : L → M} {P : M × ↥J → N} (hg : MDifferentiable I'' I g)
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' 1 P (univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Icc (0 : ℝ) 1)))
    {ω : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' 0 ω) :
    mfamilyHomotopyOperatorOpens I'' I' hJ (P ∘ Prod.map g id) ω =
      mpullback I'' I g (mfamilyHomotopyOperatorOpens I I' hJ P ω) := by
  rw [mfamilyHomotopyOperatorOpens_eq_retract, mfamilyHomotopyOperatorOpens_eq_retract]
  exact mfamilyHomotopyOperator_comp_prodMap_id_of_isSmoothForm hg
    (contMDiffOn_comp_retractOpens hJ hP) hω

section HomotopyOpensTargetNaturality

variable {E''' H''' Q : Type*} [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H'''] [TopologicalSpace Q] [ChartedSpace H''' Q]
  {I''' : ModelWithCorners ℝ E''' H'''}

/-- **Target naturality of `mfamilyHomotopyOperatorOpens`.** -/
theorem mfamilyHomotopyOperatorOpens_mpullback {J : Opens ℝ} (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ))
    {P : M × ↥J → N} {q : N → Q}
    (hP : MDifferentiableOn (I.prod 𝓘(ℝ, ℝ)) I' P
      (univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Ioo (0 : ℝ) 1)))
    (hq : MDifferentiable I' I''' q) (η : RoughForm I''' Q F (k + 1)) :
    mfamilyHomotopyOperatorOpens I I' hJ P (mpullback I' I''' q η) =
      mfamilyHomotopyOperatorOpens I I''' hJ (q ∘ P) η := by
  rw [mfamilyHomotopyOperatorOpens_eq_retract, mfamilyHomotopyOperatorOpens_eq_retract]
  exact mfamilyHomotopyOperator_mpullback (mdifferentiableOn_comp_retractOpens hJ hP) hq η

end HomotopyOpensTargetNaturality

/-- **Cylinder-pullback identification for `mfamilyHomotopyOperatorOpens`.** Whenever
`P : M × ↥J → N` is differentiable on `M × (0, 1)`, `mfamilyHomotopyOperatorOpens` agrees with
`TauCeti.homotopyOperator` applied to the cylinder pullback along
`(x, t) ↦ P (x, ⟨t, hJ t.2⟩)` on `M × [0, 1]`. -/
theorem mfamilyHomotopyOperatorOpens_eq_homotopyOperator_mpullback {J : Opens ℝ}
    (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) {P : M × ↥J → N}
    (hP : MDifferentiableOn (I.prod 𝓘(ℝ, ℝ)) I' P
      (univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Ioo (0 : ℝ) 1)))
    (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperatorOpens I I' hJ P ω =
      homotopyOperator (mpullback (I.prod (𝓡∂ 1)) I'
        (P ∘ Prod.map id (fun t : Icc (0 : ℝ) 1 ↦ (⟨t.1, hJ t.2⟩ : J))) ω) := by
  rw [mfamilyHomotopyOperatorOpens_eq_retract,
    mfamilyHomotopyOperator_eq_homotopyOperator_mpullback
      (mdifferentiableOn_comp_retractOpens hJ hP)]
  have hcomp : (P ∘ Prod.map id (retractOpens hJ)) ∘
        Prod.map id (Subtype.val : Icc (0 : ℝ) 1 → ℝ) =
      P ∘ Prod.map id (fun t : Icc (0 : ℝ) 1 ↦ (⟨t.1, hJ t.2⟩ : J)) :=
    funext fun q ↦ congrArg P (Prod.ext rfl (retractOpens_coe hJ ⟨q.2.1, hJ q.2.2⟩))
  rw [hcomp]

/-- `mfamilyHomotopyOperatorOpens` is additive on continuous forms when `P` is `C¹` on
`M × [0, 1]`. -/
theorem mfamilyHomotopyOperatorOpens_add [IsManifold I 1 M] [IsManifold I' 1 N] {J : Opens ℝ}
    (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) {P : M × ↥J → N}
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' 1 P (univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Icc (0 : ℝ) 1)))
    {ω η : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' 0 ω) (hη : IsSmoothForm I' 0 η) :
    mfamilyHomotopyOperatorOpens I I' hJ P (ω + η) =
      mfamilyHomotopyOperatorOpens I I' hJ P ω + mfamilyHomotopyOperatorOpens I I' hJ P η := by
  rw [mfamilyHomotopyOperatorOpens_eq_retract, mfamilyHomotopyOperatorOpens_eq_retract,
    mfamilyHomotopyOperatorOpens_eq_retract]
  exact mfamilyHomotopyOperator_add (contMDiffOn_comp_retractOpens hJ hP) hω hη

/-- `mfamilyHomotopyOperatorOpens` commutes with subtraction of continuous forms when `P` is `C¹`
on `M × [0, 1]`. -/
theorem mfamilyHomotopyOperatorOpens_sub [IsManifold I 1 M] [IsManifold I' 1 N] {J : Opens ℝ}
    (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) {P : M × ↥J → N}
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' 1 P (univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Icc (0 : ℝ) 1)))
    {ω η : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' 0 ω) (hη : IsSmoothForm I' 0 η) :
    mfamilyHomotopyOperatorOpens I I' hJ P (ω - η) =
      mfamilyHomotopyOperatorOpens I I' hJ P ω - mfamilyHomotopyOperatorOpens I I' hJ P η := by
  rw [mfamilyHomotopyOperatorOpens_eq_retract, mfamilyHomotopyOperatorOpens_eq_retract,
    mfamilyHomotopyOperatorOpens_eq_retract]
  exact mfamilyHomotopyOperator_sub (contMDiffOn_comp_retractOpens hJ hP) hω hη

/-- If `P : M × ↥J → N` is `C^(r + 1)` on `M × [0, 1]`, `mfamilyHomotopyOperatorOpens` sends `C^r`
forms on `N` to `C^r` forms on `M`. -/
theorem IsSmoothForm.mfamilyHomotopyOperatorOpens {r : ℕ∞} [IsManifold I 1 M]
    [IsManifold I (r + 1) M] [IsManifold I' 1 N] {J : Opens ℝ}
    (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) {P : M × ↥J → N}
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' (r + 1) P
      (univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Icc (0 : ℝ) 1)))
    {ω : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' r ω) :
    IsSmoothForm I r (TauCeti.mfamilyHomotopyOperatorOpens I I' hJ P ω) := by
  rw [mfamilyHomotopyOperatorOpens_eq_retract]
  exact hω.mfamilyHomotopyOperator (contMDiffOn_comp_retractOpens hJ hP)

/-- **The cochain-homotopy identity for a moving map `P : M × ↥J → N` over `J : Opens ℝ`.** When
`M, N` are `C²` manifolds (possibly with boundary or corners), `P` is `C²` on `M × [0, 1]`, `F` is
a Banach space, and `ω` is a `C¹` `(k + 1)`-form on `N`,
`d(K_P ω) + K_P(dω) = p₁^* ω - p₀^* ω` without invertibility of the slices `p_t`. -/
theorem mextDeriv_mfamilyHomotopyOperatorOpens_add_mfamilyHomotopyOperatorOpens_mextDeriv
    [IsManifold I 2 M] [IsManifold I' 2 N] [CompleteSpace F] {J : Opens ℝ}
    (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) {P : M × ↥J → N}
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' 2 P (univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Icc (0 : ℝ) 1)))
    {ω : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' 1 ω) (x₀ : M) :
    mextDeriv (mfamilyHomotopyOperatorOpens I I' hJ P ω) x₀ +
        mfamilyHomotopyOperatorOpens I I' hJ P (mextDeriv ω) x₀ =
      mpullback I I' (fun x ↦ P (x, ⟨1, hJ (right_mem_Icc.mpr zero_le_one)⟩)) ω x₀ -
        mpullback I I' (fun x ↦ P (x, ⟨0, hJ (left_mem_Icc.mpr zero_le_one)⟩)) ω x₀ := by
  rw [mfamilyHomotopyOperatorOpens_eq_retract, mfamilyHomotopyOperatorOpens_eq_retract]
  refine (mextDeriv_mfamilyHomotopyOperator_add_mfamilyHomotopyOperator_mextDeriv
    (contMDiffOn_comp_retractOpens hJ hP) hω x₀).trans ?_
  have h1 : (fun x : M ↦ (P ∘ Prod.map id (retractOpens hJ)) (x, 1)) =
      fun x : M ↦ P (x, ⟨1, hJ (right_mem_Icc.mpr zero_le_one)⟩) :=
    funext fun x ↦ congrArg P
      (Prod.ext rfl (retractOpens_coe hJ ⟨1, hJ (right_mem_Icc.mpr zero_le_one)⟩))
  have h0 : (fun x : M ↦ (P ∘ Prod.map id (retractOpens hJ)) (x, 0)) =
      fun x : M ↦ P (x, ⟨0, hJ (left_mem_Icc.mpr zero_le_one)⟩) :=
    funext fun x ↦ congrArg P
      (Prod.ext rfl (retractOpens_coe hJ ⟨0, hJ (left_mem_Icc.mpr zero_le_one)⟩))
  rw [h1, h0]

/-- **Closed forms along a smooth homotopy over `J : Opens ℝ`.** When `M, N` are `C²` manifolds
(possibly with boundary or corners), `P : M × ↥J → N` is `C²` on `M × [0, 1]`, `F` is a Banach
space, and `ω` is a closed `C¹` form on `N`, `d(K_P ω) = p₁^* ω - p₀^* ω`. -/
theorem mextDeriv_mfamilyHomotopyOperatorOpens [IsManifold I 2 M] [IsManifold I' 2 N]
    [CompleteSpace F] {J : Opens ℝ} (hJ : Icc (0 : ℝ) 1 ⊆ (J : Set ℝ)) {P : M × ↥J → N}
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' 2 P (univ ×ˢ ((Subtype.val : J → ℝ) ⁻¹' Icc (0 : ℝ) 1)))
    {ω : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' 1 ω) (hclosed : mextDeriv ω = 0)
    (x₀ : M) :
    mextDeriv (mfamilyHomotopyOperatorOpens I I' hJ P ω) x₀ =
      mpullback I I' (fun x ↦ P (x, ⟨1, hJ (right_mem_Icc.mpr zero_le_one)⟩)) ω x₀ -
        mpullback I I' (fun x ↦ P (x, ⟨0, hJ (left_mem_Icc.mpr zero_le_one)⟩)) ω x₀ := by
  rw [← mextDeriv_mfamilyHomotopyOperatorOpens_add_mfamilyHomotopyOperatorOpens_mextDeriv
    hJ hP hω x₀, hclosed, mfamilyHomotopyOperatorOpens_zero, Pi.zero_apply, add_zero]

end Homotopy

end TauCeti
