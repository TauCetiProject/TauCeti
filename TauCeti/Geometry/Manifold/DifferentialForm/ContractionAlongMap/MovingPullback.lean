/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ContractionAlongMap.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Contraction along moving maps, differentiation of moving pullbacks, and homotopy

Let `P : M × T → N` be a family of maps between manifolds (possibly with boundary or corners),
indexed by a `1`-dimensional real parameter space `T` modelled on `𝓘(ℝ, ℝ)` — such as `ℝ` itself
or an open interval `↥J` for `J : TopologicalSpace.Opens ℝ` — with the manifold variable first and
the parameter second. Writing `p_t x = P (x, t)` and `V_t x = dP_{(x, t)} (0, 1)`
(`TauCeti.mfamilyVelocity`), the *family contraction* (`TauCeti.mfamilyContraction`) of a
fixed-coefficient `(k + 1)`-form `ω : RoughForm I' N F (k + 1)` at parameter `t` is

`C_(p_t, V_t) ω = mcontractionAlongMap I I' (fun x ↦ P (x, t)) (mfamilyVelocity I I' P t) ω`.

Equivalently, wherever `P` is differentiable at `(x, t)`, `mfamilyContraction` pulls `ω` back
along `P` to `M × T`, contracts with the unit parameter field `(0, 1)`, and restricts to the slice
`y ↦ (y, t)` (`TauCeti.mfamilyContraction_eq_mpullback_interior_at`).

## Main results

* `TauCeti.mfamilyVelocity`, `TauCeti.mfamilyContraction`: velocity and contraction of a family
  `P : M × T → N`, unified across `T = ℝ` and `T = ↥J` (`J : Opens ℝ`), with restriction to open
  subsets of `M` and `ℝ`, source naturality, target naturality, and joint `C^m` smoothness with an
  extra parameter manifold `L`.
* `TauCeti.hasDerivAt_mpullback_family`: for `P : M × ℝ → N` that is `C²` at `(x, t)` (in
  particular `C²` on `M ×ˢ J` for any open set `J ⊆ ℝ` containing `t`) and `ω` differentiable at
  `P (x, t)`, the pulled-back forms `(p_u^* ω)_x` have derivative
  `d(C_(p_t, V_t) ω)_x + C_(p_t, V_t)(dω)_x` in the fixed fiber
  `TangentSpace I x [⋀^Fin (k + 1)]→L[ℝ] F`, with neither completeness of `F` nor boundarylessness
  of `M` or `N`.
* `TauCeti.hasDerivAt_comp_family_eq_mfamilyContraction_mextDeriv`: degree-zero counterpart
  `∂_t (f ∘ p_t)_x = C_(p_t, V_t)(df)_x 0` for differentiable `P` and `f`.
* `TauCeti.hasDerivAt_mpullback_family_form`: for a jointly differentiable family of forms `ω_u`,
  `∂_t (p_t^* ω_t)_x = (p_t^* (∂_t ω_t))_x + d(C_(p_t, V_t) ω_t)_x + C_(p_t, V_t)(dω_t)_x`.
* `TauCeti.mfamilyContraction_timeDependentFlowOf_of_mem`,
  `TauCeti.mpullback_timeDependentFlowOf_rate_eq_mfamilyContraction`: along the time-dependent
  flow `φ_{s, t}` of `X_t`, `C_(φ_{s, t}, V_t) ω = φ_{s, t}^* (ω.interior (X t))`, identifying the
  moving-form derivative with the Moser pullback derivative of
  `TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk`.
* `TauCeti.mfamilyHomotopyOperator`,
  `TauCeti.mfamilyHomotopyOperator_eq_homotopyOperator_mpullback`,
  `TauCeti.mextDeriv_mfamilyHomotopyOperator_add_mfamilyHomotopyOperator_mextDeriv`: when `P` is
  defined on an open neighbourhood of `M × [0, 1]` and `F` is complete, `K_P ω = ∫₀¹ C_(p_t, V_t) ω`
  agrees with `TauCeti.homotopyOperator` applied to the cylinder pullback of `ω` and satisfies
  `d(K_P ω) + K_P(dω) = p₁^* ω - p₀^* ω` without invertibility of `p_t`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapters 14, 17, and 22.
-/

public section

noncomputable section

open Bundle Set Filter MeasureTheory TopologicalSpace ContinuousAlternatingMap
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

/-! ### Family velocity and contraction along a moving map -/

section FamilyContraction

variable {T : Type*} [TopologicalSpace T] [ChartedSpace ℝ T]

/-- **Parameter velocity of a family of maps.** For `P : M × T → N` over a `1`-dimensional
parameter space `T` modelled on `𝓘(ℝ, ℝ)` (such as `ℝ` or `↥J` for `J : Opens ℝ`),
`mfamilyVelocity I I' P t x` is `dP_{(x, t)} (0, 1) ∈ TangentSpace I' (P (x, t))`. -/
def mfamilyVelocity (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (P : M × T → N) (t : T) (x : M) : TangentSpace I' (P (x, t)) :=
  mfderiv (I.prod 𝓘(ℝ, ℝ)) I' P (x, t) ((0 : E), (1 : ℝ))

/-- **Contraction of a differential form along a moving map `P : M × T → N`.** At parameter `t`,
this contracts `ω` along the slice `x ↦ P (x, t)` and its parameter velocity
`mfamilyVelocity I I' P t`. -/
def mfamilyContraction (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (P : M × T → N) (t : T) (ω : RoughForm I' N F (k + 1)) : RoughForm I M F k :=
  mcontractionAlongMap I I' (fun x ↦ P (x, t)) (mfamilyVelocity I I' P t) ω

theorem mfamilyVelocity_def (P : M × T → N) (t : T) (x : M) :
    mfamilyVelocity I I' P t x = mfderiv (I.prod 𝓘(ℝ, ℝ)) I' P (x, t) ((0 : E), (1 : ℝ)) := (rfl)

theorem mfamilyContraction_def (P : M × T → N) (t : T) (ω : RoughForm I' N F (k + 1)) :
    mfamilyContraction I I' P t ω =
      mcontractionAlongMap I I' (fun x ↦ P (x, t)) (mfamilyVelocity I I' P t) ω := (rfl)

@[simp]
theorem mfamilyContraction_apply (P : M × T → N) (t : T) (ω : RoughForm I' N F (k + 1))
    (x : M) (v : Fin k → TangentSpace I x) :
    mfamilyContraction I I' P t ω x v =
      ω (P (x, t)) (Matrix.vecCons (mfderiv (I.prod 𝓘(ℝ, ℝ)) I' P (x, t) ((0 : E), (1 : ℝ)))
        fun i ↦ mfderiv I I' (fun y ↦ P (y, t)) x (v i)) := by
  rw [mfamilyContraction_def, mcontractionAlongMap_apply, mfamilyVelocity_def]

/-- Where `P` is differentiable at `(x, t)`, `mfamilyVelocity` is the curve derivative of
`u ↦ P (x, u)` at `t` applied to `1`. -/
theorem mfamilyVelocity_eq_mfderiv_slice {P : M × T → N} {t : T} {x : M}
    (hP : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (x, t)) :
    mfamilyVelocity I I' P t x = mfderiv 𝓘(ℝ, ℝ) I' (fun u ↦ P (x, u)) t (1 : ℝ) := by
  have hcomp := mfderiv_comp_apply t hP (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) t)
  have hright : mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun u : T ↦ (x, u)) t
      ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) t) = ((0 : E), (1 : ℝ)) := by
    rw [mfderiv_prod_right]; rfl
  exact (congrArg (mfderiv (I.prod 𝓘(ℝ, ℝ)) I' P (x, t)) hright).symm.trans hcomp.symm

/-- On normed model spaces over `T = ℝ`, `mfamilyContraction` is `TauCeti.familyContraction`. -/
theorem mfamilyContraction_modelSpace (P : E × ℝ → E') (t : ℝ)
    (ω : RoughForm 𝓘(ℝ, E') E' F (k + 1)) :
    mfamilyContraction 𝓘(ℝ, E) 𝓘(ℝ, E') P t ω = familyContraction P t ω := by
  ext x v
  refine (mfamilyContraction_apply P t ω x v).trans
    (Eq.trans ?_ (familyContraction_apply P t ω x v).symm)
  refine congrArg (ω (P (x, t))) (funext fun i ↦ ?_)
  cases i using Fin.cases with
  | zero =>
    simp only [Matrix.cons_val_zero, ← mfamilyVelocity_def]
    by_cases hP : DifferentiableAt ℝ P (x, t)
    · have hmd : MDifferentiableAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E') P (x, t) :=
        mdifferentiableAt_iff_differentiableAt.mpr hP
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hmd
      have hslice : HasFDerivAt (fun u : ℝ ↦ P (x, u))
          ((fderiv ℝ P (x, t)).comp (.inr ℝ E ℝ)) t :=
        hP.hasFDerivAt.comp t (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t)
      refine (mfamilyVelocity_eq_mfderiv_slice hmd).trans ?_
      rw [mfderiv_eq_fderiv, hslice.fderiv]
      rfl
    · rw [mfamilyVelocity_def]
      have hm : ¬MDifferentiableAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E') P (x, t) := fun h ↦
        hP (by
          rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod,
            mdifferentiableAt_iff_differentiableAt] at h
          exact h)
      rw [mfderiv_zero_of_not_mdifferentiableAt hm, fderiv_zero_of_not_differentiableAt hP]; rfl
  | succ i =>
    simp only [Matrix.cons_val_succ, mfderiv_eq_fderiv]; rfl

/-- Where `P` is differentiable at `(x, t)`, `d(p_t)_x w = dP_{(x, t)} (w, 0)`. -/
theorem mfderiv_slice_eq_mfderiv_prod_inl {P : M × T → N} {t : T} {x : M}
    (hP : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (x, t)) (w : TangentSpace I x) :
    mfderiv I I' (fun y ↦ P (y, t)) x w =
      mfderiv (I.prod 𝓘(ℝ, ℝ)) I' P (x, t) (w, (0 : ℝ)) := by
  have hcomp := mfderiv_comp_apply x hP (mdifferentiableAt_id.prodMk mdifferentiableAt_const) w
  have hleft : mfderiv I (I.prod 𝓘(ℝ, ℝ)) (fun y : M ↦ (y, t)) x w = (w, (0 : ℝ)) := by
    rw [mfderiv_prod_left]; rfl
  exact hcomp.trans (congrArg (mfderiv (I.prod 𝓘(ℝ, ℝ)) I' P (x, t)) hleft)

/-- **Cartan-slice description.** Where `P` is differentiable at `(x, t)`, `mfamilyContraction`
equals the pullback along `y ↦ (y, t)` of `(P^* ω).interior (0, 1)` on `M × T`. -/
theorem mfamilyContraction_eq_mpullback_interior_at {P : M × T → N} {t : T} {x : M}
    (hP : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (x, t)) (ω : RoughForm I' N F (k + 1)) :
    mfamilyContraction I I' P t ω x =
      mpullback I (I.prod 𝓘(ℝ, ℝ)) (fun y ↦ (y, t))
        ((mpullback (I.prod 𝓘(ℝ, ℝ)) I' P ω).interior (fun _ ↦ ((0 : E), (1 : ℝ)))) x := by
  ext v
  let unitField : (q : M × T) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) q := fun _ ↦ ((0 : E), (1 : ℝ))
  have hrhs : mpullback I (I.prod 𝓘(ℝ, ℝ)) (fun y ↦ (y, t))
      ((mpullback (I.prod 𝓘(ℝ, ℝ)) I' P ω).interior unitField) x v =
      ω (P (x, t)) (Matrix.vecCons (mfderiv (I.prod 𝓘(ℝ, ℝ)) I' P (x, t) ((0 : E), (1 : ℝ)))
        fun i ↦ mfderiv (I.prod 𝓘(ℝ, ℝ)) I' P (x, t)
          (mfderiv I (I.prod 𝓘(ℝ, ℝ)) (fun y : M ↦ (y, t)) x (v i))) := by
    rw [mpullback_apply, RoughForm.interior_apply, mpullback_apply]
    exact congrArg (ω (P (x, t))) (funext fun i ↦ by cases i using Fin.cases <;> rfl)
  refine (mfamilyContraction_apply P t ω x v).trans (Eq.trans ?_ hrhs.symm)
  refine congrArg (ω (P (x, t))) (funext fun i ↦ ?_)
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [Matrix.cons_val_succ]
    have hleft : mfderiv I (I.prod 𝓘(ℝ, ℝ)) (fun y : M ↦ (y, t)) x (v i) = (v i, (0 : ℝ)) := by
      rw [mfderiv_prod_left]; rfl
    exact (mfderiv_slice_eq_mfderiv_prod_inl hP (v i)).trans
      (congrArg (mfderiv (I.prod 𝓘(ℝ, ℝ)) I' P (x, t)) hleft.symm)

theorem mfamilyContraction_eq_mpullback_interior {P : M × T → N}
    (hP : MDifferentiable (I.prod 𝓘(ℝ, ℝ)) I' P) (t : T) (ω : RoughForm I' N F (k + 1)) :
    mfamilyContraction I I' P t ω =
      mpullback I (I.prod 𝓘(ℝ, ℝ)) (fun y ↦ (y, t))
        ((mpullback (I.prod 𝓘(ℝ, ℝ)) I' P ω).interior (fun _ ↦ ((0 : E), (1 : ℝ)))) :=
  funext fun x ↦ mfamilyContraction_eq_mpullback_interior_at (hP (x, t)) ω

@[simp]
theorem mfamilyContraction_zero (P : M × T → N) (t : T) :
    mfamilyContraction I I' P t (0 : RoughForm I' N F (k + 1)) = 0 :=
  mcontractionAlongMap_zero _ _

@[simp]
theorem mfamilyContraction_add (P : M × T → N) (t : T) (ω η : RoughForm I' N F (k + 1)) :
    mfamilyContraction I I' P t (ω + η) =
      mfamilyContraction I I' P t ω + mfamilyContraction I I' P t η :=
  mcontractionAlongMap_add _ _ ω η

@[simp]
theorem mfamilyContraction_smul (P : M × T → N) (t : T) (c : ℝ) (ω : RoughForm I' N F (k + 1)) :
    mfamilyContraction I I' P t (c • ω) = c • mfamilyContraction I I' P t ω :=
  mcontractionAlongMap_smul _ _ c ω

@[simp]
theorem mfamilyContraction_neg (P : M × T → N) (t : T) (ω : RoughForm I' N F (k + 1)) :
    mfamilyContraction I I' P t (-ω) = -mfamilyContraction I I' P t ω :=
  mcontractionAlongMap_neg _ _ ω

@[simp]
theorem mfamilyContraction_sub (P : M × T → N) (t : T) (ω η : RoughForm I' N F (k + 1)) :
    mfamilyContraction I I' P t (ω - η) =
      mfamilyContraction I I' P t ω - mfamilyContraction I I' P t η :=
  mcontractionAlongMap_sub _ _ ω η

/-! ### Restriction and naturality of `mfamilyContraction` -/

/-- **Source naturality.** Precomposing `P : M × T → N` with `h × id : L × T → M × T` pulls
`mfamilyContraction` back along `h`. -/
theorem mfamilyContraction_comp_prodMap_id_at {h : L → M} {P : M × T → N} {t : T}
    {ω : RoughForm I' N F (k + 1)} {z : L}
    (hh : MDifferentiableAt I'' I h z)
    (hP : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (h z, t)) :
    mfamilyContraction I'' I' (P ∘ Prod.map h id) t ω z =
      mpullback I'' I h (mfamilyContraction I I' P t ω) z := by
  have hPt : MDifferentiableAt I I' (fun y ↦ P (y, t)) (h z) :=
    hP.comp (h z) (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have hvel : mfamilyVelocity I'' I' (P ∘ Prod.map h id) t z = mfamilyVelocity I I' P t (h z) := by
    have hpm : MDifferentiableAt (I''.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (Prod.map h (id : T → T)) (z, t) := hh.prodMap mdifferentiableAt_id
    let u0 : TangentSpace (I''.prod 𝓘(ℝ, ℝ)) (z, t) := ((0 : E''), (1 : ℝ))
    have hc := mfderiv_comp_apply (z, t) hP hpm u0
    have hpm_apply : mfderiv (I''.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (Prod.map h (id : T → T)) (z, t) u0 = ((0 : E), (1 : ℝ)) := by
      rw [mfderiv_prodMap (p := (z, t)) hh mdifferentiableAt_id, mfderiv_id]
      refine Prod.ext ?_ rfl
      exact _root_.map_zero (mfderiv I'' I h z)
    exact hc.trans (congrArg (mfderiv (I.prod 𝓘(ℝ, ℝ)) I' P (h z, t)) hpm_apply)
  refine (mcontractionAlongMap_congr_field_at
    (W := fun w ↦ mfamilyVelocity I I' P t (h w)) ω hvel).trans ?_
  exact mcontractionAlongMap_comp_right_at (p := fun y ↦ P (y, t)) hh hPt

theorem mfamilyContraction_comp_prodMap_id {h : L → M} {P : M × T → N} (t : T)
    (ω : RoughForm I' N F (k + 1)) (hh : MDifferentiable I'' I h)
    (hP : MDifferentiable (I.prod 𝓘(ℝ, ℝ)) I' P) :
    mfamilyContraction I'' I' (P ∘ Prod.map h id) t ω =
      mpullback I'' I h (mfamilyContraction I I' P t ω) :=
  funext fun z ↦ mfamilyContraction_comp_prodMap_id_at (hh z) (hP (h z, t))

section TargetNaturality

variable {E''' H''' Q : Type*} [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H'''] [TopologicalSpace Q] [ChartedSpace H''' Q]
  {I''' : ModelWithCorners ℝ E''' H'''}

/-- **Target naturality.** Pulling `η` back along `q : N → Q` before `mfamilyContraction` along `P`
is `mfamilyContraction` of `η` along `q ∘ P`. -/
theorem mfamilyContraction_mpullback_at {P : M × T → N} {q : N → Q} {t : T}
    {η : RoughForm I''' Q F (k + 1)} {x : M}
    (hP : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (x, t))
    (hq : MDifferentiableAt I' I''' q (P (x, t))) :
    mfamilyContraction I I' P t (mpullback I' I''' q η) x =
      mfamilyContraction I I''' (q ∘ P) t η x := by
  have hPt : MDifferentiableAt I I' (fun y ↦ P (y, t)) x :=
    hP.comp x (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  let u0 : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, t) := ((0 : E), (1 : ℝ))
  have hvel : mfderiv I' I''' q (P (x, t)) (mfamilyVelocity I I' P t x) =
      mfamilyVelocity I I''' (q ∘ P) t x :=
    (mfderiv_comp_apply (x, t) hq hP u0).symm
  exact (mcontractionAlongMap_mpullback_at (p := fun y ↦ P (y, t)) hPt hq).trans
    (mcontractionAlongMap_congr_field_at η hvel)

theorem mfamilyContraction_mpullback {P : M × T → N} {q : N → Q} (t : T)
    (η : RoughForm I''' Q F (k + 1)) (hP : MDifferentiable (I.prod 𝓘(ℝ, ℝ)) I' P)
    (hq : MDifferentiable I' I''' q) :
    mfamilyContraction I I' P t (mpullback I' I''' q η) =
      mfamilyContraction I I''' (q ∘ P) t η :=
  funext fun x ↦ mfamilyContraction_mpullback_at (hP (x, t)) (hq (P (x, t)))

end TargetNaturality

private theorem contMDiff_subtypeVal_comp {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
    {n : WithTop ℕ∞} {U : Opens M₂} {f : M₁ → U}
    (hf : ContMDiff I₁ I₂ n (Subtype.val ∘ f)) : ContMDiff I₁ I₂ n f :=
  fun x ↦ (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff f univ x).mp (hf x)

/-- **Open source restriction.** Restricting `mfamilyContraction` to `U : Opens M` contracts the
restricted family `P ∘ Prod.map Subtype.val id`. -/
@[simp]
theorem mpullback_subtype_val_mfamilyContraction (U : Opens M) (P : M × T → N) (t : T)
    (ω : RoughForm I' N F (k + 1)) :
    mpullback I I (Subtype.val : U → M) (mfamilyContraction I I' P t ω) =
      mfamilyContraction I I' (P ∘ Prod.map (Subtype.val : U → M) id) t ω := by
  rw [mfamilyContraction_def, mpullback_subtype_val_mcontractionAlongMap]
  funext x; refine mcontractionAlongMap_congr_field_at ω ?_
  let V_prod : Opens (M × T) := ⟨(U : Set M) ×ˢ univ, U.isOpen.prod isOpen_univ⟩
  let φ_open : U × T → V_prod := fun q ↦ ⟨(q.1.1, q.2), Set.mk_mem_prod q.1.2 (mem_univ _)⟩
  let ψ_open : V_prod → U × T := fun q ↦ (⟨q.1.1, (Set.mem_prod.mp q.2).1⟩, q.1.2)
  have hφ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) 1 φ_open :=
    contMDiff_subtypeVal_comp ((contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd)
  have hψ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) 1 ψ_open :=
    (contMDiff_subtypeVal_comp (contMDiff_fst.comp contMDiff_subtype_val)).prodMk
      (contMDiff_snd.comp contMDiff_subtype_val)
  let v_ut : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, t) := ((0 : E), (1 : ℝ))
  let v_vp : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (φ_open (x, t)) := ((0 : E), (1 : ℝ))
  have h_amb : mfderiv (I.prod 𝓘(ℝ, ℝ)) I' (P ∘ (Subtype.val : V_prod → M × T))
      (φ_open (x, t)) v_vp = mfamilyVelocity I I' P t (x : M) :=
    Manifold.mfderiv_comp_subtype_val_apply (J := I.prod 𝓘(ℝ, ℝ)) (I := I')
      (U := V_prod) (f := P) (x := φ_open (x, t)) v_vp
  by_cases hPd : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' (P ∘ (Subtype.val : V_prod → M × T))
      (φ_open (x, t))
  · have hφd : mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) φ_open (x, t) v_ut = v_vp := by
      apply Manifold.mfderiv_subtype_val_injective (I := I.prod 𝓘(ℝ, ℝ)) (φ_open (x, t))
      have hc1 := (mfderiv_comp_apply (x, t)
        (contMDiff_subtype_val.mdifferentiableAt one_ne_zero)
        (hφ.mdifferentiableAt one_ne_zero) v_ut).symm
      have hc2 : mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
          (Prod.map (Subtype.val : U → M) (id : T → T)) (x, t) v_ut = ((0 : E), (1 : ℝ)) := by
        rw [mfderiv_prodMap (p := (x, t))
          (contMDiff_subtype_val.mdifferentiableAt one_ne_zero) mdifferentiableAt_id, mfderiv_id]
        refine Prod.ext ?_ rfl; exact _root_.map_zero (mfderiv I I (Subtype.val : U → M) x)
      have hc3 : mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (Subtype.val : V_prod → M × T)
          (φ_open (x, t)) v_vp = ((0 : E), (1 : ℝ)) := by
        rw [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
          Manifold.tangentSpaceOpenEquiv_apply]
      exact hc1.trans (hc2.trans hc3.symm)
    have h1 := mfderiv_comp_apply (x, t) hPd (hφ.mdifferentiableAt one_ne_zero) v_ut
    exact h_amb.symm.trans ((congrArg _ hφd.symm).trans h1.symm)
  · have hPd' : ¬MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I'
        (P ∘ Prod.map (Subtype.val : U → M) id) (x, t) := fun h ↦
      hPd ((h.comp (φ_open (x, t)) (hψ.mdifferentiableAt one_ne_zero))
        |>.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl))
    have hz1 : mfderiv (I.prod 𝓘(ℝ, ℝ)) I' (P ∘ (Subtype.val : V_prod → M × T))
        (φ_open (x, t)) v_vp = 0 := by
      rw [mfderiv_zero_of_not_mdifferentiableAt hPd]; exact zero_apply _
    have hz2 : mfamilyVelocity I I' (P ∘ Prod.map (Subtype.val : U → M) id) t x = 0 := by
      change mfderiv (I.prod 𝓘(ℝ, ℝ)) I' (P ∘ Prod.map (Subtype.val : U → M) id) (x, t) v_ut = 0
      rw [mfderiv_zero_of_not_mdifferentiableAt hPd']; exact zero_apply _
    exact h_amb.symm.trans (hz1.trans hz2.symm)

end FamilyContraction

/-- **Open parameter restriction.** Restricting `P : M × ℝ → N` to `J : Opens ℝ` preserves
`mfamilyContraction` at `t : J`. -/
@[simp]
theorem mfamilyContraction_comp_prodMap_subtype_val (J : Opens ℝ) (P : M × ℝ → N) (t : J)
    (ω : RoughForm I' N F (k + 1)) :
    mfamilyContraction I I' (P ∘ Prod.map id (Subtype.val : J → ℝ)) t ω =
      mfamilyContraction I I' P (t : ℝ) ω := by
  funext x; refine mcontractionAlongMap_congr_field_at ω ?_
  let V_prod : Opens (M × ℝ) := ⟨univ ×ˢ (J : Set ℝ), isOpen_univ.prod J.isOpen⟩
  let φ_open : M × J → V_prod := fun q ↦ ⟨(q.1, q.2.1), Set.mk_mem_prod (mem_univ _) q.2.2⟩
  let ψ_open : V_prod → M × J := fun q ↦ (q.1.1, ⟨q.1.2, (Set.mem_prod.mp q.2).2⟩)
  have hφ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) 1 φ_open :=
    contMDiff_subtypeVal_comp (contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd))
  have hψ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) 1 ψ_open :=
    (contMDiff_fst.comp contMDiff_subtype_val).prodMk
      (contMDiff_subtypeVal_comp (contMDiff_snd.comp contMDiff_subtype_val))
  let v_mj : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, t) := ((0 : E), (1 : ℝ))
  let v_vp : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (φ_open (x, t)) := ((0 : E), (1 : ℝ))
  have h_amb : mfderiv (I.prod 𝓘(ℝ, ℝ)) I' (P ∘ (Subtype.val : V_prod → M × ℝ))
      (φ_open (x, t)) v_vp = mfamilyVelocity I I' P (t : ℝ) x :=
    Manifold.mfderiv_comp_subtype_val_apply (J := I.prod 𝓘(ℝ, ℝ)) (I := I')
      (U := V_prod) (f := P) (x := φ_open (x, t)) v_vp
  by_cases hPd : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' (P ∘ (Subtype.val : V_prod → M × ℝ))
      (φ_open (x, t))
  · have hφd : mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) φ_open (x, t) v_mj = v_vp := by
      apply Manifold.mfderiv_subtype_val_injective (I := I.prod 𝓘(ℝ, ℝ)) (φ_open (x, t))
      have hc1 := (mfderiv_comp_apply (x, t)
        (contMDiff_subtype_val.mdifferentiableAt one_ne_zero)
        (hφ.mdifferentiableAt one_ne_zero) v_mj).symm
      have hc2 : mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
          (Prod.map (id : M → M) (Subtype.val : J → ℝ)) (x, t) v_mj = ((0 : E), (1 : ℝ)) := by
        rw [mfderiv_prodMap (p := (x, t)) mdifferentiableAt_id
          (contMDiff_subtype_val.mdifferentiableAt one_ne_zero), mfderiv_id]
        refine Prod.ext rfl ?_; let one_t : TangentSpace 𝓘(ℝ, ℝ) t := (1 : ℝ)
        change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : J → ℝ) t one_t = (1 : ℝ)
        rw [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
          Manifold.tangentSpaceOpenEquiv_apply]
      have hc3 : mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) (Subtype.val : V_prod → M × ℝ)
          (φ_open (x, t)) v_vp = ((0 : E), (1 : ℝ)) := by
        rw [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
          Manifold.tangentSpaceOpenEquiv_apply]
      exact hc1.trans (hc2.trans hc3.symm)
    have h1 := mfderiv_comp_apply (x, t) hPd (hφ.mdifferentiableAt one_ne_zero) v_mj
    exact h1.trans ((congrArg _ hφd).trans h_amb)
  · have hPd' : ¬MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I'
        (P ∘ Prod.map id (Subtype.val : J → ℝ)) (x, t) := fun h ↦
      hPd ((h.comp (φ_open (x, t)) (hψ.mdifferentiableAt one_ne_zero))
        |>.congr_of_eventuallyEq (Eventually.of_forall fun _ ↦ rfl))
    have hz1 : mfamilyVelocity I I' (P ∘ Prod.map id (Subtype.val : J → ℝ)) t x = 0 := by
      change mfderiv (I.prod 𝓘(ℝ, ℝ)) I' (P ∘ Prod.map id (Subtype.val : J → ℝ)) (x, t) v_mj = 0
      rw [mfderiv_zero_of_not_mdifferentiableAt hPd']; exact zero_apply _
    have hz2 : mfderiv (I.prod 𝓘(ℝ, ℝ)) I' (P ∘ (Subtype.val : V_prod → M × ℝ))
        (φ_open (x, t)) v_vp = 0 := by
      rw [mfderiv_zero_of_not_mdifferentiableAt hPd]; exact zero_apply _
    exact hz1.trans (hz2.symm.trans h_amb)

/-- **Nested open parameter restriction.** Restricting `P : M × ↥J₂ → N` along `J₁ ≤ J₂` in
`Opens ℝ` preserves `mfamilyContraction`. -/
@[simp]
theorem mfamilyContraction_comp_prodMap_inclusion {J₁ J₂ : Opens ℝ} (hJ : J₁ ≤ J₂)
    (P : M × ↥J₂ → N) (t : J₁) (ω : RoughForm I' N F (k + 1)) :
    mfamilyContraction I I' (P ∘ Prod.map id (Opens.inclusion hJ)) t ω =
      mfamilyContraction I I' P (Opens.inclusion hJ t) ω := by
  classical
  let P' : M × ℝ → N := fun q ↦
    if h : q.2 ∈ J₂ then P (q.1, ⟨q.2, h⟩) else P (q.1, Opens.inclusion hJ t)
  have h₂ : P' ∘ Prod.map id (Subtype.val : J₂ → ℝ) = P := funext fun q ↦ dite_eq_left q.2.2
  have h₁ : P' ∘ Prod.map id (Subtype.val : J₁ → ℝ) = P ∘ Prod.map id (Opens.inclusion hJ) :=
    funext fun q ↦ dite_eq_left (hJ q.2.2)
  rw [← h₁, mfamilyContraction_comp_prodMap_subtype_val, ← h₂,
    mfamilyContraction_comp_prodMap_subtype_val]

/-! ### Joint smoothness with extra parameters -/

section Smooth

variable [IsManifold I 1 M] [IsManifold I' 1 N]

private theorem contMDiff_tangentBundle_mk_one_real {m : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ) : ModelWithCorners ℝ ℝ ℝ).tangent m
      (fun u : ℝ ↦ (TotalSpace.mk' ℝ u (1 : ℝ) : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
  (contMDiff_vectorSpace_iff_contDiff (V := fun _ : ℝ ↦ (1 : ℝ))).2 contDiff_const

private theorem contMDiff_tangentBundle_mk_one_opens {m : WithTop ℕ∞} (J : Opens ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ) : ModelWithCorners ℝ ℝ ℝ).tangent m
      (fun u : J ↦
        (TotalSpace.mk' ℝ u ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) u) : TangentBundle 𝓘(ℝ, ℝ) J)) := by
  intro u₀
  have hamb : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ) : ModelWithCorners ℝ ℝ ℝ).tangent m
      (fun u : J ↦ (TotalSpace.mk' ℝ (u : ℝ) (1 : ℝ) : TangentBundle 𝓘(ℝ, ℝ) ℝ)) u₀ :=
    (contMDiff_tangentBundle_mk_one_real.comp contMDiff_subtype_val).contMDiffAt
  rw [Bundle.contMDiffAt_totalSpace_iff] at hamb ⊢
  refine ⟨contMDiffAt_id, hamb.2.congr_of_eventuallyEq ?_⟩
  let eJ := trivializationAt ℝ (TangentSpace 𝓘(ℝ, ℝ) : J → Type _) u₀
  let eR := trivializationAt ℝ (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _) (u₀ : ℝ)
  filter_upwards [eJ.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' u₀),
    continuousAt_subtype_val.preimage_mem_nhds
      (eR.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (u₀ : ℝ))),
    Manifold.eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq (I := 𝓘(ℝ, ℝ)) u₀]
    with u huJ huR hsymm
  let one_u : TangentSpace 𝓘(ℝ, ℝ) u := (1 : ℝ)
  let one_uR : TangentSpace 𝓘(ℝ, ℝ) (u : ℝ) := (1 : ℝ)
  have h1 : one_u = eJ.symmL ℝ u (eR.continuousLinearMapAt ℝ (u : ℝ) one_uR) := by
    apply (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, ℝ)) u).injective
    rw [hsymm, eR.symmL_continuousLinearMapAt huR]
    exact Manifold.tangentSpaceOpenEquiv_apply (I := 𝓘(ℝ, ℝ)) u one_u
  change (eJ ⟨u, one_u⟩).2 = (eR ⟨(u : ℝ), one_uR⟩).2
  rw [← eJ.continuousLinearMapAt_apply_of_mem (R := ℝ) huJ,
    ← eR.continuousLinearMapAt_apply_of_mem (R := ℝ) huR, h1, eJ.continuousLinearMapAt_symmL huJ]

private theorem contMDiffAt_mfamilyVelocity_of_one
    {T : Type*} [TopologicalSpace T] [ChartedSpace ℝ T] [IsManifold 𝓘(ℝ, ℝ) 1 T]
    [IsManifold I'' 1 L] {m n : WithTop ℕ∞}
    (hone : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ) : ModelWithCorners ℝ ℝ ℝ).tangent m
      (fun u : T ↦
        (TotalSpace.mk' ℝ u ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) u) : TangentBundle 𝓘(ℝ, ℝ) T)))
    {P : L × (M × T) → N} {q₀ : L} {x₀ : M} {t₀ : T}
    (hP : ContMDiffAt (I''.prod (I.prod 𝓘(ℝ, ℝ))) I' n P (q₀, (x₀, t₀))) (hmn : m + 1 ≤ n) :
    ContMDiffAt (I''.prod (I.prod 𝓘(ℝ, ℝ))) I'.tangent m
      (fun r : L × (M × T) ↦
        TotalSpace.mk' E' (P r) (TauCeti.mfamilyVelocity I I' (fun p ↦ P (r.1, p)) r.2.2 r.2.1))
      (q₀, (x₀, t₀)) := by
  set r₀ : L × (M × T) := (q₀, (x₀, t₀))
  let f : L × (M × T) → M × T → N := fun r p ↦ P (r.1, p)
  let g : L × (M × T) → M × T := Prod.snd
  have hf : ContMDiffAt ((I''.prod (I.prod 𝓘(ℝ, ℝ))).prod (I.prod 𝓘(ℝ, ℝ))) I' n
      (Function.uncurry f) (r₀, g r₀) :=
    hP.comp (r₀, g r₀) ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).contMDiffAt
  have hdf := hf.mfderiv f g contMDiffAt_snd hmn
  let v_sec : (r : L × (M × T)) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) (g r) :=
    fun _ ↦ ((0 : E), (1 : ℝ))
  have hA : ContMDiff (I''.prod (I.prod 𝓘(ℝ, ℝ))) (I.prod 𝓘(ℝ, ℝ)).tangent m
      (fun r : L × (M × T) ↦
        (TotalSpace.mk' (E × ℝ) (g r) (v_sec r) : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × T))) :=
    (contMDiff_equivTangentBundleProd_symm.comp
      ((contMDiff_tangentBundle_mk_zero (contMDiff_fst.comp contMDiff_snd)).prodMk
        (hone.comp (contMDiff_snd.comp contMDiff_snd)))).congr fun _ ↦ rfl
  have hA_coord := (Bundle.contMDiffAt_totalSpace_iff.mp (hA.contMDiffAt (x := r₀))).2
  have hP_m : ContMDiffAt (I''.prod (I.prod 𝓘(ℝ, ℝ))) I' m P r₀ :=
    hP.of_le ((le_add_of_nonneg_right zero_le_one).trans hmn)
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨hP_m, (hdf.clm_apply hA_coord).congr_of_eventuallyEq ?_⟩
  set e_dom := trivializationAt (E × ℝ) (TangentSpace (I.prod 𝓘(ℝ, ℝ))) (g r₀)
  set e_cod := trivializationAt E' (TangentSpace I') (P r₀)
  filter_upwards [continuousAt_snd.preimage_mem_nhds
      (e_dom.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (g r₀))),
    hP_m.continuousAt.preimage_mem_nhds
      (e_cod.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (P r₀)))]
    with r hr_dom hr_cod
  change (e_cod ⟨P r, mfamilyVelocity I I' (fun p ↦ P (r.1, p)) r.2.2 r.2.1⟩).2 =
    inTangentCoordinates (I.prod 𝓘(ℝ, ℝ)) I' g (fun s ↦ f s (g s))
      (fun s ↦ mfderiv (I.prod 𝓘(ℝ, ℝ)) I' (f s) (g s)) r₀ r (e_dom ⟨g r, v_sec r⟩).2
  rw [← e_cod.continuousLinearMapAt_apply_of_mem (R := ℝ) hr_cod,
    ← e_dom.continuousLinearMapAt_apply_of_mem (R := ℝ) hr_dom]
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.coe_comp, Function.comp_apply, g, f, mfamilyVelocity_def]
  rw [e_dom.symmL_continuousLinearMapAt hr_dom]

private theorem contMDiffAt_mfamilyContraction_of_one
    {T : Type*} [TopologicalSpace T] [ChartedSpace ℝ T] [IsManifold 𝓘(ℝ, ℝ) 1 T]
    [IsManifold I'' 1 L] {m n : WithTop ℕ∞}
    (hone : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ) : ModelWithCorners ℝ ℝ ℝ).tangent m
      (fun u : T ↦
        (TotalSpace.mk' ℝ u ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) u) : TangentBundle 𝓘(ℝ, ℝ) T)))
    {ω : RoughForm I' N F (k + 1)} {P : L × (M × T) → N} {q₀ : L} {x₀ : M} {t₀ : T}
    (hω : ContMDiffAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F) y (ω y)) (P (q₀, (x₀, t₀))))
    (hP : ContMDiffAt (I''.prod (I.prod 𝓘(ℝ, ℝ))) I' n P (q₀, (x₀, t₀))) (hmn : m + 1 ≤ n) :
    ContMDiffAt (I''.prod (I.prod 𝓘(ℝ, ℝ))) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun r : L × (M × T) ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) r.2.1
        (TauCeti.mfamilyContraction I I' (fun p ↦ P (r.1, p)) r.2.2 ω r.2.1))
      (q₀, (x₀, t₀)) := by
  let p_fam : L × (M × T) → M → N := fun r y ↦ P (r.1, (y, r.2.2))
  let g_fam : L × (M × T) → M := fun r ↦ r.2.1
  let V_fam : (r : L × (M × T)) → (y : M) → TangentSpace I' (p_fam r y) :=
    fun r y ↦ TauCeti.mfamilyVelocity I I' (fun p ↦ P (r.1, p)) r.2.2 y
  have hswap : ContMDiff ((I''.prod (I.prod 𝓘(ℝ, ℝ))).prod I) (I''.prod (I.prod 𝓘(ℝ, ℝ))) n
      (fun s : (L × (M × T)) × M ↦ (s.1.1, (s.2, s.1.2.2))) :=
    (contMDiff_fst.comp contMDiff_fst).prodMk
      (contMDiff_snd.prodMk (contMDiff_snd.comp (contMDiff_snd.comp contMDiff_fst)))
  have hp_fam := hP.comp ((q₀, (x₀, t₀)), x₀) hswap.contMDiffAt
  have hg_fam : ContMDiffAt (I''.prod (I.prod 𝓘(ℝ, ℝ))) I m g_fam (q₀, (x₀, t₀)) :=
    (contMDiff_fst.comp contMDiff_snd).contMDiffAt
  exact hω.mcontractionAlongMap_family (p := p_fam) (g := g_fam) (V := V_fam) hp_fam hg_fam
    (contMDiffAt_mfamilyVelocity_of_one hone hP hmn) hmn

/-- **Joint `C^m` smoothness of `mfamilyVelocity` over `ℝ`.** If `P : L × (M × ℝ) → N` is `C^n` at
`(q₀, (x₀, t₀))` with `m + 1 ≤ n`, then `(q, (x, t)) ↦ (P (q, (x, t)), V_{q, t} x)` is `C^m` into
`TN` at `(q₀, (x₀, t₀))`. -/
theorem _root_.ContMDiffAt.mfamilyVelocity [IsManifold I'' 1 L] {m n : WithTop ℕ∞}
    {P : L × (M × ℝ) → N} {q₀ : L} {x₀ : M} {t₀ : ℝ}
    (hP : ContMDiffAt (I''.prod (I.prod 𝓘(ℝ, ℝ))) I' n P (q₀, (x₀, t₀))) (hmn : m + 1 ≤ n) :
    ContMDiffAt (I''.prod (I.prod 𝓘(ℝ, ℝ))) I'.tangent m
      (fun r : L × (M × ℝ) ↦ TotalSpace.mk' E' (P r)
        (TauCeti.mfamilyVelocity I I' (fun p ↦ P (r.1, p)) r.2.2 r.2.1)) (q₀, (x₀, t₀)) :=
  contMDiffAt_mfamilyVelocity_of_one contMDiff_tangentBundle_mk_one_real hP hmn

/-- **Joint `C^m` smoothness of `mfamilyVelocity` over `J : Opens ℝ`.** -/
theorem _root_.ContMDiffAt.mfamilyVelocity_opens [IsManifold I'' 1 L] {m n : WithTop ℕ∞}
    {J : Opens ℝ} {P : L × (M × ↥J) → N} {q₀ : L} {x₀ : M} {t₀ : J}
    (hP : ContMDiffAt (I''.prod (I.prod 𝓘(ℝ, ℝ))) I' n P (q₀, (x₀, t₀))) (hmn : m + 1 ≤ n) :
    ContMDiffAt (I''.prod (I.prod 𝓘(ℝ, ℝ))) I'.tangent m
      (fun r : L × (M × ↥J) ↦ TotalSpace.mk' E' (P r)
        (TauCeti.mfamilyVelocity I I' (fun p ↦ P (r.1, p)) r.2.2 r.2.1)) (q₀, (x₀, t₀)) :=
  contMDiffAt_mfamilyVelocity_of_one (contMDiff_tangentBundle_mk_one_opens J) hP hmn

/-- **Joint `C^m` smoothness of `mfamilyContraction` over `ℝ` with an extra parameter `L`.** -/
theorem _root_.ContMDiffAt.mfamilyContraction [IsManifold I'' 1 L] {m n : WithTop ℕ∞}
    {ω : RoughForm I' N F (k + 1)} {P : L × (M × ℝ) → N} {q₀ : L} {x₀ : M} {t₀ : ℝ}
    (hω : ContMDiffAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F) y (ω y)) (P (q₀, (x₀, t₀))))
    (hP : ContMDiffAt (I''.prod (I.prod 𝓘(ℝ, ℝ))) I' n P (q₀, (x₀, t₀))) (hmn : m + 1 ≤ n) :
    ContMDiffAt (I''.prod (I.prod 𝓘(ℝ, ℝ))) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun r : L × (M × ℝ) ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) r.2.1
        (TauCeti.mfamilyContraction I I' (fun p ↦ P (r.1, p)) r.2.2 ω r.2.1)) (q₀, (x₀, t₀)) :=
  contMDiffAt_mfamilyContraction_of_one contMDiff_tangentBundle_mk_one_real hω hP hmn

/-- **Joint `C^m` smoothness of `mfamilyContraction` over `J : Opens ℝ` with parameter `L`.** -/
theorem _root_.ContMDiffAt.mfamilyContraction_opens [IsManifold I'' 1 L] {m n : WithTop ℕ∞}
    {J : Opens ℝ} {ω : RoughForm I' N F (k + 1)} {P : L × (M × ↥J) → N} {q₀ : L} {x₀ : M} {t₀ : J}
    (hω : ContMDiffAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F) y (ω y)) (P (q₀, (x₀, t₀))))
    (hP : ContMDiffAt (I''.prod (I.prod 𝓘(ℝ, ℝ))) I' n P (q₀, (x₀, t₀))) (hmn : m + 1 ≤ n) :
    ContMDiffAt (I''.prod (I.prod 𝓘(ℝ, ℝ))) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun r : L × (M × ↥J) ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) r.2.1
        (TauCeti.mfamilyContraction I I' (fun p ↦ P (r.1, p)) r.2.2 ω r.2.1)) (q₀, (x₀, t₀)) :=
  contMDiffAt_mfamilyContraction_of_one (contMDiff_tangentBundle_mk_one_opens J) hω hP hmn

/-- Contracting a `C^m` form along a `C^(m + 1)` family `P : M × ℝ → N` at fixed `t` produces a
`C^m` form on `M`. -/
theorem IsSmoothForm.mfamilyContraction {m : WithTop ℕ∞} {P : M × ℝ → N} {t : ℝ}
    {ω : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' m ω)
    (hP : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' (m + 1) P) :
    IsSmoothForm I m (TauCeti.mfamilyContraction I I' P t ω) := by
  refine (isSmoothForm_def m _).mpr fun x ↦ ?_
  have hjoint := ((isSmoothForm_def m ω).mp hω (P (x, t))).mfamilyContraction (I'' := 𝓘(ℝ, ℝ))
    (P := fun r : ℝ × (M × ℝ) ↦ P r.2) (q₀ := 0) (x₀ := x) (t₀ := t)
    (hP.comp contMDiff_snd).contMDiffAt le_rfl
  exact hjoint.comp x (contMDiffAt_const.prodMk (contMDiffAt_id.prodMk contMDiffAt_const))

/-- Contracting a `C^m` form along a `C^(m + 1)` family `P : M × ↥J → N` (`J : Opens ℝ`) at fixed
`t : J` produces a `C^m` form on `M`. -/
theorem IsSmoothForm.mfamilyContraction_opens {m : WithTop ℕ∞} {J : Opens ℝ} {P : M × ↥J → N}
    {t : J} {ω : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' m ω)
    (hP : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' (m + 1) P) :
    IsSmoothForm I m (TauCeti.mfamilyContraction I I' P t ω) := by
  refine (isSmoothForm_def m _).mpr fun x ↦ ?_
  have hjoint := ((isSmoothForm_def m ω).mp hω (P (x, t))).mfamilyContraction_opens (I'' := 𝓘(ℝ, ℝ))
    (P := fun r : ℝ × (M × ↥J) ↦ P r.2) (q₀ := 0) (x₀ := x) (t₀ := t)
    (hP.comp contMDiff_snd).contMDiffAt le_rfl
  exact hjoint.comp x (contMDiffAt_const.prodMk (contMDiffAt_id.prodMk contMDiffAt_const))

namespace SmoothForm

open scoped ContDiff

/-- **Bundled contraction along a smooth moving map** `P : M × ℝ → N` at time `t`. -/
def mfamilyContraction (P : M × ℝ → N) (t : ℝ) (hP : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' ∞ P) :
    SmoothForm I' N F (k + 1) →ₗ[ℝ] SmoothForm I M F k where
  toFun φ := ⟨TauCeti.mfamilyContraction I I' P t φ.1, mem_smoothBundleForms.mpr
    ((isSmoothBundleForm_def ∞ _).mpr
      (φ.isSmoothForm.mfamilyContraction (by simpa using hP)).contMDiff)⟩
  map_add' φ η := Subtype.ext (TauCeti.mfamilyContraction_add P t φ.1 η.1)
  map_smul' c φ := Subtype.ext (TauCeti.mfamilyContraction_smul P t c φ.1)

@[simp]
theorem coe_mfamilyContraction (P : M × ℝ → N) (t : ℝ) (hP : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' ∞ P)
    (φ : SmoothForm I' N F (k + 1)) :
    (mfamilyContraction P t hP φ : RoughForm I M F k) =
      TauCeti.mfamilyContraction I I' P t φ.1 := (rfl)

end SmoothForm

end Smooth

/-! ### Differentiation of pullbacks along moving maps -/

section MovingPullbackDeriv

/-- **Differentiation of moving pullbacks in degree zero.** For `P : M × ℝ → N` differentiable at
`(x, t)` and `f : N → F` differentiable at `P (x, t)`, `u ↦ f (P (x, u))` has derivative
`C_(p_t, V_t)(df)_x 0` at `t`. -/
theorem hasDerivAt_comp_family_eq_mfamilyContraction_mextDeriv
    {P : M × ℝ → N} {f : N → F} {x : M} {t : ℝ}
    (hP : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (x, t))
    (hf : MDifferentiableAt I' 𝓘(ℝ, F) f (P (x, t))) :
    HasDerivAt (fun u ↦ f (P (x, u)))
      (mfamilyContraction I I' P t (mextDeriv (RoughForm.ofFunction I' f)) x 0) t := by
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) I' (fun u ↦ P (x, u)) t :=
    hP.comp t (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hfd : HasFDerivAt (fun u ↦ f (P (x, u))) (_ : ℝ →L[ℝ] F) t :=
    (hf.hasMFDerivAt.comp t hcurve.hasMFDerivAt).hasFDerivAt
  refine hfd.hasDerivAt.congr_deriv ?_
  change mfderiv I' 𝓘(ℝ, F) f (P (x, t)) (mfderiv 𝓘(ℝ, ℝ) I' (fun u ↦ P (x, u)) t (1 : ℝ)) = _
  rw [← mfamilyVelocity_eq_mfderiv_slice hP, mfamilyContraction_apply]
  have hvec : (Matrix.vecCons (mfamilyVelocity I I' P t x)
      fun i : Fin 0 ↦ mfderiv I I' (fun y ↦ P (y, t)) x ((0 : Fin 0 → TangentSpace I x) i)) =
      ![mfamilyVelocity I I' P t x] :=
    congrArg (Matrix.vecCons _) (Subsingleton.elim _ ![])
  rw [mfamilyVelocity_def] at hvec
  rw [hvec, mextDeriv_ofFunction_apply, mfamilyVelocity_def]

/-- In preferred charts centred at `x₀` and `y₀`, `mfamilyContraction` read at `y ∈ s` agrees with
the flat `familyContractionWithin` of the coordinate expression of the form. -/
private theorem inChartAt_mfamilyContraction_eq_familyContractionWithin
    [IsManifold I 1 M] [IsManifold I' 1 N] {m : ℕ} {P : M × ℝ → N} {t : ℝ} (x₀ : M) (y₀ : N)
    {s : Set E} (hs : s ⊆ (extChartAt I x₀).target) {y : E} (hy : y ∈ s) (hset : s =ᶠ[𝓝 y] range I)
    (hPy : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P ((extChartAt I x₀).symm y, t))
    (hy' : P ((extChartAt I x₀).symm y, t) ∈ (extChartAt I' y₀).source)
    (η : RoughForm I' N F (m + 1)) :
    (mfamilyContraction I I' P t η).inChartAt x₀ y =
      familyContractionWithin (extChartAt I' y₀ ∘ P ∘ Prod.map (extChartAt I x₀).symm id)
        s t (η.inChartAt y₀) y := by
  set e := extChartAt I x₀; set e' := extChartAt I' y₀
  set G : E × ℝ → E' := e' ∘ P ∘ Prod.map e.symm id
  have hy_tar : y ∈ e.target := hs hy
  have hy_rng : y ∈ range I := extChartAt_target_subset_range x₀ hy_tar
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I' (fun u ↦ P (e.symm y, u)) t :=
    hPy.comp t (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have he'd : MDifferentiableAt I' 𝓘(ℝ, E') e' (P (e.symm y, t)) :=
    mdifferentiableAt_extChartAt (by simpa only [e', extChartAt_source] using hy')
  have hvel : mfderivWithin 𝓘(ℝ, E') I' e'.symm (range I') (e' (P (e.symm y, t)))
      (deriv (fun u ↦ G (y, u)) t) = mfamilyVelocity I I' P t (e.symm y) := by
    have hfd : HasFDerivAt (fun u ↦ G (y, u)) (_ : ℝ →L[ℝ] E') t :=
      (he'd.hasMFDerivAt.comp t hγ.hasMFDerivAt).hasFDerivAt
    have hderiv : deriv (fun u ↦ G (y, u)) t =
        mfderiv I' 𝓘(ℝ, E') e' (P (e.symm y, t))
          (mfderiv 𝓘(ℝ, ℝ) I' (fun u ↦ P (e.symm y, u)) t (1 : ℝ)) :=
      hfd.hasDerivAt.deriv
    have hc1 := congrArg
      (mfderivWithin 𝓘(ℝ, E') I' e'.symm (range I') (e' (P (e.symm y, t)))) hderiv
    have hc2 := congrArg
      (fun L ↦ L (mfderiv 𝓘(ℝ, ℝ) I' (fun u ↦ P (e.symm y, u)) t (1 : ℝ)))
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hy')
    exact hc1.trans (hc2.trans (mfamilyVelocity_eq_mfderiv_slice hPy).symm)
  have hft : MDifferentiableAt I I' (fun w ↦ P (w, t)) (e.symm y) :=
    hPy.comp (e.symm y) (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have hslice (w : E) : mfderivWithin 𝓘(ℝ, E') I' e'.symm (range I') (e' (P (e.symm y, t)))
      (fderivWithin ℝ (fun z ↦ G (z, t)) s y w) =
      mfderiv I I' (fun z ↦ P (z, t)) (e.symm y)
        (mfderivWithin 𝓘(ℝ, E) I e.symm (range I) y w) := by
    have h1 : fderivWithin ℝ (fun z ↦ G (z, t)) s y w =
        fderivWithin ℝ (fun z ↦ G (z, t)) (range I) y w :=
      congrArg (fun L : E →L[ℝ] E' ↦ L w)
        (fderivWithin_congr_set (𝕜 := ℝ) (f := fun z ↦ G (z, t)) hset)
    have he_symm : MDifferentiableWithinAt 𝓘(ℝ, E) I e.symm (range I) y :=
      mdifferentiableWithinAt_extChartAt_symm hy_tar
    have hef : MDifferentiableAt I 𝓘(ℝ, E') (e' ∘ fun z ↦ P (z, t)) (e.symm y) :=
      he'd.comp (e.symm y) hft
    have hmw : HasMFDerivWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E') (fun z ↦ G (z, t)) (range I) y
        ((mfderiv I 𝓘(ℝ, E') (e' ∘ fun z ↦ P (z, t)) (e.symm y)).comp
          (mfderivWithin 𝓘(ℝ, E) I e.symm (range I) y)) :=
      hef.hasMFDerivAt.comp_hasMFDerivWithinAt y he_symm.hasMFDerivWithinAt
    have h2' := congrArg (fun L : TangentSpace 𝓘(ℝ, E) y →L[ℝ]
      TangentSpace 𝓘(ℝ, E') (G (y, t)) ↦ L w) (hmw.mfderivWithin (I.uniqueMDiffOn y hy_rng))
    rw [mfderivWithin_eq_fderivWithin] at h2'
    have h2 : fderivWithin ℝ (fun z ↦ G (z, t)) (range I) y w =
        mfderiv I 𝓘(ℝ, E') (e' ∘ fun z ↦ P (z, t)) (e.symm y)
          (mfderivWithin 𝓘(ℝ, E) I e.symm (range I) y w) := h2'
    have hcomp2 := mfderiv_comp_apply (e.symm y) he'd hft
      (mfderivWithin 𝓘(ℝ, E) I e.symm (range I) y w)
    have hchain : fderivWithin ℝ (fun z ↦ G (z, t)) s y w =
        mfderiv I' 𝓘(ℝ, E') e' (P (e.symm y, t))
          (mfderiv I I' (fun z ↦ P (z, t)) (e.symm y)
            (mfderivWithin 𝓘(ℝ, E) I e.symm (range I) y w)) :=
      h1.trans (h2.trans hcomp2)
    exact (congrArg
      (mfderivWithin 𝓘(ℝ, E') I' e'.symm (range I') (e' (P (e.symm y, t)))) hchain).trans
      (congrArg (fun L : TangentSpace I' (P (e.symm y, t)) →L[ℝ]
        TangentSpace I' (P (e.symm y, t)) ↦ L _)
        (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hy'))
  ext v
  rw [RoughForm.inChartAt_apply, mfamilyContraction_apply, familyContractionWithin_apply,
    RoughForm.inChartAt_apply]
  change _ = η (e'.symm (G (y, t)))
    (fun i ↦ mfderivWithin 𝓘(ℝ, E') I' e'.symm (range I') (G (y, t))
      (Matrix.vecCons (deriv (fun u ↦ G (y, u)) t)
        (fun j ↦ fderivWithin ℝ (fun z ↦ G (z, t)) s y (v j)) i))
  have hGyt : G (y, t) = e' (P (e.symm y, t)) := rfl
  rw [hGyt, e'.left_inv hy']
  refine congrArg (η (P (e.symm y, t))) (funext fun i ↦ ?_)
  cases i using Fin.cases with
  | zero => simp only [Matrix.cons_val_zero]; exact hvel.symm
  | succ i => simp only [Matrix.cons_val_succ]; exact (hslice (v i)).symm

/-- **Differentiation of moving pullbacks on manifolds.** Let `P : M × ℝ → N` be `C^r` (`2 ≤ r`) at
`(x₀, t)` between `C²` manifolds (possibly with boundary or corners), and let `ω` be a
`(k + 1)`-form on `N` differentiable at `P (x₀, t)`. Then `u ↦ (p_u^* ω)_{x₀}` has derivative
`d(C_(p_t, V_t) ω)_{x₀} + C_(p_t, V_t)(dω)_{x₀}` at `t` in the fixed fiber
`TangentSpace I x₀ [⋀^Fin (k + 1)]→L[ℝ] F`, with neither completeness of `F` nor invertibility of
the slices `p_u`. -/
theorem hasDerivAt_mpullback_family [IsManifold I 2 M] [IsManifold I' 2 N]
    {r : WithTop ℕ∞} {P : M × ℝ → N} {ω : RoughForm I' N F (k + 1)} {x₀ : M} {t : ℝ}
    (hP : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' r P (x₀, t)) (hr : 2 ≤ r)
    (hω : MDifferentiableAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F) z (ω z)) (P (x₀, t))) :
    HasDerivAt (F := E [⋀^Fin (k + 1)]→L[ℝ] F)
      (fun u ↦ mpullback I I' (fun y ↦ P (y, u)) ω x₀)
      (mextDeriv (mfamilyContraction I I' P t ω) x₀ +
        mfamilyContraction I I' P t (mextDeriv ω) x₀) t := by
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have : IsManifold I' 1 N := IsManifold.of_le one_le_two
  have : IsManifold I ((1 : ℕ∞) + 1 : WithTop ℕ∞) M := IsManifold.of_le (n := 2) (by norm_num)
  have hP2 : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' 2 P (x₀, t) := hP.of_le hr
  obtain ⟨s, hsub, hsu, -, hsn, hxs, hxc⟩ :=
    exists_convex_uniqueDiffOn_mem_nhdsWithin_extChartAt (I := I) x₀
  set e := extChartAt I x₀; set z₀ := e x₀; set y₀ := P (x₀, t); set e' := extChartAt I' y₀
  have hz₀_inv : e.symm z₀ = x₀ := extChartAt_to_inv x₀
  have hset : s =ᶠ[𝓝 z₀] range I := by
    filter_upwards [mem_nhdsWithin_iff_eventually.1 hsn] with y hy
    exact ⟨fun h ↦ extChartAt_target_subset_range x₀ (hsub h), hy⟩
  let φ : E × ℝ → M × ℝ := Prod.map e.symm id
  let G : E × ℝ → E' := e' ∘ P ∘ φ
  have hφ_pt : φ (z₀, t) = (x₀, t) := Prod.ext hz₀_inv rfl
  have hG_pt : G (z₀, t) = e' y₀ := congrArg (e' ∘ P) hφ_pt
  have hφ_smooth : ContMDiffWithinAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) 2 φ
      (s ×ˢ univ) (z₀, t) :=
    ((contMDiffOn_extChartAt_symm (n := 2) x₀).mono hsub z₀ hxs).prodMap
      (contMDiffWithinAt_id (I := 𝓘(ℝ, ℝ)))
  have hPφ_smooth : ContMDiffWithinAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I' 2 (P ∘ φ) (s ×ˢ univ) (z₀, t) :=
    hP2.comp_contMDiffWithinAt_of_eq hφ_smooth hφ_pt
  have hG_smooth : ContDiffWithinAt ℝ 2 G (s ×ˢ univ) (z₀, t) := by
    have hG_m := (contMDiffAt_extChartAt (I := I') (n := 2) (x := y₀)).comp_contMDiffWithinAt_of_eq
      hPφ_smooth (congrArg P hφ_pt)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod,
      contMDiffWithinAt_iff_contDiffWithinAt] at hG_m
    exact hG_m
  have hmaps : G ⁻¹' range I' ∈ 𝓝[s ×ˢ univ] (z₀, t) := by
    have hpre : (P ∘ φ) ⁻¹' e'.source ∈ 𝓝[s ×ˢ univ] (z₀, t) :=
      hPφ_smooth.continuousWithinAt.preimage_mem_nhdsWithin
        (by simpa only [Function.comp_apply, hφ_pt] using extChartAt_source_mem_nhds (I := I') y₀)
    filter_upwards [hpre] with q hq
    exact extChartAt_target_subset_range y₀ (e'.map_source hq)
  have hform : DifferentiableWithinAt ℝ (ω.inChartAt y₀) (range I') (G (z₀, t)) := by
    rw [hG_pt]
    exact ω.differentiableWithinAt_range_inChartAt_of_mdifferentiableAt hω
  have hflat := hasDerivAt_compContinuousLinearMap_fderivWithin_family hsu hxc hxs isOpen_univ
    (mem_univ t) hG_smooth le_rfl hmaps hform
  -- Identify the curve near `t`.
  have hcurve_eq : (fun u ↦ mpullback I I' (fun y ↦ P (y, u)) ω x₀) =ᶠ[𝓝 t]
      fun u ↦ (ω.inChartAt y₀ (G (z₀, u))).compContinuousLinearMap
        (fderivWithin ℝ (fun y ↦ G (y, u)) s z₀) := by
    have hP_nhds : ∀ᶠ u in 𝓝 t, ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' 2 P (x₀, u) :=
      ((continuous_const.prodMk continuous_id).tendsto t).eventually
        ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hP2)
    have hsrc_nhds : ∀ᶠ u in 𝓝 t, P (x₀, u) ∈ e'.source :=
      (hP2.continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt).preimage_mem_nhds
        (extChartAt_source_mem_nhds (I := I') y₀)
    filter_upwards [hP_nhds, hsrc_nhds] with u hPu hyu
    have hPu_d : MDifferentiableAt I I' (fun y ↦ P (y, u)) x₀ :=
      (hPu.comp x₀ (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt two_ne_zero
    rw [ω.mpullback_eq_compContinuousLinearMap y₀ hPu_d hyu, ← fderivWithin_congr_set hset]
    have hGu : G (z₀, u) = e' (P (x₀, u)) := by
      simp only [G, φ, Function.comp_apply, Prod.map_apply, hz₀_inv, id_eq]
    rw [hGu]; rfl
  -- Identify the first derivative term `d(C_(p_t, V_t) ω)_{x₀}`.
  obtain ⟨O, hO_eq, hO_open, hzO⟩ := mem_nhds_iff.mp hset
  have hd_contr : mextDeriv (mfamilyContraction I I' P t ω) x₀ =
      extDerivWithin (familyContractionWithin G s t (ω.inChartAt y₀)) s z₀ := by
    have he_cont : ContinuousWithinAt (fun y : E ↦ (e.symm y, t)) s z₀ :=
      (((contMDiffOn_extChartAt_symm (n := 1) x₀).mono hsub z₀ hxs).continuousWithinAt).prodMk
        continuousWithinAt_const
    have hP_s : ∀ᶠ y in 𝓝[s] z₀, ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' 2 P (e.symm y, t) :=
      he_cont.tendsto.eventually
        (by simpa only [hz₀_inv] using (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hP2)
    have hsrc_s : ∀ᶠ y in 𝓝[s] z₀, P (e.symm y, t) ∈ e'.source :=
      (ContinuousAt.comp_continuousWithinAt
        (by simpa only [hz₀_inv] using hP2.continuousAt) he_cont).preimage_mem_nhdsWithin
        (by simpa only [Function.comp_apply, hz₀_inv, y₀] using
          extChartAt_source_mem_nhds (I := I') y₀)
    have heq : (mfamilyContraction I I' P t ω).inChartAt x₀ =ᶠ[𝓝[s] z₀]
        familyContractionWithin G s t (ω.inChartAt y₀) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hO_open.mem_nhds hzO),
        hP_s, hsrc_s] with y hys hyO hPy hy'
      have hset_y : s =ᶠ[𝓝 y] range I :=
        Filter.eventually_of_mem (hO_open.mem_nhds hyO) fun w hw ↦ hO_eq hw
      exact inChartAt_mfamilyContraction_eq_familyContractionWithin (P := P) (t := t)
        x₀ y₀ hsub hys hset_y (hPy.mdifferentiableAt two_ne_zero) hy' ω
    rw [mextDeriv_def, ← extDerivWithin_congr_set hset]
    exact heq.extDerivWithin_eq (heq.self_of_nhdsWithin hxs)
  -- Identify the second derivative term `C_(p_t, V_t)(dω)_{x₀}`.
  have hcontr_d : mfamilyContraction I I' P t (mextDeriv ω) x₀ =
      familyContractionWithin G s t (extDerivWithin (ω.inChartAt y₀) (range I')) z₀ := by
    have h1 := (RoughForm.inChartAt_extChartAt_self
      (mfamilyContraction I I' P t (mextDeriv ω)) x₀).symm
    have h2 := inChartAt_mfamilyContraction_eq_familyContractionWithin (P := P) (t := t)
      x₀ y₀ hsub hxs hset
      (by rw [extChartAt_to_inv]; exact hP2.mdifferentiableAt two_ne_zero)
      (by rw [extChartAt_to_inv]; exact mem_extChartAt_source y₀) (mextDeriv ω)
    refine (h1.trans h2).trans ?_
    ext v
    change familyContractionWithin G s t ((mextDeriv ω).inChartAt y₀) z₀ v = _
    simp only [familyContractionWithin_apply, hG_pt]
    have hd_pt : (mextDeriv ω).inChartAt y₀ (e' y₀) =
        extDerivWithin (ω.inChartAt y₀) (range I') (e' y₀) :=
      (RoughForm.inChartAt_extChartAt_self (mextDeriv ω) y₀).trans (mextDeriv_def ω y₀)
    rw [hd_pt]
  rw [hd_contr, hcontr_d]
  exact hflat.congr_of_eventuallyEq hcurve_eq

/-- Pointwise evaluation of `hasDerivAt_mpullback_family` on a fixed tuple of tangent vectors. -/
theorem hasDerivAt_mpullback_family_apply [IsManifold I 2 M] [IsManifold I' 2 N]
    {r : WithTop ℕ∞} {P : M × ℝ → N} {ω : RoughForm I' N F (k + 1)} {x₀ : M} {t : ℝ}
    (hP : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' r P (x₀, t)) (hr : 2 ≤ r)
    (hω : MDifferentiableAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F) z (ω z)) (P (x₀, t)))
    (v : Fin (k + 1) → TangentSpace I x₀) :
    HasDerivAt (fun u ↦ mpullback I I' (fun y ↦ P (y, u)) ω x₀ v)
      (mextDeriv (mfamilyContraction I I' P t ω) x₀ v +
        mfamilyContraction I I' P t (mextDeriv ω) x₀ v) t := by
  let ev : (E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] F :=
    ContinuousAlternatingMap.apply ℝ E F v
  exact ev.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_mpullback_family hP hr hω)

/-- **Differentiation of moving pullbacks over an open parameter set `J : Opens ℝ`.** -/
theorem mfderiv_mpullback_family_opens_apply [IsManifold I 2 M] [IsManifold I' 2 N]
    {r : WithTop ℕ∞} {J : Opens ℝ} {P : M × ↥J → N} {ω : RoughForm I' N F (k + 1)}
    {x₀ : M} {t : J}
    (hP : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' r P (x₀, t)) (hr : 2 ≤ r)
    (hω : MDifferentiableAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F) z (ω z)) (P (x₀, t)))
    (v : Fin (k + 1) → TangentSpace I x₀) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun u : J ↦ mpullback I I' (fun y ↦ P (y, u)) ω x₀ v) t
      (1 : ℝ) =
      mextDeriv (mfamilyContraction I I' P t ω) x₀ v +
        mfamilyContraction I I' P t (mextDeriv ω) x₀ v := by
  classical
  let P' : M × ℝ → N := fun q ↦ if h : q.2 ∈ J then P (q.1, ⟨q.2, h⟩) else P (x₀, t)
  have hP'_eq : P' ∘ Prod.map id (Subtype.val : J → ℝ) = P := funext fun q ↦ dite_eq_left q.2.2
  have hP'_smooth : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' r P' (x₀, (t : ℝ)) := by
    let V_prod : Opens (M × ℝ) := ⟨univ ×ˢ (J : Set ℝ), isOpen_univ.prod J.isOpen⟩
    let ψ_open : V_prod → M × J := fun q ↦ (q.1.1, ⟨q.1.2, (Set.mem_prod.mp q.2).2⟩)
    have hψ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) r ψ_open :=
      (contMDiff_fst.comp contMDiff_subtype_val).prodMk
        (contMDiff_subtypeVal_comp (contMDiff_snd.comp contMDiff_subtype_val))
    let q₀ : V_prod := ⟨(x₀, (t : ℝ)), Set.mk_mem_prod (mem_univ _) t.2⟩
    have hcomp : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' r (P ∘ ψ_open) q₀ := hP.comp q₀ hψ.contMDiffAt
    have hsub_eq : (fun q : V_prod ↦ P' q) = P ∘ ψ_open :=
      funext fun q ↦ dite_eq_left (Set.mem_prod.mp q.2).2
    exact (contMDiffAt_subtype_iff (U := V_prod) (f := P') (x := q₀)).mp (hsub_eq.symm ▸ hcomp)
  have hω' : MDifferentiableAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F) z (ω z)) (P' (x₀, (t : ℝ))) := by
    have hpt : P' (x₀, (t : ℝ)) = P (x₀, t) := dite_eq_left t.2; rwa [hpt]
  let g : ℝ → F := fun u ↦ mpullback I I' (fun y ↦ P' (y, u)) ω x₀ v
  have hd := hasDerivAt_mpullback_family_apply hP'_smooth hr hω' v
  have hgd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) g (t : ℝ) := hd.differentiableAt.mdifferentiableAt
  have hfun : (fun u : J ↦ mpullback I I' (fun y ↦ P (y, u)) ω x₀ v) = g ∘ (Subtype.val : J → ℝ) :=
    funext fun u ↦ congrArg (fun p ↦ mpullback I I' p ω x₀ v)
      (funext fun y ↦ (show P' (y, u) = P (y, u) from dite_eq_left u.2).symm)
  let one_t : TangentSpace 𝓘(ℝ, ℝ) t := (1 : ℝ)
  have h1 : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun u : J ↦ mpullback I I' (fun y ↦ P (y, u)) ω x₀ v) t
      one_t : F) = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (g ∘ (Subtype.val : J → ℝ)) t one_t :=
    congrArg (fun k : J → F ↦ (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) k t one_t : F)) hfun
  have h2 := mfderiv_comp_apply t hgd (contMDiff_subtype_val.mdifferentiableAt one_ne_zero) one_t
  have hone : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : J → ℝ) t one_t = (1 : ℝ) := by
    rw [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
      Manifold.tangentSpaceOpenEquiv_apply]
  have h3 : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) g (t : ℝ) (1 : ℝ) : F) =
      mextDeriv (mfamilyContraction I I' P t ω) x₀ v +
        mfamilyContraction I I' P t (mextDeriv ω) x₀ v := by
    rw [mfderiv_eq_fderiv]; change fderiv ℝ g (t : ℝ) (1 : ℝ) = _; rw [hd.hasFDerivAt.fderiv]
    simp [← hP'_eq, mfamilyContraction_comp_prodMap_subtype_val]
  exact h1.trans (h2.trans ((congrArg _ hone).trans h3))

/-! ### Differentiation of moving pullbacks of moving forms -/

/-- **Differentiation of moving pullbacks for a moving family of forms.** Let `P : M × ℝ → N` be
`C^r` (`2 ≤ r`) at `(x₀, t)` between `C²` manifolds (possibly with boundary or corners), and let
`ω : ℝ → RoughForm I' N F (k + 1)` be jointly differentiable as a section along `Prod.snd` at
`(t, P (x₀, t))`. Then the pulled-back forms `u ↦ (p_u^* ω_u)_{x₀}` have derivative
`(p_t^* (∂_t ω_t))_{x₀} + d(C_(p_t, V_t) ω_t)_{x₀} + C_(p_t, V_t)(d(ω_t))_{x₀}` at `t`. -/
theorem hasDerivAt_mpullback_family_form [IsManifold I 2 M] [IsManifold I' 2 N]
    {r : WithTop ℕ∞} {P : M × ℝ → N} {ω : ℝ → RoughForm I' N F (k + 1)} {x₀ : M} {t : ℝ}
    (hP : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' r P (x₀, t)) (hr : 2 ≤ r)
    (hω : MDifferentiableAt (𝓘(ℝ, ℝ).prod I') (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun p : ℝ × N ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F)
        (E := fun z : N ↦ TangentSpace I' z [⋀^Fin (k + 1)]→L[ℝ] Trivial N F z)
        p.2 (ω p.1 p.2))
      (t, P (x₀, t))) :
    HasDerivAt (F := E [⋀^Fin (k + 1)]→L[ℝ] F)
      (fun u ↦ mpullback I I' (fun y ↦ P (y, u)) (ω u) x₀)
      (mpullback I I' (fun y ↦ P (y, t)) (fun z ↦ deriv (fun v ↦ ω v z) t) x₀ +
        mextDeriv (mfamilyContraction I I' P t (ω t)) x₀ +
        mfamilyContraction I I' P t (mextDeriv (ω t)) x₀) t := by
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have : IsManifold I' 1 N := IsManifold.of_le one_le_two
  set y₀ := P (x₀, t)
  set e' := extChartAt I' y₀
  let P_lift : M × ℝ → ℝ × N := fun q ↦ (q.2, P q)
  let α : RoughForm (𝓘(ℝ, ℝ).prod I') (ℝ × N) F (k + 1) :=
    fun p ↦ (ω p.1 p.2).compContinuousLinearMap (.snd ℝ ℝ E')
  have hP_lift : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I') r P_lift (x₀, t) :=
    contMDiffAt_snd.prodMk hP
  -- Coordinate expression of `α` in the preferred chart at `(t, y₀)`.
  let Φ : ℝ × E' → E' [⋀^Fin (k + 1)]→L[ℝ] F := fun q ↦ (ω q.1).inChartAt y₀ q.2
  let C := compContinuousLinearMapCLM (𝕜 := ℝ) (F := F) (ι := Fin (k + 1)) (.snd ℝ ℝ E')
  have hpt_chart : extChartAt (𝓘(ℝ, ℝ).prod I') (t, y₀) (t, y₀) = (t, e' y₀) := rfl
  have hsymm_eq : ⇑(extChartAt (𝓘(ℝ, ℝ).prod I') (t, y₀)).symm = Prod.map id e'.symm := rfl
  have hrng : range (𝓘(ℝ, ℝ).prod I') = univ ×ˢ range I' := by
    change range (Prod.map (id : ℝ → ℝ) I') = univ ×ˢ range I'
    rw [Set.range_prodMap, Set.range_id]
  have hΦ_diff : DifferentiableWithinAt ℝ Φ (univ ×ˢ range I') (t, e' y₀) := by
    have hω_coord : MDifferentiableAt (𝓘(ℝ, ℝ).prod I') 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F)
        (fun p : ℝ × N ↦ inCoordinates E' F y₀ p.2 y₀ p.2 (ω p.1 p.2)) (t, y₀) := by
      simpa only [← mdifferentiableWithinAt_univ] using
        ((mdifferentiableWithinAt_continuousAlternatingMap_bundle _).mp
          hω.mdifferentiableWithinAt).2
    let ψ : ℝ × E' → ℝ × N := Prod.map id e'.symm
    have hψ : MDifferentiableWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E')) (𝓘(ℝ, ℝ).prod I') ψ
        (univ ×ˢ range I') (t, e' y₀) :=
      (mdifferentiableWithinAt_id (I := 𝓘(ℝ, ℝ))).prodMap
        (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target y₀))
    have hψ_pt : ψ (t, e' y₀) = (t, y₀) := Prod.ext rfl (extChartAt_to_inv y₀)
    have hcomp : DifferentiableWithinAt ℝ ((fun p : ℝ × N ↦
        inCoordinates E' F y₀ p.2 y₀ p.2 (ω p.1 p.2)) ∘ ψ) (univ ×ˢ range I') (t, e' y₀) := by
      have hcomp_m := hω_coord.comp_mdifferentiableWithinAt_of_eq (t, e' y₀) hψ hψ_pt
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod,
        mdifferentiableWithinAt_iff_differentiableWithinAt] at hcomp_m
      exact hcomp_m
    have hev : Φ =ᶠ[𝓝[univ ×ˢ range I'] (t, e' y₀)]
        (fun p : ℝ × N ↦ inCoordinates E' F y₀ p.2 y₀ p.2 (ω p.1 p.2)) ∘ ψ := by
      have hmem : univ ×ˢ e'.target ∈ 𝓝[univ ×ˢ range I'] (t, e' y₀) := by
        rw [nhdsWithin_prod_eq]
        exact Filter.prod_mem_prod univ_mem (extChartAt_target_mem_nhdsWithin y₀)
      filter_upwards [hmem] with q hq
      have hsrc : e'.symm q.2 ∈ e'.source := e'.map_target hq.2
      simp only [Φ, ψ, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
      rw [(ω q.1).inCoordinates_eq_inChartAt hsrc, e'.right_inv hq.2]
    exact hcomp.congr_of_eventuallyEq hev
      (hev.self_of_nhdsWithin
        ⟨trivial, extChartAt_target_subset_range y₀ (mem_extChartAt_target y₀)⟩)
  have hα_chart_eq : ∀ q : ℝ × E', q.2 ∈ e'.target → α.inChartAt (t, y₀) q = C (Φ q) := by
    intro q hq
    ext u
    rw [RoughForm.inChartAt_apply]
    have hd_prod : mfderivWithin 𝓘(ℝ, ℝ × E') (𝓘(ℝ, ℝ).prod I')
        (extChartAt (𝓘(ℝ, ℝ).prod I') (t, y₀)).symm (range (𝓘(ℝ, ℝ).prod I')) q =
        ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ ℝ)
          (mfderivWithin 𝓘(ℝ, E') I' e'.symm (range I') q.2) := by
      rw [hsymm_eq, hrng, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod,
        mfderivWithin_prodMap (mdifferentiableWithinAt_id (I := 𝓘(ℝ, ℝ)))
          (mdifferentiableWithinAt_extChartAt_symm hq)
          (uniqueMDiffWithinAt_univ (I := 𝓘(ℝ, ℝ)))
          (I'.uniqueMDiffOn _ (extChartAt_target_subset_range y₀ hq)),
        mfderivWithin_univ, mfderiv_id]
      rfl
    simp only [C, Φ, compContinuousLinearMapCLM_apply, compContinuousLinearMap_apply,
      RoughForm.inChartAt_apply, α, hd_prod, hsymm_eq]
    rfl
  have hα_chart_ev : α.inChartAt (t, y₀) =ᶠ[𝓝[range (𝓘(ℝ, ℝ).prod I')]
      (extChartAt (𝓘(ℝ, ℝ).prod I') (t, y₀) (t, y₀))] C ∘ Φ := by
    rw [hpt_chart, hrng, nhdsWithin_prod_eq]
    filter_upwards [Filter.prod_mem_prod univ_mem (extChartAt_target_mem_nhdsWithin y₀)]
      with q hq using hα_chart_eq q hq.2
  have hα_diff : MDifferentiableAt (𝓘(ℝ, ℝ).prod I')
      ((𝓘(ℝ, ℝ).prod I').prod 𝓘(ℝ, (ℝ × E') [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun p ↦ TotalSpace.mk' ((ℝ × E') [⋀^Fin (k + 1)]→L[ℝ] F) p (α p)) (t, y₀) := by
    refine mdifferentiableAt_form_of_differentiableWithinAt_inChartAt_self ?_
    have hc : DifferentiableWithinAt ℝ (C ∘ Φ) (range (𝓘(ℝ, ℝ).prod I'))
        (extChartAt (𝓘(ℝ, ℝ).prod I') (t, y₀) (t, y₀)) := by
      rw [hpt_chart, hrng]
      exact C.differentiableAt.comp_differentiableWithinAt (t, e' y₀) hΦ_diff
    exact hc.congr_of_eventuallyEq hα_chart_ev
      (by rw [hpt_chart]; exact hα_chart_eq (t, e' y₀) (mem_extChartAt_target y₀))
  have hlift_deriv := hasDerivAt_mpullback_family hP_lift hr hα_diff
  -- 1. Slices `(p_lift_u)^* α` agree with `p_u^* (ω u)` for all `u`.
  have hcurve_eq (u : ℝ) : mpullback I (𝓘(ℝ, ℝ).prod I') (fun y ↦ P_lift (y, u)) α x₀ =
      mpullback I I' (fun y ↦ P (y, u)) (ω u) x₀ := by
    by_cases hPu : MDifferentiableAt I I' (fun y ↦ P (y, u)) x₀
    · ext v
      rw [mpullback_apply, mpullback_apply]
      change ω u (P (x₀, u)) (fun i ↦ (mfderiv I (𝓘(ℝ, ℝ).prod I')
        (fun y ↦ (u, P (y, u))) x₀ (v i)).2) = _
      refine congrArg (ω u (P (x₀, u))) (funext fun i ↦ ?_)
      rw [mfderiv_prodMk mdifferentiableAt_const hPu]; rfl
    · have hPu' : ¬MDifferentiableAt I (𝓘(ℝ, ℝ).prod I') (fun y ↦ P_lift (y, u)) x₀ :=
        fun h ↦ hPu (mdifferentiableAt_snd.comp x₀ h)
      ext v
      rw [mpullback_apply, mpullback_apply, mfderiv_zero_of_not_mdifferentiableAt hPu,
        mfderiv_zero_of_not_mdifferentiableAt hPu']
      simp only [zero_apply]
      rw [(α (P_lift (x₀, u))).map_coord_zero 0 rfl, (ω u (P (x₀, u))).map_coord_zero 0 rfl]
  -- 2. Near `x₀`, `mfamilyContraction` of `α` along `P_lift` agrees with that of `ω t` along `P`.
  have hcontr_eq : ∀ᶠ y in 𝓝 x₀,
      mfamilyContraction I (𝓘(ℝ, ℝ).prod I') P_lift t α y =
        mfamilyContraction I I' P t (ω t) y := by
    have hP2 : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' 2 P (x₀, t) := hP.of_le hr
    have hnhds : ∀ᶠ y in 𝓝 x₀, ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' 2 P (y, t) :=
      ((continuous_id.prodMk continuous_const).tendsto x₀).eventually
        ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hP2)
    filter_upwards [hnhds] with y hy
    have hyd : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (y, t) := hy.mdifferentiableAt two_ne_zero
    have hy_slice : MDifferentiableAt I I' (fun z ↦ P (z, t)) y :=
      hyd.comp y (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    ext v
    rw [mfamilyContraction_apply, mfamilyContraction_apply]
    change ω t (P (y, t)) (fun i ↦ (ContinuousLinearMap.snd ℝ ℝ E') (Matrix.vecCons
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I') P_lift (y, t) ((0 : E), (1 : ℝ)))
      (fun j ↦ mfderiv I (𝓘(ℝ, ℝ).prod I') (fun z ↦ P_lift (z, t)) y (v j)) i)) = _
    refine congrArg (ω t (P (y, t))) (funext fun i ↦ ?_)
    cases i using Fin.cases with
    | zero =>
      simp only [Matrix.cons_val_zero, P_lift]
      rw [mfderiv_prodMk mdifferentiableAt_snd hyd]; rfl
    | succ j =>
      simp only [Matrix.cons_val_succ, P_lift]
      rw [mfderiv_prodMk mdifferentiableAt_const hy_slice]; rfl
  -- 3. Split `mfamilyContraction` of `mextDeriv α` into temporal and spatial pieces.
  set B := fderivWithin ℝ Φ (univ ×ˢ range I') (t, e' y₀)
  have hu_prod : UniqueDiffWithinAt ℝ (univ ×ˢ range I') (t, e' y₀) :=
    uniqueDiffWithinAt_univ.prod
      (I'.uniqueDiffOn (e' y₀) (extChartAt_target_subset_range y₀ (mem_extChartAt_target y₀)))
  have hdα_pt : mextDeriv α (t, y₀) = alternatizeUncurryFin (C ∘L B) := by
    rw [mextDeriv_def, hα_chart_ev.extDerivWithin_eq
      (by rw [hpt_chart]; exact hα_chart_eq (t, e' y₀) (mem_extChartAt_target y₀)),
      hpt_chart, hrng, extDerivWithin,
      (C.hasFDerivAt.comp_hasFDerivWithinAt (t, e' y₀) hΦ_diff.hasFDerivWithinAt).fderivWithin
        hu_prod]
  have hB10 (w : Fin (k + 1) → E') : B ((1 : ℝ), (0 : E')) w = deriv (fun v ↦ ω v y₀) t w := by
    have hmaps_in : MapsTo (fun v : ℝ ↦ (v, e' y₀)) univ (univ ×ˢ range I') :=
      fun _ _ ↦ ⟨trivial, extChartAt_target_subset_range y₀ (mem_extChartAt_target y₀)⟩
    have hcurve_Φ : HasFDerivWithinAt (Φ ∘ fun v ↦ (v, e' y₀)) (B ∘L .inl ℝ ℝ E') univ t :=
      hΦ_diff.hasFDerivWithinAt.comp t
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) t (e' y₀)).hasFDerivWithinAt hmaps_in
    have hd_Φ : HasDerivAt (F := E' [⋀^Fin (k + 1)]→L[ℝ] F) (fun v ↦ Φ (v, e' y₀))
        (B ((1 : ℝ), (0 : E'))) t := by
      simpa [Function.comp_def] using (hasFDerivWithinAt_univ.mp hcurve_Φ).hasDerivAt
    have hd_ω : HasDerivAt (F := E' [⋀^Fin (k + 1)]→L[ℝ] F) (fun v ↦ ω v y₀)
        (B ((1 : ℝ), (0 : E'))) t :=
      hd_Φ.congr_of_eventuallyEq
        (Eventually.of_forall fun v ↦ (RoughForm.inChartAt_extChartAt_self (ω v) y₀).symm)
    exact congrArg (fun η : E' [⋀^Fin (k + 1)]→L[ℝ] F ↦ η w) hd_ω.deriv.symm
  have hBinr : alternatizeUncurryFin (B ∘L .inr ℝ ℝ E') = mextDeriv (ω t) y₀ := by
    have hslice_Φ : HasFDerivWithinAt (Φ ∘ fun w ↦ (t, w)) (B ∘L .inr ℝ ℝ E') (range I')
        (e' y₀) :=
      hΦ_diff.hasFDerivWithinAt.comp (e' y₀)
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) t (e' y₀)).hasFDerivWithinAt
        fun _ hw ↦ ⟨trivial, hw⟩
    have hslice_Φ' : HasFDerivWithinAt (fun w ↦ Φ (t, w)) (B ∘L .inr ℝ ℝ E') (range I')
        (e' y₀) := by
      simpa [Function.comp_def] using hslice_Φ
    rw [mextDeriv_def, extDerivWithin,
      hslice_Φ'.fderivWithin
        (I'.uniqueDiffOn (e' y₀) (extChartAt_target_subset_range y₀ (mem_extChartAt_target y₀)))]
  have hsplit : mfamilyContraction I (𝓘(ℝ, ℝ).prod I') P_lift t (mextDeriv α) x₀ =
      mpullback I I' (fun y ↦ P (y, t)) (fun z ↦ deriv (fun v ↦ ω v z) t) x₀ +
        mfamilyContraction I I' P t (mextDeriv (ω t)) x₀ := by
    have hPd : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (x₀, t) :=
      (hP.of_le hr).mdifferentiableAt two_ne_zero
    have hPtd : MDifferentiableAt I I' (fun y ↦ P (y, t)) x₀ :=
      hPd.comp x₀ (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    ext u
    rw [mfamilyContraction_apply]
    have hvel_lift : mfderiv (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I') P_lift (x₀, t) ((0 : E), (1 : ℝ)) =
        ((1 : ℝ), mfamilyVelocity I I' P t x₀) := by
      rw [mfderiv_prodMk mdifferentiableAt_snd hPd, mfderiv_snd]; rfl
    have hslice_lift (i : Fin (k + 1)) :
        mfderiv I (𝓘(ℝ, ℝ).prod I') (fun y ↦ P_lift (y, t)) x₀ (u i) =
          ((0 : ℝ), mfderiv I I' (fun y ↦ P (y, t)) x₀ (u i)) := by
      rw [mfderiv_prodMk mdifferentiableAt_const hPtd, mfderiv_const]; rfl
    set V₀ : E' := mfamilyVelocity I I' P t x₀
    set W : Fin (k + 1) → E' := fun i ↦ mfderiv I I' (fun y ↦ P (y, t)) x₀ (u i)
    change mextDeriv α (t, y₀) (Matrix.vecCons
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I') P_lift (x₀, t) ((0 : E), (1 : ℝ)))
      fun i ↦ mfderiv I (𝓘(ℝ, ℝ).prod I') (fun y ↦ P_lift (y, t)) x₀ (u i)) = _
    simp_rw [hvel_lift, hslice_lift]
    have hpt_apply : mextDeriv α (t, y₀)
        (Matrix.vecCons ((1 : ℝ), V₀) fun i ↦ ((0 : ℝ), W i)) =
        alternatizeUncurryFin (C ∘L B)
          (Matrix.vecCons ((1 : ℝ), V₀) fun i ↦ ((0 : ℝ), W i)) :=
      congrArg (fun η : TangentSpace (𝓘(ℝ, ℝ).prod I') (t, y₀) [⋀^Fin (k + 2)]→L[ℝ] F ↦
        η (Matrix.vecCons ((1 : ℝ), V₀) fun i ↦ ((0 : ℝ), W i))) hdα_pt
    refine hpt_apply.trans ?_
    have hdecomp : ((1 : ℝ), V₀) = ((1 : ℝ), (0 : E')) + ((0 : ℝ), V₀) := by simp
    rw [hdecomp]
    refine ((alternatizeUncurryFin (C ∘L B)).toAlternatingMap.map_vecCons_add
      (fun i ↦ ((0 : ℝ), W i)) ((1 : ℝ), (0 : E')) ((0 : ℝ), V₀)).trans ?_
    rw [ContinuousAlternatingMap.add_apply]
    congr 1
    · change alternatizeUncurryFin (C ∘L B)
        (Matrix.vecCons ((1 : ℝ), (0 : E')) fun i ↦ ((0 : ℝ), W i)) = _
      rw [alternatizeUncurryFin_apply, Fin.sum_univ_succ]
      simp only [ContinuousLinearMap.comp_apply]
      have hzero_tail (j : Fin (k + 1)) :
          ((-1 : ℤ) ^ j.succ.val) •
            (C (B (Matrix.vecCons ((1 : ℝ), (0 : E')) (fun i ↦ ((0 : ℝ), W i)) j.succ)))
              (Fin.removeNth j.succ
                (Matrix.vecCons ((1 : ℝ), (0 : E')) fun i ↦ ((0 : ℝ), W i))) = 0 := by
        have h0 : (ContinuousLinearMap.snd ℝ ℝ E') (Fin.removeNth j.succ
            (Matrix.vecCons ((1 : ℝ), (0 : E')) fun i ↦ ((0 : ℝ), W i)) 0) = 0 := rfl
        have hkill : (C (B (Matrix.vecCons ((1 : ℝ), (0 : E')) (fun i ↦ ((0 : ℝ), W i)) j.succ)))
            (Fin.removeNth j.succ
              (Matrix.vecCons ((1 : ℝ), (0 : E')) fun i ↦ ((0 : ℝ), W i))) = 0 :=
          (B _).map_coord_zero 0 h0
        rw [hkill, smul_zero]
      rw [Finset.sum_eq_zero fun j _ ↦ hzero_tail j, add_zero]
      simp only [Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero,
        Fin.removeNth_zero, C, compContinuousLinearMapCLM_apply,
        compContinuousLinearMap_apply, ContinuousLinearMap.coe_snd', mpullback_apply]
      exact hB10 W
    · have hinr_vec : (Matrix.vecCons ((0 : ℝ), V₀) fun i ↦ ((0 : ℝ), W i)) =
          fun i ↦ ((0 : ℝ), Matrix.vecCons V₀ W i) := by
        funext i; cases i using Fin.cases <;> rfl
      have hCB_inr : alternatizeUncurryFin (C ∘L B)
          (Matrix.vecCons ((0 : ℝ), V₀) fun i ↦ ((0 : ℝ), W i)) =
          alternatizeUncurryFin (B ∘L .inr ℝ ℝ E') (Matrix.vecCons V₀ W) := by
        rw [hinr_vec, alternatizeUncurryFin_apply, alternatizeUncurryFin_apply]
        rfl
      exact hCB_inr.trans ((congrArg (fun η : TangentSpace I' y₀ [⋀^Fin (k + 2)]→L[ℝ] F ↦
        η (Matrix.vecCons V₀ W)) hBinr).trans
        (mfamilyContraction_apply P t (mextDeriv (ω t)) x₀ u).symm)
  simp_rw [← hcurve_eq]
  refine hlift_deriv.congr_deriv ?_
  rw [mextDeriv_congr_of_eventuallyEq hcontr_eq, hsplit]; abel

/-! ### Specialization to time-dependent flows and Moser's identity -/

section TimeDependentFlow

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] [IsManifold I 2 M]

/-- **Contraction along a time-dependent flow.** Wherever the flow `φ_{s, t}` of a jointly `C²`
time-dependent vector field `X` is defined at `x`, `mfamilyContraction` along `(y, u) ↦ φ_{s, u} y`
at time `t` equals `φ_{s, t}^* (ω.interior (X t))` at `x`. -/
theorem mfamilyContraction_timeDependentFlowOf_of_mem {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {s t : ℝ} {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X)
    (ω : RoughForm I M F (k + 1)) :
    mfamilyContraction I I (fun q : M × ℝ ↦ timeDependentFlowOf X s q.2 q.1) t ω x =
      mpullback I I (timeDependentFlowOf X s t) (ω.interior (X t)) x := by
  have hX₁ := hX.of_le (m := 1) one_le_two
  let P : M × ℝ → M := fun q ↦ timeDependentFlowOf X s q.2 q.1
  have hflow : ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I 2
      (fun p : (ℝ × ℝ) × M ↦ timeDependentFlowOf X p.1.1 p.1.2 p.2) ((s, t), x) :=
    (contMDiffOn_timeDependentFlowOf (n := 2) (by norm_num) hX).contMDiffAt
      ((isOpen_timeDependentFlowDomain hX₁).mem_nhds h)
  have hP : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I P (x, t) :=
    (hflow.comp (x, t)
      (((contMDiff_const (c := s)).prodMk contMDiff_snd).prodMk contMDiff_fst).contMDiffAt)
      |>.mdifferentiableAt two_ne_zero
  have hvel : mfamilyVelocity I I P t x = X t (timeDependentFlowOf X s t x) :=
    (mfamilyVelocity_eq_mfderiv_slice hP).trans
      ((congrArg (fun L : ℝ →L[ℝ] E ↦ L (1 : ℝ))
        (hasMFDerivAt_timeDependentFlowOf hX₁ h).mfderiv).trans (one_smul ℝ _))
  exact (mcontractionAlongMap_congr_field_at ω hvel).trans
    (congrFun (mcontractionAlongMap_comp_field (timeDependentFlowOf X s t) (X t) ω) x)

/-- **Moser rate identification.** For a jointly `C²` time-dependent vector field `X` with flow
`φ_{s, t}` defined at `x` and a `(k + 1)`-form `α` on `ℝ × M` that is `C¹` at `(t, φ_{s, t} x)`,
the Lie-derivative rate `φ_{s, t}^* (ι_t^* L_{∂_t} α + L_{X_t} α_t)` of
`TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk` equals the moving-pullback
derivative `(φ_{s, t}^* (ι_t^* L_{∂_t} α))_x + d(C_(φ_{s, t}, V_t) α_t)_x +
C_(φ_{s, t}, V_t)(dα_t)_x`. -/
theorem mpullback_timeDependentFlowOf_rate_eq_mfamilyContraction
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {α : RoughForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)}
    {s t : ℝ} {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X)
    (hα : ContMDiffAt (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin (k + 1)]→L[ℝ] F)) 1
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin (k + 1)]→L[ℝ] F) p (α p))
      (t, timeDependentFlowOf X s t x)) :
    mpullback I I (timeDependentFlowOf X s t)
        (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
            (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) +
          mlieDerivForm (X t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α)) x =
      mpullback I I (timeDependentFlowOf X s t)
          (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
            (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α)) x +
        mextDeriv
          (mfamilyContraction I I (fun q : M × ℝ ↦ timeDependentFlowOf X s q.2 q.1) t
            (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α)) x +
        mfamilyContraction I I (fun q : M × ℝ ↦ timeDependentFlowOf X s q.2 q.1) t
          (mextDeriv (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α)) x := by
  have hX₁ := hX.of_le (m := 1) one_le_two
  let P : M × ℝ → M := fun q ↦ timeDependentFlowOf X s q.2 q.1
  have hflow : ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I 2
      (fun p : (ℝ × ℝ) × M ↦ timeDependentFlowOf X p.1.1 p.1.2 p.2) ((s, t), x) :=
    (contMDiffOn_timeDependentFlowOf (n := 2) (by norm_num) hX).contMDiffAt
      ((isOpen_timeDependentFlowDomain hX₁).mem_nhds h)
  have hP : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I 2 P (x, t) :=
    hflow.comp (x, t)
      (((contMDiff_const (c := s)).prodMk contMDiff_snd).prodMk contMDiff_fst).contMDiffAt
  let slice : ℝ → RoughForm I M F (k + 1) := fun u ↦ mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α
  have hslice_smooth : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] F)
        (E := fun z : M ↦ TangentSpace I z [⋀^Fin (k + 1)]→L[ℝ] Trivial M F z)
        p.2 (slice p.1 p.2)) (t, P (x, t)) := by
    let f_mk : ℝ × M → M → ℝ × M := fun p z ↦ (p.1, z)
    have hf_mk : ContMDiff ((𝓘(ℝ, ℝ).prod I).prod I) (𝓘(ℝ, ℝ).prod I) 2 (Function.uncurry f_mk) :=
      (contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd
    exact hα.mpullback_form_family (f := f_mk) (g := Prod.snd) hf_mk.contMDiffAt
      contMDiffAt_snd le_rfl
  have hd1 := hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk hX h hα
  have hd2 := hasDerivAt_mpullback_family_form hP le_rfl
    (hslice_smooth.mdifferentiableAt one_ne_zero)
  have hslice_deriv : deriv (fun v ↦ slice v (timeDependentFlowOf X s t x)) t =
      mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) (timeDependentFlowOf X s t x) :=
    (hasDerivAt_mpullback_prodMk t (timeDependentFlowOf X s t x)
      (hα.mdifferentiableAt one_ne_zero)).deriv
  have hterm1 : mpullback I I (fun y ↦ P (y, t)) (fun z ↦ deriv (fun v ↦ slice v z) t) x =
      mpullback I I (timeDependentFlowOf X s t)
        (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α)) x := by
    ext w; rw [mpullback_apply, mpullback_apply]
    change deriv (fun v ↦ slice v (timeDependentFlowOf X s t x)) t
      (fun i ↦ mfderiv I I (timeDependentFlowOf X s t) x (w i)) = _
    rw [hslice_deriv]
  exact (hd1.unique hd2).trans (by rw [hterm1])

end TimeDependentFlow

/-! ### Homotopy operator of a family of maps -/

section Homotopy

private def mfamilyIntegrand (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (P : M × ℝ → N) (ω : RoughForm I' N F (k + 1)) (x : M) (t : ℝ) : E [⋀^Fin k]→L[ℝ] F :=
  mfamilyContraction I I' P t ω x

/-- **Homotopy operator of a moving map `P : M × ℝ → N`.** Integrates
`mfamilyContraction I I' P t ω` over `t ∈ [0, 1]`. When `P` is `C²` on an open neighbourhood of
`M × [0, 1]` and `F` is complete, this satisfies `d(K_P ω) + K_P(dω) = p₁^* ω - p₀^* ω` without
invertibility of `p_t`. -/
def mfamilyHomotopyOperator (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    (P : M × ℝ → N) (ω : RoughForm I' N F (k + 1)) : RoughForm I M F k :=
  fun x ↦ intervalIntegral (E := E [⋀^Fin k]→L[ℝ] F) (mfamilyIntegrand I I' P ω x) 0 1 volume

theorem mfamilyHomotopyOperator_apply (P : M × ℝ → N) (ω : RoughForm I' N F (k + 1)) (x : M) :
    mfamilyHomotopyOperator I I' P ω x = intervalIntegral (E := E [⋀^Fin k]→L[ℝ] F)
      (fun t ↦ (mfamilyContraction I I' P t ω x : E [⋀^Fin k]→L[ℝ] F)) 0 1 volume := (rfl)

@[simp]
theorem mfamilyHomotopyOperator_zero (P : M × ℝ → N) :
    mfamilyHomotopyOperator I I' P (0 : RoughForm I' N F (k + 1)) = 0 := by
  funext x; rw [mfamilyHomotopyOperator_apply]; simp_rw [mfamilyContraction_zero]
  exact intervalIntegral.integral_zero (E := E [⋀^Fin k]→L[ℝ] F) (a := 0) (b := 1)

@[simp]
theorem mfamilyHomotopyOperator_smul (P : M × ℝ → N) (c : ℝ) (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperator I I' P (c • ω) = c • mfamilyHomotopyOperator I I' P ω := by
  funext x; rw [mfamilyHomotopyOperator_apply, Pi.smul_apply, mfamilyHomotopyOperator_apply]
  simp_rw [mfamilyContraction_smul]
  exact intervalIntegral.integral_smul (E := E [⋀^Fin k]→L[ℝ] F) (μ := volume) (a := 0) (b := 1) c _

@[simp]
theorem mfamilyHomotopyOperator_neg (P : M × ℝ → N) (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperator I I' P (-ω) = -mfamilyHomotopyOperator I I' P ω := by
  rw [← neg_one_smul ℝ ω, mfamilyHomotopyOperator_smul, neg_one_smul]

/-- **Cylinder-pullback identification.** Whenever `P : M × ℝ → N` is differentiable at `(x, t)` for
all `t ∈ [0, 1]`, `mfamilyHomotopyOperator I I' P ω x` agrees with `TauCeti.homotopyOperator`
applied to the cylinder pullback `(P ∘ (id × Subtype.val))^* ω` on `M × [0, 1]`. -/
theorem mfamilyHomotopyOperator_eq_homotopyOperator_mpullback_at
    {P : M × ℝ → N} {x : M}
    (hP : ∀ t ∈ Icc (0 : ℝ) 1, MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (x, t))
    (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperator I I' P ω x =
      homotopyOperator
        (mpullback (I.prod (𝓡∂ 1)) I' (P ∘ Prod.map id (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) ω) x := by
  rw [mfamilyHomotopyOperator_apply, homotopyOperator_apply]
  refine intervalIntegral.integral_congr (E := E [⋀^Fin k]→L[ℝ] F) fun t ht ↦ ?_
  rw [uIcc_of_le zero_le_one] at ht
  let t' : Icc (0 : ℝ) 1 := ⟨t, ht⟩
  have hproj : projIcc 0 1 zero_le_one t = t' := projIcc_of_mem zero_le_one ht
  have hsub_d : MDifferentiableAt (I.prod (𝓡∂ 1)) (I.prod 𝓘(ℝ, ℝ))
      (Prod.map (id : M → M) (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) (x, t') :=
    mdifferentiableAt_id.prodMap ((contMDiff_subtypeVal_Icc t').mdifferentiableAt one_ne_zero)
  ext v
  rw [mfamilyContraction_apply]
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
    rw [mfderiv_slice_eq_mfderiv_prod_inl (hP t ht) (v i)]
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

theorem mfamilyHomotopyOperator_eq_homotopyOperator_mpullback
    {P : M × ℝ → N} {W : Set (M × ℝ)} (hW : IsOpen W) (hIcc : univ ×ˢ Icc (0 : ℝ) 1 ⊆ W)
    (hP : MDifferentiableOn (I.prod 𝓘(ℝ, ℝ)) I' P W) (ω : RoughForm I' N F (k + 1)) :
    mfamilyHomotopyOperator I I' P ω =
      homotopyOperator
        (mpullback (I.prod (𝓡∂ 1)) I' (P ∘ Prod.map id (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) ω) :=
  funext fun x ↦ mfamilyHomotopyOperator_eq_homotopyOperator_mpullback_at
    (fun t ht ↦
      (hP (x, t) (hIcc ⟨trivial, ht⟩)).mdifferentiableAt (hW.mem_nhds (hIcc ⟨trivial, ht⟩)))
    ω

private theorem contMDiff_comp_subtypeVal_Icc {r : WithTop ℕ∞}
    {P : M × ℝ → N} {W : Set (M × ℝ)} (hW : IsOpen W) (hIcc : univ ×ˢ Icc (0 : ℝ) 1 ⊆ W)
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' r P W) :
    ContMDiff (I.prod (𝓡∂ 1)) I' r (P ∘ Prod.map id (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) := fun q ↦
  ((hP (q.1, q.2.1) (hIcc ⟨trivial, q.2.2⟩)).contMDiffAt
    (hW.mem_nhds (hIcc ⟨trivial, q.2.2⟩))).comp q
    (contMDiff_id.prodMap contMDiff_subtypeVal_Icc).contMDiffAt

/-- `mfamilyHomotopyOperator` is additive on continuous forms when `P` is `C¹` on an open
neighbourhood of `M × [0, 1]`. -/
theorem mfamilyHomotopyOperator_add [IsManifold I 1 M] [IsManifold I' 1 N]
    {P : M × ℝ → N} {W : Set (M × ℝ)} (hW : IsOpen W) (hIcc : univ ×ˢ Icc (0 : ℝ) 1 ⊆ W)
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' 1 P W)
    {ω η : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' 0 ω) (hη : IsSmoothForm I' 0 η) :
    mfamilyHomotopyOperator I I' P (ω + η) =
      mfamilyHomotopyOperator I I' P ω + mfamilyHomotopyOperator I I' P η := by
  have hP_cyl : ContMDiff (I.prod (𝓡∂ 1)) I' ((0 : ℕ∞) + 1)
      (P ∘ Prod.map id (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) :=
    (contMDiff_comp_subtypeVal_Icc hW hIcc hP).of_le (by simp)
  have hP_mdiff : MDifferentiableOn (I.prod 𝓘(ℝ, ℝ)) I' P W := fun q hq ↦
    (hP q hq).mdifferentiableWithinAt one_ne_zero
  rw [mfamilyHomotopyOperator_eq_homotopyOperator_mpullback hW hIcc hP_mdiff (ω + η),
    mfamilyHomotopyOperator_eq_homotopyOperator_mpullback hW hIcc hP_mdiff ω,
    mfamilyHomotopyOperator_eq_homotopyOperator_mpullback hW hIcc hP_mdiff η,
    mpullback_add, homotopyOperator_add (hω.mpullback hP_cyl) (hη.mpullback hP_cyl)]

theorem mfamilyHomotopyOperator_sub [IsManifold I 1 M] [IsManifold I' 1 N]
    {P : M × ℝ → N} {W : Set (M × ℝ)} (hW : IsOpen W) (hIcc : univ ×ˢ Icc (0 : ℝ) 1 ⊆ W)
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' 1 P W)
    {ω η : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' 0 ω) (hη : IsSmoothForm I' 0 η) :
    mfamilyHomotopyOperator I I' P (ω - η) =
      mfamilyHomotopyOperator I I' P ω - mfamilyHomotopyOperator I I' P η := by
  rw [sub_eq_add_neg, mfamilyHomotopyOperator_add hW hIcc hP hω hη.neg,
    ← neg_one_smul ℝ η, mfamilyHomotopyOperator_smul, neg_one_smul, sub_eq_add_neg]

/-- If `P` is `C^(r + 1)` on an open neighbourhood `W` of `M × [0, 1]`, `mfamilyHomotopyOperator`
sends `C^r` forms on `N` to `C^r` forms on `M`. -/
theorem IsSmoothForm.mfamilyHomotopyOperator {r : ℕ∞} [IsManifold I 1 M] [IsManifold I (r + 1) M]
    [IsManifold I' 1 N] {P : M × ℝ → N} {W : Set (M × ℝ)} (hW : IsOpen W)
    (hIcc : univ ×ˢ Icc (0 : ℝ) 1 ⊆ W)
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' (r + 1) P W) {ω : RoughForm I' N F (k + 1)}
    (hω : IsSmoothForm I' r ω) :
    IsSmoothForm I r (TauCeti.mfamilyHomotopyOperator I I' P ω) := by
  have hP_mdiff : MDifferentiableOn (I.prod 𝓘(ℝ, ℝ)) I' P W := fun q hq ↦
    (hP q hq).mdifferentiableWithinAt (by simp)
  rw [mfamilyHomotopyOperator_eq_homotopyOperator_mpullback hW hIcc hP_mdiff]
  exact (hω.mpullback (contMDiff_comp_subtypeVal_Icc hW hIcc hP)).homotopyOperator

/-- **The cochain-homotopy identity for a moving map `P : M × ℝ → N`.** When `P` is `C²` on an open
neighbourhood `W` of `M × [0, 1]` between `C²` manifolds (possibly with boundary or corners), `F` is
a Banach space, and `ω` is a `C¹` `(k + 1)`-form on `N`,
`d(K_P ω) + K_P(dω) = p₁^* ω - p₀^* ω` without invertibility of the slices `p_t`. -/
theorem mextDeriv_mfamilyHomotopyOperator_add_mfamilyHomotopyOperator_mextDeriv_of_isOpen
    [IsManifold I 2 M] [IsManifold I' 2 N] [CompleteSpace F]
    {P : M × ℝ → N} {W : Set (M × ℝ)} (hW : IsOpen W) (hIcc : univ ×ˢ Icc (0 : ℝ) 1 ⊆ W)
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' 2 P W)
    {ω : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' 1 ω) (x₀ : M) :
    mextDeriv (mfamilyHomotopyOperator I I' P ω) x₀ +
        mfamilyHomotopyOperator I I' P (mextDeriv ω) x₀ =
      mpullback I I' (fun x ↦ P (x, 1)) ω x₀ - mpullback I I' (fun x ↦ P (x, 0)) ω x₀ := by
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have : IsManifold I' 1 N := IsManifold.of_le one_le_two
  have hP_cyl := contMDiff_comp_subtypeVal_Icc hW hIcc hP
  have hP_mdiff : MDifferentiableOn (I.prod 𝓘(ℝ, ℝ)) I' P W := fun q hq ↦
    (hP q hq).mdifferentiableWithinAt two_ne_zero
  have hφ := hω.mpullback (hP_cyl.of_le (m := (1 : ℕ∞) + 1) (by norm_num))
  have hd_pull := mpullback_mextDeriv hP_cyl ((isSmoothBundleForm_def 1 ω).mpr hω.contMDiff)
  rw [mfamilyHomotopyOperator_eq_homotopyOperator_mpullback hW hIcc hP_mdiff ω,
    mfamilyHomotopyOperator_eq_homotopyOperator_mpullback hW hIcc hP_mdiff (mextDeriv ω), hd_pull]
  refine (mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv hφ x₀).trans ?_
  have hend (c : Icc (0 : ℝ) 1) : mpullback I (I.prod (𝓡∂ 1)) (fun x ↦ (x, c))
      (mpullback (I.prod (𝓡∂ 1)) I' _ ω) x₀ = mpullback I I' (fun x ↦ P (x, (c : ℝ))) ω x₀ :=
    (mpullback_comp_at (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
      (hP_cyl.mdifferentiable two_ne_zero (x₀, c)) ω).symm
  rw [hend 1, hend 0]; rfl

/-- **The cochain-homotopy identity for a globally `C²` moving map `P : M × ℝ → N`.** -/
theorem mextDeriv_mfamilyHomotopyOperator_add_mfamilyHomotopyOperator_mextDeriv
    [IsManifold I 2 M] [IsManifold I' 2 N] [CompleteSpace F]
    {P : M × ℝ → N} (hP : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' 2 P)
    {ω : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' 1 ω) (x₀ : M) :
    mextDeriv (mfamilyHomotopyOperator I I' P ω) x₀ +
        mfamilyHomotopyOperator I I' P (mextDeriv ω) x₀ =
      mpullback I I' (fun x ↦ P (x, 1)) ω x₀ - mpullback I I' (fun x ↦ P (x, 0)) ω x₀ :=
  mextDeriv_mfamilyHomotopyOperator_add_mfamilyHomotopyOperator_mextDeriv_of_isOpen
    isOpen_univ (subset_univ _) hP.contMDiffOn hω x₀

/-- **Closed forms along a smooth homotopy.** When `P` is `C²` on an open neighbourhood `W` of
`M × [0, 1]` and `ω` is a closed `C¹` form with values in a Banach space,
`p₁^* ω - p₀^* ω = d(K_P ω)`. -/
theorem mextDeriv_mfamilyHomotopyOperator_of_isOpen
    [IsManifold I 2 M] [IsManifold I' 2 N] [CompleteSpace F]
    {P : M × ℝ → N} {W : Set (M × ℝ)} (hW : IsOpen W) (hIcc : univ ×ˢ Icc (0 : ℝ) 1 ⊆ W)
    (hP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I' 2 P W)
    {ω : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' 1 ω) (hclosed : mextDeriv ω = 0)
    (x₀ : M) :
    mextDeriv (mfamilyHomotopyOperator I I' P ω) x₀ =
      mpullback I I' (fun x ↦ P (x, 1)) ω x₀ - mpullback I I' (fun x ↦ P (x, 0)) ω x₀ := by
  rw [← mextDeriv_mfamilyHomotopyOperator_add_mfamilyHomotopyOperator_mextDeriv_of_isOpen
    hW hIcc hP hω x₀, hclosed, mfamilyHomotopyOperator_zero, Pi.zero_apply, add_zero]

theorem mextDeriv_mfamilyHomotopyOperator
    [IsManifold I 2 M] [IsManifold I' 2 N] [CompleteSpace F]
    {P : M × ℝ → N} (hP : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' 2 P)
    {ω : RoughForm I' N F (k + 1)} (hω : IsSmoothForm I' 1 ω) (hclosed : mextDeriv ω = 0)
    (x₀ : M) :
    mextDeriv (mfamilyHomotopyOperator I I' P ω) x₀ =
      mpullback I I' (fun x ↦ P (x, 1)) ω x₀ - mpullback I I' (fun x ↦ P (x, 0)) ω x₀ :=
  mextDeriv_mfamilyHomotopyOperator_of_isOpen isOpen_univ (subset_univ _) hP.contMDiffOn hω
    hclosed x₀

end Homotopy

end MovingPullbackDeriv

end TauCeti
