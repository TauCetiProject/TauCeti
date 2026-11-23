/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ContractionAlongMap.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Restriction
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Contraction of differential forms along moving families of maps

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

This module develops the velocity and family-contraction API — linearity, stationarity, source and
target naturality, open-subset restrictions on `M`, `N`, and `ℝ`, joint `C^m` smoothness with an
extra parameter manifold `L`, and bundled linear maps on `SmoothForm` — that feeds moving-pullback
differentiation in `TauCeti.Geometry.Manifold.DifferentialForm.ContractionAlongMap.MovingPullback`
and the moving-pullback homotopy operator in
`TauCeti.Geometry.Manifold.DifferentialForm.ContractionAlongMap.Homotopy`.

## Main declarations

* `TauCeti.mfamilyVelocity`, `TauCeti.mfamilyContraction`: parameter velocity and family
  contraction along `P : M × T → N`, unified across `T = ℝ` and `T = ↥J` (`J : Opens ℝ`).
* `TauCeti.mfamilyContraction_eq_mpullback_interior_at`,
  `TauCeti.mfamilyContraction_eq_mpullback_interior`: Cartan-slice identification
  `(y ↦ (y, t))^* ((P^* ω).interior (0, 1))`.
* `TauCeti.mfamilyVelocity_comp_prodMap_id_at`, `TauCeti.mfamilyVelocity_comp_at`,
  `TauCeti.mfamilyContraction_comp_prodMap_id`, `TauCeti.mfamilyContraction_mpullback`: source and
  target naturality.
* `TauCeti.mfamilyVelocity_comp_prodMap_subtype_val_left`,
  `TauCeti.mfamilyVelocity_comp_prodMap_subtype_val_right`,
  `TauCeti.mpullback_subtype_val_mfamilyContraction`,
  `TauCeti.mfamilyContraction_mpullback_subtype_val`,
  `TauCeti.mfamilyContraction_comp_prodMap_subtype_val` (and their `Opens.inclusion` counterparts):
  unconditional open-subset restrictions on `M`, `N`, and `ℝ`.
* `ContMDiffAt.mfamilyVelocity`, `ContMDiffAt.mfamilyVelocity_opens`,
  `ContMDiffAt.mfamilyContraction`, `ContMDiffAt.mfamilyContraction_opens`,
  `TauCeti.IsSmoothForm.mfamilyContraction`, `TauCeti.IsSmoothForm.mfamilyContraction_opens`,
  `TauCeti.SmoothForm.mfamilyContraction`, `TauCeti.SmoothForm.mfamilyContractionOpens`: joint
  `C^m` smoothness with an extra parameter manifold `L` and bundled linear maps on `SmoothForm`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapters 14 and 17.
-/

public section

noncomputable section

open Bundle Set Filter TopologicalSpace ContinuousAlternatingMap
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

/-- Where `P` is differentiable at `(x, t)`, `mfamilyVelocity` is the curve derivative of the
right slice `u ↦ P (x, u)` at `t` applied to `1`. -/
theorem mfamilyVelocity_eq_mfderiv_slice_right_apply {P : M × T → N} {t : T} {x : M}
    (hP : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (x, t)) :
    mfamilyVelocity I I' P t x = mfderiv 𝓘(ℝ, ℝ) I' (fun u ↦ P (x, u)) t (1 : ℝ) :=
  (mfderiv_slice_right_apply hP (1 : ℝ)).symm

/-- If `u ↦ P (x, u)` is locally constant near `t`, then `mfamilyVelocity I I' P t x = 0`, with no
differentiability assumption on `P`. -/
theorem mfamilyVelocity_eq_zero_of_eventuallyEq_const {P : M × T → N} {t : T} {x : M} {y : N}
    (hP : ∀ᶠ u in 𝓝 t, P (x, u) = y) :
    mfamilyVelocity I I' P t x = 0 := by
  by_cases hd : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (x, t)
  · rw [mfamilyVelocity_eq_mfderiv_slice_right_apply hd]
    have hcongr : (fun u ↦ P (x, u)) =ᶠ[𝓝 t] fun _ ↦ y := hP
    rw [hcongr.mfderiv_eq, mfderiv_const]; rfl
  · rw [mfamilyVelocity_def, mfderiv_zero_of_not_mdifferentiableAt hd]; rfl

/-- A time-independent family `p ∘ Prod.fst` has zero parameter velocity. -/
@[simp]
theorem mfamilyVelocity_comp_fst (p : M → N) (t : T) (x : M) :
    mfamilyVelocity I I' (p ∘ (Prod.fst : M × T → M)) t x = 0 :=
  mfamilyVelocity_eq_zero_of_eventuallyEq_const (y := p x) (Eventually.of_forall fun _ ↦ rfl)

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
      refine (mfamilyVelocity_eq_mfderiv_slice_right_apply hmd).trans ?_
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
          (mfderiv I (I.prod 𝓘(ℝ, ℝ)) (fun y ↦ (y, t)) x (v i))) := by
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
    exact (mfderiv_slice_left_apply hP (v i)).trans
      (congrArg (mfderiv (I.prod 𝓘(ℝ, ℝ)) I' P (x, t)) hleft.symm)

/-- **Global Cartan-slice description.** For a differentiable family `P : M × T → N`,
`mfamilyContraction` at `t` equals the pullback along `y ↦ (y, t)` of `(P^* ω).interior (0, 1)`. -/
theorem mfamilyContraction_eq_mpullback_interior {P : M × T → N}
    (hP : MDifferentiable (I.prod 𝓘(ℝ, ℝ)) I' P) (t : T) (ω : RoughForm I' N F (k + 1)) :
    mfamilyContraction I I' P t ω =
      mpullback I (I.prod 𝓘(ℝ, ℝ)) (fun y ↦ (y, t))
        ((mpullback (I.prod 𝓘(ℝ, ℝ)) I' P ω).interior (fun _ ↦ ((0 : E), (1 : ℝ)))) :=
  funext fun x ↦ mfamilyContraction_eq_mpullback_interior_at (hP (x, t)) ω

/-- Contracting along a time-independent family `p ∘ Prod.fst` vanishes identically. -/
@[simp]
theorem mfamilyContraction_comp_fst (p : M → N) (t : T) (ω : RoughForm I' N F (k + 1)) :
    mfamilyContraction I I' (p ∘ (Prod.fst : M × T → M)) t ω = 0 := by
  ext x v
  rw [mfamilyContraction_def, mcontractionAlongMap_apply, mfamilyVelocity_comp_fst]
  exact (ω (p x)).map_coord_zero 0 rfl

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

/-! ### Restriction and naturality of `mfamilyVelocity` and `mfamilyContraction` -/

/-- **Source naturality of `mfamilyVelocity`.** Precomposing `P : M × T → N` with
`h × id : L × T → M × T` evaluates the parameter velocity at `h z`. -/
theorem mfamilyVelocity_comp_prodMap_id_at {h : L → M} {P : M × T → N} {t : T} {z : L}
    (hh : MDifferentiableAt I'' I h z)
    (hP : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (h z, t)) :
    mfamilyVelocity I'' I' (P ∘ Prod.map h id) t z = mfamilyVelocity I I' P t (h z) := by
  have hpm : MDifferentiableAt (I''.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
      (Prod.map h (id : T → T)) (z, t) := hh.prodMap mdifferentiableAt_id
  let u0 : TangentSpace (I''.prod 𝓘(ℝ, ℝ)) (z, t) := ((0 : E''), (1 : ℝ))
  have hc := mfderiv_comp_apply (z, t) hP hpm u0
  have hpm_apply : mfderiv (I''.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
      (Prod.map h (id : T → T)) (z, t) u0 = ((0 : E), (1 : ℝ)) := by
    rw [mfderiv_prodMap (p := (z, t)) hh mdifferentiableAt_id, mfderiv_id]
    exact Prod.ext (_root_.map_zero (mfderiv I'' I h z)) rfl
  exact hc.trans (congrArg (mfderiv (I.prod 𝓘(ℝ, ℝ)) I' P (h z, t)) hpm_apply)

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
  refine (mcontractionAlongMap_congr_field_at
    (W := fun w ↦ mfamilyVelocity I I' P t (h w)) ω
    (mfamilyVelocity_comp_prodMap_id_at hh hP)).trans ?_
  exact mcontractionAlongMap_comp_right_at (p := fun y ↦ P (y, t)) hh hPt

/-- **Global source naturality.** For differentiable `h : L → M` and `P : M × T → N`,
`mfamilyContraction` along `P ∘ (h × id)` is the pullback along `h` of `mfamilyContraction` along
`P`. -/
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

/-- **Target naturality of `mfamilyVelocity`.** Postcomposing `P : M × T → N` with `q : N → Q`
pushes the parameter velocity forward along `dq`. -/
theorem mfamilyVelocity_comp_at {P : M × T → N} {q : N → Q} {t : T} {x : M}
    (hP : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (x, t))
    (hq : MDifferentiableAt I' I''' q (P (x, t))) :
    mfamilyVelocity I I''' (q ∘ P) t x =
      mfderiv I' I''' q (P (x, t)) (mfamilyVelocity I I' P t x) :=
  mfderiv_comp_apply (x, t) hq hP ((0 : E), (1 : ℝ))

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
  exact (mcontractionAlongMap_mpullback_at (p := fun y ↦ P (y, t)) hPt hq).trans
    (mcontractionAlongMap_congr_field_at η (mfamilyVelocity_comp_at hP hq).symm)

/-- **Global target naturality.** For differentiable `P : M × T → N` and `q : N → Q`, contracting
`q^* η` along `P` equals contracting `η` along `q ∘ P`. -/
theorem mfamilyContraction_mpullback {P : M × T → N} {q : N → Q} (t : T)
    (η : RoughForm I''' Q F (k + 1)) (hP : MDifferentiable (I.prod 𝓘(ℝ, ℝ)) I' P)
    (hq : MDifferentiable I' I''' q) :
    mfamilyContraction I I' P t (mpullback I' I''' q η) =
      mfamilyContraction I I''' (q ∘ P) t η :=
  funext fun x ↦ mfamilyContraction_mpullback_at (hP (x, t)) (hq (P (x, t)))

end TargetNaturality

/-- Pushing `mfderiv` through an open-submanifold identification given by a pair of `C¹` mutually
inverse maps `φ : M₁ → V` and `ψ : V → M₁`, handling both differentiable and non-differentiable
points uniformly. -/
private theorem mfderiv_comp_subtypeVal_comp_of_rightInverse
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁] {J₁ : ModelWithCorners ℝ E₁ H₁}
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂] {J₂ : ModelWithCorners ℝ E₂ H₂}
    {V : Opens M₂} {P : M₂ → N} {φ : M₁ → V} {ψ : V → M₁} {p : M₁}
    (hφ : ContMDiff J₁ J₂ 1 φ) (hψ : ContMDiff J₂ J₁ 1 ψ)
    (hleft : ψ (φ p) = p) (hright : Function.RightInverse ψ φ)
    {v : TangentSpace J₁ p} {w : TangentSpace J₂ (φ p)}
    (hd : mfderiv J₁ J₂ ((Subtype.val : V → M₂) ∘ φ) p v = w) :
    mfderiv J₁ I' (P ∘ (Subtype.val : V → M₂) ∘ φ) p v = mfderiv J₂ I' P (φ p : M₂) w := by
  have h_amb : mfderiv J₂ I' (P ∘ (Subtype.val : V → M₂)) (φ p) w =
      mfderiv J₂ I' P (φ p : M₂) w :=
    Manifold.mfderiv_comp_subtype_val_apply (J := J₂) (I := I') (U := V) (f := P) (x := φ p) w
  by_cases hPd : MDifferentiableAt J₂ I' (P ∘ (Subtype.val : V → M₂)) (φ p)
  · have hφd : mfderiv J₁ J₂ φ p v = w := by
      apply Manifold.mfderiv_subtype_val_injective (I := J₂) (φ p)
      have hc1 := (mfderiv_comp_apply p
        (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero)
        (hφ.mdifferentiableAt one_ne_zero) v).symm
      have hc2 : mfderiv J₂ J₂ (Subtype.val : V → M₂) (φ p) w = w := by
        rw [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
          Manifold.tangentSpaceOpenEquiv_apply]
      exact hc1.trans (hd.trans hc2.symm)
    have h1 := mfderiv_comp_apply p hPd (hφ.mdifferentiableAt one_ne_zero) v
    exact h1.trans ((congrArg (mfderiv J₂ I' (P ∘ Subtype.val) (φ p)) hφd).trans h_amb)
  · have hPd' : ¬MDifferentiableAt J₁ I' (P ∘ (Subtype.val : V → M₂) ∘ φ) p := fun h ↦
      hPd ((MDifferentiableAt.comp_of_eq (φ p) h
        (hψ.mdifferentiableAt one_ne_zero) hleft).congr_of_eventuallyEq
        (Eventually.of_forall fun q ↦ (congrArg (P ∘ Subtype.val) (hright q)).symm))
    have hz1 : mfderiv J₁ I' (P ∘ (Subtype.val : V → M₂) ∘ φ) p v = 0 := by
      rw [mfderiv_zero_of_not_mdifferentiableAt hPd']; exact zero_apply _
    have hz2 : mfderiv J₂ I' (P ∘ (Subtype.val : V → M₂)) (φ p) w = 0 := by
      rw [mfderiv_zero_of_not_mdifferentiableAt hPd]; exact zero_apply _
    exact hz1.trans (hz2.symm.trans h_amb)

private def prodOpenLeft (U : Opens M) : Opens (M × T) :=
  ⟨(U : Set M) ×ˢ univ, U.isOpen.prod isOpen_univ⟩

private def toProdOpenLeft (U : Opens M) (q : U × T) : prodOpenLeft (T := T) U :=
  ⟨(q.1.val, q.2), Set.mk_mem_prod q.1.property (mem_univ _)⟩

private def ofProdOpenLeft (U : Opens M) (q : prodOpenLeft (T := T) U) : U × T :=
  (⟨q.val.1, (Set.mem_prod.mp q.property).1⟩, q.val.2)

private theorem contMDiff_toProdOpenLeft {r : WithTop ℕ∞} (U : Opens M) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) r (toProdOpenLeft (T := T) U) :=
  (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).mp
    ((contMDiff_subtypeVal.comp contMDiff_fst).prodMk contMDiff_snd)

private theorem contMDiff_ofProdOpenLeft {r : WithTop ℕ∞} (U : Opens M) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) r (ofProdOpenLeft (T := T) U) :=
  ((TauCeti.ContMDiff.subtypeVal_comp_iff _ _).mp
    (contMDiff_fst.comp contMDiff_subtypeVal)).prodMk
    (contMDiff_snd.comp contMDiff_subtypeVal)

/-- **Open source restriction of `mfamilyVelocity`.** Restricting `P : M × T → N` to `U : Opens M`
preserves its parameter velocity, with no regularity hypothesis. -/
@[simp]
theorem mfamilyVelocity_comp_prodMap_subtype_val_left (U : Opens M) (P : M × T → N) (t : T)
    (x : U) :
    mfamilyVelocity I I' (P ∘ Prod.map (Subtype.val : U → M) id) t x =
      mfamilyVelocity I I' P t (x : M) := by
  refine mfderiv_comp_subtypeVal_comp_of_rightInverse (V := prodOpenLeft U)
    (φ := toProdOpenLeft U) (ψ := ofProdOpenLeft U)
    (contMDiff_toProdOpenLeft U) (contMDiff_ofProdOpenLeft U) rfl (fun _ ↦ rfl) ?_
  have hcomp : (Subtype.val : prodOpenLeft (T := T) U → M × T) ∘ toProdOpenLeft U =
      Prod.map (Subtype.val : U → M) id := rfl
  have hd : mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
      (Prod.map (Subtype.val : U → M) (id : T → T)) (x, t) =
      (mfderiv I I (Subtype.val : U → M) x).prodMap
        (ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) t)) := by
    rw [mfderiv_prodMap (p := (x, t)) (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero)
      mdifferentiableAt_id, mfderiv_id]
  refine (congrArg (fun f ↦ mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) f (x, t)
    ((0 : E), (1 : ℝ))) hcomp).trans ?_
  refine (congrArg (fun L ↦ L ((0 : E), (1 : ℝ))) hd).trans ?_
  exact Prod.ext (_root_.map_zero (mfderiv I I (Subtype.val : U → M) x)) rfl

/-- **Nested open source restriction of `mfamilyVelocity`.** Restricting `P : W × T → N` along
`U ≤ W` in `Opens M` preserves its parameter velocity, with no regularity hypothesis. -/
@[simp]
theorem mfamilyVelocity_comp_prodMap_inclusion_left {U W : Opens M} (h : U ≤ W) (P : W × T → N)
    (t : T) (x : U) :
    mfamilyVelocity I I' (P ∘ Prod.map (Opens.inclusion h) id) t x =
      mfamilyVelocity I I' P t (Opens.inclusion h x) := by
  classical
  let P' : M × T → N := fun q ↦
    if hq : q.1 ∈ W then P (⟨q.1, hq⟩, q.2) else P (Opens.inclusion h x, q.2)
  have hW : P' ∘ Prod.map (Subtype.val : W → M) id = P :=
    funext fun q ↦ dite_eq_left q.1.property
  have hU : P' ∘ Prod.map (Subtype.val : U → M) id = P ∘ Prod.map (Opens.inclusion h) id :=
    funext fun q ↦ dite_eq_left (h q.1.property)
  rw [← hU, mfamilyVelocity_comp_prodMap_subtype_val_left, ← hW,
    mfamilyVelocity_comp_prodMap_subtype_val_left]

/-- **Open target restriction of `mfamilyVelocity`.** Following `P : M × T → U'` by
`Subtype.val : U' → N` preserves its parameter velocity, with no regularity hypothesis. -/
@[simp]
theorem mfamilyVelocity_subtype_val_comp (U' : Opens N) (P : M × T → U') (t : T) (x : M) :
    mfamilyVelocity I I' ((Subtype.val : U' → N) ∘ P) t x = mfamilyVelocity I I' P t x :=
  Manifold.mfderiv_subtype_val_comp_apply _

/-- **Nested open target restriction of `mfamilyVelocity`.** Following `P : M × T → U'` by
`Opens.inclusion h` for `U' ≤ W'` preserves its parameter velocity, with no regularity
hypothesis. -/
@[simp]
theorem mfamilyVelocity_inclusion_comp {U' W' : Opens N} (h : U' ≤ W') (P : M × T → U') (t : T)
    (x : M) :
    mfamilyVelocity I I' (Opens.inclusion h ∘ P) t x = mfamilyVelocity I I' P t x := by
  have h1 := mfamilyVelocity_subtype_val_comp (I := I) (I' := I') U' P t x
  have h2 := mfamilyVelocity_subtype_val_comp (I := I) (I' := I') W' (Opens.inclusion h ∘ P) t x
  exact h2.symm.trans h1

/-- **Open source restriction.** Restricting `mfamilyContraction` to `U : Opens M` contracts the
restricted family `P ∘ Prod.map Subtype.val id`, with no regularity hypothesis. -/
@[simp]
theorem mpullback_subtype_val_mfamilyContraction (U : Opens M) (P : M × T → N) (t : T)
    (ω : RoughForm I' N F (k + 1)) :
    mpullback I I (Subtype.val : U → M) (mfamilyContraction I I' P t ω) =
      mfamilyContraction I I' (P ∘ Prod.map (Subtype.val : U → M) id) t ω := by
  rw [mfamilyContraction_def, mpullback_subtype_val_mcontractionAlongMap]
  funext x
  exact mcontractionAlongMap_congr_field_at ω
    (mfamilyVelocity_comp_prodMap_subtype_val_left U P t x).symm

/-- **Nested open source restriction.** Restricting `mfamilyContraction` along `Opens.inclusion h`
for `U ≤ W` in `Opens M` contracts along `P ∘ Prod.map (Opens.inclusion h) id`, with no regularity
hypothesis. -/
@[simp]
theorem mpullback_inclusion_mfamilyContraction {U W : Opens M} (h : U ≤ W) (P : W × T → N) (t : T)
    (ω : RoughForm I' N F (k + 1)) :
    mpullback I I (Opens.inclusion h) (mfamilyContraction I I' P t ω) =
      mfamilyContraction I I' (P ∘ Prod.map (Opens.inclusion h) id) t ω := by
  rw [mfamilyContraction_def, mpullback_inclusion_mcontractionAlongMap]
  funext x
  exact mcontractionAlongMap_congr_field_at ω
    (mfamilyVelocity_comp_prodMap_inclusion_left h P t x).symm

/-- **Open target restriction.** Contracting a form restricted to an open target `U' : Opens N`
along `P : M × T → U'` agrees with contracting the ambient form along `Subtype.val ∘ P`, with no
regularity hypothesis. -/
@[simp]
theorem mfamilyContraction_mpullback_subtype_val (U' : Opens N) (P : M × T → U') (t : T)
    (ω : RoughForm I' N F (k + 1)) :
    mfamilyContraction I I' P t (mpullback I' I' (Subtype.val : U' → N) ω) =
      mfamilyContraction I I' ((Subtype.val : U' → N) ∘ P) t ω := by
  rw [mfamilyContraction_def, mcontractionAlongMap_mpullback_subtype_val]
  funext x
  exact mcontractionAlongMap_congr_field_at ω
    (mfamilyVelocity_subtype_val_comp U' P t x).symm

/-- **Nested open target restriction.** Contracting a form restricted along `Opens.inclusion h`
for `U' ≤ W'` in `Opens N` along `P : M × T → U'` agrees with contracting along
`Opens.inclusion h ∘ P`, with no regularity hypothesis. -/
@[simp]
theorem mfamilyContraction_mpullback_inclusion {U' W' : Opens N} (h : U' ≤ W') (P : M × T → U')
    (t : T) (ω : RoughForm I' W' F (k + 1)) :
    mfamilyContraction I I' P t (mpullback I' I' (Opens.inclusion h) ω) =
      mfamilyContraction I I' (Opens.inclusion h ∘ P) t ω := by
  rw [mfamilyContraction_def, mcontractionAlongMap_mpullback_inclusion]
  funext x
  exact mcontractionAlongMap_congr_field_at ω
    (mfamilyVelocity_inclusion_comp h P t x).symm

end FamilyContraction

private def prodOpenRight (J : Opens ℝ) : Opens (M × ℝ) :=
  ⟨univ ×ˢ (J : Set ℝ), isOpen_univ.prod J.isOpen⟩

private def toProdOpenRight (J : Opens ℝ) (q : M × J) : prodOpenRight (M := M) J :=
  ⟨(q.1, q.2.val), Set.mk_mem_prod (mem_univ _) q.2.property⟩

private def ofProdOpenRight (J : Opens ℝ) (q : prodOpenRight (M := M) J) : M × J :=
  (q.val.1, ⟨q.val.2, (Set.mem_prod.mp q.property).2⟩)

private theorem contMDiff_toProdOpenRight {r : WithTop ℕ∞} (J : Opens ℝ) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) r (toProdOpenRight (M := M) J) :=
  (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).mp
    (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp contMDiff_snd))

private theorem contMDiff_ofProdOpenRight {r : WithTop ℕ∞} (J : Opens ℝ) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) r (ofProdOpenRight (M := M) J) :=
  (contMDiff_fst.comp contMDiff_subtypeVal).prodMk
    ((TauCeti.ContMDiff.subtypeVal_comp_iff _ _).mp
      (contMDiff_snd.comp contMDiff_subtypeVal))

/-- **Open parameter restriction of `mfamilyVelocity`.** Restricting `P : M × ℝ → N` to
`J : Opens ℝ` preserves its parameter velocity at `t : J`, with no regularity hypothesis. -/
@[simp]
theorem mfamilyVelocity_comp_prodMap_subtype_val_right (J : Opens ℝ) (P : M × ℝ → N) (t : J)
    (x : M) :
    mfamilyVelocity I I' (P ∘ Prod.map id (Subtype.val : J → ℝ)) t x =
      mfamilyVelocity I I' P (t : ℝ) x := by
  refine mfderiv_comp_subtypeVal_comp_of_rightInverse (V := prodOpenRight J)
    (φ := toProdOpenRight J) (ψ := ofProdOpenRight J)
    (contMDiff_toProdOpenRight J) (contMDiff_ofProdOpenRight J) rfl (fun _ ↦ rfl) ?_
  have hcomp : (Subtype.val : prodOpenRight (M := M) J → M × ℝ) ∘ toProdOpenRight J =
      Prod.map id (Subtype.val : J → ℝ) := rfl
  have hd : mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
      (Prod.map (id : M → M) (Subtype.val : J → ℝ)) (x, t) =
      (ContinuousLinearMap.id ℝ (TangentSpace I x)).prodMap
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : J → ℝ) t) := by
    rw [mfderiv_prodMap (p := (x, t)) mdifferentiableAt_id
      (contMDiff_subtypeVal.mdifferentiableAt one_ne_zero), mfderiv_id]
  refine (congrArg (fun f ↦ mfderiv (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) f (x, t)
    ((0 : E), (1 : ℝ))) hcomp).trans ?_
  refine (congrArg (fun L ↦ L ((0 : E), (1 : ℝ))) hd).trans ?_
  let oneT : TangentSpace 𝓘(ℝ, ℝ) t := (1 : ℝ)
  exact Prod.ext rfl <|
    (congrArg (fun L ↦ L oneT) (Manifold.mfderiv_subtype_val (I := 𝓘(ℝ, ℝ)) t)).trans
      (Manifold.tangentSpaceOpenEquiv_apply t oneT)

/-- **Nested open parameter restriction of `mfamilyVelocity`.** Restricting `P : M × ↥J₂ → N`
along `J₁ ≤ J₂` in `Opens ℝ` preserves its parameter velocity, with no regularity hypothesis. -/
@[simp]
theorem mfamilyVelocity_comp_prodMap_inclusion_right {J₁ J₂ : Opens ℝ} (hJ : J₁ ≤ J₂)
    (P : M × ↥J₂ → N) (t : J₁) (x : M) :
    mfamilyVelocity I I' (P ∘ Prod.map id (Opens.inclusion hJ)) t x =
      mfamilyVelocity I I' P (Opens.inclusion hJ t) x := by
  classical
  let P' : M × ℝ → N := fun q ↦
    if h : q.2 ∈ J₂ then P (q.1, ⟨q.2, h⟩) else P (q.1, Opens.inclusion hJ t)
  have h₂ : P' ∘ Prod.map id (Subtype.val : J₂ → ℝ) = P :=
    funext fun q ↦ dite_eq_left q.2.property
  have h₁ : P' ∘ Prod.map id (Subtype.val : J₁ → ℝ) = P ∘ Prod.map id (Opens.inclusion hJ) :=
    funext fun q ↦ dite_eq_left (hJ q.2.property)
  rw [← h₁, mfamilyVelocity_comp_prodMap_subtype_val_right, ← h₂,
    mfamilyVelocity_comp_prodMap_subtype_val_right]

/-- **Open parameter restriction.** Restricting `P : M × ℝ → N` to `J : Opens ℝ` preserves
`mfamilyContraction` at `t : J`, with no regularity hypothesis. -/
@[simp]
theorem mfamilyContraction_comp_prodMap_subtype_val (J : Opens ℝ) (P : M × ℝ → N) (t : J)
    (ω : RoughForm I' N F (k + 1)) :
    mfamilyContraction I I' (P ∘ Prod.map id (Subtype.val : J → ℝ)) t ω =
      mfamilyContraction I I' P (t : ℝ) ω :=
  funext fun x ↦ mcontractionAlongMap_congr_field_at ω
    (mfamilyVelocity_comp_prodMap_subtype_val_right J P t x)

/-- **Nested open parameter restriction.** Restricting `P : M × ↥J₂ → N` along `J₁ ≤ J₂` in
`Opens ℝ` preserves `mfamilyContraction`, with no regularity hypothesis. -/
@[simp]
theorem mfamilyContraction_comp_prodMap_inclusion {J₁ J₂ : Opens ℝ} (hJ : J₁ ≤ J₂)
    (P : M × ↥J₂ → N) (t : J₁) (ω : RoughForm I' N F (k + 1)) :
    mfamilyContraction I I' (P ∘ Prod.map id (Opens.inclusion hJ)) t ω =
      mfamilyContraction I I' P (Opens.inclusion hJ t) ω :=
  funext fun x ↦ mcontractionAlongMap_congr_field_at ω
    (mfamilyVelocity_comp_prodMap_inclusion_right hJ P t x)

/-! ### Joint smoothness with extra parameters -/

section Smooth

variable [IsManifold I 1 M] [IsManifold I' 1 N]

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
  have hcod := e_cod.continuousLinearMapAt_apply_of_mem (R := ℝ) hr_cod
    (mfamilyVelocity I I' (fun p ↦ P (r.1, p)) r.2.2 r.2.1)
  have hdom := e_dom.continuousLinearMapAt_apply_of_mem (R := ℝ) hr_dom (v_sec r)
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.coe_comp, Function.comp_apply, g, f, mfamilyVelocity_def] at hcod hdom ⊢
  rw [← hcod, ← hdom, e_dom.symmL_continuousLinearMapAt hr_dom]

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

private theorem contMDiff_tangentBundle_mk_one {m : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ)).tangent m
      (fun t : ℝ ↦ (TotalSpace.mk' ℝ t ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) t) :
        TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
  contMDiff_tangentBundle_mk_modelSpace contMDiff_id contMDiff_const

private theorem contMDiff_tangentBundle_mk_one_opens {m : WithTop ℕ∞} (J : Opens ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ)).tangent m
      (fun t : J ↦ (TotalSpace.mk' ℝ t ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) t) :
        TangentBundle 𝓘(ℝ, ℝ) J)) := fun t ↦
  (Manifold.contMDiffAt_tangentBundle_opens_iff (I := 𝓘(ℝ, ℝ)) (n := m) (U := J)
    (g := id) (V := fun _ : J ↦ (1 : ℝ)) (q := t)).2
    (contMDiff_tangentBundle_mk_modelSpace (contMDiff_subtypeVal (I := 𝓘(ℝ, ℝ)) (U := J))
      contMDiff_const t)

/-- **Joint `C^m` smoothness of `mfamilyVelocity` over `ℝ`.** If `P : L × (M × ℝ) → N` is `C^n` at
`(q₀, (x₀, t₀))` with `m + 1 ≤ n`, then `(q, (x, t)) ↦ (P (q, (x, t)), V_{q, t} x)` is `C^m` into
`TN` at `(q₀, (x₀, t₀))`. -/
theorem _root_.ContMDiffAt.mfamilyVelocity [IsManifold I'' 1 L] {m n : WithTop ℕ∞}
    {P : L × (M × ℝ) → N} {q₀ : L} {x₀ : M} {t₀ : ℝ}
    (hP : ContMDiffAt (I''.prod (I.prod 𝓘(ℝ, ℝ))) I' n P (q₀, (x₀, t₀))) (hmn : m + 1 ≤ n) :
    ContMDiffAt (I''.prod (I.prod 𝓘(ℝ, ℝ))) I'.tangent m
      (fun r : L × (M × ℝ) ↦ TotalSpace.mk' E' (P r)
        (TauCeti.mfamilyVelocity I I' (fun p ↦ P (r.1, p)) r.2.2 r.2.1)) (q₀, (x₀, t₀)) :=
  contMDiffAt_mfamilyVelocity_of_one contMDiff_tangentBundle_mk_one hP hmn

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
  contMDiffAt_mfamilyContraction_of_one contMDiff_tangentBundle_mk_one hω hP hmn

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
  toFun φ := ⟨TauCeti.mfamilyContraction I I' P t φ.val, mem_smoothBundleForms.mpr
    ((isSmoothBundleForm_def ∞ _).mpr
      (φ.isSmoothForm.mfamilyContraction (by simpa using hP)).contMDiff)⟩
  map_add' φ η := Subtype.ext (TauCeti.mfamilyContraction_add P t φ.val η.val)
  map_smul' c φ := Subtype.ext (TauCeti.mfamilyContraction_smul P t c φ.val)

/-- The underlying rough form of `SmoothForm.mfamilyContraction` is
`TauCeti.mfamilyContraction`. -/
@[simp]
theorem coe_mfamilyContraction (P : M × ℝ → N) (t : ℝ) (hP : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' ∞ P)
    (φ : SmoothForm I' N F (k + 1)) :
    (mfamilyContraction P t hP φ).val =
      TauCeti.mfamilyContraction I I' P t φ.val := (rfl)

/-- Evaluation of `SmoothForm.mfamilyContraction` on tangent vectors. Simplification also obtains
this from `coe_mfamilyContraction` and `TauCeti.mfamilyContraction_apply`. -/
theorem mfamilyContraction_apply (P : M × ℝ → N) (t : ℝ) (hP : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' ∞ P)
    (φ : SmoothForm I' N F (k + 1)) (x : M) (v : Fin k → TangentSpace I x) :
    (mfamilyContraction P t hP φ).val x v =
      φ.val (P (x, t)) (Matrix.vecCons (TauCeti.mfamilyVelocity I I' P t x)
        fun i ↦ mfderiv I I' (fun y ↦ P (y, t)) x (v i)) :=
  TauCeti.mfamilyContraction_apply P t φ.val x v

/-- **Bundled contraction along a smooth moving map over `J : Opens ℝ`** at time `t : J`. -/
def mfamilyContractionOpens {J : Opens ℝ} (P : M × ↥J → N) (t : J)
    (hP : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' ∞ P) :
    SmoothForm I' N F (k + 1) →ₗ[ℝ] SmoothForm I M F k where
  toFun φ := ⟨TauCeti.mfamilyContraction I I' P t φ.val, mem_smoothBundleForms.mpr
    ((isSmoothBundleForm_def ∞ _).mpr
      (φ.isSmoothForm.mfamilyContraction_opens (by simpa using hP)).contMDiff)⟩
  map_add' φ η := Subtype.ext (TauCeti.mfamilyContraction_add P t φ.val η.val)
  map_smul' c φ := Subtype.ext (TauCeti.mfamilyContraction_smul P t c φ.val)

/-- The underlying rough form of `SmoothForm.mfamilyContractionOpens` is
`TauCeti.mfamilyContraction`. -/
@[simp]
theorem coe_mfamilyContractionOpens {J : Opens ℝ} (P : M × ↥J → N) (t : J)
    (hP : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' ∞ P) (φ : SmoothForm I' N F (k + 1)) :
    (mfamilyContractionOpens P t hP φ).val =
      TauCeti.mfamilyContraction I I' P t φ.val := (rfl)

/-- Evaluation of `SmoothForm.mfamilyContractionOpens` on tangent vectors. Simplification also
obtains this from `coe_mfamilyContractionOpens` and `TauCeti.mfamilyContraction_apply`. -/
theorem mfamilyContractionOpens_apply {J : Opens ℝ} (P : M × ↥J → N) (t : J)
    (hP : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I' ∞ P) (φ : SmoothForm I' N F (k + 1)) (x : M)
    (v : Fin k → TangentSpace I x) :
    (mfamilyContractionOpens P t hP φ).val x v =
      φ.val (P (x, t)) (Matrix.vecCons (TauCeti.mfamilyVelocity I I' P t x)
        fun i ↦ mfderiv I I' (fun y ↦ P (y, t)) x (v i)) :=
  TauCeti.mfamilyContraction_apply P t φ.val x v

end SmoothForm

end Smooth

end TauCeti
