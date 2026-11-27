/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Section
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SecondCovariantDerivative
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# Second covariant derivatives of bilinear forms

The native Hom connection on covariant bilinear forms agrees with
`CovariantDerivative.derivBilinearTensor`. Its second covariant derivative is therefore the
ordinary second derivative of a covariant two-tensor, with two derivative directions first.
The evaluation formulas keep track of the correction in each tensor slot. These formulas
are used to differentiate the contracted Bianchi identities and the metric connection velocity.

## References

* P. Topping, *Lectures on the Ricci Flow*, CUP (2006), §§2.3–2.5.
* [Poincaré Conjecture](https://github.com/frenzymath/PoincareConjecture).
* [Lean evaluation submissions](https://github.com/frenzymath/lean-eval-submissions).
-/

public noncomputable section

open Bundle FiberBundle
open scoped ContDiff Manifold RealInnerProductSpace

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  (cov : CovariantDerivative I F V)

/-- The connection induced on covariant bilinear forms by the native iterated Hom connection.
The value bundle has its ordinary flat connection. -/
def bilinear : CovariantDerivative I (F →L[ℝ] F →L[ℝ] ℝ)
    (fun x : M ↦ V x →L[ℝ] V x →L[ℝ] ℝ) :=
  cov.hom (cov.hom (trivial ℝ))

/-- The bilinear connection is the iterated Hom connection with flat scalar values. -/
theorem bilinear_def : cov.bilinear = cov.hom (cov.hom (trivial ℝ)) :=
  (rfl)

/-- On a differentiable bilinear-form section, the induced Hom derivative agrees with the
bilinear-tensor derivative. The derivative direction is first on the left and last on the right.
-/
theorem bilinear_apply
    {b : Π x : M, V x →L[ℝ] V x →L[ℝ] ℝ} {x : M}
    (hb : MDiffAt (fun y ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
      (E := fun z : M ↦ V z →L[ℝ] V z →L[ℝ] ℝ) y (b y)) x)
    (a : TangentSpace I x) (u v : V x) :
    cov.bilinear b x a u v = cov.derivBilinearTensor b x u v a := by
  let U := extend F u
  let W := extend F v
  have hU : MDiffAt (T% U) x := mdifferentiableAt_extend I F u
  have hW : MDiffAt (T% W) x := mdifferentiableAt_extend I F v
  have hpair ⦃σ τ : Π y : M, V y⦄ (hσ : MDiffAt (T% σ) x)
      (hτ : MDiffAt (T% τ) x) : MDiffAt (fun y ↦ b y (σ y) (τ y)) x :=
    hb.clm_bundle_apply₂_trivial hσ hτ
  have h := hom_hom_apply cov cov (trivial ℝ) hb hU hW a
  rw [trivial_apply] at h
  rw [cov.derivBilinearTensor_apply_eq_extend hpair]
  simpa only [bilinear, U, W, extend_apply_self] using h

section Smooth

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
  [ContMDiffVectorBundle ∞ F V I] [ContMDiffCovariantDerivative cov ∞]

/-- The connection on covariant bilinear forms induced by a smooth connection is smooth. -/
instance : ContMDiffCovariantDerivative cov.bilinear ∞ := by
  rw [bilinear_def]
  infer_instance

variable (covT : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- Two covariant derivatives preserve symmetry in the bilinear-form inputs; the two
derivative directions are kept fixed. -/
theorem secondCovariantDerivative_bilinear_apply_comm
    {b : Π x : M, V x →L[ℝ] V x →L[ℝ] ℝ}
    (hs : ∀ y (u v : V y), b y u v = b y v u)
    (x : M) (a c : TangentSpace I x) (u v : V x) :
    cov.bilinear.secondCovariantDerivative covT b x a c u v =
      cov.bilinear.secondCovariantDerivative covT b x a c v u := by
  by_cases hb : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun z : M ↦ V z →L[ℝ] V z →L[ℝ] ℝ) y (b y))
  · obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E ∞ c
    have hD := contMDiff_apply cov.bilinear hY (by simpa using hb)
    have hsym (y : M) (u v : V y) :
        cov.bilinear b y (Y y) u v = cov.bilinear b y (Y y) v u := by
      rw [cov.bilinear_apply (hb.mdifferentiableAt (by simp)),
        cov.bilinear_apply (hb.mdifferentiableAt (by simp)),
        cov.derivBilinearTensor_apply_comm hs]
    rw [secondCovariantDerivative_apply _ _ hb x hY]
    simp only [sub_apply]
    rw [cov.bilinear_apply (hD.mdifferentiableAt (by simp)),
      cov.bilinear_apply (hD.mdifferentiableAt (by simp)),
      cov.bilinear_apply (hb.mdifferentiableAt (by simp)),
      cov.bilinear_apply (hb.mdifferentiableAt (by simp)),
      cov.derivBilinearTensor_apply_comm hsym, cov.derivBilinearTensor_apply_comm hs]
  · rw [cov.bilinear.secondCovariantDerivative_of_not_contMDiff covT hb]
    -- The nonsmooth branch is the zero bilinear map in both evaluation orders.
    rfl

/-- On smooth fields, the second derivative of a bilinear form is the derivative of its
first evaluation minus a correction for each of the three varying inputs. -/
theorem secondCovariantDerivative_bilinear_apply
    {b : Π x : M, V x →L[ℝ] V x →L[ℝ] ℝ}
    (hb : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun z : M ↦ V z →L[ℝ] V z →L[ℝ] ℝ) y (b y)))
    {Y : Π y : M, TangentSpace I y} {σ τ : Π y : M, V y}
    (hY : CMDiff ∞ (T% Y)) (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ))
    (x : M) (a : TangentSpace I x) :
    cov.bilinear.secondCovariantDerivative covT b x a (Y x) (σ x) (τ x) =
      mvfderiv I (fun y ↦ cov.bilinear b y (Y y) (σ y) (τ y)) x a -
        cov.bilinear b x (Y x) (cov σ x a) (τ x) -
        cov.bilinear b x (Y x) (σ x) (cov τ x a) -
        cov.bilinear b x (covT Y x a) (σ x) (τ x) := by
  have hD := contMDiff_apply cov.bilinear hY (by simpa using hb)
  have hpair ⦃α β : Π y : M, V y⦄ (hα : MDiffAt (T% α) x)
      (hβ : MDiffAt (T% β) x) :
      MDiffAt (fun y ↦ cov.bilinear b y (Y y) (α y) (β y)) x :=
    (hD.mdifferentiableAt (by simp)).clm_bundle_apply₂_trivial hα hβ
  rw [secondCovariantDerivative_apply _ _ hb x hY]
  simp only [sub_apply]
  rw [cov.bilinear_apply (hD.mdifferentiableAt (by simp)),
    derivBilinearTensor_apply _ hpair (hσ.mdifferentiableAt (by simp))
      (hτ.mdifferentiableAt (by simp))]

end Smooth

end CovariantDerivative

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- Contracting the last input of the covariant derivative of a bilinear form with a vector
field gives another bilinear-form section. -/
def bilinearDerivativeApplyRight
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (B : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (W : Π y : M, TangentSpace I y) (y : M) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
  letI := (VectorBundle.continuousLinearEquivAt ℝ E (TangentSpace I) y).isNormableSpace
  (ContinuousLinearMap.compL ℝ (TangentSpace I y) (TangentSpace I y →L[ℝ] ℝ) ℝ
    (ContinuousLinearMap.apply ℝ ℝ (W y))) ∘L cov.bilinear B y

omit [T2Space M] in
/-- The right contraction evaluates the last input of the bilinear derivative. -/
@[simp]
theorem bilinearDerivativeApplyRight_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (B : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (W : Π y : M, TangentSpace I y) (y : M) (u v : TangentSpace I y) :
    cov.bilinearDerivativeApplyRight B W y u v = cov.bilinear B y u v (W y) :=
  (rfl)

/-- The right contraction of the derivative of a smooth bilinear form pairs differentiable
sections to a differentiable scalar function. -/
theorem mdifferentiableAt_bilinearDerivativeApplyRight
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    {B : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) y (B y)))
    {W : Π y : M, TangentSpace I y} (hW : CMDiff ∞ (T% W))
    {x : M} {σ τ : Π y : M, TangentSpace I y}
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    MDiffAt (fun y ↦ cov.bilinearDerivativeApplyRight B W y (σ y) (τ y)) x := by
  have hK := cov.bilinear.contMDiff_covariantDerivative (n := ∞) (by simpa using hB)
  simpa using ((hK.mdifferentiableAt (by simp)).clm_bundle_apply hσ).clm_bundle_apply₂_trivial hτ
    (hW.mdifferentiableAt (by simp))

/-- Differentiating the contraction of the first derivative of a bilinear form with a
smooth vector field gives its second derivative and the derivative of that field. -/
theorem derivBilinearTensor_bilinearDerivativeApplyRight_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    {B : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) y (B y)))
    {W : Π y : M, TangentSpace I y} (hW : CMDiff ∞ (T% W))
    (x : M) (a u v : TangentSpace I x) :
    cov.derivBilinearTensor (cov.bilinearDerivativeApplyRight B W) x u v a =
      cov.bilinear.secondCovariantDerivative cov B x a u v (W x) +
        cov.bilinear B x u v (cov W x a) := by
  have hpair ⦃σ τ : Π y : M, TangentSpace I y⦄ (hσ : MDiffAt (T% σ) x)
      (hτ : MDiffAt (T% τ) x) :
      MDiffAt (fun y ↦ cov.bilinearDerivativeApplyRight B W y (σ y) (τ y)) x :=
    cov.mdifferentiableAt_bilinearDerivativeApplyRight hB hW hσ hτ
  obtain ⟨U, hU, rfl⟩ := exists_contMDiff_section_eq I E ∞ u
  obtain ⟨V, hV, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  rw [cov.derivBilinearTensor_apply hpair (hU.mdifferentiableAt (by simp))
    (hV.mdifferentiableAt (by simp))]
  rw [cov.secondCovariantDerivative_bilinear_apply cov hB hU hV hW]
  simp only [bilinearDerivativeApplyRight_apply]
  ring

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
  [ContMDiffCovariantDerivative cov ∞]

/-- Differentiating the three metric-dual terms of a connection velocity differentiates
the corresponding two-tensor once more, with all connection corrections retained. -/
theorem IsMetricCompatible.inner_hom_hom_eq_secondCovariantDerivative_bilinear
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov)
    {B : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ}
    (hB : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) y (B y)))
    {C : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TangentSpace I y}
    (hC : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] TangentSpace I z)
        y (C y)))
    (hpair : ∀ y u v w, inner ℝ (C y u v) w =
      -cov.bilinear B y v u w - cov.bilinear B y u v w + cov.bilinear B y w u v)
    (x : M) (a u v w : TangentSpace I x) :
    inner ℝ (cov.hom (cov.hom cov) C x a u v) w =
      -cov.bilinear.secondCovariantDerivative cov B x a v u w -
        cov.bilinear.secondCovariantDerivative cov B x a u v w +
          cov.bilinear.secondCovariantDerivative cov B x a w u v := by
  obtain ⟨U, hU, rfl⟩ := exists_contMDiff_section_eq I E ∞ u
  obtain ⟨V, hV, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  obtain ⟨W, hW, rfl⟩ := exists_contMDiff_section_eq I E ∞ w
  have hK := cov.bilinear.contMDiff_covariantDerivative (n := ∞) (by simpa using hB)
  have hp {X Y Z : Π y : M, TangentSpace I y} (hX : CMDiff ∞ (T% X))
      (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
      MDiffAt (fun y ↦ cov.bilinear B y (X y) (Y y) (Z y)) x :=
    ((hK.mdifferentiableAt (by simp)).clm_bundle_apply
      (hX.mdifferentiableAt (by simp))).clm_bundle_apply₂_trivial
        (hY.mdifferentiableAt (by simp)) (hZ.mdifferentiableAt (by simp))
  have hf : (fun y ↦ inner ℝ (C y (U y) (V y)) (W y)) = fun y ↦
      -cov.bilinear B y (V y) (U y) (W y) -
        cov.bilinear B y (U y) (V y) (W y) + cov.bilinear B y (W y) (U y) (V y) :=
    funext fun y ↦ hpair y _ _ _
  have hd := hcov.mvfderiv_inner_eq (x := x) (extend E a)
    (((hC.mdifferentiableAt (by simp)).clm_bundle_apply
      (hU.mdifferentiableAt (by simp))).clm_bundle_apply (hV.mdifferentiableAt (by simp)))
    (hW.mdifferentiableAt (by simp))
  simp only [extend_apply_self] at hd
  rw [hf] at hd
  have hsum := mvfderiv_add ((hp hV hU hW).neg.sub (hp hU hV hW)) (hp hW hU hV)
  have hsub := mvfderiv_sub (hp hV hU hW).neg (hp hU hV hW)
  have hneg := mvfderiv_neg (I := I) (𝕜 := ℝ)
    (g := fun y ↦ cov.bilinear B y (V y) (U y) (W y)) (x := x)
  have hdiff := congrArg (fun L ↦ L a) hsum
  simp only [hsub, hneg, add_apply, sub_apply, neg_apply] at hdiff
  -- The scalar derivative laws use pointwise function operations. Normalize their
  -- eta-expanded input to the same scalar function used in the metric product rule.
  change mvfderiv I (fun y ↦ -cov.bilinear B y (V y) (U y) (W y) -
    cov.bilinear B y (U y) (V y) (W y) + cov.bilinear B y (W y) (U y) (V y)) x a = _
    at hdiff
  have hh := congrArg (fun z ↦ inner ℝ z (W x))
    (hom_hom_apply cov cov cov (hC.mdifferentiableAt (by simp))
      (hU.mdifferentiableAt (by simp)) (hV.mdifferentiableAt (by simp)) a)
  simp only [inner_sub_left] at hh
  rw [hpair, hpair] at hh
  rw [hpair] at hd
  have h₁ := cov.secondCovariantDerivative_bilinear_apply cov hB hV hU hW x a
  have h₂ := cov.secondCovariantDerivative_bilinear_apply cov hB hU hV hW x a
  have h₃ := cov.secondCovariantDerivative_bilinear_apply cov hB hW hU hV x a
  linarith only [hd, hh, h₁, h₂, h₃, hdiff]

end CovariantDerivative
