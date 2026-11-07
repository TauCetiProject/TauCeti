/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.WarpedProd
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Vanishing mixed curvature components of a warped product

For the metric `g_M + f² g_N`, curvature with two horizontal inputs annihilates vertical
vectors, and curvature with two vertical inputs annihilates horizontal vectors. These
identities remove the off-diagonal components when taking the Ricci contraction of the
warped-product curvature tensor. They do not assert that mixed sectional curvature vanishes.

## References

* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press (1983), Chapter 7, Proposition 42.
-/

public section

noncomputable section

open Bundle CovariantDerivative FiberBundle Manifold VectorField
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
  [RiemannianBundle (fun p : M × N ↦ TangentSpace (I.prod J) p)]
  [IsContMDiffRiemannianBundle (I.prod J) ∞ (E × F)
    (fun p : M × N ↦ TangentSpace (I.prod J) p)]
  {f : M → ℝ}

/- The proofs use the Levi-Civita formula on product fields. In the horizontal calculation the
second derivatives of `f` cancel by the commutator identity; in the vertical calculation the
remaining terms cancel by torsion-freeness on the fibre. -/

private theorem IsWarpedProduct.cov_horizontal_vertical (h : IsWarpedProduct I J N f)
    (hf : MDifferentiable I 𝓘(ℝ) f)
    {X : Π x : M, TangentSpace I x} {V : Π y : N, TangentSpace J y}
    (hX : MDiff (T% X)) (p : M × N) :
    leviCivitaConnection (I.prod J) (M × N) (prodVectorField (J := J) X 0) p
        (prodVectorField (I := I) 0 V p) =
      (mvfderiv I f p.1 (X p.1) / f p.1) • prodVectorField (I := I) 0 V p := by
  apply (tangentSpaceProdEquiv p).injective
  simpa only [map_smul, tangentSpaceProdEquiv_prodVectorField, Pi.zero_apply,
    Prod.fst_zero, Prod.snd_zero, ContinuousLinearMap.map_zero, sub_zero, add_zero, zero_add,
    inner_zero_right, mul_zero, zero_mul, zero_smul, smul_zero, zero_div, zero_sub,
    CovariantDerivative.zero, _root_.zero_apply, Prod.smul_mk] using
    h.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField (Y₁ := X) (Y₂ := 0)
      (hf p.1) (hX p.1) (mdifferentiableAt_zeroSection ..) (prodVectorField (I := I) 0 V p)

private theorem IsWarpedProduct.curvatureOperator_vertical_vertical_horizontal
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    {X : Π x : M, TangentSpace I x} {V W : Π y : N, TangentSpace J y}
    (hX : CMDiff ∞ (T% X)) (hV : CMDiff ∞ (T% V)) (hW : CMDiff ∞ (T% W))
    (p : M × N) (hp : f p.1 ≠ 0) :
    (leviCivitaConnection (I.prod J) (M × N)).curvatureOperator
      (prodVectorField (I := I) 0 V) (prodVectorField (I := I) 0 W)
      (prodVectorField (J := J) X 0) p = 0 := by
  have : IsManifold I (minSmoothness ℝ 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (minSmoothness ℝ 2) N := .of_le (n := ∞) (by simp)
  let a : M → ℝ := fun x ↦ mvfderiv I f x (X x) / f x
  have hfd := hf.mdifferentiable (by simp)
  have hXd := hX.mdifferentiable (by simp)
  have hVd := hV.mdifferentiable (by simp)
  have hWd := hW.mdifferentiable (by simp)
  have ha : MDiffAt a p.1 :=
    (((hf.contMDiff_mvfderiv_apply (m := 1) (by norm_num)).comp
      (hX.of_le (by simp))).mdifferentiableAt (by simp)).div (hfd p.1) hp
  -- The scalar coefficient depends only on the base, so its vertical derivatives vanish.
  have hmul {U : Π y : N, TangentSpace J y} (hU : MDiff (T% U))
      (v : TangentSpace (I.prod J) p) :
      leviCivitaConnection (I.prod J) (M × N)
          ((a ∘ (Prod.fst : M × N → M)) • prodVectorField (I := I) 0 U) p v =
        a p.1 • leviCivitaConnection (I.prod J) (M × N) (prodVectorField (I := I) 0 U) p v +
          mvfderiv I a p.1 (tangentSpaceProdEquiv p v).1 • prodVectorField (I := I) 0 U p := by
    rw [(leviCivitaConnection (I.prod J) (M × N)).isCovariantDerivativeOnUniv.leibniz
      (σ := prodVectorField (I := I) 0 U) (g := a ∘ Prod.fst)
      (mdifferentiableAt_prodVectorField (I := I) (J := J)
        (mdifferentiableAt_zeroSection ..) (hU p.2))
      (ha.comp p mdifferentiableAt_fst)]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, Function.comp_apply,
      mvfderiv_comp_fst_apply, tangentSpaceProdEquiv_apply]
  have hfirst (U : Π y : N, TangentSpace J y) :
      (fun q ↦ leviCivitaConnection (I.prod J) (M × N) (prodVectorField (J := J) X 0) q
        (prodVectorField (I := I) 0 U q)) =
          (a ∘ (Prod.fst : M × N → M)) • prodVectorField (I := I) 0 U :=
    funext fun q ↦ h.cov_horizontal_vertical hfd hXd q
  -- The horizontal terms cancel by symmetry of the fibre metric, the vertical ones by torsion.
  have ht := (leviCivitaConnection J N).torsion_eq_zero_iff.mp
    (torsion_leviCivitaConnection_eq_zero J) (hVd p.2) (hWd p.2)
  apply (tangentSpaceProdEquiv p).injective
  rw [curvatureOperator_apply, hfirst W, hfirst V, hmul hWd, hmul hVd,
    mlieBracket_prodVectorField (I := I) (J := J) (X₁ := 0) (Y₁ := 0)
      (mdifferentiableAt_zeroSection ..)
      (mdifferentiableAt_zeroSection ..) (hVd p.2) (hWd p.2)]
  simp only [map_sub, map_add, map_smul]
  rw [h.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField (Y₁ := 0) (Y₂ := W) (hfd p.1)
      (mdifferentiableAt_zeroSection ..) (hWd p.2),
    h.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField (Y₁ := 0) (Y₂ := V) (hfd p.1)
      (mdifferentiableAt_zeroSection ..) (hVd p.2),
    h.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField (Y₁ := X) (Y₂ := 0)
      (hfd p.1) (hXd p.1) (mdifferentiableAt_zeroSection ..)]
  simp only [tangentSpaceProdEquiv_prodVectorField, Pi.zero_apply,
    zero_smul, smul_zero, zero_div, inner_zero_right, mul_zero, zero_add, add_zero, sub_zero,
    zero_sub,
    CovariantDerivative.zero, _root_.zero_apply, real_inner_comm, ← ht,
    map_zero, Prod.smul_mk, Prod.mk_sub_mk, smul_sub, mlieBracket_self]
  simp only [a, sub_self, Prod.mk_zero_zero]

private theorem IsWarpedProduct.curvatureOperator_horizontal_horizontal_vertical
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    {X Y : Π x : M, TangentSpace I x} {V : Π y : N, TangentSpace J y}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hV : CMDiff ∞ (T% V))
    (p : M × N) (hp : f p.1 ≠ 0) :
    (leviCivitaConnection (I.prod J) (M × N)).curvatureOperator
      (prodVectorField X 0) (prodVectorField Y 0) (prodVectorField 0 V) p = 0 := by
  have : IsManifold I (minSmoothness ℝ 2) M := .of_le (n := ∞) (by simp)
  have : IsManifold J (minSmoothness ℝ 2) N := .of_le (n := ∞) (by simp)
  let a (U : Π x : M, TangentSpace I x) : M → ℝ := fun x ↦ mvfderiv I f x (U x) / f x
  have hfd := hf.mdifferentiable (by simp)
  have hVd := hV.mdifferentiable (by simp)
  -- Differentiating the first covariant derivative contributes the derivative of `df(U)/f`.
  have hfirst (U : Π x : M, TangentSpace I x) (q : M × N) :
      leviCivitaConnection (I.prod J) (M × N) (prodVectorField (I := I) 0 V) q
          (prodVectorField (J := J) U 0 q) =
        a U q.1 • prodVectorField (I := I) 0 V q := by
    apply (tangentSpaceProdEquiv q).injective
    simpa only [map_smul, tangentSpaceProdEquiv_prodVectorField, Pi.zero_apply,
      map_zero, zero_smul, smul_zero, inner_zero_left, mul_zero, sub_zero, zero_div,
      zero_add, add_zero, Prod.smul_mk, CovariantDerivative.zero, _root_.zero_apply, a] using
      h.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField (Y₁ := 0) (Y₂ := V)
        (hfd q.1) (mdifferentiableAt_zeroSection ..) (hVd q.2) (prodVectorField U 0 q)
  have hdU {U : Π x : M, TangentSpace I x} (hU : CMDiff ∞ (T% U)) :
      MDiffAt (fun x ↦ mvfderiv I f x (U x)) p.1 :=
    ((hf.contMDiff_mvfderiv_apply (m := 1) (by norm_num)).comp
      (hU.of_le (by simp))).mdifferentiableAt (by simp)
  have hsecond {U Z : Π x : M, TangentSpace I x} (hU : CMDiff ∞ (T% U)) :
      leviCivitaConnection (I.prod J) (M × N)
          ((a U ∘ (Prod.fst : M × N → M)) • prodVectorField (I := I) 0 V) p
          (prodVectorField (J := J) Z 0 p) =
        (a U p.1 * a Z p.1 + mvfderiv I (a U) p.1 (Z p.1)) •
          prodVectorField (I := I) 0 V p := by
    rw [(leviCivitaConnection (I.prod J) (M × N)).isCovariantDerivativeOnUniv.leibniz
      (σ := prodVectorField (I := I) 0 V) (g := a U ∘ Prod.fst)
      (mdifferentiableAt_prodVectorField (mdifferentiableAt_zeroSection ..) (hVd p.2))
      (((hdU hU).div (hfd p.1) hp).comp p mdifferentiableAt_fst)]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      mvfderiv_comp_fst_apply, prodVectorField_fst, Function.comp_apply, hfirst,
      smul_smul, add_smul]
  have hc := mvfderiv_div_commutator_eq_zero a (fun _ ↦ rfl) (hf p.1)
    (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp)) (hdU hX) (hdU hY) hp
  have hfirst' (U : Π x : M, TangentSpace I x) :
      (fun q ↦ leviCivitaConnection (I.prod J) (M × N) (prodVectorField (I := I) 0 V) q
        (prodVectorField (J := J) U 0 q)) =
          (a U ∘ (Prod.fst : M × N → M)) • prodVectorField (I := I) 0 V := by
    funext q
    simpa only [Pi.smul_apply', Function.comp_apply] using hfirst U q
  rw [curvatureOperator_apply, hfirst' Y, hfirst' X, hsecond hY, hsecond hX,
    mlieBracket_prodVectorField (I := I) (J := J) (X₂ := 0) (Y₂ := 0)
      (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp))
      (mdifferentiableAt_zeroSection ..) (mdifferentiableAt_zeroSection ..),
    mlieBracket_self, hfirst, ← sub_smul, ← sub_smul, hc, zero_smul]

variable [T2Space M] [T2Space N]

/-- Curvature with two vertical inputs annihilates horizontal vectors in a warped product.
The C² warping function need only be nonzero at the point of evaluation. -/
theorem IsWarpedProduct.curvatureTensor_vertical_vertical_horizontal
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) 2 f) (p : M × N)
    (hp : f p.1 ≠ 0) (u v : TangentSpace J p.2) (w : TangentSpace I p.1) :
    (leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p (0, u) (0, v) (w, 0) = 0 := by
  -- Work through the continuous linear tangent identification, then normalize the statement.
  suffices hc : (leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p
      ((tangentSpaceProdEquiv p).symm (0, u)) ((tangentSpaceProdEquiv p).symm (0, v))
      ((tangentSpaceProdEquiv p).symm (w, 0)) = 0 by
    simp only [tangentSpaceProdEquiv_symm_apply] at hc
    convert hc using 1
    rfl
  obtain ⟨X, hX, hXp⟩ := exists_contMDiff_section_eq I E ∞ (V := TangentSpace I) w
  obtain ⟨V, hV, hVp⟩ := exists_contMDiff_section_eq J F ∞ (V := TangentSpace J) u
  obtain ⟨W, hW, hWp⟩ := exists_contMDiff_section_eq J F ∞ (V := TangentSpace J) v
  have hvalue : (tangentSpaceProdEquiv p).symm (w, 0) = prodVectorField (J := J) X 0 p ∧
      (tangentSpaceProdEquiv p).symm (0, u) = prodVectorField (I := I) 0 V p ∧
      (tangentSpaceProdEquiv p).symm (0, v) = prodVectorField (I := I) 0 W p := by
    refine ⟨?_, ?_, ?_⟩ <;> apply (tangentSpaceProdEquiv p).injective <;>
      simp only [ContinuousLinearEquiv.apply_symm_apply, tangentSpaceProdEquiv_prodVectorField,
        Pi.zero_apply, hXp, hVp, hWp]
  have hzI : CMDiff ∞ (T% (0 : Π x : M, TangentSpace I x)) := contMDiff_zeroSection _ _
  have hzJ : CMDiff ∞ (T% (0 : Π y : N, TangentSpace J y)) := contMDiff_zeroSection _ _
  rw [hvalue.1, hvalue.2.1, hvalue.2.2,
    curvatureTensor_apply _ p (contMDiff_prodVectorField hzI hV)
      (contMDiff_prodVectorField hzI hW) (contMDiff_prodVectorField hX hzJ)]
  exact h.curvatureOperator_vertical_vertical_horizontal hf hX hV hW p hp

/-- Curvature with two horizontal inputs annihilates vertical vectors in a warped product.
The C² warping function need only be nonzero at the point of evaluation. -/
theorem IsWarpedProduct.curvatureTensor_horizontal_horizontal_vertical
    (h : IsWarpedProduct I J N f) (hf : ContMDiff I 𝓘(ℝ) 2 f) (p : M × N)
    (hp : f p.1 ≠ 0) (u v : TangentSpace I p.1) (w : TangentSpace J p.2) :
    (leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p (u, 0) (v, 0) (0, w) = 0 := by
  -- Work through the continuous linear tangent identification, then normalize the statement.
  suffices hc : (leviCivitaConnection (I.prod J) (M × N)).curvatureTensor p
      ((tangentSpaceProdEquiv p).symm (u, 0)) ((tangentSpaceProdEquiv p).symm (v, 0))
      ((tangentSpaceProdEquiv p).symm (0, w)) = 0 by
    simp only [tangentSpaceProdEquiv_symm_apply] at hc
    convert hc using 1
    rfl
  obtain ⟨X, hX, hXp⟩ := exists_contMDiff_section_eq I E ∞ (V := TangentSpace I) u
  obtain ⟨Y, hY, hYp⟩ := exists_contMDiff_section_eq I E ∞ (V := TangentSpace I) v
  obtain ⟨V, hV, hVp⟩ := exists_contMDiff_section_eq J F ∞ (V := TangentSpace J) w
  have hvalue : (tangentSpaceProdEquiv p).symm (u, 0) = prodVectorField (J := J) X 0 p ∧
      (tangentSpaceProdEquiv p).symm (v, 0) = prodVectorField (J := J) Y 0 p ∧
      (tangentSpaceProdEquiv p).symm (0, w) = prodVectorField (I := I) 0 V p := by
    refine ⟨?_, ?_, ?_⟩ <;> apply (tangentSpaceProdEquiv p).injective <;>
      simp only [ContinuousLinearEquiv.apply_symm_apply, tangentSpaceProdEquiv_prodVectorField,
        Pi.zero_apply, hXp, hYp, hVp]
  have hzI : CMDiff ∞ (T% (0 : Π x : M, TangentSpace I x)) := contMDiff_zeroSection _ _
  have hzJ : CMDiff ∞ (T% (0 : Π y : N, TangentSpace J y)) := contMDiff_zeroSection _ _
  rw [hvalue.1, hvalue.2.1, hvalue.2.2,
    curvatureTensor_apply _ p (contMDiff_prodVectorField hX hzJ)
      (contMDiff_prodVectorField hY hzJ) (contMDiff_prodVectorField hzI hV)]
  exact h.curvatureOperator_horizontal_horizontal_vertical hf hX hY hV p hp

end TauCeti.Manifold
