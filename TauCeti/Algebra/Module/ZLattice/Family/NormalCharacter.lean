/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.MultipleFiber
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic
import all TauCeti.Analysis.Complex.RootsOfUnity.Manifold
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Level
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Map
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# The normal character of a cyclic multiple fibre

Let a cyclic group act freely on a family of tori over a disc, lifting the base rotations.
At a lift `x` in the central torus, the differential of the family projection gives a
coordinate on the normal space to the multiple fibre at `[x]`. In this coordinate the
change of lift from `x` to `g • x` acts by multiplication by `g`.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, A. Van de Ven, *Compact Complex Surfaces*, second
  edition, Chapter V, section *Logarithmic transformations*.
-/

public section

open Function MulAction Manifold
open scoped Manifold ContDiff

namespace TauCeti

noncomputable section

variable {m : ℕ} [NeZero m] {r : ℝ} {Λ E : Type*} [AddCommGroup Λ]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (P : rootsOfUnityBall m r → Λ →ₗ[ℤ] E)
  [∀ z, DiscreteTopology (LinearMap.range (P z))] [∀ z, IsZLattice ℝ (LinearMap.range (P z))]
  (hinj : ∀ z, Injective (P z))
  {n : ℕ∞ω} (hP : ∀ l, ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) n fun z ↦ P z l)

section CentralTorus

variable {u₀ : rootsOfUnityBall m r} (hn : 1 ≤ n)

private def centralTorusEmbedding :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    SmoothEmbedding 𝓘(ℂ, E) (𝓘(ℂ).prod 𝓘(ℂ, E)) n
      (AddAction.orbitRel.Quotient (LinearMap.range (P u₀)) E)
      (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)) :=
  letI := periodAddAction P
  letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  SmoothEmbedding.ofIsSmoothEmbedding _ (isSmoothEmbedding_torusFamilyFiberMap P hinj hP hn u₀)

private def centralTorusNormalCoord (x : AddAction.orbitRel.Quotient (LinearMap.range (P u₀)) E) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    (centralTorusEmbedding P hinj hP (u₀ := u₀) hn).NormalSpace x
      (ne_of_gt (zero_lt_one.trans_le hn)) ≃L[ℂ] ℂ := by
  letI := periodAddAction P
  letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  let i := centralTorusEmbedding P hinj hP (u₀ := u₀) hn
  have hn₀ : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hp := isSubmersionOfComplement_torusFamilyProjection P hinj hP
  have hs : IsRegularPoint (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ)
      (torusFamilyProjection P) (i x) :=
    isRegularPoint_iff.mpr ((hp.isSubmersionAt (i x)).surjective_mfderiv hn₀)
  have hi : ⇑i = torusFamilyFiberMap P u₀ := by
    simp only [i, centralTorusEmbedding, SmoothEmbedding.coe_ofIsSmoothEmbedding]
  refine (i.normalSpaceEquivOfSurjective x hn₀ hs ?_).toContinuousLinearEquiv
  rw [SmoothEmbedding.tangentRange, hi]
  exact range_mfderiv_torusFamilyFiberMap P hinj hP hn u₀ x

private theorem centralTorusNormalCoord_normalClass
    (x : AddAction.orbitRel.Quotient (LinearMap.range (P u₀)) E) (w : ℂ × E) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    centralTorusNormalCoord P hinj hP hn x
      ((centralTorusEmbedding P hinj hP hn).normalClass x (ne_of_gt (zero_lt_one.trans_le hn)) w) =
      mfderiv (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ)
        (((↑) : rootsOfUnityBall m r → ℂ) ∘ torusFamilyProjection P)
        (torusFamilyFiberMap P u₀ x) w := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  rw [centralTorusNormalCoord]
  dsimp only
  refine (SmoothEmbedding.normalSpaceEquivOfSurjective_normalClass
    (centralTorusEmbedding P hinj hP hn) x _ _ _ w).trans ?_
  rw [centralTorusEmbedding, SmoothEmbedding.ofIsSmoothEmbedding_apply]
  exact (Manifold.mfderiv_subtype_val_comp_apply (I := 𝓘(ℂ)) (J := 𝓘(ℂ).prod 𝓘(ℂ, E))
    (U := rootsOfUnityBall.opens m r) (f := torusFamilyProjection P) w).symm

end CentralTorus

variable (R : rootsOfUnity m ℂ → rootsOfUnityBall m r → E →+ E)
  (ρ : Representation ℤ (rootsOfUnity m ℂ) Λ)
  (hequiv : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (l : Λ),
    P (g • z) (ρ g l) = R g z (P z l))
  (b : rootsOfUnity m ℂ → rootsOfUnityBall m r →
    letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))
  (hb : ∀ (g : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    torusFamilyProjection P (b g z) = g • z)
  (hone : ∀ (z : rootsOfUnityBall m r) (v : E), R 1 z v = v)
  (hmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r) (v : E),
    R (g * h) z v = R g (h • z) (R h z v))
  (hbmul : ∀ (g h : rootsOfUnity m ℂ) (z : rootsOfUnityBall m r),
    b (g * h) z = torusFamilyAffineMap R P ρ hequiv b hb g (b h z))
  (hR : ∀ g : rootsOfUnity m ℂ, ContMDiff (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ, E) n
    fun p : rootsOfUnityBall m r × E ↦ R g p.1 p.2)
  (hbc : letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    ∀ g, ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, E)) n (b g))
  (hfree : letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    IsCancelSMul (rootsOfUnity m ℂ) (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))
  {u₀ : rootsOfUnityBall m r} (hu₀ : (u₀ : ℂ) = 0) (hn : 1 ≤ n)

include hR hbc hn in
private theorem mfderiv_torusFamilyProjection_smul (g : rootsOfUnity m ℂ)
    (x : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))
    (w : ℂ × E) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    mfderiv (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ)
        (((↑) : rootsOfUnityBall m r → ℂ) ∘ torusFamilyProjection P) (g • x)
        (mfderiv (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) (g • ·) x w) =
      ((g : ℂˣ) : ℂ) •
        (mfderiv (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ)
          (((↑) : rootsOfUnityBall m r → ℂ) ∘ torusFamilyProjection P) x w) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let _ := contMDiffConstSMul_torusFamilyAffineMulAction
    P hinj hP R ρ hequiv b hb hone hmul hbmul hR hbc
  have hn₀ := ne_of_gt (zero_lt_one.trans_le hn)
  let p := ((↑) : rootsOfUnityBall m r → ℂ) ∘ torusFamilyProjection P
  have hp := rootsOfUnityBall.contMDiff_val.comp (contMDiff_torusFamilyProjection P hinj hP)
  let L := ((g : ℂˣ) : ℂ) • ContinuousLinearMap.id ℂ ℂ
  have hcomp : p ∘ (g • ·) = L ∘ p := by
    ext y
    simp only [p, L, Function.comp_apply, torusFamilyAffineMulAction_smul,
      torusFamilyProjection_affineMap, SubMulAction.val_smul, smul_apply,
      ContinuousLinearMap.id_apply]
    rfl
  have hg : MDifferentiableAt (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) (g • ·) x :=
    (contMDiff_const_smul (n := n) g).mdifferentiableAt hn₀
  have h := congrArg (fun f ↦ (mfderiv (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ) f x) w) hcomp
  rw [mfderiv_comp x (hp.mdifferentiableAt hn₀) hg,
    mfderiv_comp x L.hasFDerivAt.hasMFDerivAt.mdifferentiableAt (hp.mdifferentiableAt hn₀),
    L.hasFDerivAt.hasMFDerivAt.mfderiv] at h
  exact h

private def centralTorusNormalQuotientEquiv
    (x : AddAction.orbitRel.Quotient (LinearMap.range (P u₀)) E) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) P hinj R ρ hequiv b hb hone hmul hbmul
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbmul
      (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g)
    letI := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbmul
      (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g) (fun l ↦ (hP l).continuous)
      (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
    (centralTorusEmbedding P hinj hP hn).NormalSpace x (ne_of_gt (zero_lt_one.trans_le hn)) ≃L[ℂ]
      (torusFamilyMultipleFiberEmbedding P hinj hP R ρ hequiv b hb hone hmul hbmul hR hbc hfree
        hu₀ hn).NormalSpace (Quotient.mk _ x) (ne_of_gt (zero_lt_one.trans_le hn)) := by
  letI := periodAddAction P
  letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) P hinj R ρ hequiv b hb hone hmul hbmul
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
  letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbmul
      (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g)
  letI := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbmul
      (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g) (fun l ↦ (hP l).continuous)
      (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
  have hn₀ : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  have hX := isLocalDiffeomorph_torusFamilyAffineQuotient_mk
    P hinj hP R ρ hequiv b hb hone hmul hbmul hR hbc hfree
  have hT := isLocalDiffeomorph_torusFamilyFiberQuotient_mk
    P hinj hP R ρ hequiv b hb hone hmul hbmul hR hbc hfree
    (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g)
  exact (centralTorusEmbedding P hinj hP hn).normalSpaceEquiv
    (torusFamilyMultipleFiberEmbedding P hinj hP R ρ hequiv b hb hone hmul hbmul hR hbc hfree
      hu₀ hn) hn₀ hn₀
    (hX.isInvertible_mfderiv hn₀ _) (hT.isInvertible_mfderiv hn₀ x).surjective
    (Filter.Eventually.of_forall fun y ↦ by
      simpa only [Function.comp_apply, centralTorusEmbedding,
        SmoothEmbedding.ofIsSmoothEmbedding_apply]
        using (torusFamilyMultipleFiberEmbedding_mk P hinj hP R ρ hequiv b hb hone hmul hbmul
          hR hbc hfree hu₀ hn y).symm)

/-- A lift to the central torus gives a complex-linear coordinate on the normal space to the
reduced multiple fibre. It reads an ambient vector by lifting through the differential of the
orbit map and projecting to the disc direction. -/
def torusFamilyMultipleFiberNormalCoord
    (x : AddAction.orbitRel.Quotient (LinearMap.range (P u₀)) E) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) P hinj R ρ hequiv b hb hone hmul hbmul
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbmul
      (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g)
    letI := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbmul
      (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g) (fun l ↦ (hP l).continuous)
      (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
    (torusFamilyMultipleFiberEmbedding P hinj hP R ρ hequiv b hb hone hmul hbmul hR hbc hfree
        hu₀ hn).NormalSpace (Quotient.mk _ x) (ne_of_gt (zero_lt_one.trans_le hn)) ≃L[ℂ] ℂ :=
  letI := periodAddAction P
  letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) P hinj R ρ hequiv b hb hone hmul hbmul
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
  letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbmul
      (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g)
  letI := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbmul
      (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g) (fun l ↦ (hP l).continuous)
      (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
  (centralTorusNormalQuotientEquiv P hinj hP R ρ hequiv b hb hone hmul hbmul hR hbc hfree hu₀ hn
    x).symm.trans (centralTorusNormalCoord P hinj hP hn x)

/-- A normal class represented by the image of an upstairs ambient vector has normal coordinate
equal to the derivative of the base coordinate on that vector. -/
@[simp]
theorem torusFamilyMultipleFiberNormalCoord_symm_mfderiv
    (x : AddAction.orbitRel.Quotient (LinearMap.range (P u₀)) E) (w : ℂ × E) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) P hinj R ρ hequiv b hb hone hmul hbmul
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbmul
      (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g)
    letI := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbmul
      (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g) (fun l ↦ (hP l).continuous)
      (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
    (torusFamilyMultipleFiberNormalCoord P hinj hP R ρ hequiv b hb hone hmul hbmul hR hbc hfree
      hu₀ hn x).symm
      (mfderiv (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ)
        (fun y ↦ (↑(torusFamilyProjection P y) : ℂ))
        (torusFamilyFiberMap P u₀ x) w) =
      (torusFamilyMultipleFiberEmbedding P hinj hP R ρ hequiv b hb hone hmul hbmul hR hbc hfree
        hu₀ hn).normalClass (Quotient.mk _ x) (ne_of_gt (zero_lt_one.trans_le hn))
        (mfderiv (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E))
          (Quotient.mk (orbitRel (rootsOfUnity m ℂ)
            (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E))))
          (torusFamilyFiberMap P u₀ x) w) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let _ := torusFamilyAffineQuotientChartedSpace (H := ℂ) P hinj R ρ hequiv b hb hone hmul hbmul
    (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
  let _ := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbmul
    (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g)
  let _ := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbmul
    (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g) (fun l ↦ (hP l).continuous)
    (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
  let e := centralTorusNormalQuotientEquiv P hinj hP R ρ hequiv b hb hone hmul hbmul
    hR hbc hfree hu₀ hn x
  let i := centralTorusEmbedding P hinj hP (u₀ := u₀) hn
  let j := torusFamilyMultipleFiberEmbedding P hinj hP R ρ hequiv b hb hone hmul hbmul
    hR hbc hfree hu₀ hn
  let q := Quotient.mk
    (orbitRel (rootsOfUnity m ℂ) (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))
  have hv : e (i.normalClass x (ne_of_gt (zero_lt_one.trans_le hn)) w) =
      j.normalClass (Quotient.mk _ x) (ne_of_gt (zero_lt_one.trans_le hn))
        (mfderiv (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) q (torusFamilyFiberMap P u₀ x) w) := by
    dsimp only [e, i]
    rw [centralTorusNormalQuotientEquiv]
    dsimp only
    refine (SmoothEmbedding.normalSpaceEquiv_normalClass _ _ _ _ _ _ _ w).trans ?_
    have hi : centralTorusEmbedding P hinj hP (u₀ := u₀) hn x = torusFamilyFiberMap P u₀ x := by
      rw [centralTorusEmbedding, SmoothEmbedding.ofIsSmoothEmbedding_apply]
    exact congrArg (fun z ↦ j.normalClass (Quotient.mk _ x) (ne_of_gt (zero_lt_one.trans_le hn))
      (mfderiv (𝓘(ℂ).prod 𝓘(ℂ, E)) (𝓘(ℂ).prod 𝓘(ℂ, E)) q z w)) hi
  let c := centralTorusNormalCoord P hinj hP hn x
  have hc := centralTorusNormalCoord_normalClass P hinj hP hn x w
  have hcoord : torusFamilyMultipleFiberNormalCoord P hinj hP R ρ hequiv b hb hone hmul hbmul
      hR hbc hfree hu₀ hn x = e.symm.trans c := (rfl)
  apply (e.symm.trans c).injective
  calc
    _ = _ := by
      rw [hcoord]
      exact (e.symm.trans c).apply_symm_apply _
    _ = c (i.normalClass x (ne_of_gt (zero_lt_one.trans_le hn)) w) := hc.symm
    _ = (e.symm.trans c) (e (i.normalClass x (ne_of_gt (zero_lt_one.trans_le hn)) w)) :=
      (congrArg c (e.symm_apply_apply _)).symm
    _ = _ := congrArg (e.symm.trans c) hv

private theorem torusFamilyMultipleFiberNormalCoord_symm_smul_mfderiv
    (g : rootsOfUnity m ℂ) (x : AddAction.orbitRel.Quotient (LinearMap.range (P u₀)) E)
    (w : ℂ × E) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) P hinj R ρ hequiv b hb hone hmul hbmul
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbmul
      (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g)
    letI := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbmul
      (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g) (fun l ↦ (hP l).continuous)
      (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
    let i := torusFamilyMultipleFiberEmbedding P hinj hP R ρ hequiv b hb hone hmul hbmul
      hR hbc hfree hu₀ hn
    let v := mfderiv (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ)
      (fun y ↦ (↑(torusFamilyProjection P y) : ℂ))
      (torusFamilyFiberMap P u₀ x) w
    Bundle.TotalSpace.mk' (E := fun z ↦ i.NormalSpace z (ne_of_gt (zero_lt_one.trans_le hn)))
      ℂ (Quotient.mk _ (g • x))
      ((torusFamilyMultipleFiberNormalCoord P hinj hP R ρ hequiv b hb hone hmul hbmul
        hR hbc hfree hu₀ hn (g • x)).symm (((g : ℂˣ) : ℂ) • v)) =
      Bundle.TotalSpace.mk' ℂ (Quotient.mk _ x)
        ((torusFamilyMultipleFiberNormalCoord P hinj hP R ρ hequiv b hb hone hmul hbmul
          hR hbc hfree hu₀ hn x).symm v) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let _ := torusFamilyAffineQuotientChartedSpace (H := ℂ) P hinj R ρ hequiv b hb hone hmul hbmul
    (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
  let _ := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbmul
    (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g)
  let _ := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbmul
    (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g) (fun l ↦ (hP l).continuous)
    (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
  let _ := contMDiffConstSMul_torusFamilyAffineMulAction
    P hinj hP R ρ hequiv b hb hone hmul hbmul hR hbc
  let i := torusFamilyMultipleFiberEmbedding P hinj hP R ρ hequiv b hb hone hmul hbmul
    hR hbc hfree hu₀ hn
  let p := fun y ↦ (↑(torusFamilyProjection P y) : ℂ)
  let q := Quotient.mk
    (orbitRel (rootsOfUnity m ℂ) (AddAction.orbitRel.Quotient Λ (rootsOfUnityBall m r × E)))
  let y := torusFamilyFiberMap P u₀ x
  have hn₀ := ne_of_gt (zero_lt_one.trans_le hn)
  have hgy : torusFamilyFiberMap P u₀ (g • x) = g • y :=
    torusFamilyFiberMap_smul R hone hmul P ρ hequiv b hb hbmul
      (fun h ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ h) g x
  let A := 𝓘(ℂ).prod 𝓘(ℂ, E)
  let w' := mfderiv A A (g • ·) y w
  have hchar : mfderiv A 𝓘(ℂ) p (torusFamilyFiberMap P u₀ (g • x)) w' =
      ((g : ℂˣ) : ℂ) • mfderiv A 𝓘(ℂ) p y w := by
    rw [hgy]
    exact (mfderiv_torusFamilyProjection_smul P hinj hP R ρ hequiv b hb hone hmul hbmul
      hR hbc hn g y w)
  have hleft := (congrArg
    (torusFamilyMultipleFiberNormalCoord P hinj hP R ρ hequiv b hb hone hmul hbmul
      hR hbc hfree hu₀ hn (g • x)).symm hchar).symm.trans
    (torusFamilyMultipleFiberNormalCoord_symm_mfderiv P hinj hP R ρ hequiv b hb hone hmul hbmul
      hR hbc hfree hu₀ hn (g • x) w')
  have hdq := (isLocalDiffeomorph_torusFamilyAffineQuotient_mk
    P hinj hP R ρ hequiv b hb hone hmul hbmul hR hbc hfree).contMDiff.mdifferentiable hn₀
  have hd := mfderiv_quotientMk_smul_apply (I := A) hn₀ (g := g) (x := y) (hdq (g • y)) w
  dsimp only [p, y] at hleft ⊢
  rw [hleft, torusFamilyMultipleFiberNormalCoord_symm_mfderiv]
  have hqt : (Quotient.mk (orbitRel (rootsOfUnity m ℂ) _) (g • x)) = Quotient.mk _ x :=
    MulAction.orbitRel.Quotient.quotient_smul_eq
  let normalClass z (t : ℂ × E) :=
    Bundle.TotalSpace.mk' (E := fun a ↦ i.NormalSpace a hn₀) ℂ z (i.normalClass z hn₀ t)
  have hdiff := (congrArg (fun z ↦ mfderiv A A q z w') hgy).trans hd
  exact (congrArg (normalClass (Quotient.mk _ (g • x))) hdiff).trans
    (congrArg (fun z ↦ normalClass z (mfderiv A A q y w)) hqt)

/-- **Normal character of the multiple fibre.** If a point of the central torus is replaced by its
translate under `g`, its normal coordinate must be multiplied by `g` to represent the same normal
vector downstairs. This is the defining representation of the roots of unity on the complex line
with the diagonal action convention `(x, v) ↦ (g • x, g * v)`. -/
theorem torusFamilyMultipleFiberNormalCoord_symm_smul
    (g : rootsOfUnity m ℂ) (x : AddAction.orbitRel.Quotient (LinearMap.range (P u₀)) E) (v : ℂ) :
    letI := periodAddAction P
    letI := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
    letI := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
    letI := torusFamilyAffineQuotientChartedSpace (H := ℂ) P hinj R ρ hequiv b hb hone hmul hbmul
      (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
    letI := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbmul
      (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g)
    letI := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbmul
      (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g) (fun l ↦ (hP l).continuous)
      (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
    let i := torusFamilyMultipleFiberEmbedding P hinj hP R ρ hequiv b hb hone hmul hbmul
      hR hbc hfree hu₀ hn
    Bundle.TotalSpace.mk' (E := fun z ↦ i.NormalSpace z (ne_of_gt (zero_lt_one.trans_le hn)))
      ℂ (Quotient.mk _ (g • x))
      ((torusFamilyMultipleFiberNormalCoord P hinj hP R ρ hequiv b hb hone hmul hbmul
        hR hbc hfree hu₀ hn (g • x)).symm (((g : ℂˣ) : ℂ) • v)) =
      Bundle.TotalSpace.mk' ℂ (Quotient.mk _ x)
        ((torusFamilyMultipleFiberNormalCoord P hinj hP R ρ hequiv b hb hone hmul hbmul
          hR hbc hfree hu₀ hn x).symm v) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := ℂ) P (fun l ↦ (hP l).continuous) hinj
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hequiv b hb hbmul
  let _ := torusFamilyAffineQuotientChartedSpace (H := ℂ) P hinj R ρ hequiv b hb hone hmul hbmul
    (fun l ↦ (hP l).continuous) (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
  let _ := torusFamilyFiberMulAction R hone hmul P ρ hequiv b hb hbmul
    (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g)
  let _ := torusFamilyFiberQuotientChartedSpace P R ρ hequiv b hb hone hmul hbmul
    (fun g ↦ smul_rootsOfUnityBall_of_coe_eq_zero hu₀ g) (fun l ↦ (hP l).continuous)
    (fun g ↦ (hR g).continuous) (fun g ↦ (hbc g).continuous) hfree
  let y := torusFamilyFiberMap P u₀ x
  have hn₀ := ne_of_gt (zero_lt_one.trans_le hn)
  have hp := isSubmersionOfComplement_torusFamilyProjection P hinj hP
  obtain ⟨w, hw⟩ := (hp.isSubmersionAt y).surjective_mfderiv hn₀ v
  have hwp : mfderiv (𝓘(ℂ).prod 𝓘(ℂ, E)) 𝓘(ℂ)
      (((↑) : rootsOfUnityBall m r → ℂ) ∘ torusFamilyProjection P) y w = v := by
    rw [← hw]
    exact Manifold.mfderiv_subtype_val_comp_apply (U := rootsOfUnityBall.opens m r) w
  clear hw
  subst v
  exact torusFamilyMultipleFiberNormalCoord_symm_smul_mfderiv
    P hinj hP R ρ hequiv b hb hone hmul hbmul hR hbc hfree hu₀ hn g x w

end

end TauCeti
