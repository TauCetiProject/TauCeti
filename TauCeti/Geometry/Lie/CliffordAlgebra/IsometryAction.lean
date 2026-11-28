/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Regular.Euclidean
public import TauCeti.Geometry.Manifold.Instances.Unitary
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality

/-!
# Orthogonal action on a negative Clifford algebra

The orthogonal group acts by algebra automorphisms extending its action on generators.
This action preserves the scalar-part metric. Smoothness follows by induction on Clifford elements,
using the generator formula and continuous bilinearity of Clifford multiplication.
-/

public noncomputable section

open TauCeti
open scoped Manifold ContDiff CliffordAlgebra.NegativeMetric

namespace CliffordAlgebra

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω} {m : M} (e : M → V ≃ₗᵢ[ℝ] W)

/-- A smooth family of linear isometries induces a smooth family of Clifford equivalences,
including joint evaluation on a varying Clifford element. -/
theorem contMDiffAt_equivOfIsometry_apply
    (he : ∀ v, ContMDiffAt IM 𝓘(ℝ, W) n (fun y ↦ e y v) m)
    {x : M → CliffordAlgebra (negNormSqForm V)}
    (hx : ContMDiffAt IM 𝓘(ℝ, CliffordAlgebra (negNormSqForm V)) n x m) :
    ContMDiffAt IM 𝓘(ℝ, CliffordAlgebra (negNormSqForm W)) n
      (fun y ↦ equivOfIsometry (e y).negNormSqFormIsometryEquiv (x y)) m := by
  have hfixed (a : CliffordAlgebra (negNormSqForm V)) :
      ContMDiffAt IM 𝓘(ℝ, CliffordAlgebra (negNormSqForm W)) n
        (fun y ↦ equivOfIsometry (e y).negNormSqFormIsometryEquiv a) m := by
    induction a using CliffordAlgebra.induction with
    | algebraMap r => simpa only [AlgEquiv.commutes] using contMDiffAt_const
    | ι v =>
      simp only [equivOfIsometry_ι, LinearIsometryEquiv.negNormSqFormIsometryEquiv_apply]
      exact (CliffordAlgebra.ι (negNormSqForm W)).toContinuousLinearMap.contMDiffAt.comp m (he v)
    | mul a b ha hb =>
      simp only [map_mul]
      exact ((NegativeMetric.mulCLM W).isBoundedBilinearMap.contDiff.contMDiff.contMDiffAt.comp m
        (ha.prodMk_space hb)).congr_of_eventuallyEq <|
          Filter.Eventually.of_forall fun _ ↦ (NegativeMetric.mulCLM_apply W _ _).symm
    | add a b ha hb =>
      exact (ha.add hb).congr_of_eventuallyEq <| Filter.Eventually.of_forall fun y ↦
        map_add (equivOfIsometry (e y).negNormSqFormIsometryEquiv) a b
  let f (y : M) :=
    (equivOfIsometry (e y).negNormSqFormIsometryEquiv).toLinearMap.toContinuousLinearMap
  have hf : ContMDiffAt IM 𝓘(ℝ, CliffordAlgebra (negNormSqForm V) →L[ℝ]
      CliffordAlgebra (negNormSqForm W)) n f m :=
    TauCeti.contMDiffAt_clm_apply.mpr fun a ↦ by
      simpa only [f, LinearMap.coe_toContinuousLinearMap', AlgEquiv.toLinearMap_apply] using
        hfixed a
  simpa only [f, LinearMap.coe_toContinuousLinearMap', AlgEquiv.toLinearMap_apply] using
    hf.clm_apply hx

end CliffordAlgebra

namespace Unitary

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

local notation "C" => CliffordAlgebra (negNormSqForm V)

section Algebra

variable [CompleteSpace V]

/-- The Clifford algebra automorphism extending an orthogonal transformation. -/
def cliffordAlgEquiv (g : unitary (V →L[ℝ] V)) : C ≃ₐ[ℝ] C :=
  CliffordAlgebra.equivOfIsometry (linearIsometryEquiv g).negNormSqFormIsometryEquiv

/-- The orthogonal automorphism is induced by the corresponding quadratic isometry. -/
theorem cliffordAlgEquiv_def (g : unitary (V →L[ℝ] V)) :
    cliffordAlgEquiv g =
      CliffordAlgebra.equivOfIsometry (linearIsometryEquiv g).negNormSqFormIsometryEquiv := (rfl)

@[simp]
theorem cliffordAlgEquiv_ι (g : unitary (V →L[ℝ] V)) (v : V) :
    cliffordAlgEquiv g (CliffordAlgebra.ι (negNormSqForm V) v) =
      CliffordAlgebra.ι (negNormSqForm V) (g • v) := by
  have hv : linearIsometryEquiv g v = g • v :=
    congrArg (fun f : V →L[ℝ] V ↦ f v) (coe_linearIsometryEquiv_apply g)
  simp only [cliffordAlgEquiv_def, CliffordAlgebra.equivOfIsometry_ι,
    LinearIsometryEquiv.negNormSqFormIsometryEquiv_apply, hv]

/-- The identity orthogonal transformation induces the identity Clifford automorphism. -/
@[simp]
theorem cliffordAlgEquiv_one : cliffordAlgEquiv (1 : unitary (V →L[ℝ] V)) =
    AlgEquiv.refl := by
  simp [cliffordAlgEquiv_def, LinearIsometryEquiv.one_def]

/-- Composition of the induced Clifford automorphisms corresponds to orthogonal multiplication. -/
@[simp]
theorem cliffordAlgEquiv_mul (g h : unitary (V →L[ℝ] V)) :
    (cliffordAlgEquiv h).trans (cliffordAlgEquiv g) = cliffordAlgEquiv (g * h) := by
  simp [cliffordAlgEquiv_def, LinearIsometryEquiv.mul_def]

/-- The orthogonal group acts by semiring automorphisms extending its action on generators. -/
instance instMulSemiringActionCliffordAlgebra : MulSemiringAction (unitary (V →L[ℝ] V)) C where
  smul g x := cliffordAlgEquiv g x
  smul_zero g := map_zero (cliffordAlgEquiv g)
  smul_add g := map_add (cliffordAlgEquiv g)
  smul_one g := map_one (cliffordAlgEquiv g)
  smul_mul g := map_mul (cliffordAlgEquiv g)
  one_smul x := by exact DFunLike.congr_fun cliffordAlgEquiv_one x
  mul_smul g h x := by exact DFunLike.congr_fun (cliffordAlgEquiv_mul g h).symm x

/-- A Clifford algebra action by orthogonal transformations commutes with real scalars. -/
instance instSMulCommClassCliffordAlgebra : SMulCommClass (unitary (V →L[ℝ] V)) ℝ C where
  smul_comm g r x := (cliffordAlgEquiv g).toLinearMap.map_smul r x

/-- The action on Clifford elements is the induced algebra automorphism. -/
theorem smul_clifford_eq (g : unitary (V →L[ℝ] V)) (x : C) :
    g • x = cliffordAlgEquiv g x := (rfl)

/-- The orthogonal action on a Clifford generator is the action on its generating vector. -/
@[simp]
theorem smul_clifford_ι (g : unitary (V →L[ℝ] V)) (v : V) :
    g • CliffordAlgebra.ι (negNormSqForm V) v = CliffordAlgebra.ι (negNormSqForm V) (g • v) := by
  rw [smul_clifford_eq, cliffordAlgEquiv_ι]

/-- Orthogonal transformations commute with Clifford conjugation. -/
@[simp]
theorem smul_clifford_star (g : unitary (V →L[ℝ] V)) (x : C) :
    g • star x = star (g • x) := by
  simp only [smul_clifford_eq, cliffordAlgEquiv_def, CliffordAlgebra.equivOfIsometry_star]

/-- Orthogonal transformations commute with the Clifford grade involution. -/
@[simp]
theorem smul_clifford_involute (g : unitary (V →L[ℝ] V)) (x : C) :
    g • CliffordAlgebra.involute x = CliffordAlgebra.involute (g • x) := by
  simp only [smul_clifford_eq, cliffordAlgEquiv_def, CliffordAlgebra.equivOfIsometry_involute]

end Algebra

variable [FiniteDimensional ℝ V]

/-- The orthogonal action preserves the Euclidean Clifford norm. -/
instance instIsIsometricSMulCliffordAlgebra : IsIsometricSMul (unitary (V →L[ℝ] V)) C where
  isometry_smul g := AddMonoidHomClass.isometry_of_norm (cliffordAlgEquiv g) fun x ↦ by
    simp only [CliffordAlgebra.NegativeMetric.norm_eq_regularNorm]
    exact CliffordAlgebra.regularNorm_equivOfIsometry (negNormSqForm V)
      (linearIsometryEquiv g).negNormSqFormIsometryEquiv x

private theorem contMDiff_cliffordAlgEquiv_apply (x : C) :
    ContMDiff (model (V →L[ℝ] V)) 𝓘(ℝ, C) ∞ (fun g ↦ cliffordAlgEquiv g x) := by
  simp only [cliffordAlgEquiv_def]
  intro g
  apply CliffordAlgebra.contMDiffAt_equivOfIsometry_apply (fun h ↦ linearIsometryEquiv h)
  · intro v
    have h := ((contMDiff_val (R := V →L[ℝ] V)).clm_apply
      (contMDiff_const (c := v))).contMDiffAt (x := g)
    refine h.congr_of_eventuallyEq <| Filter.Eventually.of_forall fun h ↦ ?_
    exact congrArg (fun f : V →L[ℝ] V ↦ f v) (coe_linearIsometryEquiv_apply h)
  · exact contMDiffAt_const

/-- The orthogonal action on the Euclidean Clifford algebra is smooth. -/
instance instContMDiffSMulCliffordAlgebra :
    ContMDiffSMul (model (V →L[ℝ] V)) 𝓘(ℝ, C) ∞ (unitary (V →L[ℝ] V)) C where
  contMDiff_smul := by
    let ρ : unitary (V →L[ℝ] V) → C →L[ℝ] C :=
      fun g ↦ (cliffordAlgEquiv g).toLinearMap.toContinuousLinearMap
    have hρ : ContMDiff (model (V →L[ℝ] V)) 𝓘(ℝ, C →L[ℝ] C) ∞ ρ := by
      intro g
      exact TauCeti.contMDiffAt_clm_apply.mpr fun x ↦
        (contMDiff_cliffordAlgEquiv_apply x).contMDiffAt
    refine ((hρ.comp contMDiff_fst).clm_apply contMDiff_snd).congr fun (g, x) ↦ ?_
    simp only [smul_clifford_eq, ρ, Function.comp_apply, LinearMap.coe_toContinuousLinearMap',
      AlgEquiv.toLinearMap_apply]

/-- The smooth orthogonal action is continuous in the Euclidean Clifford topology. -/
instance instContinuousSMulCliffordAlgebra : ContinuousSMul (unitary (V →L[ℝ] V)) C :=
  ⟨(contMDiff_smul (I := model (V →L[ℝ] V)) (I' := 𝓘(ℝ, C)) (n := ∞)).continuous⟩

end Unitary
