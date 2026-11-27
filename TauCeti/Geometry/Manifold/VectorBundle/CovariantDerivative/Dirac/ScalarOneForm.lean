/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Dirac.Energy
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.ScalarOneForm

/-!
# The split Dirac energy identity for a connection twisted by a scalar one-form

Let `V` be a Riemannian vector bundle over a Riemannian manifold `M` without boundary, with a
metric connection `∇` and a smooth Clifford multiplication `c` by skew-adjoint endomorphisms,
satisfying the Clifford relation `c(v) c(v) = -‖v‖²` and compatible with `∇` and the
Levi-Civita connection. Let `J` be a smooth parallel field of skew-adjoint endomorphisms of `V`
commuting with Clifford multiplication, such as multiplication by `i` on a complex Clifford
module, and let `θ` be a smooth real one-form. This file applies the energy identity of a Dirac
operator split along a parallel unit field
(`CovariantDerivative.IsMetricCompatible.integral_norm_diracOperator_sq_eq_sum_curvatureOperator`)
to the twisted connection `∇' = ∇ + θ ⊗ J` (`CovariantDerivative.smulRightOneForm`).

The twisted connection satisfies the hypotheses of that identity: it is smooth and metric
(`CovariantDerivative.contMDiffCovariantDerivative_addOneForm_smulRightOneForm`,
`CovariantDerivative.IsMetricCompatible.addOneForm_smulRightOneForm`) and it stays compatible with
Clifford multiplication (`CovariantDerivative.addOneForm_smulRightOneForm_clifford_apply`). Its
curvature is `R' = R + dθ ⊗ J`
(`CovariantDerivative.curvatureOperator_addOneForm_smulRightOneForm`).
So, for a parallel unit field `T` and smooth fields `e₁, …, eₖ` completing it to an orthonormal
frame and commuting with it, the curvature term of the identity splits as

`c(T) ∑ᵢ c(eᵢ) R'(T, eᵢ) σ = c(T) ∑ᵢ c(eᵢ) R(T, eᵢ) σ + c(T) c(a) J σ`,  `a = ∑ᵢ dθ(T, eᵢ) eᵢ`

(`CovariantDerivative.sum_clifford_curvatureOperator_addOneForm_smulRightOneForm`). The vector `a`
is the metric dual of the contraction `ι_T dθ`, since `dθ(T, T) = 0`. When the curvature of `∇`
vanishes along `T`, as on a Riemannian product `S¹ × Y` with `T = ∂ₛ`, only the twisting term
remains, and for every compactly supported smooth section `σ`

`∫ ‖D' σ‖² dV = ∫ ‖∇'_T σ‖² dV + ∫ ‖B'_T σ‖² dV + ∫ ⟪σ, c(T) c(a) J σ⟫ dV`

(`IsMetricCompatible.integral_norm_diracOperator_addOneForm_smulRightOneForm_sq_eq`, in the
namespace `CovariantDerivative`), where `D'` and `B'_T` are the Dirac and transverse Dirac
operators of `∇'`.

For the spinor bundle of a `Spinᶜ` structure on `S¹ × Y`, changing the connection on the
determinant line by an imaginary one-form `i b` changes the spin connection by the twist with
`θ = b / 2` and `J` the multiplication by `i`. The twisting term is then
`(i / 2) c(T) c(ι_T db) σ`, the mixed half-determinant curvature term of the square of the product
Dirac operator, whose pairing with a solution of the unperturbed Seiberg–Witten equations is
computed in `TauCeti.SeibergWitten.re_inner_I_div_two_smul_ι_mul_ι_twoVectorContraction`.

## Main results

* `CovariantDerivative.addOneForm_smulRightOneForm_clifford_apply`: the twisted connection is
  compatible with Clifford multiplication and the Levi-Civita connection when `∇` is and `J`
  commutes with Clifford multiplication.
* `CovariantDerivative.sum_clifford_curvatureOperator_addOneForm_smulRightOneForm`: the frame sum
  `∑ᵢ c(eᵢ) R'(T, eᵢ) σ` of the twisted connection.
* `IsMetricCompatible.integral_norm_diracOperator_addOneForm_smulRightOneForm_sq_eq_sum`, in the
  namespace `CovariantDerivative`: the energy identity of the twisted Dirac operator.
* `IsMetricCompatible.integral_norm_diracOperator_addOneForm_smulRightOneForm_sq_eq`, in the
  namespace `CovariantDerivative`: its form when the curvature of `∇` vanishes along `T`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Appendix D (the spinor bundles of a `Spinᶜ` structure and their connections).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §5.2.
* S. Baldridge, *Seiberg–Witten invariants, orbifolds, and circle actions*, Trans. Amer. Math.
  Soc. 355 (2003), 1669–1697, Theorem 15.
-/

public section

noncomputable section

open MeasureTheory Bundle TauCeti TauCeti.Manifold
open scoped ContDiff Manifold RealInnerProductSpace

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {c : Π x : M, TangentSpace I x →L[ℝ] V x →L[ℝ] V x} {T : Π x : M, TangentSpace I x}
  {J : Π x : M, V x →L[ℝ] V x}

section Clifford

variable [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

omit [VectorBundle ℝ F V] in
/-- **The twisted connection is compatible with Clifford multiplication.** If `∇` satisfies
`∇_u (c(Y) τ) = c(∇^LC_u Y) τ + c(Y) ∇_u τ` and every `J x` commutes with Clifford
multiplication, then so does `∇ + θ ⊗ J`, at every point where the identity for `∇` holds. -/
theorem addOneForm_smulRightOneForm_clifford_apply (θ : SmoothForm I M ℝ 1)
    {cov : _root_.CovariantDerivative I F V}
    (hJc : ∀ x (v : TangentSpace I x) (s : V x), J x (c x v s) = c x v (J x s))
    {Y : Π y : M, TangentSpace I y} {τ : Π y : M, V y} {x : M} {u : TangentSpace I x}
    (hcomp : cov (fun y ↦ c y (Y y) (τ y)) x u =
      c x (leviCivitaConnection I M Y x u) (τ x) + c x (Y x) (cov τ x u)) :
    cov.addOneForm (smulRightOneForm θ J) (fun y ↦ c y (Y y) (τ y)) x u =
      c x (leviCivitaConnection I M Y x u) (τ x) +
        c x (Y x) (cov.addOneForm (smulRightOneForm θ J) τ x u) := by
  simp only [addOneForm_smulRightOneForm_apply, hcomp, hJc, map_add, map_smul]
  abel

end Clifford

omit [FiniteDimensional ℝ E] in
/-- **The frame sum of the curvature of the twisted connection.** If `J` is parallel for `∇`
along `σ` at `x`, then for vector fields `T` and `e₁, …, eₖ`

`∑ᵢ c(eᵢ) R^(∇ + θ ⊗ J)(T, eᵢ) σ = ∑ᵢ c(eᵢ) R^∇(T, eᵢ) σ + c(∑ᵢ dθ(T, eᵢ) eᵢ) J σ`

at `x`. The other hypotheses are the differentiability at `x` of the vector fields and of the
sections `∇_T σ`, `∇_{eᵢ} σ` and `J σ`. -/
theorem sum_clifford_curvatureOperator_addOneForm_smulRightOneForm [IsManifold I 1 M]
    (θ : SmoothForm I M ℝ 1) (cov : _root_.CovariantDerivative I F V) {ι : Type*} [Fintype ι]
    {e : ι → Π y : M, TangentSpace I y} {σ : Π y : M, V y} {x : M}
    (hT : MDiffAt (T% T) x) (he : ∀ i, MDiffAt (T% (e i)) x)
    (hTσ : MDiffAt (T% (fun y ↦ cov σ y (T y))) x)
    (heσ : ∀ i, MDiffAt (T% (fun y ↦ cov σ y (e i y))) x)
    (hJσ : MDiffAt (T% (fun y ↦ J y (σ y))) x)
    (hJ : ∀ v, cov (fun y ↦ J y (σ y)) x v = J x (cov σ x v)) :
    ∑ i, c x (e i x) (curvatureOperator (cov.addOneForm (smulRightOneForm θ J)) T (e i) σ x) =
      ∑ i, c x (e i x) (curvatureOperator cov T (e i) σ x) +
        c x (∑ i, mextDeriv θ.val x ![T x, e i x] • e i x) (J x (σ x)) := by
  simp only [curvatureOperator_addOneForm_smulRightOneForm cov θ J hT (he _) hTσ (heσ _) hJσ hJ,
    map_add, map_smul, Finset.sum_add_distrib, map_sum, sum_apply, smul_apply]

variable [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V]
  [T2Space M] [I.Boundaryless] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {cov : _root_.CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]

local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

namespace IsMetricCompatible

/-- **The energy identity of a Dirac operator twisted by a scalar one-form.** Let `∇` be a smooth
metric connection compatible with a smooth Clifford multiplication `c` by skew-adjoint
endomorphisms satisfying the Clifford relation `c(v) c(v) = -⟪v, v⟫`, and with the Levi-Civita
connection. Let `J` be a smooth field of skew-adjoint endomorphisms commuting with Clifford
multiplication and parallel for `∇`, let `θ` be a smooth real one-form, and let `T` be a parallel
unit vector field completed to an orthonormal frame by smooth fields `e₁, …, eₖ` commuting with
`T`. Then the Dirac operator `D'` and the transverse Dirac operator `B'_T` of `∇' = ∇ + θ ⊗ J`
satisfy, for every compactly supported smooth section `σ`,

`∫ ‖D' σ‖² dV = ∫ ‖∇'_T σ‖² dV + ∫ ‖B'_T σ‖² dV`
`    + ∫ ⟪σ, c(T) (∑ᵢ c(eᵢ) R^∇(T, eᵢ) σ + c(∑ᵢ dθ(T, eᵢ) eᵢ) J σ)⟫ dV`

for the Riemannian volume. -/
theorem integral_norm_diracOperator_addOneForm_smulRightOneForm_sq_eq_sum (θ : SmoothForm I M ℝ 1)
    (hc : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F →L[ℝ] F)
        (E := fun y ↦ TangentSpace I y →L[ℝ] V y →L[ℝ] V y) x (c x)))
    (hskew : ∀ x (v : TangentSpace I x) (s t : V x), ⟪c x v s, t⟫ = -⟪s, c x v t⟫)
    (hcomp : ∀ (Y : Π y : M, TangentSpace I y) (τ : Π y : M, V y), CMDiff ∞ (T% Y) →
      CMDiff ∞ (T% τ) → ∀ x u, cov (fun y ↦ c y (Y y) (τ y)) x u =
        c x (leviCivitaConnection I M Y x u) (τ x) + c x (Y x) (cov τ x u))
    (hcov : cov.IsMetricCompatible)
    (hcl : ∀ x (v : TangentSpace I x) (s : V x), c x v (c x v s) = -⟪v, v⟫ • s)
    (hJs : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun y ↦ V y →L[ℝ] V y) x (J x)))
    (hJskew : ∀ x (s t : V x), ⟪J x s, t⟫ = -⟪s, J x t⟫)
    (hJc : ∀ x (v : TangentSpace I x) (s : V x), J x (c x v s) = c x v (J x s))
    (hJpar : ∀ τ : Π y : M, V y, CMDiff ∞ (T% τ) →
      ∀ x v, cov (fun y ↦ J y (τ y)) x v = J x (cov τ x v))
    (hTs : CMDiff ∞ (T% T)) (hTpar : ∀ x, leviCivitaConnection I M T x = 0)
    (hT1 : ∀ x, ‖T x‖ = 1) {ι : Type*} [Fintype ι] (e : ι → Π y : M, TangentSpace I y)
    (he : ∀ i, CMDiff ∞ (T% (e i)))
    (hframe : ∀ x, ∃ b : OrthonormalBasis (Option ι) ℝ (TangentSpace I x),
      b none = T x ∧ ∀ i, b (some i) = e i x)
    (hbr : ∀ i x, VectorField.mlieBracket I T (e i) x = 0)
    {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) (hσc : IsCompact (closure {x | σ x ≠ 0})) :
    ∫ x, ‖(cov.addOneForm (smulRightOneForm θ J)).diracOperator c σ x‖ ^ 2
        ∂riemannianVolume I M =
      ∫ x, ‖cov.addOneForm (smulRightOneForm θ J) σ x (T x)‖ ^ 2 ∂riemannianVolume I M +
        ∫ x, ‖(cov.addOneForm (smulRightOneForm θ J)).transverseDiracOperator c T σ x‖ ^ 2
          ∂riemannianVolume I M +
          ∫ x, ⟪σ x, c x (T x) (∑ i, c x (e i x) (curvatureOperator cov T (e i) σ x) +
            c x (∑ i, mextDeriv θ.val x ![T x, e i x] • e i x) (J x (σ x)))⟫
              ∂riemannianVolume I M := by
  have := contMDiffCovariantDerivative_addOneForm_smulRightOneForm
    (inferInstance : ContMDiffCovariantDerivative cov ∞) θ hJs
  rw [integral_norm_diracOperator_sq_eq_sum_curvatureOperator hc hskew
    (fun Y τ hY hτ x u ↦ addOneForm_smulRightOneForm_clifford_apply θ hJc (hcomp Y τ hY hτ x u))
    (hcov.addOneForm_smulRightOneForm θ hJskew) hcl hTs hTpar hT1 e he hframe hbr hσ hσc]
  congr 1
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  have hσ' : CMDiff (∞ + 1) (T% σ) := by simpa using hσ
  dsimp only
  rw [sum_clifford_curvatureOperator_addOneForm_smulRightOneForm θ cov
    (hTs.mdifferentiableAt (by simp)) (fun i ↦ (he i).mdifferentiableAt (by simp))
    ((cov.contMDiff_apply hTs hσ').mdifferentiableAt (by simp))
    (fun i ↦ (cov.contMDiff_apply (he i) hσ').mdifferentiableAt (by simp))
    ((hJs.clm_bundle_apply hσ).mdifferentiableAt (by simp)) (hJpar σ hσ x)]

/-- **The energy identity of a Dirac operator twisted by a scalar one-form, on a product.** Under
the hypotheses of
`IsMetricCompatible.integral_norm_diracOperator_addOneForm_smulRightOneForm_sq_eq_sum`, if the
curvature `R^∇(T, eᵢ) σ` of `∇` vanishes, as on a Riemannian product `S¹ × Y` with `T = ∂ₛ`, then

`∫ ‖D' σ‖² dV = ∫ ‖∇'_T σ‖² dV + ∫ ‖B'_T σ‖² dV + ∫ ⟪σ, c(T) c(∑ᵢ dθ(T, eᵢ) eᵢ) J σ⟫ dV`

for the Dirac operator `D'` and the transverse Dirac operator `B'_T` of `∇' = ∇ + θ ⊗ J`. -/
theorem integral_norm_diracOperator_addOneForm_smulRightOneForm_sq_eq (θ : SmoothForm I M ℝ 1)
    (hc : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F →L[ℝ] F)
        (E := fun y ↦ TangentSpace I y →L[ℝ] V y →L[ℝ] V y) x (c x)))
    (hskew : ∀ x (v : TangentSpace I x) (s t : V x), ⟪c x v s, t⟫ = -⟪s, c x v t⟫)
    (hcomp : ∀ (Y : Π y : M, TangentSpace I y) (τ : Π y : M, V y), CMDiff ∞ (T% Y) →
      CMDiff ∞ (T% τ) → ∀ x u, cov (fun y ↦ c y (Y y) (τ y)) x u =
        c x (leviCivitaConnection I M Y x u) (τ x) + c x (Y x) (cov τ x u))
    (hcov : cov.IsMetricCompatible)
    (hcl : ∀ x (v : TangentSpace I x) (s : V x), c x v (c x v s) = -⟪v, v⟫ • s)
    (hJs : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun y ↦ V y →L[ℝ] V y) x (J x)))
    (hJskew : ∀ x (s t : V x), ⟪J x s, t⟫ = -⟪s, J x t⟫)
    (hJc : ∀ x (v : TangentSpace I x) (s : V x), J x (c x v s) = c x v (J x s))
    (hJpar : ∀ τ : Π y : M, V y, CMDiff ∞ (T% τ) →
      ∀ x v, cov (fun y ↦ J y (τ y)) x v = J x (cov τ x v))
    (hTs : CMDiff ∞ (T% T)) (hTpar : ∀ x, leviCivitaConnection I M T x = 0)
    (hT1 : ∀ x, ‖T x‖ = 1) {ι : Type*} [Fintype ι] (e : ι → Π y : M, TangentSpace I y)
    (he : ∀ i, CMDiff ∞ (T% (e i)))
    (hframe : ∀ x, ∃ b : OrthonormalBasis (Option ι) ℝ (TangentSpace I x),
      b none = T x ∧ ∀ i, b (some i) = e i x)
    (hbr : ∀ i x, VectorField.mlieBracket I T (e i) x = 0)
    {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) (hσc : IsCompact (closure {x | σ x ≠ 0}))
    (hR : ∀ i x, curvatureOperator cov T (e i) σ x = 0) :
    ∫ x, ‖(cov.addOneForm (smulRightOneForm θ J)).diracOperator c σ x‖ ^ 2
        ∂riemannianVolume I M =
      ∫ x, ‖cov.addOneForm (smulRightOneForm θ J) σ x (T x)‖ ^ 2 ∂riemannianVolume I M +
        ∫ x, ‖(cov.addOneForm (smulRightOneForm θ J)).transverseDiracOperator c T σ x‖ ^ 2
          ∂riemannianVolume I M +
          ∫ x, ⟪σ x, c x (T x) (c x (∑ i, mextDeriv θ.val x ![T x, e i x] • e i x)
            (J x (σ x)))⟫ ∂riemannianVolume I M := by
  rw [integral_norm_diracOperator_addOneForm_smulRightOneForm_sq_eq_sum θ hc hskew hcomp hcov hcl
    hJs hJskew hJc hJpar hTs hTpar hT1 e he hframe hbr hσ hσc]
  simp only [hR, map_zero, Finset.sum_const_zero, zero_add]

end IsMetricCompatible

end CovariantDerivative
