/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Dirac.DifferentialOperator
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Dirac.Split
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Dirac.Square
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# The energy identity of a Dirac operator split along a parallel unit field

Let `V` be a Riemannian vector bundle over a Riemannian manifold `M` without boundary, with a
metric connection `∇` and a smooth Clifford multiplication `c` by skew-adjoint endomorphisms,
satisfying the Clifford relation `c(v) c(v) = -‖v‖²` and compatible with `∇` and the
Levi-Civita connection. For a unit vector field `T`, the Dirac operator splits as
`D σ = c(T) ∇_T σ + B_T σ` (`CovariantDerivative.diracOperator_eq_add_transverseDiracOperator`),
where the transverse Dirac operator `B_T` differentiates only orthogonally to `T`.

This file integrates that splitting. When `T` is a Killing field of constant length, both `D`
and `c(T) ∇_T` are formally self-adjoint, hence so is their difference `B_T`
(`CovariantDerivative.IsMetricCompatible.integral_inner_transverseDiracOperator_left_eq_right`).
When `T` is moreover parallel and of unit length, as the field `∂ₛ` of a product `S¹ × Y` with
the product metric, Clifford multiplication by `T` anticommutes with `B_T`
(`CovariantDerivative.transverseDiracOperator_clifford_eq`). Integrating the cross term of
`‖c(T) ∇_T σ + B_T σ‖²` by parts in two ways then turns it into a commutator, and for every
compactly supported smooth section `σ`

`∫ ‖D σ‖² dV = ∫ ‖∇_T σ‖² dV + ∫ ‖B_T σ‖² dV + ∫ ⟪σ, c(T) (∇_T (B_T σ) - B_T (∇_T σ))⟫ dV`

for the Riemannian volume `dV`
(`CovariantDerivative.IsMetricCompatible.integral_norm_diracOperator_sq_eq`). The last term is
the integral of the curvature term of `D²`: under the frame hypotheses of
`CovariantDerivative.covariantDerivative_transverseDiracOperator_sub_eq_sum`, the commutator
`∇_T B_T - B_T ∇_T` is `∑ᵢ c(eᵢ) R(T, eᵢ)`. For a harmonic spinor, `D σ = 0`, the identity
expresses the vanishing of the sum of the three terms.

On a product `S¹ × Y` with the product metric, `T = ∂ₛ`, the spinor bundle of a `Spinᶜ`
structure and the spin connection of a unitary connection `A` on its determinant line `L`, the
curvature term `c(T) ∑ᵢ c(eᵢ) R(T, eᵢ)` is `(1 / 2) c₂(ds ∧ ι_T F_A)`, and its pairing with a
solution of the unperturbed Seiberg–Witten equations is computed in
`TauCeti.SeibergWitten.re_inner_I_div_two_smul_ι_mul_ι_twoVectorContraction`. Together they turn
the identity, for such a solution `(A, ψ)`, into Taubes's energy identity
`0 = ‖∇_T ψ‖² + ‖B_A ψ‖² + ‖ι_T F_A‖² + 2π² ⟨c₁(L)², [S¹ × Y]⟩`. That identification of the
curvature of the spin connection is not made here.

## Main results

* `CovariantDerivative.contMDiff_transverseDiracOperator`: `B_T` preserves smooth sections.
* `CovariantDerivative.IsMetricCompatible.integral_inner_transverseDiracOperator_left_eq_right`:
  `B_T` is formally self-adjoint along a Killing field of constant length.
* `CovariantDerivative.IsMetricCompatible.two_mul_integral_inner_clifford_transverseDiracOperator`:
  along a parallel unit field, the integrated cross term `2 ∫ ⟪c(T) ∇_T σ, B_T σ⟫` is the
  integral of `⟪σ, c(T) (∇_T B_T - B_T ∇_T) σ⟫`.
* `CovariantDerivative.IsMetricCompatible.integral_norm_diracOperator_sq_eq`: the integrated
  splitting of `‖D σ‖²` along a parallel unit field.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter II, §5 (Dirac operators of Clifford bundles and their formal self-adjointness).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §5.2.
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
-/

public section

noncomputable section

open MeasureTheory Bundle TauCeti TauCeti.Manifold
open scoped ContDiff Manifold RealInnerProductSpace

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {cov : _root_.CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]
  {c : Π x : M, TangentSpace I x →L[ℝ] V x →L[ℝ] V x} {T : Π x : M, TangentSpace I x}

omit [T2Space M] [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] in
variable (cov) in
/-- The transverse Dirac operator of a smooth Clifford multiplication along a smooth vector field
sends smooth sections to smooth sections. -/
theorem contMDiff_transverseDiracOperator
    (hc : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F →L[ℝ] F)
        (E := fun y ↦ TangentSpace I y →L[ℝ] V y →L[ℝ] V y) x (c x)))
    (hT : CMDiff ∞ (T% T)) {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ)) :
    CMDiff ∞ (T% (cov.transverseDiracOperator c T σ)) := by
  have h : cov.transverseDiracOperator c T σ =
      cov.diracOperator c σ - fun y ↦ c y (T y) (cov σ y (T y)) :=
    funext fun y ↦ cov.transverseDiracOperator_def c T σ y
  rw [h]
  exact (cov.contMDiff_diracOperator hc hσ).sub_section
    ((hc.clm_bundle_apply hT).clm_bundle_apply (cov.contMDiff_apply hT (by simpa using hσ)))

variable [IsContMDiffRiemannianBundle I ∞ F V]
  [I.Boundaryless] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]

local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

variable
  (hc : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F →L[ℝ] F)) ∞
    (fun x ↦ TotalSpace.mk' (E →L[ℝ] F →L[ℝ] F)
      (E := fun y ↦ TangentSpace I y →L[ℝ] V y →L[ℝ] V y) x (c x)))
  (hskew : ∀ x (v : TangentSpace I x) (s t : V x), ⟪c x v s, t⟫ = -⟪s, c x v t⟫)
  (hcomp : ∀ (Y : Π y : M, TangentSpace I y) (τ : Π y : M, V y), CMDiff ∞ (T% Y) →
    CMDiff ∞ (T% τ) → ∀ x u, cov (fun y ↦ c y (Y y) (τ y)) x u =
      c x (leviCivitaConnection I M Y x u) (τ x) + c x (Y x) (cov τ x u))

namespace IsMetricCompatible

include hc hskew hcomp

/-- **The transverse Dirac operator is formally self-adjoint along a Killing field.** Let `∇` be
a metric connection compatible with a smooth Clifford multiplication `c` by skew-adjoint
endomorphisms and with the Levi-Civita connection, and let `T` be a Killing field of constant
length. For smooth sections `σ` and `τ`, one of which has compact support,
`∫ ⟪B_T σ, τ⟫ dV = ∫ ⟪σ, B_T τ⟫ dV` for the Riemannian volume: `B_T = D - c(T) ∇_T` is the
difference of two formally self-adjoint operators. -/
theorem integral_inner_transverseDiracOperator_left_eq_right (hcov : cov.IsMetricCompatible)
    (hT : IsKillingField I T) {r : ℝ} (hTr : ∀ x, ‖T x‖ = r) {σ τ : Π y : M, V y}
    (hσ : CMDiff ∞ (T% σ)) (hτ : CMDiff ∞ (T% τ))
    (hστ : IsCompact (closure {x | σ x ≠ 0}) ∨ IsCompact (closure {x | τ x ≠ 0})) :
    ∫ x, ⟪cov.transverseDiracOperator c T σ x, τ x⟫ ∂riemannianVolume I M =
      ∫ x, ⟪σ x, cov.transverseDiracOperator c T τ x⟫ ∂riemannianVolume I M := by
  have : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
      (V := V)
  have hcT {ρ : Π y : M, V y} (hρ : CMDiff ∞ (T% ρ)) :
      CMDiff ∞ (T% (fun y ↦ c y (T y) (cov ρ y (T y)))) :=
    (hc.clm_bundle_apply hT.contMDiff).clm_bundle_apply
      (cov.contMDiff_apply hT.contMDiff (by simpa using hρ))
  -- Off the closure of the nonzero locus of a section, the section, its Dirac operator and
  -- `c(T) ∇_T` of it all vanish.
  have hvan {ρ : Π y : M, V y} {y : M} (hy : y ∉ closure {x | ρ x ≠ 0}) :
      ρ y = 0 ∧ cov.diracOperator c ρ y = 0 ∧ c y (T y) (cov ρ y (T y)) = 0 := by
    have h0 := cov.apply_eq_zero_of_notMem_closure hy
    exact ⟨Bundle.apply_eq_zero_of_notMem_closure hy,
      cov.diracOperator_eq_zero_of_eq_zero c y h0, by simp [h0]⟩
  have hint {f g : Π y : M, V y} (hf : CMDiff ∞ (T% f)) (hg : CMDiff ∞ (T% g))
      (hfσ : ∀ y ∉ closure {x | σ x ≠ 0}, f y = 0) (hgτ : ∀ y ∉ closure {x | τ x ≠ 0}, g y = 0) :
      Integrable (fun x ↦ ⟪f x, g x⟫) (riemannianVolume I M) := by
    refine (hf.continuous.inner_bundle hg.continuous).integrable_of_hasCompactSupport ?_
    rcases hστ with h | h
    · exact .intro' h isClosed_closure fun y hy ↦ by simp [hfσ y hy]
    · exact .intro' h isClosed_closure fun y hy ↦ by simp [hgτ y hy]
  simp only [transverseDiracOperator_def, inner_sub_left, inner_sub_right]
  rw [integral_sub (hint (cov.contMDiff_diracOperator hc hσ) hτ (fun _ hy ↦ (hvan hy).2.1)
      fun _ hy ↦ (hvan hy).1)
      (hint (hcT hσ) hτ (fun _ hy ↦ (hvan hy).2.2) fun _ hy ↦ (hvan hy).1),
    integral_sub (hint hσ (cov.contMDiff_diracOperator hc hτ) (fun _ hy ↦ (hvan hy).1)
      fun _ hy ↦ (hvan hy).2.1)
      (hint hσ (hcT hτ) (fun _ hy ↦ (hvan hy).1) fun _ hy ↦ (hvan hy).2.2),
    hcov.integral_inner_clifford_covariantDerivative_left_eq_right hskew hcomp
      (fun _ _ hY hρ ↦ (hc.clm_bundle_apply hY).clm_bundle_apply hρ) hT hTr hσ hτ hστ]
  rcases hστ with h | h
  · rw [hcov.integral_inner_diracOperator_left_eq_right_of_isCompact_left hc hskew hcomp hσ hτ h]
  · rw [hcov.integral_inner_diracOperator_left_eq_right hc hskew hcomp hσ hτ h]

/-- **The cross term of the split Dirac operator is a commutator.** Let `∇` be a metric
connection compatible with a smooth Clifford multiplication `c` by skew-adjoint endomorphisms
satisfying the Clifford relation `c(v) c(v) = -⟪v, v⟫`, and with the Levi-Civita connection, and
let `T` be a parallel vector field of unit length. For every compactly supported smooth section
`σ`, the cross term of `‖c(T) ∇_T σ + B_T σ‖²` integrates to

`2 ∫ ⟪c(T) ∇_T σ, B_T σ⟫ dV = ∫ ⟪σ, c(T) (∇_T (B_T σ) - B_T (∇_T σ))⟫ dV`

for the Riemannian volume. -/
theorem two_mul_integral_inner_clifford_transverseDiracOperator
    (hcov : cov.IsMetricCompatible)
    (hcl : ∀ x (v : TangentSpace I x) (s : V x), c x v (c x v s) = -⟪v, v⟫ • s)
    (hTs : CMDiff ∞ (T% T)) (hTpar : ∀ x, leviCivitaConnection I M T x = 0)
    (hT1 : ∀ x, ‖T x‖ = 1) {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ))
    (hσc : IsCompact (closure {x | σ x ≠ 0})) :
    2 * ∫ x, ⟪c x (T x) (cov σ x (T x)), cov.transverseDiracOperator c T σ x⟫
        ∂riemannianVolume I M =
      ∫ x, ⟪σ x, c x (T x) (cov (cov.transverseDiracOperator c T σ) x (T x) -
        cov.transverseDiracOperator c T (fun y ↦ cov σ y (T y)) x)⟫ ∂riemannianVolume I M := by
  have : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
      (V := V)
  set μ := riemannianVolume I M
  have hTK : IsKillingField I T :=
    (isMetricCompatible_leviCivitaConnection I).isKillingField_of_forall_eq_zero
      (torsion_leviCivitaConnection_eq_zero I) hTs hTpar
  have hcT {ρ : Π y : M, V y} (hρ : CMDiff ∞ (T% ρ)) :
      CMDiff ∞ (T% (fun y ↦ c y (T y) (ρ y))) :=
    (hc.clm_bundle_apply hTs).clm_bundle_apply hρ
  -- The polarized Clifford relation with `T`, and `c(T)` is parallel since `T` is.
  have hpol (x : M) (u : TangentSpace I x) (w : V x) :
      c x u (c x (T x) w) + c x (T x) (c x u w) = -(2 * ⟪u, T x⟫) • w := by
    simpa using LinearMap.apply_apply_add_swap_eq_neg_two_inner
      ((ContinuousLinearMap.coeLM ℝ).comp (c x).toLinearMap) (by simpa using hcl x) u (T x) w
  have hpar {τ : Π y : M, V y} (hτ : CMDiff ∞ (T% τ)) (x : M) :
      cov (fun y ↦ c y (T y) (τ y)) x = c x (T x) ∘L cov τ x := by
    ext u
    simp [hcomp T τ hTs hτ x u, hTpar x]
  have hTσ : CMDiff ∞ (T% (fun y ↦ cov σ y (T y))) := cov.contMDiff_apply hTs (by simpa using hσ)
  have hBσ := cov.contMDiff_transverseDiracOperator hc hTs hσ
  -- Pairings with `σ` are integrable.
  have hint {g : Π y : M, V y} (hg : CMDiff ∞ (T% g)) : Integrable (fun x ↦ ⟪σ x, g x⟫) μ :=
    (hσ.continuous.inner_bundle hg.continuous).integrable_of_hasCompactSupport
      (.intro' hσc isClosed_closure fun y hy ↦ by simp [Bundle.apply_eq_zero_of_notMem_closure hy])
  -- The cross term, integrated by parts in two ways: through the formal self-adjointness of
  -- `c(T) ∇_T`, and through that of `B_T` and the anticommutation of `c(T)` with `B_T`.
  have hcross₁ : ∫ x, ⟪c x (T x) (cov σ x (T x)), cov.transverseDiracOperator c T σ x⟫ ∂μ =
      ∫ x, ⟪σ x, c x (T x) (cov (cov.transverseDiracOperator c T σ) x (T x))⟫ ∂μ :=
    hcov.integral_inner_clifford_covariantDerivative_left_eq_right hskew hcomp
      (fun _ _ hY hρ ↦ (hc.clm_bundle_apply hY).clm_bundle_apply hρ) hTK hT1 hσ hBσ (.inl hσc)
  have hcross₂ : ∫ x, ⟪c x (T x) (cov σ x (T x)), cov.transverseDiracOperator c T σ x⟫ ∂μ =
      ∫ x, ⟪σ x, -c x (T x) (cov.transverseDiracOperator c T (fun y ↦ cov σ y (T y)) x)⟫ ∂μ := by
    calc _ = ∫ x, ⟪cov.transverseDiracOperator c T σ x, c x (T x) (cov σ x (T x))⟫ ∂μ :=
          integral_congr_ae (.of_forall fun x ↦ real_inner_comm _ _)
      _ = ∫ x, ⟪σ x, cov.transverseDiracOperator c T
            (fun y ↦ c y (T y) (cov σ y (T y))) x⟫ ∂μ :=
          integral_inner_transverseDiracOperator_left_eq_right hc hskew hcomp hcov hTK hT1 hσ
            (hcT hTσ) (.inl hσc)
      _ = _ := integral_congr_ae (.of_forall fun x ↦ congrArg (⟪σ x, ·⟫)
          (cov.transverseDiracOperator_clifford_eq c T (hT1 x) (hpol x) (hpar hTσ x)))
  have h₂ : Integrable (fun x ↦ ⟪σ x,
      -c x (T x) (cov.transverseDiracOperator c T (fun y ↦ cov σ y (T y)) x)⟫) μ :=
    hint (hcT (cov.contMDiff_transverseDiracOperator hc hTs hTσ)).neg_section
  rw [two_mul]
  nth_rw 2 [hcross₂]
  rw [hcross₁, ← integral_add (hint (hcT (cov.contMDiff_apply hTs (by simpa using hBσ)))) h₂]
  exact integral_congr_ae (.of_forall fun x ↦ by
    simp only [sub_eq_add_neg, map_add, map_neg, inner_add_right])

/-- **The energy identity of a Dirac operator split along a parallel unit field.** Let `∇` be a
metric connection compatible with a smooth Clifford multiplication `c` by skew-adjoint
endomorphisms satisfying the Clifford relation `c(v) c(v) = -⟪v, v⟫`, and with the Levi-Civita
connection, and let `T` be a parallel vector field of unit length. For every compactly supported
smooth section `σ`,

`∫ ‖D σ‖² dV = ∫ ‖∇_T σ‖² dV + ∫ ‖B_T σ‖² dV + ∫ ⟪σ, c(T) (∇_T (B_T σ) - B_T (∇_T σ))⟫ dV`

for the Riemannian volume, where `B_T = D - c(T) ∇_T` is the transverse Dirac operator. -/
theorem integral_norm_diracOperator_sq_eq (hcov : cov.IsMetricCompatible)
    (hcl : ∀ x (v : TangentSpace I x) (s : V x), c x v (c x v s) = -⟪v, v⟫ • s)
    (hTs : CMDiff ∞ (T% T)) (hTpar : ∀ x, leviCivitaConnection I M T x = 0)
    (hT1 : ∀ x, ‖T x‖ = 1) {σ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ))
    (hσc : IsCompact (closure {x | σ x ≠ 0})) :
    ∫ x, ‖cov.diracOperator c σ x‖ ^ 2 ∂riemannianVolume I M =
      ∫ x, ‖cov σ x (T x)‖ ^ 2 ∂riemannianVolume I M +
        ∫ x, ‖cov.transverseDiracOperator c T σ x‖ ^ 2 ∂riemannianVolume I M +
          ∫ x, ⟪σ x, c x (T x) (cov (cov.transverseDiracOperator c T σ) x (T x) -
            cov.transverseDiracOperator c T (fun y ↦ cov σ y (T y)) x)⟫
              ∂riemannianVolume I M := by
  have : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := F)
      (V := V)
  set μ := riemannianVolume I M
  -- Clifford multiplication by the unit vector `T` is isometric.
  have hnorm (x : M) (w : V x) : ‖c x (T x) w‖ = ‖w‖ := by
    have h : ⟪c x (T x) w, c x (T x) w⟫ = ⟪w, w⟫ := by
      rw [hskew, hcl, real_inner_self_eq_norm_sq (T x), hT1, inner_smul_right]
      simp
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h
  -- The integrands are continuous and vanish off the compact closure of the support of `σ`.
  have hTσ : CMDiff ∞ (T% (fun y ↦ cov σ y (T y))) := cov.contMDiff_apply hTs (by simpa using hσ)
  have hBσ := cov.contMDiff_transverseDiracOperator hc hTs hσ
  have hcov0 {y : M} (hy : y ∉ closure {x | σ x ≠ 0}) : cov σ y = 0 :=
    cov.apply_eq_zero_of_notMem_closure hy
  have hint {f g : Π y : M, V y} (hf : CMDiff ∞ (T% f)) (hg : CMDiff ∞ (T% g))
      (h : ∀ y ∉ closure {x | σ x ≠ 0}, f y = 0) : Integrable (fun x ↦ ⟪f x, g x⟫) μ :=
    (hf.continuous.inner_bundle hg.continuous).integrable_of_hasCompactSupport
      (.intro' hσc isClosed_closure fun y hy ↦ by simp [h y hy])
  have hBσ0 (y : M) (hy : y ∉ closure {x | σ x ≠ 0}) : cov.transverseDiracOperator c T σ y = 0 := by
    simp [transverseDiracOperator_def, cov.diracOperator_eq_zero_of_eq_zero c y (hcov0 hy),
      hcov0 hy]
  have hDint : Integrable (fun x ↦ ‖cov σ x (T x)‖ ^ 2) μ := by
    simpa [real_inner_self_eq_norm_sq] using hint hTσ hTσ fun y hy ↦ by simp [hcov0 hy]
  have hBint : Integrable (fun x ↦ ‖cov.transverseDiracOperator c T σ x‖ ^ 2) μ := by
    simpa [real_inner_self_eq_norm_sq] using hint hBσ hBσ hBσ0
  have hXint : Integrable
      (fun x ↦ 2 * ⟪c x (T x) (cov σ x (T x)), cov.transverseDiracOperator c T σ x⟫) μ :=
    (hint ((hc.clm_bundle_apply hTs).clm_bundle_apply hTσ) hBσ fun y hy ↦ by
      simp [hcov0 hy]).const_mul 2
  have hDBint : Integrable
      (fun x ↦ ‖cov σ x (T x)‖ ^ 2 + ‖cov.transverseDiracOperator c T σ x‖ ^ 2) μ :=
    hDint.add hBint
  -- Pointwise, `‖D σ‖² = ‖∇_T σ‖² + ‖B_T σ‖² + 2 ⟪c(T) ∇_T σ, B_T σ⟫`.
  have hpt (x : M) : ‖cov.diracOperator c σ x‖ ^ 2 = ‖cov σ x (T x)‖ ^ 2 +
      ‖cov.transverseDiracOperator c T σ x‖ ^ 2 +
        2 * ⟪c x (T x) (cov σ x (T x)), cov.transverseDiracOperator c T σ x⟫ := by
    rw [cov.diracOperator_eq_add_transverseDiracOperator c T σ x, norm_add_sq_real, hnorm]
    ring
  simp_rw [hpt]
  rw [integral_add hDBint hXint, integral_add hDint hBint, integral_const_mul,
    two_mul_integral_inner_clifford_transverseDiracOperator hc hskew hcomp
      hcov hcl hTs hTpar hT1 hσ hσc]

end IsMetricCompatible

end CovariantDerivative
