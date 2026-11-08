/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Riemann
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.LinearAlgebra.BilinearForm.KulkarniNomizu

/-!
# Sectional curvature determines the curvature tensor

For a metric-compatible torsion-free connection on a Riemannian tangent bundle, the
metric-lowered curvature tensor `Rm(u, v, w, z) = ⟨R(u, v)w, z⟩` is antisymmetric in each pair of
arguments and satisfies the first Bianchi identity. By the polarization identity
`LinearMap.six_mul_apply_eq_of_cyclic_eq_zero` it is therefore determined by the numerators
`⟨R(u, v)v, u⟩` of the sectional curvatures, and in fact by their values on linearly independent
pairs `u, v`, which are the pairs spanning a tangent two-plane
(`CovariantDerivative.IsMetricCompatible.riemannCurvatureTensor_eq_of_forall_linearIndependent`).

In particular, the tangent two-planes at a point all have sectional curvature `κ` exactly when
the curvature tensor there has the constant-curvature form

`R(w, u)v = κ (⟨u, v⟩ w - ⟨w, v⟩ u)`.

So constant sectional curvature `κ` is equivalent to the constant-curvature tensor equation
`Bundle.RiemannianMetric.IsConstantCurvatureTensor`, and it forces `Ric = (n - 1) κ g` and
`Scal = n (n - 1) κ` in dimension `n`. In dimension at most one there are no tangent two-planes,
so every `κ` is a sectional curvature
(`CovariantDerivative.hasSectionalCurvatureAt_of_finrank_le_one`), and correspondingly the
constant-curvature equation then holds for every `κ`. From dimension two on the sectional
curvature at a point is unique (`CovariantDerivative.HasSectionalCurvatureAt.eq_of_one_lt_finrank`).

In dimension exactly two the tangent space is itself the only tangent two-plane, and its sectional
curvature, the Gaussian curvature, is half the scalar curvature. So on a surface the scalar
curvature alone determines the curvature tensor,
`R(w, u)v = (Scal / 2) (⟨u, v⟩ w - ⟨w, v⟩ u)`, and a metric has constant curvature `κ` exactly
when its scalar curvature is the constant `2 κ`. This is how the scalar-curvature equation of a
conformal metric on a surface produces a metric of constant curvature.

## Main results

* `CovariantDerivative.hasSectionalCurvatureAt_iff_curvatureTensor_eq_smul_inner_sub`: sectional
  curvature `κ` at a point is the constant-curvature form of the curvature tensor there.
* `CovariantDerivative.hasConstantSectionalCurvature_iff_isConstantCurvatureTensor`: the global
  version.
* `CovariantDerivative.HasSectionalCurvatureAt.ricciTensor_eq` and
  `CovariantDerivative.HasSectionalCurvatureAt.scalarCurvature_eq`: the Ricci and scalar curvature
  of a point of sectional curvature `κ`.
* `CovariantDerivative.hasSectionalCurvatureAt_scalarCurvature_div_two`: in dimension two the
  sectional curvature is half the scalar curvature.
* `CovariantDerivative.exists_curvatureTensor_eq_smul_inner_sub_of_finrank_eq_two` and
  `CovariantDerivative.curvatureTensor_eq_scalarCurvature_div_two_smul`: in dimension two a
  metric-compatible connection has curvature tensor `R(w, u)v = (Scal / 2) (⟨u, v⟩ w - ⟨w, v⟩ u)`,
  with no torsion hypothesis.
* `isConstantCurvatureTensor_iff_scalarCurvature_eq_of_finrank_eq_two`, in the namespace
  `Bundle.ContMDiffRiemannianMetric`: a metric on a surface has constant curvature `κ` exactly when
  its scalar curvature is `2 κ`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 8, Propositions 8.31 and 8.36.
-/

public section

open Bundle LinearMap.BilinForm
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)

/-- At a point where every tangent two-plane has sectional curvature `κ`, the curvature tensor of
a metric-compatible torsion-free connection has the constant-curvature form
`R(w, u)v = κ (⟨u, v⟩ w - ⟨w, v⟩ u)`. -/
theorem HasSectionalCurvatureAt.curvatureTensor_eq_smul_inner_sub
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov}
    {x : M} {κ : ℝ} (h : cov.HasSectionalCurvatureAt hcov x κ) (ht : cov.torsion = 0)
    (w u v : TangentSpace I x) :
    curvature x w u v = κ • (⟪u, v⟫_ℝ • w - ⟪w, v⟫_ℝ • u) := by
  set g := innerₗ (TangentSpace I x)
  have hg : LinearMap.BilinForm.IsSymm g := isSymm_iff.mpr isSymm_inner
  have hκg : LinearMap.BilinForm.IsSymm ((κ / 2) • g) := isSymm_def.2 fun a b ↦ by
    simp only [LinearMap.smul_apply, hg.eq a b]
  -- The constant-curvature tensor is `(κ / 2) g ⊙ g`.
  have hRm : cov.riemannCurvatureTensor x = kulkarniNomizu ((κ / 2) • g) g :=
    hcov.riemannCurvatureTensor_eq_of_forall_linearIndependent ht x
      (kulkarniNomizu_antisymm_first _ _) (kulkarniNomizu_antisymm_last _ _)
      (IsSymm.kulkarniNomizu_cyclic_eq_zero hκg hg) fun a b hab ↦ by
        have hab' := h.sectionalCurvature_eq a b hab
        rw [sectionalCurvature_apply,
          div_eq_iff (Matrix.det_gram_ne_zero_iff_linearIndependent.2 hab),
          Matrix.real_det_gram_fin_two] at hab'
        simp only [riemannCurvatureTensor_apply, hab', kulkarniNomizu_apply, LinearMap.smul_apply,
          smul_eq_mul, g, innerₗ_apply_apply, real_inner_comm b a]
        ring
  refine ext_inner_right ℝ fun z ↦ ?_
  have hz := congrArg (fun T ↦ T w u v z) hRm
  simp only [riemannCurvatureTensor_apply, kulkarniNomizu_apply, LinearMap.smul_apply,
    smul_eq_mul, g, innerₗ_apply_apply] at hz
  simp only [hz, inner_smul_left, inner_sub_left, RCLike.conj_to_real]
  ring

/-- At a point where every tangent two-plane has sectional curvature `κ`, the Jacobi operator
`w ↦ R(w, u)u` of a metric-compatible torsion-free connection acts on the orthogonal complement of
`u` as multiplication by `κ ‖u‖²`. -/
theorem HasSectionalCurvatureAt.curvatureTensor_apply_self_of_inner_eq_zero
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov}
    {x : M} {κ : ℝ} (h : cov.HasSectionalCurvatureAt hcov x κ) (ht : cov.torsion = 0)
    {w u : TangentSpace I x} (hwu : ⟪w, u⟫_ℝ = 0) :
    curvature x w u u = (κ * ‖u‖ ^ 2) • w := by
  rw [h.curvatureTensor_eq_smul_inner_sub ht, hwu, real_inner_self_eq_norm_sq, zero_smul,
    sub_zero, smul_smul]

variable (cov) in
/-- For a metric-compatible torsion-free connection, every tangent two-plane at `x` has sectional
curvature `κ` if and only if the curvature tensor at `x` has the constant-curvature form
`R(w, u)v = κ (⟨u, v⟩ w - ⟨w, v⟩ u)`. -/
theorem hasSectionalCurvatureAt_iff_curvatureTensor_eq_smul_inner_sub
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) (x : M) (κ : ℝ) :
    cov.HasSectionalCurvatureAt hcov x κ ↔
      ∀ w u v : TangentSpace I x, curvature x w u v = κ • (⟪u, v⟫_ℝ • w - ⟪w, v⟫_ℝ • u) :=
  ⟨fun h ↦ h.curvatureTensor_eq_smul_inner_sub ht,
    cov.hasSectionalCurvatureAt_of_curvatureTensor_eq_smul_inner_sub hcov x κ⟩

variable (cov) in
/-- A metric-compatible torsion-free connection has constant sectional curvature `κ` if and only
if its curvature tensor is the constant-curvature tensor `R(w, u)v = κ (⟨u, v⟩ w - ⟨w, v⟩ u)` at
every point. Applied to the Levi-Civita connection, this identifies constant sectional curvature
of a Riemannian manifold with the constant-curvature equation. -/
theorem hasConstantSectionalCurvature_iff_isConstantCurvatureTensor
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) (κ : ℝ) :
    cov.HasConstantSectionalCurvature hcov κ ↔
      (RiemannianBundle.g (E := fun x : M ↦ TangentSpace I x)).IsConstantCurvatureTensor cov
        inferInstance κ := by
  -- The metric `⟨RiemannianBundle.g⟩` installed by `isConstantCurvatureTensor_iff` is the ambient
  -- `RiemannianBundle` instance up to structure eta, so the two sides agree definitionally.
  rw [hasConstantSectionalCurvature_iff, RiemannianMetric.isConstantCurvatureTensor_iff]
  exact forall_congr' fun x ↦
    hasSectionalCurvatureAt_iff_curvatureTensor_eq_smul_inner_sub cov hcov ht x κ

/-- At a point where every tangent two-plane has sectional curvature `κ`, the Ricci tensor of a
metric-compatible torsion-free connection is `(n - 1) κ g` in dimension `n`. -/
theorem HasSectionalCurvatureAt.ricciTensor_eq
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov}
    {x : M} {κ : ℝ} (h : cov.HasSectionalCurvatureAt hcov x κ) (ht : cov.torsion = 0) :
    cov.ricciTensor x =
      ((Module.finrank ℝ (TangentSpace I x) - 1 : ℝ) * κ) • innerₗ (TangentSpace I x) :=
  cov.ricciTensor_eq_of_curvatureTensor_eq_smul_inner_sub x κ
    (h.curvatureTensor_eq_smul_inner_sub ht)

/-- At a point where every tangent two-plane has sectional curvature `κ`, the scalar curvature of
a metric-compatible torsion-free connection is `n (n - 1) κ` in dimension `n`. -/
theorem HasSectionalCurvatureAt.scalarCurvature_eq
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov}
    {x : M} {κ : ℝ} (h : cov.HasSectionalCurvatureAt hcov x κ) :
    cov.scalarCurvature x = (Module.finrank ℝ (TangentSpace I x) : ℝ) *
      (Module.finrank ℝ (TangentSpace I x) - 1) * κ := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hterm (j k : Fin (Module.finrank ℝ (TangentSpace I x))) :
      ⟪b k, curvature x (b k) (b j) (b j)⟫_ℝ = if k = j then 0 else κ := by
    split_ifs with hkj
    · subst hkj
      simp [cov.curvatureTensor_self]
    · have horth : Orthonormal ℝ ![b k, b j] := by
        have := b.orthonormal.comp ![k, j] (by
          intro a c hac
          fin_cases a <;> fin_cases c <;> simp_all [eq_comm])
        convert this using 1
        ext a
        fin_cases a <;> rfl
      rw [real_inner_comm, ← cov.sectionalCurvature_eq_of_orthonormal hcov x _ _ horth]
      exact h.sectionalCurvature_eq _ _ horth.linearIndependent
  rw [cov.scalarCurvature_eq_sum_inner_curvatureTensor x b]
  simp only [hterm, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
  have hcard (j : Fin (Module.finrank ℝ (TangentSpace I x))) :
      ({k | ¬k = j} : Finset (Fin (Module.finrank ℝ (TangentSpace I x)))).card =
        Module.finrank ℝ (TangentSpace I x) - 1 := by
    simp [Finset.filter_not, Finset.card_sdiff_of_subset, Finset.filter_eq']
  simp only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ (TangentSpace I x)) with hn | hn
  · simp [hn]
  · rw [Nat.cast_sub hn]
    simp [mul_assoc]

variable (cov) in
/-- In dimension two the curvature tensor of a metric-compatible connection has the
constant-curvature form `R(w, u)v = K (⟨u, v⟩ w - ⟨w, v⟩ u)` for some real `K`, the Gaussian
curvature. Neither torsion-freeness nor the Bianchi identity is needed: in an orthonormal basis,
antisymmetry in the first two arguments and metric compatibility leave the single number
`⟨R(e₀, e₁)e₁, e₀⟩`. -/
theorem exists_curvatureTensor_eq_smul_inner_sub_of_finrank_eq_two
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {x : M} (hx : Module.finrank ℝ (TangentSpace I x) = 2) :
    ∃ K : ℝ, ∀ w u v : TangentSpace I x,
      curvature x w u v = K • (⟪u, v⟫_ℝ • w - ⟪w, v⟫_ℝ • u) := by
  let e := (stdOrthonormalBasis ℝ (TangentSpace I x)).reindex (finCongr hx)
  set K := ⟪curvature x (e 0) (e 1) (e 1), e 0⟫_ℝ with hK
  have hzero (w : TangentSpace I x) : ⟪curvature x (e 0) (e 1) w, w⟫_ℝ = 0 := by
    have := hcov.inner_curvatureTensor_eq_neg x (e 0) (e 1) w w
    rw [real_inner_comm w] at this ⊢
    linarith
  have hswap : ⟪curvature x (e 0) (e 1) (e 0), e 1⟫_ℝ = -K := by
    rw [hcov.inner_curvatureTensor_eq_neg, real_inner_comm]
  have he := e.orthonormal
  have h00 : ⟪e 0, e 0⟫_ℝ = 1 := inner_self_eq_one_of_norm_eq_one (he.1 0)
  have h11 : ⟪e 1, e 1⟫_ℝ = 1 := inner_self_eq_one_of_norm_eq_one (he.1 1)
  have h01 : ⟪e 0, e 1⟫_ℝ = 0 := he.2 (by decide)
  have h10 : ⟪e 1, e 0⟫_ℝ = 0 := he.2 (by decide)
  have hexp (w : TangentSpace I x) : ∃ a b : ℝ, w = a • e 0 + b • e 1 :=
    ⟨_, _, by simpa only [Fin.sum_univ_two] using (e.sum_repr' w).symm⟩
  refine ⟨K, fun w u v ↦ ?_⟩
  refine ext_inner_right ℝ fun z ↦ ?_
  obtain ⟨a, b, rfl⟩ := hexp w
  obtain ⟨c, d, rfl⟩ := hexp u
  obtain ⟨f, g, rfl⟩ := hexp v
  obtain ⟨p, q, rfl⟩ := hexp z
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, cov.curvatureTensor_self,
    cov.curvatureTensor_antisymm x (e 1) (e 0), LinearMap.neg_apply, smul_zero, zero_add, add_zero,
    smul_neg, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_neg_left,
    inner_sub_left, hzero, hswap, ← hK, h00, h11, h01, h10, RCLike.conj_to_real]
  ring

variable (cov) in
/-- **The curvature tensor of a surface.** In dimension two the curvature tensor of a
metric-compatible connection is determined by the scalar curvature:
`R(w, u)v = (Scal / 2) (⟨u, v⟩ w - ⟨w, v⟩ u)`. -/
theorem curvatureTensor_eq_scalarCurvature_div_two_smul
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {x : M} (hx : Module.finrank ℝ (TangentSpace I x) = 2) (w u v : TangentSpace I x) :
    curvature x w u v = (cov.scalarCurvature x / 2) • (⟪u, v⟫_ℝ • w - ⟪w, v⟫_ℝ • u) := by
  obtain ⟨K, hK⟩ := cov.exists_curvatureTensor_eq_smul_inner_sub_of_finrank_eq_two hcov hx
  have hscal := cov.scalarCurvature_eq_of_curvatureTensor_eq_smul_inner_sub x K hK
  rw [hx] at hscal
  rw [hK, hscal]
  norm_num

variable (cov) in
/-- **The Gaussian curvature of a surface is half its scalar curvature.** In dimension two the
tangent space at `x` is the only tangent two-plane there, and for a metric-compatible connection
its sectional curvature is `Scal(x) / 2`. -/
theorem hasSectionalCurvatureAt_scalarCurvature_div_two
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {x : M} (hx : Module.finrank ℝ (TangentSpace I x) = 2) :
    cov.HasSectionalCurvatureAt hcov x (cov.scalarCurvature x / 2) :=
  cov.hasSectionalCurvatureAt_of_curvatureTensor_eq_smul_inner_sub hcov x _
    (cov.curvatureTensor_eq_scalarCurvature_div_two_smul hcov hx)

end CovariantDerivative

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- **Constant curvature on a surface.** A smooth metric on a surface has constant curvature `κ`,
in the tensor form `R(w, u)v = κ (⟨u, v⟩ w - ⟨w, v⟩ u)`, exactly when its scalar curvature is the
constant `2 κ`. In particular it has constant curvature `-1` exactly when its scalar curvature
is `-2`. -/
theorem isConstantCurvatureTensor_iff_scalarCurvature_eq_of_finrank_eq_two
    (hE : Module.finrank ℝ E = 2) (κ : ℝ) :
    g.IsConstantCurvatureTensor κ ↔ ∀ x, g.scalarCurvature x = 2 * κ := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hx (x : M) : Module.finrank ℝ (TangentSpace I x) = 2 := by
    rw [TauCeti.finrank_tangentSpace, hE]
  rw [isConstantCurvatureTensor_iff]
  refine ⟨fun h x ↦ ?_, fun h x w u v ↦ ?_⟩
  · rw [scalarCurvature_def,
      CovariantDerivative.scalarCurvature_eq_of_curvatureTensor_eq_smul_inner_sub _ x κ (h x), hx x]
    norm_num
  · rw [CovariantDerivative.curvatureTensor_eq_scalarCurvature_div_two_smul _
      (CovariantDerivative.isMetricCompatible_leviCivitaConnection I) (hx x), ← scalarCurvature_def,
      h x, mul_div_cancel_left₀ _ two_ne_zero]

end Bundle.ContMDiffRiemannianMetric
