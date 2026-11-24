/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Frame.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.SecondCovariantDerivative
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Dirac.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.RoughLaplacian
import TauCeti.Algebra.BigOperators.Finset.Pairs
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# The Weitzenböck formula for the square of a Dirac operator

Let `D σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ` be the Dirac operator of a connection `∇` on a vector bundle `V`
over a Riemannian manifold and a Clifford multiplication `c`
(`CovariantDerivative.diracOperator`). If `c` satisfies the Clifford relation
`c(u) c(w) + c(w) c(u) = -2 ⟪u, w⟫` and is parallel for `∇` and the Levi-Civita connection, its
square is the rough Laplacian plus a curvature endomorphism:

`D² σ = ∇*∇ σ + (1 / 2) ∑ᵢ ∑ⱼ c(eᵢ) c(eⱼ) R(eᵢ, eⱼ) σ`

for every orthonormal basis `eᵢ` of the tangent space at the point, where `R` is the curvature of
`∇` (`CovariantDerivative.diracOperator_diracOperator_eq_roughLaplacian_add`). Since
`c(eⱼ) c(eᵢ) R(eⱼ, eᵢ) = c(eᵢ) c(eⱼ) R(eᵢ, eⱼ)` for `i ≠ j` and the diagonal terms vanish, the
curvature term is the sum `∑_{i < j} c(eᵢ) c(eⱼ) R(eᵢ, eⱼ)` over unordered pairs. This is the
general Weitzenböck (or Bochner) formula for the connection-induced Dirac operator of a Clifford
bundle. For the spinor bundle of a spin manifold with its spin connection, the curvature term is
`Scal / 4`, which is the Clifford contraction
`TauCeti.FourTensor.sum_sum_inv_two_smul_ι_mul_ι_mul_inv_four_smul_sum_sum_smul_ι_mul_ι` of the
Riemann tensor; identifying the curvature of the spin connection is not done here.

The proof is the normal-frame calculation. In an orthonormal frame `eᵢ` near `x` whose
Levi-Civita derivatives vanish at `x`, a geodesic frame
(`TauCeti.Manifold.exists_contMDiff_geodesicFrame`), the parallel Clifford multiplications
`c(eᵢ)` pass through `∇` at `x`, and

`D² σ = ∑ᵢ ∑ⱼ c(eᵢ) c(eⱼ) ∇²σ(eᵢ, eⱼ)`

at `x` (`CovariantDerivative.diracOperator_diracOperator_eq_sum_sum_secondCovariantDerivative`).
The Clifford relation splits this double sum into the diagonal part `-∑ᵢ ∇²σ(eᵢ, eᵢ) = ∇*∇ σ`
and half the antisymmetrization of `∇²σ` (`TauCeti.two_nsmul_sum_sum_apply_apply_eq`), which the
Ricci identity `∇²σ(u, w) - ∇²σ(w, u) = R(u, w) σ` turns into the curvature term.

Parallelism of `c` is stated through the Leibniz rule at the point,
`∇_u (c(Y) τ) = c(∇_u Y) τ + c(Y) ∇_u τ`, together with differentiability of `c(Y) τ`, both for
smooth vector fields `Y` and smooth sections `τ`.

## Main results

* `CovariantDerivative.diracOperator_diracOperator_eq_sum_sum_secondCovariantDerivative`:
  `D² σ = ∑ᵢ ∑ⱼ c(eᵢ) c(eⱼ) ∇²σ(eᵢ, eⱼ)` in an orthonormal frame parallel at the point.
* `CovariantDerivative.diracOperator_diracOperator_eq_roughLaplacian_add_of_frame`: the
  Weitzenböck formula in such a frame, for any torsion-free connection on the tangent bundle.
* `CovariantDerivative.diracOperator_diracOperator_eq_roughLaplacian_add`: the Weitzenböck
  formula for the Levi-Civita connection, in every orthonormal basis.
* `CovariantDerivative.diracOperator_diracOperator_eq_roughLaplacian_add_sum_lt`: the same, with
  the curvature term summed over pairs `i < j`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter II, Theorem 8.2.
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 2nd ed., World Scientific, 2007,
  Theorem 12.1.67.
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold RealInnerProductSpace Topology

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
  (c : Π x : M, TangentSpace I x →L[ℝ] V x →L[ℝ] V x)
  {σ : Π y : M, V y}

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I] in
/-- **The square of the Dirac operator in a frame parallel at a point.** Let `e₁, …, eₖ` be
smooth vector fields forming an orthonormal frame near `x`, with vanishing covariant derivatives
`∇ᵀ eᵢ = 0` at `x`. Suppose that each `c(eᵢ)` is parallel at `x` on the section `∇_{eᵢ} σ`,
and that the sections `c(eᵢ) ∇_{eᵢ} σ` are differentiable at `x`. Then for a smooth section `σ`,

`D (D σ) = ∑ᵢ ∑ⱼ c(eᵢ) c(eⱼ) ∇²σ(eᵢ, eⱼ)`

at `x`, where `∇²σ` is the second covariant derivative for `∇` and `∇ᵀ`. -/
theorem diracOperator_diracOperator_eq_sum_sum_secondCovariantDerivative
    (hσ : CMDiff ∞ (T% σ)) {ι : Type*} [Fintype ι] (e : ι → Π y : M, TangentSpace I y)
    (he : ∀ i, CMDiff ∞ (T% (e i))) {x : M}
    (hframe : ∀ᶠ y in 𝓝 x, ∃ b : OrthonormalBasis ι ℝ (TangentSpace I y), ∀ i, b i = e i y)
    (hpar : ∀ i, covT (e i) x = 0)
    (hc : ∀ i u, cov (fun y ↦ c y (e i y) (cov σ y (e i y))) x u =
      c x (e i x) (cov (fun y ↦ cov σ y (e i y)) x u))
    (hdiff : ∀ i, MDiffAt (T% (fun y ↦ c y (e i y) (cov σ y (e i y)))) x) :
    cov.diracOperator c (cov.diracOperator c σ) x =
      ∑ i, ∑ j, c x (e i x) (c x (e j x)
        (cov.secondCovariantDerivative covT σ x (e i x) (e j x))) := by
  -- Near `x` the Dirac operator of `σ` is the frame sum `∑ⱼ c(eⱼ) ∇_{eⱼ} σ`.
  set S : ι → Π y : M, V y := fun j y ↦ c y (e j y) (cov σ y (e j y)) with hS
  have hsum : ∀ᶠ y in 𝓝 x, cov.diracOperator c σ y = (∑ j, S j) y := by
    filter_upwards [hframe] with y ⟨b, hb⟩
    rw [diracOperator_eq_sum cov c σ y b, Finset.sum_apply]
    simp only [hb, hS]
  have hsumdiff : MDiffAt (T% (∑ j, S j)) x := by
    simpa [Finset.sum_apply] using
      MDifferentiableAt.sum_section (s := Finset.univ) fun j _ ↦ hdiff j
  have hDdiff : MDiffAt (T% (cov.diracOperator c σ)) x :=
    hsumdiff.congr_of_eventuallyEq (hsum.mono fun y hy ↦ by simp only [hy])
  -- At `x`, `∇_u (c(eⱼ) ∇_{eⱼ} σ) = c(eⱼ) ∇²σ(u, eⱼ)`, since `∇ᵀ eⱼ = 0` there.
  have hsecond (j : ι) (u : TangentSpace I x) :
      cov.secondCovariantDerivative covT σ x u (e j x) =
        cov (fun y ↦ cov σ y (e j y)) x u := by
    simp [secondCovariantDerivative_apply cov covT hσ x (he j) u, hpar j]
  obtain ⟨b, hb⟩ := hframe.self_of_nhds
  rw [diracOperator_eq_sum cov c _ x b,
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hDdiff hsumdiff univ_mem hsum,
    cov.isCovariantDerivativeOnUniv.sum fun j _ ↦ hdiff j]
  simp only [hb, FunLike.coe_sum, Finset.sum_apply, map_sum, hc, hsecond]

/-- **The Weitzenböck formula in a frame parallel at a point.** Let `∇ᵀ` be a torsion-free
connection on the tangent bundle and `e₁, …, eₖ` smooth vector fields forming an orthonormal frame
near `x`, with `∇ᵀ eᵢ = 0` at `x`. Suppose that Clifford multiplication satisfies the Clifford
relation `c(u) c(w) + c(w) c(u) = -2 ⟪u, w⟫` at `x`, that each `c(eᵢ)` is parallel at `x` on the
section `∇_{eᵢ} σ`, and that the sections `c(eᵢ) ∇_{eᵢ} σ` are differentiable at `x`. Then for a
smooth section `σ`,

`D (D σ) = ∇*∇ σ + (1 / 2) ∑ᵢ ∑ⱼ c(eᵢ) c(eⱼ) R(eᵢ, eⱼ) σ`

at `x`, where `∇*∇` is the rough Laplacian and `R` the curvature of `∇`. -/
theorem diracOperator_diracOperator_eq_roughLaplacian_add_of_frame (ht : covT.IsTorsionFree)
    (hσ : CMDiff ∞ (T% σ)) {ι : Type*} [Fintype ι] (e : ι → Π y : M, TangentSpace I y)
    (he : ∀ i, CMDiff ∞ (T% (e i))) {x : M}
    (hframe : ∀ᶠ y in 𝓝 x, ∃ b : OrthonormalBasis ι ℝ (TangentSpace I y), ∀ i, b i = e i y)
    (hpar : ∀ i, covT (e i) x = 0)
    (hcl : ∀ u w s, c x u (c x w s) + c x w (c x u s) = -(2 * ⟪u, w⟫) • s)
    (hc : ∀ i u, cov (fun y ↦ c y (e i y) (cov σ y (e i y))) x u =
      c x (e i x) (cov (fun y ↦ cov σ y (e i y)) x u))
    (hdiff : ∀ i, MDiffAt (T% (fun y ↦ c y (e i y) (cov σ y (e i y)))) x) :
    cov.diracOperator c (cov.diracOperator c σ) x =
      cov.roughLaplacian covT σ x +
        (2 : ℝ)⁻¹ • ∑ i, ∑ j, c x (e i x) (c x (e j x)
          (cov.curvatureTensor x (e i x) (e j x) (σ x))) := by
  classical
  obtain ⟨b, hb⟩ := hframe.self_of_nhds
  -- The Clifford multiplications by the frame vectors at `x` satisfy the Clifford relations.
  have hγ (i j : ι) (s : V x) : c x (e i x) (c x (e j x) s) + c x (e j x) (c x (e i x) s) =
      if i = j then -(2 • s) else 0 := by
    rw [hcl, ← hb i, ← hb j, orthonormal_iff_ite.mp b.orthonormal i j]
    split_ifs <;> simp [two_smul]
  have h := TauCeti.two_nsmul_sum_sum_apply_apply_eq (fun i ↦ c x (e i x)) hγ
    (fun i j ↦ cov.secondCovariantDerivative covT σ x (e i x) (e j x))
  simp only [secondCovariantDerivative_sub_swap_of_isTorsionFree cov covT ht hσ x] at h
  rw [diracOperator_diracOperator_eq_sum_sum_secondCovariantDerivative cov covT c hσ e he hframe
      hpar hc hdiff, roughLaplacian_eq_sum cov covT σ x b]
  simp only [hb]
  simp only [← Nat.cast_smul_eq_nsmul ℝ 2, Nat.cast_ofNat] at h
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  rw [← inv_smul_smul₀ h2 (∑ i, ∑ j, _), h, smul_add, smul_neg, inv_smul_smul₀ h2]

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] [I.Boundaryless]

/-- **The Weitzenböck formula.** Let `∇` be a smooth connection on `V` and `c` a Clifford
multiplication satisfying the Clifford relation `c(u) c(w) + c(w) c(u) = -2 ⟪u, w⟫` at `x`.
Suppose that `c` is parallel at `x` for `∇` and the Levi-Civita connection `∇ᵀ`, in the sense of
the Leibniz rule `∇_u (c(Y) τ) = c(∇ᵀ_u Y) τ + c(Y) ∇_u τ` at `x`, and that the sections `c(Y) τ`
are differentiable at `x`, for all smooth vector fields `Y` and smooth sections `τ`. Then for a
smooth section `σ` and every orthonormal basis `eᵢ` of the tangent space at `x`,

`D (D σ) = ∇*∇ σ + (1 / 2) ∑ᵢ ∑ⱼ c(eᵢ) c(eⱼ) R(eᵢ, eⱼ) σ`

at `x`, where `∇*∇` is the rough Laplacian and `R` the curvature of `∇`. -/
theorem diracOperator_diracOperator_eq_roughLaplacian_add (hσ : CMDiff ∞ (T% σ)) {x : M}
    (hcl : ∀ u w s, c x u (c x w s) + c x w (c x u s) = -(2 * ⟪u, w⟫) • s)
    (hc : ∀ (Y : Π y : M, TangentSpace I y) (τ : Π y : M, V y), CMDiff ∞ (T% Y) →
      CMDiff ∞ (T% τ) → ∀ u, cov (fun y ↦ c y (Y y) (τ y)) x u =
        c x (leviCivitaConnection I M Y x u) (τ x) + c x (Y x) (cov τ x u))
    (hdiff : ∀ (Y : Π y : M, TangentSpace I y) (τ : Π y : M, V y), CMDiff ∞ (T% Y) →
      CMDiff ∞ (T% τ) → MDiffAt (T% (fun y ↦ c y (Y y) (τ y))) x)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.diracOperator c (cov.diracOperator c σ) x =
      cov.roughLaplacian (leviCivitaConnection I M) σ x +
        (2 : ℝ)⁻¹ • ∑ i, ∑ j, c x (b i) (c x (b j) (cov.curvatureTensor x (b i) (b j) (σ x))) := by
  -- Extend `b` to a geodesic frame.
  obtain ⟨e, he, hframe, hpar, hex⟩ :=
    TauCeti.Manifold.exists_contMDiff_geodesicFrame (I := I) (M := M) b
  have hσ' : CMDiff (∞ + 1) (T% σ) := by simpa using hσ
  have hτ (i : ι) : CMDiff ∞ (T% (fun y ↦ cov σ y (e i y))) :=
    cov.contMDiff_apply (he i) hσ'
  have hσ1 := diracOperator_diracOperator_eq_roughLaplacian_add_of_frame cov
    (leviCivitaConnection I M) c
    ((isTorsionFree_iff_torsion_eq_zero _).2
      (isLeviCivitaConnection_leviCivitaConnection I).torsion)
    hσ e he hframe hpar hcl
    (fun i u ↦ by simp [hc (e i) _ (he i) (hτ i), hpar i])
    (fun i ↦ hdiff (e i) _ (he i) (hτ i))
  simpa only [hex] using hσ1

/-- **The Weitzenböck formula over pairs `i < j`.** Under the hypotheses of
`diracOperator_diracOperator_eq_roughLaplacian_add`, for every orthonormal basis `eᵢ` of the
tangent space at `x` indexed by a linear order,

`D (D σ) = ∇*∇ σ + ∑_{i < j} c(eᵢ) c(eⱼ) R(eᵢ, eⱼ) σ`

at `x`. -/
theorem diracOperator_diracOperator_eq_roughLaplacian_add_sum_lt (hσ : CMDiff ∞ (T% σ)) {x : M}
    (hcl : ∀ u w s, c x u (c x w s) + c x w (c x u s) = -(2 * ⟪u, w⟫) • s)
    (hc : ∀ (Y : Π y : M, TangentSpace I y) (τ : Π y : M, V y), CMDiff ∞ (T% Y) →
      CMDiff ∞ (T% τ) → ∀ u, cov (fun y ↦ c y (Y y) (τ y)) x u =
        c x (leviCivitaConnection I M Y x u) (τ x) + c x (Y x) (cov τ x u))
    (hdiff : ∀ (Y : Π y : M, TangentSpace I y) (τ : Π y : M, V y), CMDiff ∞ (T% Y) →
      CMDiff ∞ (T% τ) → MDiffAt (T% (fun y ↦ c y (Y y) (τ y))) x)
    {ι : Type*} [Fintype ι] [LinearOrder ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.diracOperator c (cov.diracOperator c σ) x =
      cov.roughLaplacian (leviCivitaConnection I M) σ x +
        ∑ i, ∑ j with i < j, c x (b i) (c x (b j) (cov.curvatureTensor x (b i) (b j) (σ x))) := by
  rw [cov.diracOperator_diracOperator_eq_roughLaplacian_add c hσ hcl hc hdiff b]
  congr 1
  set f : ι → ι → V x := fun i j ↦ c x (b i) (c x (b j) (cov.curvatureTensor x (b i) (b j) (σ x)))
  -- The summand is symmetric in `(i, j)`, since `c(eⱼ) c(eᵢ) = -c(eᵢ) c(eⱼ)` for `i ≠ j` and the
  -- curvature is antisymmetric, and it vanishes on the diagonal.
  have hsymm (i j : ι) : f i j = f j i := by
    obtain rfl | hij := eq_or_ne i j
    · rfl
    have hanti := hcl (b i) (b j) (cov.curvatureTensor x (b i) (b j) (σ x))
    simp only [orthonormal_iff_ite.mp b.orthonormal i j, hij, ↓reduceIte, mul_zero, neg_zero,
      zero_smul, add_eq_zero_iff_eq_neg] at hanti
    simp only [f, cov.curvatureTensor_antisymm x (b j) (b i), LinearMap.neg_apply, map_neg, hanti]
  have hpairs : ∑ p : {p : ι × ι // p.1 < p.2}, f p.val.1 p.val.2 = ∑ i, ∑ j with i < j, f i j := by
    rw [← Finset.sum_subtype {p : ι × ι | p.1 < p.2} (by simp) fun p ↦ f p.1 p.2,
      Finset.sum_filter, Fintype.sum_prod_type]
    simp only [Finset.sum_filter]
  rw [TauCeti.sum_symmetric_pairs f hsymm, Finset.sum_eq_zero fun i _ ↦ by simp [f], zero_add,
    hpairs, ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_ofNat, inv_smul_smul₀ two_ne_zero]

end CovariantDerivative
