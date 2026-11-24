/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Dirac.Basic

/-!
# The square of a Dirac operator split along a unit vector field

Let `D σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ` be the Dirac operator of a connection `∇` and a Clifford
multiplication `c` on a vector bundle over a Riemannian manifold
(`CovariantDerivative.diracOperator`), and let `T` be a vector field of unit length. Separating
the direction `T` splits the Dirac operator as

`D σ = c(T) ∇_T σ + B_T σ`,

where the **transverse Dirac operator** `B_T σ = D σ - c(T) ∇_T σ`
(`CovariantDerivative.transverseDiracOperator`) only differentiates in directions orthogonal to
`T`: in an orthonormal basis `(T, e₁, …, eₖ)` it is `∑ᵢ c(eᵢ) ∇_{eᵢ} σ`
(`CovariantDerivative.transverseDiracOperator_eq_sum`).

On a product `X = S¹ × Y` with the product metric and `T = ∂ₛ`, this is the splitting
`D = c(ds) ∇_T + B_A` of the Seiberg–Witten Dirac operator, and its square is

`D² = -∇_T² + B_T² + c(T) ∑ᵢ c(eᵢ) R(T, eᵢ)`,

where `eᵢ` completes `T` to an orthonormal frame and `R` is the curvature of `∇`
(`CovariantDerivative.curvatureOperator`). For the spin connection of a unitary connection `A`
on the determinant line, the Riemannian part of `R(T, eᵢ)` vanishes on a product and
`R(T, eᵢ) = F_A(T, eᵢ) / 2`, so that the last term is `(1 / 2) c₂(ds ∧ ι_T F_A)`; that
identification of the curvature is not made here. The pairing of this term with a Seiberg–Witten
spinor is computed in
`TauCeti.SeibergWitten.re_inner_I_div_two_smul_ι_mul_ι_twoVectorContraction`.

The identity rests on two properties of the product, assumed here at a single point `x`:

* Clifford multiplication by `T` anticommutes with Clifford multiplication by covectors
  orthogonal to `T` and squares to `-1`: the Clifford relation
  `c(u) c(T) + c(T) c(u) = -2 ⟪u, T⟫`, together with `‖T x‖ = 1`;
* `c(T)` is parallel, `∇ (c(T) τ) = c(T) ∇ τ`, which holds when `T` is parallel and `c` is
  compatible with `∇` and the Levi-Civita connection.

Under these, Clifford multiplication by `T` anticommutes with the Dirac operator up to a
derivative along `T`: `D (c(T) τ) = -c(T) D τ - 2 ∇_T τ`
(`CovariantDerivative.diracOperator_clifford_eq`). Expanding `D (D σ)` then gives

`D² σ = -∇_T ∇_T σ + B_T (B_T σ) + c(T) (∇_T (B_T σ) - B_T (∇_T σ))`

(`CovariantDerivative.diracOperator_diracOperator_eq`). The commutator of `∇_T` with `B_T` is a
curvature term: if near `x` the fields `T, e₁, …, eₖ` form an orthonormal frame, each `c(eᵢ)` is
parallel along `T` at `x` and the brackets `[T, eᵢ]` vanish at `x`, as for the coordinate
field `∂ₛ` and fields lifted from `Y`, then

`∇_T (B_T σ) - B_T (∇_T σ) = ∑ᵢ c(eᵢ) R(T, eᵢ) σ`

at `x` (`CovariantDerivative.covariantDerivative_transverseDiracOperator_sub_eq_sum`), and the
square of the Dirac operator is the displayed product formula
(`CovariantDerivative.diracOperator_diracOperator_eq_sum_curvatureOperator`).

## Main definitions

* `CovariantDerivative.transverseDiracOperator`: the transverse Dirac operator
  `B_T σ = D σ - c(T) ∇_T σ`.

## Main results

* `CovariantDerivative.transverseDiracOperator_eq_sum`: `B_T σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ` in an
  orthonormal basis `(T, e₁, …, eₖ)`.
* `CovariantDerivative.transverseDiracOperator_add`, `transverseDiracOperator_smul` and their
  companions: linearity and the Leibniz rule
  `B_T (f σ) = f B_T σ + c(grad f) σ - df(T) c(T) σ`.
* `CovariantDerivative.diracOperator_clifford_eq`: `D (c(T) τ) = -c(T) D τ - 2 ∇_T τ`.
* `CovariantDerivative.diracOperator_diracOperator_eq`:
  `D² σ = -∇_T ∇_T σ + B_T² σ + c(T) (∇_T (B_T σ) - B_T (∇_T σ))`.
* `CovariantDerivative.covariantDerivative_transverseDiracOperator_sub_eq_sum`: the commutator
  `∇_T B_T - B_T ∇_T` is `∑ᵢ c(eᵢ) R(T, eᵢ)` in a frame commuting with `T`.
* `CovariantDerivative.diracOperator_diracOperator_eq_sum_curvatureOperator`:
  `D² σ = -∇_T ∇_T σ + B_T² σ + c(T) ∑ᵢ c(eᵢ) R(T, eᵢ) σ`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter II, §5 and §8 (Dirac operators of Clifford bundles and their squares).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §5.2.
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold RealInnerProductSpace Topology

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V]
  (cov : _root_.CovariantDerivative I F V)
  (c : Π x : M, TangentSpace I x →L[ℝ] V x →L[ℝ] V x)
  (T : Π x : M, TangentSpace I x)
  {σ τ : Π y : M, V y}

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The **transverse Dirac operator** `B_T σ = D σ - c(T) ∇_T σ` of a connection `∇` and a
Clifford multiplication `c`, along a vector field `T`. When `T` has unit length, it is the part
of the Dirac operator differentiating orthogonally to `T`: in an orthonormal basis
`(T, e₁, …, eₖ)` it is `∑ᵢ c(eᵢ) ∇_{eᵢ} σ` (`transverseDiracOperator_eq_sum`). -/
def transverseDiracOperator (σ : Π y : M, V y) (x : M) : V x :=
  cov.diracOperator c σ x - c x (T x) (cov σ x (T x))

theorem transverseDiracOperator_def (σ : Π y : M, V y) (x : M) :
    cov.transverseDiracOperator c T σ x =
      cov.diracOperator c σ x - c x (T x) (cov σ x (T x)) :=
  (rfl)

/-- **Splitting the Dirac operator along `T`.** `D σ = c(T) ∇_T σ + B_T σ`. -/
theorem diracOperator_eq_add_transverseDiracOperator (σ : Π y : M, V y) (x : M) :
    cov.diracOperator c σ x =
      c x (T x) (cov σ x (T x)) + cov.transverseDiracOperator c T σ x := by
  rw [transverseDiracOperator_def, add_sub_cancel]

/-- The transverse Dirac operator of the zero section is zero. -/
@[simp]
theorem transverseDiracOperator_zero [VectorBundle ℝ F V] (x : M) :
    cov.transverseDiracOperator c T (0 : Π y : M, V y) x = 0 := by
  simp [transverseDiracOperator_def]

/-- The transverse Dirac operator is additive on sections differentiable at the point. -/
theorem transverseDiracOperator_add {x : M} (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    cov.transverseDiracOperator c T (σ + τ) x =
      cov.transverseDiracOperator c T σ x + cov.transverseDiracOperator c T τ x := by
  simp only [transverseDiracOperator_def, cov.diracOperator_add c hσ hτ,
    cov.isCovariantDerivativeOnUniv.add hσ hτ, add_apply, map_add]
  abel

/-- The transverse Dirac operator commutes with multiplication of a differentiable section by a
constant. -/
theorem transverseDiracOperator_const_smul {x : M} (a : ℝ) (hσ : MDiffAt (T% σ) x) :
    cov.transverseDiracOperator c T (a • σ) x = a • cov.transverseDiracOperator c T σ x := by
  simp only [transverseDiracOperator_def, cov.diracOperator_const_smul c a hσ,
    cov.isCovariantDerivativeOnUniv.smul_const a hσ, smul_apply, map_smul, smul_sub]

/-- The transverse Dirac operator commutes with negation of a differentiable section. -/
theorem transverseDiracOperator_neg {x : M} (hσ : MDiffAt (T% σ) x) :
    cov.transverseDiracOperator c T (-σ) x = -cov.transverseDiracOperator c T σ x := by
  rw [← neg_one_smul ℝ σ, cov.transverseDiracOperator_const_smul c T (-1) hσ, neg_one_smul]

/-- The transverse Dirac operator commutes with differences of differentiable sections. -/
theorem transverseDiracOperator_sub [VectorBundle ℝ F V] {x : M} (hσ : MDiffAt (T% σ) x)
    (hτ : MDiffAt (T% τ) x) :
    cov.transverseDiracOperator c T (σ - τ) x =
      cov.transverseDiracOperator c T σ x - cov.transverseDiracOperator c T τ x := by
  rw [sub_eq_add_neg, cov.transverseDiracOperator_add c T hσ (mdifferentiableAt_neg_section hτ),
    cov.transverseDiracOperator_neg c T hτ, sub_eq_add_neg]

/-- **The Leibniz rule for the transverse Dirac operator.** For a function `f` and a section
`σ`, both differentiable at `x`, `B_T (f σ) = f B_T σ + c(grad f) σ - df(T) c(T) σ`: the
commutator of `B_T` with multiplication by `f` is Clifford multiplication by the part
`grad f - df(T) T` of the gradient transverse to a unit vector `T`. -/
theorem transverseDiracOperator_smul [IsManifold I 1 M] {f : M → ℝ} {x : M} (hf : MDiffAt f x)
    (hσ : MDiffAt (T% σ) x) :
    cov.transverseDiracOperator c T (f • σ) x =
      f x • cov.transverseDiracOperator c T σ x +
        c x (TauCeti.Manifold.mgradient I f x) (σ x) - d% f x (T x) • c x (T x) (σ x) := by
  simp only [transverseDiracOperator_def, cov.diracOperator_smul c hf hσ,
    cov.isCovariantDerivativeOnUniv.leibniz hσ hf, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul]
  module

/-- **The transverse Dirac operator in an orthonormal frame.** If `b` is an orthonormal basis of
the tangent space at `x`, indexed by `Option ι`, whose vector `b none` is `T x`, then
`B_T σ = ∑ᵢ c(b i) ∇_{b i} σ`, the sum running over the remaining basis vectors. -/
theorem transverseDiracOperator_eq_sum (σ : Π y : M, V y) {x : M} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis (Option ι) ℝ (TangentSpace I x)) (hb : b none = T x) :
    cov.transverseDiracOperator c T σ x = ∑ i, c x (b (some i)) (cov σ x (b (some i))) := by
  rw [transverseDiracOperator_def, diracOperator_eq_sum cov c σ x b, Fintype.sum_option, hb,
    add_sub_cancel_left]

/-- **Clifford multiplication by `T` anticommutes with the Dirac operator up to `∇_T`.** Suppose
that at `x` Clifford multiplication satisfies the Clifford relation
`c(u) c(T) + c(T) c(u) = -2 ⟪u, T⟫` with `T`, and that `c(T)` is parallel at `x`,
`∇ (c(T) τ) = c(T) ∇ τ`. Then `D (c(T) τ) = -c(T) D τ - 2 ∇_T τ` at `x`. -/
theorem diracOperator_clifford_eq {x : M}
    (hc : ∀ u w, c x u (c x (T x) w) + c x (T x) (c x u w) = -(2 * ⟪u, T x⟫) • w)
    (hT : cov (fun y ↦ c y (T y) (τ y)) x = c x (T x) ∘L cov τ x) :
    cov.diracOperator c (fun y ↦ c y (T y) (τ y)) x =
      -c x (T x) (cov.diracOperator c τ x) - (2 : ℝ) • cov τ x (T x) := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  -- Each term `c(eᵢ) c(T) ∇_{eᵢ} τ` is `-c(T) c(eᵢ) ∇_{eᵢ} τ - 2 ⟪eᵢ, T⟫ ∇_{eᵢ} τ`, and the
  -- second parts sum to `-2 ∇_T τ` since `T = ∑ᵢ ⟪eᵢ, T⟫ eᵢ`.
  have hterm (i) : c x (b i) (c x (T x) (cov τ x (b i))) =
      -c x (T x) (c x (b i) (cov τ x (b i))) - (2 : ℝ) • cov τ x (⟪b i, T x⟫ • b i) := by
    rw [map_smul, smul_smul]
    linear_combination (norm := module) hc (b i) (cov τ x (b i))
  rw [diracOperator_eq_sum cov c _ x b, diracOperator_eq_sum cov c τ x b, hT]
  simp only [ContinuousLinearMap.comp_apply, hterm, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, ← map_sum, ← Finset.smul_sum, b.sum_repr']

/-- **The square of the Dirac operator split along a unit vector field.** Suppose that at `x`
the vector `T x` has unit length, Clifford multiplication satisfies the Clifford relation
`c(u) c(T) + c(T) c(u) = -2 ⟪u, T⟫` with `T`, and `c(T)` is parallel on the section `∇_T σ`.
If `c(T) ∇_T σ` and `B_T σ` are differentiable at `x`, then at `x`

`D (D σ) = -∇_T ∇_T σ + B_T (B_T σ) + c(T) (∇_T (B_T σ) - B_T (∇_T σ))`. -/
theorem diracOperator_diracOperator_eq {x : M} (hTx : ‖T x‖ = 1)
    (hc : ∀ u w, c x u (c x (T x) w) + c x (T x) (c x u w) = -(2 * ⟪u, T x⟫) • w)
    (hT : cov (fun y ↦ c y (T y) (cov σ y (T y))) x =
      c x (T x) ∘L cov (fun y ↦ cov σ y (T y)) x)
    (h₁ : MDiffAt (T% (fun y ↦ c y (T y) (cov σ y (T y)))) x)
    (h₂ : MDiffAt (T% (cov.transverseDiracOperator c T σ)) x) :
    cov.diracOperator c (cov.diracOperator c σ) x =
      -cov (fun y ↦ cov σ y (T y)) x (T x) +
        cov.transverseDiracOperator c T (cov.transverseDiracOperator c T σ) x +
          c x (T x) (cov (cov.transverseDiracOperator c T σ) x (T x) -
            cov.transverseDiracOperator c T (fun y ↦ cov σ y (T y)) x) := by
  -- Clifford multiplication by the unit vector `T x` squares to `-1`.
  have hsq (w : V x) : c x (T x) (c x (T x) w) = -w := by
    have h := hc (T x) w
    rw [real_inner_self_eq_norm_sq, hTx] at h
    linear_combination (norm := module) (2⁻¹ : ℝ) • h
  have hD : cov.diracOperator c σ =
      (fun y ↦ c y (T y) (cov σ y (T y))) + cov.transverseDiracOperator c T σ :=
    funext fun y ↦ cov.diracOperator_eq_add_transverseDiracOperator c T σ y
  rw [hD, cov.diracOperator_add c h₁ h₂, cov.diracOperator_clifford_eq c T hc hT,
    cov.diracOperator_eq_add_transverseDiracOperator c T (fun y ↦ cov σ y (T y)) x,
    cov.diracOperator_eq_add_transverseDiracOperator c T (cov.transverseDiracOperator c T σ) x,
    map_add, hsq, map_sub]
  module

/-- **The commutator of `∇_T` with the transverse Dirac operator is a curvature term.** Let
`e₁, …, eₖ` be vector fields which, together with `T`, form an orthonormal frame near `x`.
Suppose that at `x` each `c(eᵢ)` is parallel along `T` on the section `∇_{eᵢ} σ` and each
bracket `[T, eᵢ]` vanishes. If `B_T σ` and the sections `c(eᵢ) ∇_{eᵢ} σ` are differentiable at
`x`, then at `x`

`∇_T (B_T σ) - B_T (∇_T σ) = ∑ᵢ c(eᵢ) R(T, eᵢ) σ`. -/
theorem covariantDerivative_transverseDiracOperator_sub_eq_sum [VectorBundle ℝ F V]
    {ι : Type*} [Fintype ι] (e : ι → Π y : M, TangentSpace I y) {x : M}
    (hframe : ∀ᶠ y in 𝓝 x, ∃ b : OrthonormalBasis (Option ι) ℝ (TangentSpace I y),
      b none = T y ∧ ∀ i, b (some i) = e i y)
    (hpar : ∀ i, cov (fun y ↦ c y (e i y) (cov σ y (e i y))) x (T x) =
      c x (e i x) (cov (fun y ↦ cov σ y (e i y)) x (T x)))
    (hbr : ∀ i, VectorField.mlieBracket I T (e i) x = 0)
    (hdiff : ∀ i, MDiffAt (T% (fun y ↦ c y (e i y) (cov σ y (e i y)))) x)
    (hB : MDiffAt (T% (cov.transverseDiracOperator c T σ)) x) :
    cov (cov.transverseDiracOperator c T σ) x (T x) -
        cov.transverseDiracOperator c T (fun y ↦ cov σ y (T y)) x =
      ∑ i, c x (e i x) (curvatureOperator cov T (e i) σ x) := by
  -- Near `x` the transverse Dirac operator of `σ` is the frame sum `∑ᵢ c(eᵢ) ∇_{eᵢ} σ`.
  set S : ι → Π y : M, V y := fun i y ↦ c y (e i y) (cov σ y (e i y)) with hS
  have hsum : ∀ᶠ y in 𝓝 x, cov.transverseDiracOperator c T σ y = (∑ i, S i) y := by
    filter_upwards [hframe] with y ⟨b, hb, he⟩
    rw [cov.transverseDiracOperator_eq_sum c T σ b hb, Finset.sum_apply]
    simp only [he, hS]
  have hsumdiff : MDiffAt (T% (∑ i, S i)) x := by
    simpa [Finset.sum_apply] using
      MDifferentiableAt.sum_section (s := Finset.univ) fun i _ ↦ hdiff i
  obtain ⟨b, hb, he⟩ := hframe.self_of_nhds
  rw [cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hB hsumdiff univ_mem hsum,
    cov.isCovariantDerivativeOnUniv.sum fun i _ ↦ hdiff i,
    cov.transverseDiracOperator_eq_sum c T _ b hb]
  simp only [he, FunLike.coe_sum, Finset.sum_apply, hpar, ← Finset.sum_sub_distrib,
    ← map_sub, curvatureOperator_def, hbr, map_zero, sub_zero]

/-- **The square of the Dirac operator on a product.** Let `T` be a vector field and
`e₁, …, eₖ` vector fields forming with `T` an orthonormal frame near `x`. Suppose that at `x`
Clifford multiplication satisfies the Clifford relation `c(u) c(T) + c(T) c(u) = -2 ⟪u, T⟫` with
`T`, that `c(T)` is parallel on `∇_T σ` and each `c(eᵢ)` parallel along `T` on `∇_{eᵢ} σ`, and that
the brackets `[T, eᵢ]` vanish. Under the differentiability hypotheses at `x`, the square of the
Dirac operator is

`D (D σ) = -∇_T ∇_T σ + B_T (B_T σ) + c(T) ∑ᵢ c(eᵢ) R(T, eᵢ) σ`

at `x`. These are the hypotheses met by the coordinate field `T = ∂ₛ` of a product `S¹ × Y`
with the product metric, fields `eᵢ` lifted from an orthonormal frame of `Y`, and a Clifford
multiplication compatible with `∇` and the Levi-Civita connection; checking them in that
setting is not done here. -/
theorem diracOperator_diracOperator_eq_sum_curvatureOperator [VectorBundle ℝ F V]
    {ι : Type*} [Fintype ι] (e : ι → Π y : M, TangentSpace I y) {x : M}
    (hframe : ∀ᶠ y in 𝓝 x, ∃ b : OrthonormalBasis (Option ι) ℝ (TangentSpace I y),
      b none = T y ∧ ∀ i, b (some i) = e i y)
    (hc : ∀ u w, c x u (c x (T x) w) + c x (T x) (c x u w) = -(2 * ⟪u, T x⟫) • w)
    (hT : cov (fun y ↦ c y (T y) (cov σ y (T y))) x =
      c x (T x) ∘L cov (fun y ↦ cov σ y (T y)) x)
    (hpar : ∀ i, cov (fun y ↦ c y (e i y) (cov σ y (e i y))) x (T x) =
      c x (e i x) (cov (fun y ↦ cov σ y (e i y)) x (T x)))
    (hbr : ∀ i, VectorField.mlieBracket I T (e i) x = 0)
    (h₁ : MDiffAt (T% (fun y ↦ c y (T y) (cov σ y (T y)))) x)
    (hdiff : ∀ i, MDiffAt (T% (fun y ↦ c y (e i y) (cov σ y (e i y)))) x)
    (hB : MDiffAt (T% (cov.transverseDiracOperator c T σ)) x) :
    cov.diracOperator c (cov.diracOperator c σ) x =
      -cov (fun y ↦ cov σ y (T y)) x (T x) +
        cov.transverseDiracOperator c T (cov.transverseDiracOperator c T σ) x +
          c x (T x) (∑ i, c x (e i x) (curvatureOperator cov T (e i) σ x)) := by
  -- The unit length of `T x` is the norm of the basis vector `b none`.
  obtain ⟨b, hb, -⟩ := hframe.self_of_nhds
  have hTx : ‖T x‖ = 1 := hb ▸ b.orthonormal.1 none
  rw [cov.diracOperator_diracOperator_eq c T hTx hc hT h₁ hB,
    cov.covariantDerivative_transverseDiracOperator_sub_eq_sum c T e hframe hpar hbr hdiff hB]

end CovariantDerivative
