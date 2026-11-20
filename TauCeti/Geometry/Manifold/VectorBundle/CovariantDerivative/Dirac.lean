/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# The Dirac operator of a Clifford multiplication and a connection

Let `M` be a Riemannian manifold, `V` a real vector bundle over `M` with a connection `∇`, and
`c` a *Clifford multiplication*: a field of linear maps `c_x : T_x M → End (V_x)`. The **Dirac
operator** of `(c, ∇)` sends a section `σ` of `V` to the section

`D σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ`

for any orthonormal basis `eᵢ` of the tangent space at the point. At each point this is the metric
trace of the bilinear map `(u, w) ↦ c(u) (∇_w σ)`, the contraction of the `V`-valued one-form
`∇σ` against `c` through the canonical covariant tensor
`InnerProductSpace.canonicalCovariantTensor`. So the definition involves no choice of frame, and
every orthonormal frame computes it (`CovariantDerivative.diracOperator_eq_sum`).

When `V` is a Clifford module, `c(v)² = -|v|²`, and `∇` is compatible with `c` and the
Levi-Civita connection, this is the Dirac operator of spin geometry; for the spinor bundle of a
`Spinᶜ` structure and the connection induced by a connection `A` on its determinant line, it is
the operator `D_A` of the Seiberg–Witten equations. The properties proved here need neither the
Clifford relation nor the compatibility, except where stated:

* **Linearity.** `D` is additive and commutes with constant multiples on sections differentiable
  at the point (`CovariantDerivative.diracOperator_add`,
  `CovariantDerivative.diracOperator_const_smul`).
* **Locality.** `D σ x` depends only on `∇σ` at `x` (`CovariantDerivative.diracOperator_congr`),
  hence, for sections differentiable at the point, only on the germ of `σ` at `x`
  (`CovariantDerivative.diracOperator_congr_of_eventuallyEq`).
* **Leibniz rule.** For a function `f`, `D (f σ) = f D σ + c(grad f) σ`
  (`CovariantDerivative.diracOperator_smul`). So the commutator `[D, f]` is Clifford
  multiplication by `grad f`, which is the principal symbol of `D`
  (`CovariantDerivative.diracOperator_smul_sub`), and every double commutator `[[D, f], g]`
  vanishes: `D` has order one (`CovariantDerivative.diracOperator_smul_smul_sub`).
* **Ellipticity.** Under the Clifford relation `c(v) c(v) = -⟪v, v⟫`, the symbol `c(grad f)` is
  injective where `df ≠ 0`: if `[D, f] σ` vanishes at such a point, so does `σ`
  (`CovariantDerivative.eq_zero_of_diracOperator_smul_sub_eq_zero`).
* **Change of connection.** Adding to `∇` a one-form `A` with values in `End V` adds
  `∑ᵢ c(eᵢ) A(eᵢ)` to `D` (`CovariantDerivative.diracOperator_addOneForm`). For a one-form
  `A_x(σ_x) = ⟪u, ·⟫ v`, such as the change `A ↦ A + a` of the determinant connection of a
  `Spinᶜ` structure, the change is `c(u) v`
  (`CovariantDerivative.diracOperator_addOneForm_of_apply_eq_inner_smul`).
* **Gradings.** If an endomorphism `γ` anticommutes with Clifford multiplication and `∇σ` lies in
  its `a`-eigenspace at a point, then `D σ` lies in its `-a`-eigenspace there
  (`CovariantDerivative.apply_diracOperator_eq_neg_smul`).
* **Naturality.** A fibrewise linear map `L : V → W` that intertwines the Clifford multiplications
  and the connections intertwines the Dirac operators, `D_W (L σ) = L (D_V σ)`
  (`CovariantDerivative.diracOperator_linearMap_apply`). Gauge transformations commuting with `c`
  are the main instance. If `L` anticommutes with the Clifford multiplications instead, then
  `D_W (L σ) = -L (D_V σ)` (`CovariantDerivative.diracOperator_linearMap_apply_eq_neg`). This
  applies to a parallel grading `γ` anticommuting with `c`, such as the chirality of an
  even-dimensional Clifford module, and gives `D γ = -γ D`: the Dirac operator exchanges the two
  eigenbundles of `γ`.

## Main definitions

* `CovariantDerivative.diracOperator`: the Dirac operator `D σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ` at a point.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter II, §5 (Dirac operators of Clifford bundles).
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific, 2021,
  Definition 12.1.64 and Proposition 12.1.65.
* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators*, Springer, 1992,
  Section 3.3.
-/

public section

open Bundle Filter Topology
open scoped ContDiff Manifold RealInnerProductSpace

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
  (c : Π x : M, TangentSpace I x →ₗ[ℝ] Module.End ℝ (V x))
  {σ τ : Π y : M, V y} {x : M}

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The bilinear map `(u, w) ↦ c(u) (∇_w σ)` on the tangent space at `x`, whose metric trace is
the Dirac operator. -/
private def cliffordDerivative (σ : Π y : M, V y) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] V x :=
  LinearMap.mk₂ ℝ (fun u w ↦ c x u (cov σ x w))
    (fun u u' w ↦ by simp only [map_add, LinearMap.add_apply])
    (fun a u w ↦ by simp only [map_smul, LinearMap.smul_apply])
    (fun u w w' ↦ by simp only [map_add])
    (fun a u w ↦ by simp only [map_smul])

/-- The **Dirac operator** `D σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ` of the Clifford multiplication `c` and the
connection `∇`, at the point `x`: the metric trace of the bilinear map `(u, w) ↦ c(u) (∇_w σ)`
on the tangent space at `x`. In an orthonormal basis it is `∑ᵢ c(eᵢ) ∇_{eᵢ} σ`
(`diracOperator_eq_sum`). -/
def diracOperator (σ : Π y : M, V y) (x : M) : V x :=
  TensorProduct.lift (cliffordDerivative cov c σ x)
    (InnerProductSpace.canonicalCovariantTensor (TangentSpace I x))

/-- **Frame independence.** In every orthonormal basis `eᵢ` of the tangent space at `x`, the
Dirac operator is `D σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ`. -/
theorem diracOperator_eq_sum (σ : Π y : M, V y) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.diracOperator c σ x = ∑ i, c x (b i) (cov σ x (b i)) := by
  rw [diracOperator, InnerProductSpace.canonicalCovariantTensor_eq_sum _ b, map_sum]
  simp only [TensorProduct.lift.tmul, cliffordDerivative, LinearMap.mk₂_apply]

/-- The Dirac operator at `x` depends on `σ` only through its covariant derivative `∇σ` at `x`. -/
theorem diracOperator_congr (h : cov σ x = cov τ x) :
    cov.diracOperator c σ x = cov.diracOperator c τ x := by
  simp only [diracOperator_eq_sum cov c _ x (stdOrthonormalBasis ℝ _), h]

/-- **Locality.** For sections differentiable at `x`, the Dirac operator at `x` depends only on
their germ at `x`. -/
theorem diracOperator_congr_of_eventuallyEq (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x)
    (h : ∀ᶠ y in 𝓝 x, σ y = τ y) :
    cov.diracOperator c σ x = cov.diracOperator c τ x :=
  cov.diracOperator_congr c <|
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hσ hτ univ_mem h

/-- The Dirac operator of the zero section vanishes. -/
@[simp]
theorem diracOperator_zero [VectorBundle ℝ F V] (x : M) :
    cov.diracOperator c (0 : Π y : M, V y) x = 0 := by
  simp [diracOperator_eq_sum cov c _ x (stdOrthonormalBasis ℝ _)]

/-- The Dirac operator is additive on sections differentiable at the point. -/
theorem diracOperator_add (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    cov.diracOperator c (σ + τ) x = cov.diracOperator c σ x + cov.diracOperator c τ x := by
  simp only [diracOperator_eq_sum cov c _ x (stdOrthonormalBasis ℝ _),
    cov.isCovariantDerivativeOnUniv.add hσ hτ, add_apply, map_add,
    Finset.sum_add_distrib]

/-- The Dirac operator commutes with multiplication of a section by a constant. -/
theorem diracOperator_const_smul (a : ℝ) (hσ : MDiffAt (T% σ) x) :
    cov.diracOperator c (a • σ) x = a • cov.diracOperator c σ x := by
  simp only [diracOperator_eq_sum cov c _ x (stdOrthonormalBasis ℝ _),
    cov.isCovariantDerivativeOnUniv.smul_const a hσ, smul_apply, map_smul,
    Finset.smul_sum]

/-- The Dirac operator commutes with negation of a section differentiable at the point. -/
theorem diracOperator_neg (hσ : MDiffAt (T% σ) x) :
    cov.diracOperator c (-σ) x = -cov.diracOperator c σ x := by
  rw [← neg_one_smul ℝ σ, diracOperator_const_smul cov c _ hσ, neg_one_smul]

/-- The Dirac operator commutes with differences of sections differentiable at the point. -/
theorem diracOperator_sub [VectorBundle ℝ F V] (hσ : MDiffAt (T% σ) x)
    (hτ : MDiffAt (T% τ) x) :
    cov.diracOperator c (σ - τ) x = cov.diracOperator c σ x - cov.diracOperator c τ x := by
  rw [sub_eq_add_neg, diracOperator_add cov c hσ (mdifferentiableAt_neg_section hτ),
    diracOperator_neg cov c hτ, sub_eq_add_neg]

/-! ### The Leibniz rule and the principal symbol -/

section Leibniz

variable [IsManifold I 1 M] {f g : M → ℝ}

/-- **Leibniz rule for the Dirac operator.** For a function `f` and a section `σ` differentiable
at `x`, `D (f σ) = f D σ + c(grad f) σ` at `x`. -/
theorem diracOperator_smul (hf : MDiffAt f x) (hσ : MDiffAt (T% σ) x) :
    cov.diracOperator c (f • σ) x =
      f x • cov.diracOperator c σ x + c x (TauCeti.Manifold.mgradient I f x) (σ x) := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  -- `grad f = ∑ᵢ df(eᵢ) eᵢ`, so `c(grad f) σ = ∑ᵢ df(eᵢ) c(eᵢ) σ`.
  have hgrad : c x (TauCeti.Manifold.mgradient I f x) (σ x) =
      ∑ i, d% f x (b i) • c x (b i) (σ x) := by
    conv_lhs => rw [← b.sum_repr' (TauCeti.Manifold.mgradient I f x)]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      TauCeti.Manifold.inner_mgradient_right]
  rw [diracOperator_eq_sum cov c _ x b, diracOperator_eq_sum cov c _ x b, hgrad,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [cov.isCovariantDerivativeOnUniv.leibniz hσ hf]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul]

/-- **The principal symbol of the Dirac operator.** The commutator of `D` with multiplication by a
function `f` is Clifford multiplication by its gradient: `D (f σ) - f D σ = c(grad f) σ`. -/
theorem diracOperator_smul_sub (hf : MDiffAt f x) (hσ : MDiffAt (T% σ) x) :
    cov.diracOperator c (f • σ) x - f x • cov.diracOperator c σ x =
      c x (TauCeti.Manifold.mgradient I f x) (σ x) := by
  rw [diracOperator_smul cov c hf hσ, add_sub_cancel_left]

/-- **The Dirac operator has order one.** Every double commutator of `D` with multiplications by
functions vanishes: `D (f g σ) - f D (g σ) - g D (f σ) + f g D σ = 0`. -/
theorem diracOperator_smul_smul_sub [VectorBundle ℝ F V] (hf : MDiffAt f x) (hg : MDiffAt g x)
    (hσ : MDiffAt (T% σ) x) :
    cov.diracOperator c (f • g • σ) x - f x • cov.diracOperator c (g • σ) x -
        g x • cov.diracOperator c (f • σ) x + (f x * g x) • cov.diracOperator c σ x = 0 := by
  rw [diracOperator_smul cov c hf (hg.smul_section hσ), diracOperator_smul cov c hg hσ,
    diracOperator_smul cov c hf hσ, Pi.smul_apply', map_smul]
  module

/-- **Ellipticity of the Dirac operator.** If the Clifford multiplication satisfies the Clifford
relation `c(v) c(v) = -⟪v, v⟫` at `x` and `df ≠ 0` at `x`, then the commutator `[D, f] σ` vanishes
at `x` only if `σ` does: the principal symbol `c(grad f)` is injective. -/
theorem eq_zero_of_diracOperator_smul_sub_eq_zero
    (hc : ∀ (v : TangentSpace I x) (s : V x), c x v (c x v s) = -⟪v, v⟫ • s)
    (hf : MDiffAt f x) (hσ : MDiffAt (T% σ) x) (hdf : TauCeti.Manifold.mgradient I f x ≠ 0)
    (h : cov.diracOperator c (f • σ) x - f x • cov.diracOperator c σ x = 0) :
    σ x = 0 := by
  rw [diracOperator_smul_sub cov c hf hσ] at h
  have h2 := hc (TauCeti.Manifold.mgradient I f x) (σ x)
  rw [h, map_zero, eq_comm, neg_smul, neg_eq_zero] at h2
  exact (smul_eq_zero.1 h2).resolve_left (inner_self_ne_zero.2 hdf)

end Leibniz

/-! ### Change of connection -/

/-- **Change of connection.** Adding to `∇` a one-form `A` with values in the endomorphisms of `V`
adds `∑ᵢ c(eᵢ) A(eᵢ)` to the Dirac operator, for any orthonormal basis `eᵢ` of the tangent space
at `x`. -/
theorem diracOperator_addOneForm (A : Π x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x)
    (σ : Π y : M, V y) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    (cov.addOneForm A).diracOperator c σ x =
      cov.diracOperator c σ x + ∑ i, c x (b i) (A x (σ x) (b i)) := by
  rw [diracOperator_eq_sum _ c _ x b, diracOperator_eq_sum cov c _ x b, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [addOneForm_apply, add_apply, map_add]

/-- **Change of connection by a scalar one-form.** If the one-form `A` acts on `σ` at `x` by
`A_x(σ_x)(w) = ⟪u, w⟫ v`, then adding it to `∇` adds `c(u) v` to the Dirac operator at `x`. For
`v = σ_x` this is the change `D_{∇ + u♭} = D_∇ + c(u)` under the addition of a real one-form;
for the spinors of a `Spinᶜ` structure and an imaginary one-form `i a` added to the determinant
connection, `v = (i / 2) σ_x`. -/
theorem diracOperator_addOneForm_of_apply_eq_inner_smul
    (A : Π x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x) {u : TangentSpace I x} {v : V x}
    (hA : ∀ w, A x (σ x) w = ⟪u, w⟫ • v) :
    (cov.addOneForm A).diracOperator c σ x = cov.diracOperator c σ x + c x u v := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [diracOperator_addOneForm cov c A σ x b]
  congr 1
  conv_rhs => rw [← b.sum_repr' u]
  simp only [hA, map_smul, map_sum, LinearMap.sum_apply, LinearMap.smul_apply, real_inner_comm u]

/-! ### Gradings -/

/-- **The Dirac operator exchanges the eigenspaces of a grading.** Let `γ` be an endomorphism of
the fibre at `x` anticommuting with Clifford multiplication, `γ c(v) = -c(v) γ`. If every
covariant derivative `∇_w σ` at `x` is an eigenvector of `γ` with eigenvalue `a`, then `D σ` at `x`
is an eigenvector with eigenvalue `-a`. For a parallel grading `γ` and a section `σ` of its
`±1`-eigenbundle, `∇σ` lies in the same eigenbundle, so `D σ` lies in the other one: this is the
block form of the Dirac operator of a graded Clifford module. -/
theorem apply_diracOperator_eq_neg_smul (γ : Module.End ℝ (V x)) (a : ℝ)
    (hc : ∀ (v : TangentSpace I x) (s : V x), γ (c x v s) = -c x v (γ s))
    (hσ : ∀ w, γ (cov σ x w) = a • cov σ x w) :
    γ (cov.diracOperator c σ x) = -(a • cov.diracOperator c σ x) := by
  rw [diracOperator_eq_sum cov c σ x (stdOrthonormalBasis ℝ _), map_sum, Finset.smul_sum,
    ← Finset.sum_neg_distrib]
  simp only [hc, hσ, map_smul]

/-! ### Naturality -/

section Naturality

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul ℝ (W x)]
  [FiberBundle F' W]
  (covW : _root_.CovariantDerivative I F' W)
  (cW : Π x : M, TangentSpace I x →ₗ[ℝ] Module.End ℝ (W x))
  (L : Π x : M, V x →ₗ[ℝ] W x)

/-- **Naturality of the Dirac operator.** Let `L` be a fibrewise linear map from `V` to `W` which
intertwines the Clifford multiplications at `x`, `L c_V(v) = c_W(v) L`, and the connections along
`σ` at `x`, `∇^W (L σ) = L ∇^V σ`. Then `D_W (L σ) = L (D_V σ)` at `x`. For `L` a gauge
transformation commuting with the Clifford multiplication, and `∇^W` the transformed connection,
this is the gauge covariance of the Dirac operator. -/
theorem diracOperator_linearMap_apply
    (hc : ∀ (v : TangentSpace I x) (s : V x), L x (c x v s) = cW x v (L x s))
    (hL : ∀ w, covW (fun y ↦ L y (σ y)) x w = L x (cov σ x w)) :
    covW.diracOperator cW (fun y ↦ L y (σ y)) x = L x (cov.diracOperator c σ x) := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [diracOperator_eq_sum covW cW _ x b, diracOperator_eq_sum cov c _ x b, map_sum]
  simp only [hL, hc]

/-- **Anti-naturality of the Dirac operator.** If the fibrewise linear map `L` anticommutes with
the Clifford multiplications at `x`, `L c_V(v) = -c_W(v) L`, and intertwines the connections along
`σ` at `x`, then `D_W (L σ) = -L (D_V σ)` at `x`. For a parallel grading `γ` of `V` anticommuting
with Clifford multiplication, such as the chirality of an even-dimensional Clifford module, this
says `D γ = -γ D`. -/
theorem diracOperator_linearMap_apply_eq_neg
    (hc : ∀ (v : TangentSpace I x) (s : V x), L x (c x v s) = -cW x v (L x s))
    (hL : ∀ w, covW (fun y ↦ L y (σ y)) x w = L x (cov σ x w)) :
    covW.diracOperator cW (fun y ↦ L y (σ y)) x = -L x (cov.diracOperator c σ x) := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [diracOperator_eq_sum covW cW _ x b, diracOperator_eq_sum cov c _ x b, map_sum,
    ← Finset.sum_neg_distrib]
  simp only [hL, hc, neg_neg]

end Naturality

end CovariantDerivative
