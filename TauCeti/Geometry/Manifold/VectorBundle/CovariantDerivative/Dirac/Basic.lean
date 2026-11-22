/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Trace.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# The Dirac operator of a connection and a Clifford multiplication

Let `V` be a vector bundle over a Riemannian manifold `M`, with a connection `∇` and a
*Clifford multiplication* `c`, a family of linear maps `c x : T_x M → End (V x)`. The
**Dirac operator** of `(∇, c)` sends a section `σ` to the metric contraction of the bilinear map
`(u, w) ↦ c(u) (∇_w σ)`,

`D σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ`,

for any orthonormal basis `eᵢ` of the tangent space (`CovariantDerivative.diracOperator_eq_sum`).
The contraction is the metric trace `LinearMap.BilinMap.metricTrace`, against the canonical
covariant tensor `InnerProductSpace.canonicalCovariantTensor`, so the definition involves no
choice of frame (`CovariantDerivative.diracOperator_def`).

When `V` is a Hermitian Clifford module, so that `c(v)² = -‖v‖²` and each `c(v)` is
skew-adjoint, and `∇` is compatible with `c` and the Levi-Civita connection, this is the Dirac
operator of the Clifford module. For the spinor bundle of a `Spinᶜ` structure on a
four-manifold and the spin connection `∇_A` of a unitary connection `A` on its determinant line,
its restriction to the positive spinors is the Dirac operator `D_A` of the Seiberg–Witten
equations. None of these hypotheses is used by the first-order calculus of this file:

* `D` is additive on differentiable sections and commutes with constants
  (`diracOperator_add`, `diracOperator_const_smul`).
* **Locality.** `D σ x` depends only on `∇σ` at `x` (`diracOperator_congr`), hence, for sections
  differentiable at the point, only on the germ of `σ` at `x`
  (`diracOperator_congr_of_eventuallyEq`).
* **Leibniz rule.** For a differentiable function `f`,
  `D (f σ) = f D σ + c(grad f) σ` (`diracOperator_smul`). So the commutator of `D` with
  multiplication by `f` is the operator of order zero `c(grad f)` (`diracOperator_smul_sub`):
  the principal symbol of `D` at a covector `ξ` is Clifford multiplication by its metric dual
  `ξ♯`, in the geometric convention. Every double commutator `[[D, f], g]` vanishes, so `D` has
  order one (`diracOperator_smul_smul_sub`).
* **Ellipticity.** Under the Clifford relation `c(v) c(v) = -⟪v, v⟫`, the symbol `c(grad f)` is
  injective where `df ≠ 0`: if `[D, f] σ` vanishes at such a point, so does `σ`
  (`eq_zero_of_diracOperator_smul_sub_eq_zero`).
* **Gradings.** If an endomorphism `γ` anticommutes with Clifford multiplication and `∇σ` lies in
  its `a`-eigenspace at a point, then `D σ` lies in its `-a`-eigenspace there
  (`apply_diracOperator_eq_neg_smul`).
* **Naturality.** If `∇' τ = g ∘ ∇ σ` at `x` for an endomorphism `g` commuting with Clifford
  multiplication, then `D' τ = g (D σ)` (`diracOperator_eq_apply_of_eq_comp`); this is the gauge
  covariance of `D`. More generally, a fibrewise linear map `L : V → W` that intertwines the
  Clifford multiplications and the connections intertwines the Dirac operators,
  `D_W (L σ) = L (D_V σ)` (`diracOperator_linearMap_apply`). If `L` anticommutes with the Clifford
  multiplications instead, then `D_W (L σ) = -L (D_V σ)`
  (`diracOperator_linearMap_apply_eq_neg`); for a parallel grading `γ` anticommuting with `c`,
  such as the chirality of an even-dimensional Clifford module, this gives `D γ = -γ D`.
* **Change of connection.** Adding to `∇` a one-form `A` with values in the endomorphisms of `V`
  adds the term of order zero `∑ᵢ c(eᵢ) A(eᵢ)`, the metric trace of `(u, w) ↦ c(u) A(w)`, to `D`
  (`diracOperator_addOneForm`). When `A(w) σ = θ(w) L σ` at `x` for a real one-form `θ` and an
  endomorphism `L`, this term is `c(θ♯) L σ`
  (`diracOperator_addOneForm_of_forall_apply_eq`). For the spin connection of `A + a`, with `a`
  an imaginary one-form on the determinant line, `∇_{A + a} = ∇_A + a / 2`, so this is the law
  `D_{A + a} = D_A + c(a) / 2`. More generally, if `A_x(σ_x) = ⟪u, ·⟫ v`, the change is `c(u) v`
  (`diracOperator_addOneForm_of_apply_eq_inner_smul`).

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter II, §5 (Dirac operators of Clifford bundles).
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific,
  Definition 12.1.64 and Proposition 12.1.65.
* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators*, Springer, 1992,
  Section 3.3.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Princeton University Press, 1996, §3.1.
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
  (c : Π x : M, TangentSpace I x →L[ℝ] V x →L[ℝ] V x)
  {σ τ : Π y : M, V y}

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The **Dirac operator** `D σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ` of a connection `∇` and a Clifford
multiplication `c` at `x`: the metric contraction of the bilinear map `(u, w) ↦ c(u) (∇_w σ)`
on the tangent space (`diracOperator_def`). In an orthonormal basis it is the sum
`∑ᵢ c(eᵢ) ∇_{eᵢ} σ` (`diracOperator_eq_sum`). -/
def diracOperator (σ : Π y : M, V y) (x : M) : V x :=
  LinearMap.BilinMap.metricTrace
    ((ContinuousLinearMap.toLinearMap₁₂ (c x)).compl₂ (cov σ x).toLinearMap)

/-- The Dirac operator is the metric trace of the Clifford pairing `(u, w) ↦ c(u) (∇_w σ)`,
the bilinear map `c x` precomposed in its second argument with `∇ σ x`. -/
theorem diracOperator_def (σ : Π y : M, V y) (x : M) :
    cov.diracOperator c σ x = LinearMap.BilinMap.metricTrace
      ((ContinuousLinearMap.toLinearMap₁₂ (c x)).compl₂ (cov σ x).toLinearMap) := by
  rw [diracOperator]

/-- **The Dirac operator in an orthonormal frame.** For every orthonormal basis `eᵢ` of the
tangent space at `x`, `D σ = ∑ᵢ c(eᵢ) ∇_{eᵢ} σ`. In particular the sum does not depend on the
basis. -/
theorem diracOperator_eq_sum (σ : Π y : M, V y) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.diracOperator c σ x = ∑ i, c x (b i) (cov σ x (b i)) := by
  rw [diracOperator_def, LinearMap.BilinMap.metricTrace_eq_sum _ b]
  simp only [LinearMap.compl₂_apply, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
    ContinuousLinearMap.coe_coe]

/-- The Dirac operator of a section whose covariant derivative vanishes at `x` vanishes at `x`.
In particular `D 0 = 0`. -/
theorem diracOperator_eq_zero_of_eq_zero (x : M) (hσ : cov σ x = 0) :
    cov.diracOperator c σ x = 0 := by
  simp [diracOperator_eq_sum cov c σ x (stdOrthonormalBasis ℝ (TangentSpace I x)), hσ]

/-- The Dirac operator of the zero section is zero. -/
@[simp]
theorem diracOperator_zero [VectorBundle ℝ F V] (x : M) :
    cov.diracOperator c (0 : Π y : M, V y) x = 0 :=
  cov.diracOperator_eq_zero_of_eq_zero c x (by simp)

/-- The Dirac operator at `x` depends on `σ` only through its covariant derivative `∇σ` at `x`. -/
theorem diracOperator_congr {x : M} (h : cov σ x = cov τ x) :
    cov.diracOperator c σ x = cov.diracOperator c τ x := by
  simp only [diracOperator_eq_sum cov c _ x (stdOrthonormalBasis ℝ (TangentSpace I x)), h]

/-- **Locality.** For sections differentiable at `x`, the Dirac operator at `x` depends only on
their germ at `x`. -/
theorem diracOperator_congr_of_eventuallyEq {x : M} (hσ : MDiffAt (T% σ) x)
    (hτ : MDiffAt (T% τ) x) (h : ∀ᶠ y in 𝓝 x, σ y = τ y) :
    cov.diracOperator c σ x = cov.diracOperator c τ x :=
  cov.diracOperator_congr c <|
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hσ hτ univ_mem h

/-- The Dirac operator is additive on sections differentiable at the point. -/
theorem diracOperator_add {x : M} (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    cov.diracOperator c (σ + τ) x = cov.diracOperator c σ x + cov.diracOperator c τ x := by
  simp only [diracOperator_eq_sum cov c _ x (stdOrthonormalBasis ℝ (TangentSpace I x)),
    cov.isCovariantDerivativeOnUniv.add hσ hτ, add_apply, map_add,
    Finset.sum_add_distrib]

/-- The Dirac operator commutes with multiplication of a differentiable section by a
constant. -/
theorem diracOperator_const_smul {x : M} (a : ℝ) (hσ : MDiffAt (T% σ) x) :
    cov.diracOperator c (a • σ) x = a • cov.diracOperator c σ x := by
  simp only [diracOperator_eq_sum cov c _ x (stdOrthonormalBasis ℝ (TangentSpace I x)),
    cov.isCovariantDerivativeOnUniv.smul_const a hσ, smul_apply, map_smul,
    Finset.smul_sum]

/-- The Dirac operator commutes with negation of a differentiable section. -/
theorem diracOperator_neg {x : M} (hσ : MDiffAt (T% σ) x) :
    cov.diracOperator c (-σ) x = -cov.diracOperator c σ x := by
  rw [← neg_one_smul ℝ σ, cov.diracOperator_const_smul c (-1) hσ, neg_one_smul]

/-- The Dirac operator commutes with differences of differentiable sections. -/
theorem diracOperator_sub [VectorBundle ℝ F V] {x : M} (hσ : MDiffAt (T% σ) x)
    (hτ : MDiffAt (T% τ) x) :
    cov.diracOperator c (σ - τ) x = cov.diracOperator c σ x - cov.diracOperator c τ x := by
  rw [sub_eq_add_neg, cov.diracOperator_add c hσ (mdifferentiableAt_neg_section hτ),
    cov.diracOperator_neg c hτ, sub_eq_add_neg]

/-- **Naturality of the Dirac operator.** Let `g` be an endomorphism of the fibre at `x` which
commutes with Clifford multiplication. If a second connection `∇'` differentiates `τ` at `x` as
`g` applied to the covariant derivative of `σ`, `∇' τ = g ∘ ∇ σ`, then `D' τ = g (D σ)` at `x`.
For a gauge transformation `u` commuting with `c` and the transformed connection
`∇^u = u ∘ ∇ ∘ u⁻¹`, applied to `τ = u σ`, this is the gauge covariance
`D_{∇^u} (u σ) = u (D_∇ σ)`. -/
theorem diracOperator_eq_apply_of_eq_comp (cov' : _root_.CovariantDerivative I F V) {x : M}
    (g : V x →L[ℝ] V x) (hg : ∀ v, g ∘L c x v = c x v ∘L g) (h : cov' τ x = g ∘L cov σ x) :
    cov'.diracOperator c τ x = g (cov.diracOperator c σ x) := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [diracOperator_eq_sum cov' c τ x b, diracOperator_eq_sum cov c σ x b, h, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact (DFunLike.congr_fun (hg (b i)) (cov σ x (b i))).symm

/-! ### The Leibniz rule and the principal symbol -/

section Leibniz

variable [IsManifold I 1 M] {f g : M → ℝ}

/-- **The Leibniz rule for the Dirac operator.** For a function `f` and a section `σ`, both
differentiable at `x`, `D (f σ) = f D σ + c(grad f) σ`. Thus the commutator of `D` with
multiplication by `f` is Clifford multiplication by the gradient of `f`. -/
theorem diracOperator_smul {x : M} (hf : MDiffAt f x) (hσ : MDiffAt (T% σ) x) :
    cov.diracOperator c (f • σ) x =
      f x • cov.diracOperator c σ x + c x (TauCeti.Manifold.mgradient I f x) (σ x) := by
  -- The Leibniz correction contracts `c x` against the rank-one map `w ↦ ⟪grad f, w⟫ • σ x`.
  have h : (ContinuousLinearMap.toLinearMap₁₂ (c x)).compl₂ (cov (f • σ) x).toLinearMap =
      f x • (ContinuousLinearMap.toLinearMap₁₂ (c x)).compl₂ (cov σ x).toLinearMap +
        (ContinuousLinearMap.toLinearMap₁₂ (c x)).compl₂
          ((innerₗ (TangentSpace I x) (TauCeti.Manifold.mgradient I f x)).smulRight (σ x)) :=
    LinearMap.ext₂ fun u w ↦ by
      simp only [LinearMap.compl₂_apply, ContinuousLinearMap.coe_coe,
        cov.isCovariantDerivativeOnUniv.leibniz hσ hf, add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smulRight_apply, innerₗ_apply_apply, TauCeti.Manifold.inner_mgradient, map_add,
        map_smul]
  rw [diracOperator_def, diracOperator_def, h, map_add, map_smul,
    LinearMap.BilinMap.metricTrace_compl₂_innerₗ_smulRight,
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]

/-- **The principal symbol of the Dirac operator.** The commutator of `D` with multiplication by a
function `f` is Clifford multiplication by its gradient: `D (f σ) - f D σ = c(grad f) σ`. -/
theorem diracOperator_smul_sub {x : M} (hf : MDiffAt f x) (hσ : MDiffAt (T% σ) x) :
    cov.diracOperator c (f • σ) x - f x • cov.diracOperator c σ x =
      c x (TauCeti.Manifold.mgradient I f x) (σ x) := by
  rw [diracOperator_smul cov c hf hσ, add_sub_cancel_left]

/-- **The Dirac operator has order one.** Every double commutator of `D` with multiplications by
functions vanishes: `D (f g σ) - f D (g σ) - g D (f σ) + f g D σ = 0`. -/
theorem diracOperator_smul_smul_sub [VectorBundle ℝ F V] {x : M} (hf : MDiffAt f x)
    (hg : MDiffAt g x) (hσ : MDiffAt (T% σ) x) :
    cov.diracOperator c (f • g • σ) x - f x • cov.diracOperator c (g • σ) x -
        g x • cov.diracOperator c (f • σ) x + (f x * g x) • cov.diracOperator c σ x = 0 := by
  rw [diracOperator_smul cov c hf (hg.smul_section hσ), diracOperator_smul cov c hg hσ,
    diracOperator_smul cov c hf hσ, Pi.smul_apply', map_smul]
  module

/-- **Ellipticity of the Dirac operator.** If the Clifford multiplication satisfies the Clifford
relation `c(v) c(v) = -⟪v, v⟫` at `x` and `df ≠ 0` at `x`, then the commutator `[D, f] σ` vanishes
at `x` only if `σ` does: the principal symbol `c(grad f)` is injective. -/
theorem eq_zero_of_diracOperator_smul_sub_eq_zero {x : M}
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

/-- **Change of connection.** Adding to `∇` a one-form `A` with values in the endomorphisms of
`V` adds to the Dirac operator the metric trace of the pairing `(u, w) ↦ c(u) (A(w) σ)`, that is
`∑ᵢ c(eᵢ) A(eᵢ) σ` in any orthonormal basis `eᵢ` of the tangent space at `x`
(`LinearMap.BilinMap.metricTrace_eq_sum`). -/
theorem diracOperator_addOneForm (A : Π y : M, V y →L[ℝ] TangentSpace I y →L[ℝ] V y)
    (σ : Π y : M, V y) (x : M) :
    (cov.addOneForm A).diracOperator c σ x =
      cov.diracOperator c σ x + LinearMap.BilinMap.metricTrace
        ((ContinuousLinearMap.toLinearMap₁₂ (c x)).compl₂ (A x (σ x)).toLinearMap) := by
  rw [diracOperator_def, diracOperator_def, addOneForm_apply, ← map_add]
  congr 1
  ext u w
  simp only [LinearMap.compl₂_apply, ContinuousLinearMap.toLinearMap_add, LinearMap.add_apply,
    map_add]

/-- **Change of connection by an inner-product one-form.** If the one-form `A` acts on `σ` at `x`
by `A_x(σ_x)(w) = ⟪u, w⟫ v`, then adding it to `∇` adds `c(u) v` to the Dirac operator at `x`.
For `v = σ_x` this is the change `D_{∇ + u♭} = D_∇ + c(u)` under the addition of a real one-form;
for the spinors of a `Spinᶜ` structure and an imaginary one-form `i a` added to the determinant
connection, `v = (i / 2) σ_x`. -/
theorem diracOperator_addOneForm_of_apply_eq_inner_smul
    (A : Π y : M, V y →L[ℝ] TangentSpace I y →L[ℝ] V y) {x : M} {u : TangentSpace I x}
    {v : V x} (hA : ∀ w, A x (σ x) w = ⟪u, w⟫ • v) :
    (cov.addOneForm A).diracOperator c σ x = cov.diracOperator c σ x + c x u v := by
  -- The correction contracts `c x` against the rank-one map `w ↦ ⟪u, w⟫ • v`.
  have hA' : (A x (σ x)).toLinearMap = (innerₗ (TangentSpace I x) u).smulRight v :=
    LinearMap.ext fun w ↦ by
      rw [ContinuousLinearMap.coe_coe, hA, LinearMap.smulRight_apply, innerₗ_apply_apply]
  rw [cov.diracOperator_addOneForm c A σ x, hA',
    LinearMap.BilinMap.metricTrace_compl₂_innerₗ_smulRight,
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]

/-- **Change of connection by a scalar one-form.** If the endomorphism-valued one-form `A` acts on
`σ` at `x` as `A(w)(σ_x) = θ(w) L(σ_x)`, for a real covector `θ` and an endomorphism `L` of the
fibre, then adding `A` to `∇` adds `c(θ♯) L σ` to the Dirac operator at `x`, where `θ♯` is the
metric dual of `θ`. For the spin connection of a unitary connection on the determinant line,
changing the connection by an imaginary one-form `a = i θ` changes the spin connection by
`a / 2`, that is `L = i / 2`, and this is the law `D_{A + a} = D_A + c(a) / 2`. -/
theorem diracOperator_addOneForm_of_forall_apply_eq [IsManifold I 1 M]
    (A : Π y : M, V y →L[ℝ] TangentSpace I y →L[ℝ] V y) (σ : Π y : M, V y) {x : M}
    (θ : TangentSpace I x →L[ℝ] ℝ) (L : V x →L[ℝ] V x) (hA : ∀ w, A x (σ x) w = θ w • L (σ x)) :
    (cov.addOneForm A).diracOperator c σ x =
      cov.diracOperator c σ x + c x (Riemannian.Tensor.rieszDual x θ) (L (σ x)) :=
  cov.diracOperator_addOneForm_of_apply_eq_inner_smul c A fun w ↦ by
    rw [hA, Riemannian.Tensor.inner_rieszDual]

/-! ### Gradings -/

/-- **The Dirac operator exchanges the eigenspaces of a grading.** Let `γ` be an endomorphism of
the fibre at `x` anticommuting with Clifford multiplication, `γ c(v) = -c(v) γ`. If every
covariant derivative `∇_w σ` at `x` is an eigenvector of `γ` with eigenvalue `a`, then `D σ` at `x`
is an eigenvector with eigenvalue `-a`. For a parallel grading `γ` and a section `σ` of its
`±1`-eigenbundle, `∇σ` lies in the same eigenbundle, so `D σ` lies in the other one: this is the
block form of the Dirac operator of a graded Clifford module. -/
theorem apply_diracOperator_eq_neg_smul {x : M} (γ : Module.End ℝ (V x)) (a : ℝ)
    (hc : ∀ (v : TangentSpace I x) (s : V x), γ (c x v s) = -c x v (γ s))
    (hσ : ∀ w, γ (cov σ x w) = a • cov σ x w) :
    γ (cov.diracOperator c σ x) = -(a • cov.diracOperator c σ x) := by
  rw [diracOperator_eq_sum cov c σ x (stdOrthonormalBasis ℝ (TangentSpace I x)), map_sum,
    Finset.smul_sum, ← Finset.sum_neg_distrib]
  simp only [hc, hσ, map_smul]

/-! ### Naturality between bundles -/

section Naturality

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul ℝ (W x)]
  [FiberBundle F' W]
  (covW : _root_.CovariantDerivative I F' W)
  (cW : Π x : M, TangentSpace I x →L[ℝ] W x →L[ℝ] W x)
  (L : Π x : M, V x →ₗ[ℝ] W x)

/-- **Naturality of the Dirac operator.** Let `L` be a fibrewise linear map from `V` to `W` which
intertwines the Clifford multiplications at `x`, `L c_V(v) = c_W(v) L`, and the connections along
`σ` at `x`, `∇^W (L σ) = L ∇^V σ`. Then `D_W (L σ) = L (D_V σ)` at `x`. For `L` a gauge
transformation commuting with the Clifford multiplication, and `∇^W` the transformed connection,
this is the gauge covariance of the Dirac operator. -/
theorem diracOperator_linearMap_apply {x : M}
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
theorem diracOperator_linearMap_apply_eq_neg {x : M}
    (hc : ∀ (v : TangentSpace I x) (s : V x), L x (c x v s) = -cW x v (L x s))
    (hL : ∀ w, covW (fun y ↦ L y (σ y)) x w = L x (cov σ x w)) :
    covW.diracOperator cW (fun y ↦ L y (σ y)) x = -L x (cov.diracOperator c σ x) := by
  set b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [diracOperator_eq_sum covW cW _ x b, diracOperator_eq_sum cov c _ x b, map_sum,
    ← Finset.sum_neg_distrib]
  simp only [hL, hc, neg_neg]

end Naturality

end CovariantDerivative
