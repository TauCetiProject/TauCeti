/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Spectral.Diagonal
public import TauCeti.Analysis.InnerProductSpace.TensorProduct.Completion
public import TauCeti.Order.Northcott.Prod
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
import TauCeti.Order.Northcott.Comparison

/-!
# Hilbert bases of completed tensor products and tensor sums of operators

Let `b` and `c` be Hilbert bases of inner product spaces `E` and `F` over `𝕜`. The pure tensors
`b i ⊗ₜ c j` form a Hilbert basis `HilbertBasis.tensorProduct b c`, indexed by `ι × κ`, of the
completed Hilbert tensor product `E ⊗̂ F = UniformSpace.Completion (E ⊗[𝕜] F)`. They are
orthonormal by Mathlib's `Orthonormal.tmul`, and their span is dense: its closure contains
`x ⊗ₜ c j` for every `x`, since `b` spans a dense subspace of `E`, then `x ⊗ₜ y` for all `x` and
`y`, and the pure tensors span a dense subspace of `E ⊗̂ F` (`TensorProduct.dense_span_coe_tmul`).
The coordinates of a pure tensor are the products of the coordinates of its factors
(`HilbertBasis.tensorProduct_repr_coe_tmul_apply`).

This is the eigenbasis of a *tensor sum* `A ⊗ 1 + 1 ⊗ B` of two operators with eigenbases, for
instance of the Laplacian `L_E ⊗ 1 + 1 ⊗ L_F` of an external product of bundles, or of the square
`D_P² ⊗ 1 + 1 ⊗ D_Q²` of the graded product of two self-adjoint operators. If `A` and `B` have the
Hilbert bases `b` and `c` of eigenvectors, with eigenvalues `λ i` and `μ j`, the tensor sum is the
diagonal operator

`(b.tensorProduct c).diagonalPMap fun p ↦ λ p.1 + μ p.2`

in the product basis. When `A ≤ b.diagonalPMap λ` and `B ≤ c.diagonalPMap μ`, for instance for
symmetric `A` and `B` (`LinearPMap.IsFormalAdjoint.le_diagonalPMap`), it acts on pure tensors of
vectors of the domains by the Leibniz rule `x ⊗ y ↦ A x ⊗ y + x ⊗ B y`
(`HilbertBasis.coe_tmul_mem_graph_diagonalPMap_tensorProduct`). When moreover each `b i` lies in
the domain of `A` with `A (b i) = λ i • b i`, and each `c j` in the domain of `B` with
`B (c j) = μ j • c j`, every closed operator that acts on pure tensors of domain vectors by the
Leibniz rule contains it (`LinearPMap.IsClosed.diagonalPMap_tensorProduct_le`), and every closed
symmetric one equals it (`LinearPMap.IsFormalAdjoint.eq_diagonalPMap_tensorProduct`). For real
eigenvalues it is self-adjoint (`HilbertBasis.isSelfAdjoint_diagonalPMap`).

For nonnegative eigenvalues, `λ i + μ j = 0` exactly when `λ i = 0` and `μ j = 0`, so the kernel of
the tensor sum is spanned by the products of the eigenvectors in the two kernels
(`HilbertBasis.ker_diagonalPMap_tensorProduct`), and its `finrank` is the product of the
`finrank`s of the kernels of `b.diagonalPMap λ` and `c.diagonalPMap μ`
(`HilbertBasis.finrank_ker_diagonalPMap_tensorProduct`). For closed symmetric `A` and `B` these
diagonal operators are `A` and `B` (`LinearPMap.IsFormalAdjoint.eq_diagonalPMap`), so then

`dim ker (A ⊗ 1 + 1 ⊗ B) = dim ker A * dim ker B`.

Nonnegativity is needed: for `λ = 1` and `μ = -1` on one-dimensional spaces the tensor sum is
zero, while both kernels are trivial. Applied to `D_P² ⊗ 1 + 1 ⊗ D_Q²`, whose kernel is that of
the graded product operator, this is the dimension count behind the product formula for the index
of two elliptic operators.

The tensor sum of two operators with compact resolvent and real eigenvalues bounded below has
compact resolvent (`LinearPMap.HasCompactResolvent.hasCompactResolvent_diagonalPMap_tensorProduct`).
A diagonal operator has compact resolvent exactly when only finitely many of its coefficients lie in
each bounded set (`HilbertBasis.hasCompactResolvent_diagonalPMap_iff`); for real families `λ` and
`μ` bounded below this means that `λ i` and `μ j` tend to `+∞`, and then only finitely many pairs
have `λ i + μ j ≤ R` (`Northcott.prod_add`). The lower bounds are needed: for `λ n = n` and
`μ n = -n` on `ℓ²(ℕ)` the tensor sum has the eigenvalue `0` with infinite multiplicity, although
both diagonal operators with coefficients `λ` and `μ` have compact resolvent.

## Main definitions

* `HilbertBasis.tensorProduct b c`: the Hilbert basis `(i, j) ↦ b i ⊗ₜ c j` of the completed tensor
  product.

## Main results

* `HilbertBasis.tensorProduct_apply`, `HilbertBasis.inner_tensorProduct_coe_tmul` and
  `HilbertBasis.tensorProduct_repr_coe_tmul_apply`: its vectors and the coordinates of pure tensors.
* `HilbertBasis.coe_tmul_mem_graph_diagonalPMap_tensorProduct`: when `A ≤ b.diagonalPMap λ` and
  `B ≤ c.diagonalPMap μ`, the diagonal operator with coefficients `λ i + μ j` extends
  `A ⊗ 1 + 1 ⊗ B` on pure tensors of domain vectors.
* `LinearPMap.IsClosed.diagonalPMap_tensorProduct_le` and
  `LinearPMap.IsFormalAdjoint.eq_diagonalPMap_tensorProduct`: when the `b i` and `c j` are
  eigenvectors in the domains of `A` and `B` with eigenvalues `λ i` and `μ j`, every closed
  operator acting on pure tensors of domain vectors by the Leibniz rule contains it, and every
  closed symmetric one equals it.
* `HilbertBasis.ker_diagonalPMap_tensorProduct` and
  `HilbertBasis.finrank_ker_diagonalPMap_tensorProduct`: the kernel of a tensor sum with
  nonnegative coefficients and its dimension.
* `HilbertBasis.hasCompactResolvent_diagonalPMap_tensorProduct` and
  `LinearPMap.HasCompactResolvent.hasCompactResolvent_diagonalPMap_tensorProduct`: compact
  resolvent of a tensor sum.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, Academic
  Press, 1980, §II.4, Proposition 2 (orthonormal bases of tensor products of Hilbert spaces), and
  §VIII.10, Theorem VIII.33 (the tensor sum `A ⊗ 1 + 1 ⊗ B` of self-adjoint operators).
* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §9, for the product of two elliptic operators and its kernel.
-/

public section

noncomputable section

open UniformSpace TensorProduct LinearPMap
open scoped InnerProductSpace ComplexOrder

variable {ι κ 𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace HilbertBasis

/-! ### The Hilbert basis of a completed tensor product -/

variable (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)

/-- The closed span of the pure tensors `b i ⊗ₜ c j` of two Hilbert bases is the whole completed
tensor product. -/
private theorem top_le_topologicalClosure_span_coe_tmul :
    ⊤ ≤ (Submodule.span 𝕜 (Set.range fun p : ι × κ ↦
      ((b p.1 ⊗ₜ[𝕜] c p.2 : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)))).topologicalClosure := by
  set S := (Submodule.span 𝕜 (Set.range fun p : ι × κ ↦
    ((b p.1 ⊗ₜ[𝕜] c p.2 : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)))).topologicalClosure
  have hS : IsClosed (S : Set (Completion (E ⊗[𝕜] F))) := Submodule.isClosed_topologicalClosure _
  -- First `x ⊗ₜ c j ∈ S` for every `x`, then `x ⊗ₜ y ∈ S` for all `x` and `y`.
  have hmem (x : E) (y : F) : ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) ∈ S := by
    refine c.apply_mem_of_forall_apply_mem hS (Completion.toComplL ∘L mkL 𝕜 E F x)
      (fun j ↦ ?_) y
    exact b.apply_mem_of_forall_apply_mem hS (Completion.toComplL ∘L (mkL 𝕜 E F).flip (c j))
      (fun i ↦ Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(i, j), rfl⟩)) x
  rw [← dense_span_coe_tmul 𝕜 E F]
  refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) hS
  rintro _ ⟨⟨x, y⟩, rfl⟩
  exact hmem x y

/-- **The Hilbert basis of a completed tensor product.** For Hilbert bases `b` of `E` and `c` of
`F`, the pure tensors `b i ⊗ₜ c j` form a Hilbert basis of the completed Hilbert tensor product
`E ⊗̂ F = UniformSpace.Completion (E ⊗[𝕜] F)`, indexed by `ι × κ`. -/
protected def tensorProduct : HilbertBasis (ι × κ) 𝕜 (Completion (E ⊗[𝕜] F)) :=
  HilbertBasis.mk ((b.orthonormal.tmul c.orthonormal).comp_linearIsometry Completion.toComplₗᵢ)
    (b.top_le_topologicalClosure_span_coe_tmul c)

/-- The `(i, j)` vector of the product basis is the pure tensor `b i ⊗ₜ c j`. -/
@[simp]
theorem tensorProduct_apply (i : ι) (j : κ) :
    b.tensorProduct c (i, j) = ((b i ⊗ₜ[𝕜] c j : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) :=
  congrFun (HilbertBasis.coe_mk _ _) (i, j)

/-- The vector of the product basis at `p` is the pure tensor `b p.1 ⊗ₜ c p.2`. -/
theorem tensorProduct_apply' (p : ι × κ) :
    b.tensorProduct c p = ((b p.1 ⊗ₜ[𝕜] c p.2 : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) :=
  tensorProduct_apply b c p.1 p.2

/-- The inner product of a vector of the product basis with a pure tensor is the product of the
inner products of the factors. -/
theorem inner_tensorProduct_coe_tmul (i : ι) (j : κ) (x : E) (y : F) :
    ⟪b.tensorProduct c (i, j), ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F))⟫_𝕜 =
      ⟪b i, x⟫_𝕜 * ⟪c j, y⟫_𝕜 := by
  rw [tensorProduct_apply, Completion.inner_coe, inner_tmul]

/-- The coordinates of a pure tensor in the product basis are the products of the coordinates of
its factors. -/
@[simp]
theorem tensorProduct_repr_coe_tmul_apply (x : E) (y : F) (i : ι) (j : κ) :
    (b.tensorProduct c).repr ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) (i, j) =
      c.repr y j * b.repr x i := by
  rw [(b.tensorProduct c).repr_apply_apply, inner_tensorProduct_coe_tmul, b.repr_apply_apply,
    c.repr_apply_apply, mul_comm]

/-! ### Tensor sums of operators with eigenbases -/

variable {b c} {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {lam : ι → 𝕜} {mu : κ → 𝕜}

/-- **The tensor sum on pure tensors.** If `A` and `B` are restrictions of the diagonal operators
with coefficients `λ` and `μ` in the Hilbert bases `b` and `c`, for instance symmetric operators
with these eigenbases (`LinearPMap.IsFormalAdjoint.le_diagonalPMap`), then the diagonal operator
with coefficients `λ i + μ j` in the product basis sends `x ⊗ y` to `A x ⊗ y + x ⊗ B y`, for `x` in
the domain of `A` and `y` in the domain of `B`. -/
theorem coe_tmul_mem_graph_diagonalPMap_tensorProduct (hA : A ≤ b.diagonalPMap lam)
    (hB : B ≤ c.diagonalPMap mu) (x : A.domain) (y : B.domain) :
    ((((x : E) ⊗ₜ[𝕜] (y : F) : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)),
      ((A x ⊗ₜ[𝕜] (y : F) + (x : E) ⊗ₜ[𝕜] B y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F))) ∈
      ((b.tensorProduct c).diagonalPMap fun p ↦ lam p.1 + mu p.2).graph := by
  rw [mem_graph_diagonalPMap_iff]
  rintro ⟨i, j⟩
  rw [Completion.coe_add, inner_add_right, inner_tensorProduct_coe_tmul,
    inner_tensorProduct_coe_tmul, inner_tensorProduct_coe_tmul,
    (b.le_diagonalPMap_iff lam).1 hA x i, (c.le_diagonalPMap_iff mu).1 hB y j]
  ring

/-- An operator acting on pure tensors of eigenvectors of `A` and `B` by the Leibniz rule has the
vectors of the product basis as eigenvectors, with the eigenvalues `λ i + μ j`. -/
private theorem exists_apply_tensorProduct_eq_smul {T : Completion (E ⊗[𝕜] F) →ₗ.[𝕜] _}
    (hA : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = lam i • b i)
    (hB : ∀ j, ∃ hj : c j ∈ B.domain, B ⟨c j, hj⟩ = mu j • c j)
    (hT : ∀ (x : A.domain) (y : B.domain),
      ((((x : E) ⊗ₜ[𝕜] (y : F) : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)),
        ((A x ⊗ₜ[𝕜] (y : F) + (x : E) ⊗ₜ[𝕜] B y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F))) ∈ T.graph)
    (p : ι × κ) :
    ∃ hp : b.tensorProduct c p ∈ T.domain,
      T ⟨b.tensorProduct c p, hp⟩ = (lam p.1 + mu p.2) • b.tensorProduct c p := by
  obtain ⟨hi, hAi⟩ := hA p.1
  obtain ⟨hj, hBj⟩ := hB p.2
  obtain ⟨u, hu, hTu⟩ := (mem_graph_iff T).1 (hT ⟨b p.1, hi⟩ ⟨c p.2, hj⟩)
  rw [← tensorProduct_apply'] at hu
  obtain ⟨u, hu'⟩ := u
  subst hu
  refine ⟨hu', ?_⟩
  rw [hTu]
  dsimp only
  rw [hAi, hBj, ← smul_tmul', tmul_smul, ← add_smul, Completion.coe_smul, tensorProduct_apply']

end HilbertBasis

namespace LinearPMap

variable {b : HilbertBasis ι 𝕜 E} {c : HilbertBasis κ 𝕜 F} {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
  {lam : ι → 𝕜} {mu : κ → 𝕜} {T : Completion (E ⊗[𝕜] F) →ₗ.[𝕜] Completion (E ⊗[𝕜] F)}

/-- **Every closed operator acting by the Leibniz rule contains the tensor sum.** Let `A` and `B`
have Hilbert bases `b` and `c` of eigenvectors, with eigenvalues `λ i` and `μ j`. A closed operator
`T` on the completed tensor product that sends `x ⊗ y` to `A x ⊗ y + x ⊗ B y` for `x` in the domain
of `A` and `y` in the domain of `B` contains the diagonal operator with coefficients `λ i + μ j` in
the product basis. -/
theorem IsClosed.diagonalPMap_tensorProduct_le (hT : T.IsClosed)
    (hA : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = lam i • b i)
    (hB : ∀ j, ∃ hj : c j ∈ B.domain, B ⟨c j, hj⟩ = mu j • c j)
    (hTAB : ∀ (x : A.domain) (y : B.domain),
      ((((x : E) ⊗ₜ[𝕜] (y : F) : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)),
        ((A x ⊗ₜ[𝕜] (y : F) + (x : E) ⊗ₜ[𝕜] B y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F))) ∈ T.graph) :
    (b.tensorProduct c).diagonalPMap (fun p ↦ lam p.1 + mu p.2) ≤ T :=
  hT.diagonalPMap_le (HilbertBasis.exists_apply_tensorProduct_eq_smul hA hB hTAB)

/-- **Uniqueness of the tensor sum.** Let `A` and `B` have Hilbert bases `b` and `c` of
eigenvectors, with eigenvalues `λ i` and `μ j`. A closed symmetric operator `T` on the completed
tensor product that sends `x ⊗ y` to `A x ⊗ y + x ⊗ B y` for `x` in the domain of `A` and `y` in
the domain of `B` is the diagonal operator with coefficients `λ i + μ j` in the product basis. -/
theorem IsFormalAdjoint.eq_diagonalPMap_tensorProduct (hT : T.IsFormalAdjoint T)
    (hcl : T.IsClosed) (hA : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = lam i • b i)
    (hB : ∀ j, ∃ hj : c j ∈ B.domain, B ⟨c j, hj⟩ = mu j • c j)
    (hTAB : ∀ (x : A.domain) (y : B.domain),
      ((((x : E) ⊗ₜ[𝕜] (y : F) : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)),
        ((A x ⊗ₜ[𝕜] (y : F) + (x : E) ⊗ₜ[𝕜] B y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F))) ∈ T.graph) :
    T = (b.tensorProduct c).diagonalPMap fun p ↦ lam p.1 + mu p.2 :=
  hT.eq_diagonalPMap hcl (HilbertBasis.exists_apply_tensorProduct_eq_smul hA hB hTAB)

end LinearPMap

namespace HilbertBasis

/-! ### The kernel of a tensor sum -/

variable (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) {lam : ι → 𝕜} {mu : κ → 𝕜}

/-- For nonnegative coefficients, `λ i + μ j` vanishes exactly when `λ i` and `μ j` both vanish. -/
private theorem setOf_add_eq_zero (hlam : ∀ i, 0 ≤ lam i) (hmu : ∀ j, 0 ≤ mu j) :
    {p : ι × κ | lam p.1 + mu p.2 = 0} = {i | lam i = 0} ×ˢ {j | mu j = 0} := by
  ext p
  exact add_eq_zero_iff_of_nonneg (hlam p.1) (hmu p.2)

/-- **The kernel of a tensor sum.** For nonnegative coefficients `λ` and `μ`, the kernel of the
diagonal operator with coefficients `λ i + μ j` in the product basis is the closed span of the
pure tensors `b i ⊗ₜ c j` with `λ i = 0` and `μ j = 0`. -/
theorem ker_diagonalPMap_tensorProduct (hlam : ∀ i, 0 ≤ lam i) (hmu : ∀ j, 0 ≤ mu j) :
    ((b.tensorProduct c).diagonalPMap fun p ↦ lam p.1 + mu p.2).ker =
      (Submodule.span 𝕜
        (b.tensorProduct c '' {i | lam i = 0} ×ˢ {j | mu j = 0})).topologicalClosure := by
  rw [ker_diagonalPMap, setOf_add_eq_zero hlam hmu]

/-- **The dimension of the kernel of a tensor sum.** For nonnegative coefficients `λ` and `μ`, the
kernel of the diagonal operator with coefficients `λ i + μ j` in the product basis has dimension
`dim ker (b.diagonalPMap λ) * dim ker (c.diagonalPMap μ)`. When a kernel is infinite-dimensional
both sides are `0`. -/
theorem finrank_ker_diagonalPMap_tensorProduct (hlam : ∀ i, 0 ≤ lam i) (hmu : ∀ j, 0 ≤ mu j) :
    Module.finrank 𝕜 ((b.tensorProduct c).diagonalPMap fun p ↦ lam p.1 + mu p.2).ker =
      Module.finrank 𝕜 (b.diagonalPMap lam).ker * Module.finrank 𝕜 (c.diagonalPMap mu).ker := by
  rw [finrank_ker_diagonalPMap, finrank_ker_diagonalPMap, finrank_ker_diagonalPMap,
    setOf_add_eq_zero hlam hmu, Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]

/-! ### Compact resolvent of a tensor sum -/

/-- **Compact resolvent of a tensor sum of diagonal operators.** If the real families `λ` and `μ`
have only finitely many members below every bound, then so has the family of sums `λ i + μ j`, and
the diagonal operator with these coefficients in the product basis has compact resolvent. -/
theorem hasCompactResolvent_diagonalPMap_tensorProduct {lam : ι → ℝ} {mu : κ → ℝ}
    [Northcott lam] [Northcott mu] :
    ((b.tensorProduct c).diagonalPMap fun p ↦ (lam p.1 : 𝕜) + mu p.2).HasCompactResolvent := by
  rw [hasCompactResolvent_diagonalPMap_iff]
  have := Northcott.prod_add lam mu
  exact Northcott.of_le_add (h := fun p : ι × κ ↦ lam p.1 + mu p.2) 0 fun p ↦ by
    rw [add_zero, ← RCLike.ofReal_add, RCLike.norm_ofReal]
    exact le_abs_self _

variable {b c} in
/-- **Compact resolvent of the tensor sum of two operators.** Let `A` and `B` have compact
resolvent and Hilbert bases `b` and `c` of eigenvectors whose real eigenvalues `λ i` and `μ j` are
bounded below, for instance self-adjoint operators with compact resolvent that are bounded below.
Then the tensor sum `A ⊗ 1 + 1 ⊗ B`, the diagonal operator with coefficients `λ i + μ j` in the
product basis, has compact resolvent. By `LinearPMap.IsFormalAdjoint.eq_diagonalPMap_tensorProduct`
this applies to every closed symmetric operator acting on pure tensors by the Leibniz rule.

The lower bounds are needed: for `λ n = n` and `μ n = -n` the eigenvalue `0` of the tensor sum has
infinite multiplicity. -/
theorem _root_.LinearPMap.HasCompactResolvent.hasCompactResolvent_diagonalPMap_tensorProduct
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} (hA : A.HasCompactResolvent) (hB : B.HasCompactResolvent)
    {lam : ι → ℝ} {mu : κ → ℝ}
    (hAb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : 𝕜) • b i)
    (hBc : ∀ j, ∃ hj : c j ∈ B.domain, B ⟨c j, hj⟩ = (mu j : 𝕜) • c j) {a a' : ℝ}
    (hlam : ∀ i, a ≤ lam i) (hmu : ∀ j, a' ≤ mu j) :
    ((b.tensorProduct c).diagonalPMap fun p ↦ (lam p.1 : 𝕜) + mu p.2).HasCompactResolvent := by
  -- The eigenvalue norms are Northcott, and with a lower bound so are the eigenvalues.
  have hNA := hA.northcott_norm_of_orthonormal b.orthonormal hAb
  have hNB := hB.northcott_norm_of_orthonormal c.orthonormal hBc
  -- For `a ≤ x` we have `|x| ≤ x + 2 |a|`.
  have key (a x : ℝ) (hax : a ≤ x) : ‖(x : 𝕜)‖ ≤ x + 2 * |a| := by
    rw [RCLike.norm_ofReal, abs_le]
    constructor <;> linarith [neg_abs_le a, le_abs_self a]
  have : Northcott lam := Northcott.of_le_add (2 * |a|) fun i ↦ key a _ (hlam i)
  have : Northcott mu := Northcott.of_le_add (2 * |a'|) fun j ↦ key a' _ (hmu j)
  exact HilbertBasis.hasCompactResolvent_diagonalPMap_tensorProduct b c

end HilbertBasis
