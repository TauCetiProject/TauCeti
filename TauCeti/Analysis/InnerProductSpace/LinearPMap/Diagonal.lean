/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
import TauCeti.Analysis.InnerProductSpace.Parseval

/-!
# Diagonal operators in a Hilbert basis

Let `b` be a Hilbert basis of a Hilbert space `E` and `c : ι → 𝕜` an arbitrary family of scalars.
The *diagonal operator* `b.diagonal c` multiplies the `i`-th coordinate `⟪b i, x⟫` of a vector by
`c i`. It is a partial linear map, defined on the vectors whose rescaled coordinates are still
square-summable,

`dom (b.diagonal c) = {x | ∑ᵢ ‖c i * ⟪b i, x⟫‖² < ∞}`,

and it is unbounded unless `c` is. Its graph is described coordinatewise
(`HilbertBasis.mem_graph_diagonal_iff`), its domain contains every basis vector and is dense, its
adjoint is the diagonal operator of the conjugate family (`HilbertBasis.adjoint_diagonal`), so it is
closed, and self-adjoint for a real family. Composition multiplies the families
(`HilbertBasis.diagonal_apply_diagonal_apply`) and addition adds them on the common domain
(`HilbertBasis.diagonal_add_diagonal_le`).

Diagonal operators are the functional calculus of operators with a Hilbert basis of eigenvectors.
If a self-adjoint operator `A` has a Hilbert basis `b` of eigenvectors, with real eigenvalues
`λ i`, then `A` *is* the diagonal operator `b.diagonal λ` (`IsSelfAdjoint.eq_diagonal`). This gives
the graph-domain criterion: `x` lies in the domain of `A` if and only if
`∑ᵢ (1 + λ i ²) ‖⟪b i, x⟫‖² < ∞`, and this sum is the squared graph norm `‖x‖² + ‖A x‖²`. For any
function `f : ℝ → 𝕜` the operator `f(A) = b.diagonal (f ∘ λ)` does not depend on the chosen
eigenbasis (`LinearPMap.IsFormalAdjoint.diagonal_eq_diagonal`): an eigenvector of one eigenbasis is
orthogonal to the vectors of another eigenbasis with different eigenvalues. By
`IsSelfAdjoint.exists_hilbertBasis_forall_apply_eq_smul_of_hasCompactResolvent`, a self-adjoint
operator with compact resolvent, such as the Dirac operator of a spectral triple, has such an
eigenbasis, and this calculus defines its absolute value, sign, heat operators and powers.

No measurability of `f` is needed: `b.diagonal (f ∘ λ)` acts coordinatewise in the eigenbasis,
so `f` only enters through its values `f (λ i)` at the eigenvalues.

## Main definitions

* `HilbertBasis.diagonal b c`: the diagonal partial linear map with coefficients `c` in the Hilbert
  basis `b`.

## Main results

* `HilbertBasis.mem_diagonal_domain_iff`, `HilbertBasis.inner_diagonal_apply`,
  `HilbertBasis.mem_graph_diagonal_iff`: the domain, the coordinates and the graph of a diagonal
  operator.
* `HilbertBasis.hasSum_diagonal_apply`: the expansion `b.diagonal c x = ∑ᵢ c i ⟪b i, x⟫ • b i`.
* `HilbertBasis.diagonal_domain_eq_top`: a bounded family gives an everywhere defined operator.
* `HilbertBasis.adjoint_diagonal`, `HilbertBasis.isClosed_diagonal`,
  `HilbertBasis.isSelfAdjoint_diagonal`: the adjoint of `b.diagonal c` is `b.diagonal (star c)`,
  so diagonal operators are closed, and self-adjoint for self-adjoint coefficient families.
* `HilbertBasis.le_diagonal_iff`: the restrictions of a diagonal operator.
* `HilbertBasis.diagonal_apply_mem_diagonal_domain_iff`,
  `HilbertBasis.diagonal_apply_diagonal_apply`, `HilbertBasis.diagonal_add_diagonal_le`:
  composition and sum of diagonal operators.
* `LinearPMap.IsFormalAdjoint.le_diagonal` and `IsSelfAdjoint.eq_diagonal`: a symmetric operator
  with a Hilbert basis of eigenvectors is contained in, and a self-adjoint one is equal to, the
  diagonal operator of its eigenvalues.
* `LinearPMap.IsFormalAdjoint.hasSum_norm_sq_add_norm_apply_sq` and
  `IsSelfAdjoint.mem_domain_iff_summable`: the graph norm in an eigenbasis and the graph-domain
  criterion.
* `LinearPMap.IsFormalAdjoint.diagonal_eq_diagonal`: the eigenbasis functional calculus is
  independent of the eigenbasis.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  §VIII.3 (multiplication operators and the spectral theorem).
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics IV: Analysis of Operators*,
  §XIII.14.
* A. Connes, *Noncommutative Geometry*, Chapter IV, §2.
-/

public section

noncomputable section

open LinearPMap
open scoped InnerProductSpace

namespace HilbertBasis

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  (b : HilbertBasis ι 𝕜 E) (c d : ι → 𝕜)

/-- The **diagonal operator** with coefficients `c` in the Hilbert basis `b`: the partial linear map
multiplying the `i`-th coordinate `⟪b i, x⟫` by `c i`. Its domain consists of the vectors `x` for
which `∑ᵢ ‖c i * ⟪b i, x⟫‖²` is finite (`HilbertBasis.mem_diagonal_domain_iff`). -/
def diagonal : E →ₗ.[𝕜] E where
  domain :=
    { carrier := {x | Memℓp (fun i ↦ c i * ⟪b i, x⟫_𝕜) 2}
      add_mem' {x y} hx hy := by
        simp only [Set.mem_ofPred_eq, inner_add_right, mul_add]
        exact hx.add hy
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, inner_zero_right, mul_zero]
        exact zero_memℓp
      smul_mem' a x hx := by
        simpa only [Set.mem_ofPred_eq, inner_smul_right, mul_left_comm] using hx.const_mul a }
  toFun :=
    { toFun x := b.repr.symm ⟨fun i ↦ c i * ⟪b i, (x : E)⟫_𝕜, x.2⟩
      map_add' x y := by
        rw [← _root_.map_add]
        congr 1
        ext i
        simp only [lp.coeFn_add, Pi.add_apply, Submodule.coe_add, inner_add_right, mul_add]
      map_smul' a x := by
        rw [RingHom.id_apply, ← _root_.map_smul]
        congr 1
        ext i
        simp [inner_smul_right, mul_left_comm] }

private theorem diagonal_apply_eq_repr_symm (x : (b.diagonal c).domain) :
    b.diagonal c x = b.repr.symm ⟨fun i ↦ c i * ⟪b i, (x : E)⟫_𝕜, x.2⟩ :=
  rfl

/-- A vector lies in the domain of `b.diagonal c` if and only if its rescaled coordinate family
`c i * ⟪b i, x⟫` lies in `ℓ²`. -/
theorem mem_diagonal_domain_iff_memℓp {x : E} :
    x ∈ (b.diagonal c).domain ↔ Memℓp (fun i ↦ c i * ⟪b i, x⟫_𝕜) 2 :=
  Iff.rfl

/-- A vector lies in the domain of the diagonal operator `b.diagonal c` if and only if its
rescaled coordinates `c i * ⟪b i, x⟫` are square-summable. -/
theorem mem_diagonal_domain_iff {x : E} :
    x ∈ (b.diagonal c).domain ↔ Summable fun i ↦ ‖c i * ⟪b i, x⟫_𝕜‖ ^ 2 := by
  rw [mem_diagonal_domain_iff_memℓp, memℓp_gen_iff (by norm_num)]
  norm_num

/-- The coordinates of `b.diagonal c x` in the Hilbert basis `b` are `c i * ⟪b i, x⟫`. -/
@[simp]
theorem repr_diagonal_apply (x : (b.diagonal c).domain) (i : ι) :
    b.repr (b.diagonal c x) i = c i * ⟪b i, (x : E)⟫_𝕜 := by
  rw [diagonal_apply_eq_repr_symm, LinearIsometryEquiv.apply_symm_apply]

/-- The coordinates of `b.diagonal c x` in the Hilbert basis `b` are `c i * ⟪b i, x⟫`. -/
@[simp]
theorem inner_diagonal_apply (x : (b.diagonal c).domain) (i : ι) :
    ⟪b i, b.diagonal c x⟫_𝕜 = c i * ⟪b i, (x : E)⟫_𝕜 := by
  rw [← b.repr_apply_apply, repr_diagonal_apply]

/-- A vector `y` is the image of `x` under the diagonal operator if and only if its coordinates are
those of `x` multiplied by `c`. -/
theorem diagonal_apply_eq_iff (x : (b.diagonal c).domain) {y : E} :
    b.diagonal c x = y ↔ ∀ i, ⟪b i, y⟫_𝕜 = c i * ⟪b i, (x : E)⟫_𝕜 := by
  refine ⟨fun h i ↦ h ▸ b.inner_diagonal_apply c x i, fun h ↦ ?_⟩
  refine b.repr.injective (lp.ext (funext fun i ↦ ?_))
  rw [repr_diagonal_apply, b.repr_apply_apply, h]

/-- **The graph of a diagonal operator.** A pair `(x, y)` lies in the graph of `b.diagonal c` if
and only if `⟪b i, y⟫ = c i * ⟪b i, x⟫` for every `i`; in that case `x` automatically lies in the
domain. -/
theorem mem_graph_diagonal_iff {x y : E} :
    (x, y) ∈ (b.diagonal c).graph ↔ ∀ i, ⟪b i, y⟫_𝕜 = c i * ⟪b i, x⟫_𝕜 := by
  rw [mem_graph_iff]
  constructor
  · rintro ⟨x', hx, hy⟩
    simp only at hx hy
    subst hx hy
    exact (b.diagonal_apply_eq_iff c x').1 rfl
  · intro h
    have hx : x ∈ (b.diagonal c).domain := by
      have hf : (fun i ↦ c i * ⟪b i, x⟫_𝕜) = ⇑(b.repr y) :=
        funext fun i ↦ by rw [b.repr_apply_apply, h]
      rw [mem_diagonal_domain_iff_memℓp, hf]
      exact lp.memℓp _
    exact ⟨⟨x, hx⟩, rfl, (b.diagonal_apply_eq_iff c ⟨x, hx⟩).2 h⟩

/-- **Basis expansion of a diagonal operator.** `b.diagonal c x = ∑ᵢ (c i * ⟪b i, x⟫) • b i`. -/
theorem hasSum_diagonal_apply (x : (b.diagonal c).domain) :
    HasSum (fun i ↦ (c i * ⟪b i, (x : E)⟫_𝕜) • b i) (b.diagonal c x) := by
  simpa only [repr_diagonal_apply] using b.hasSum_repr (b.diagonal c x)

/-- **Parseval's identity for a diagonal operator.**
`‖b.diagonal c x‖² = ∑ᵢ ‖c i * ⟪b i, x⟫‖²`. -/
theorem hasSum_norm_diagonal_apply_sq (x : (b.diagonal c).domain) :
    HasSum (fun i ↦ ‖c i * ⟪b i, (x : E)⟫_𝕜‖ ^ 2) (‖b.diagonal c x‖ ^ 2) := by
  simpa only [inner_diagonal_apply] using b.hasSum_norm_sq_inner (b.diagonal c x)

/-- The coordinates of `c i • b i` are those of `b i` multiplied by `c`. -/
private theorem inner_smul_self (i j : ι) : ⟪b j, c i • b i⟫_𝕜 = c j * ⟪b j, b i⟫_𝕜 := by
  classical
  rw [inner_smul_right, orthonormal_iff_ite.1 b.orthonormal j i]
  split_ifs with h <;> simp [h]

/-- Every vector of the Hilbert basis lies in the domain of a diagonal operator. -/
@[simp]
theorem self_mem_diagonal_domain (i : ι) : b i ∈ (b.diagonal c).domain :=
  mem_domain_of_mem_graph <| (b.mem_graph_diagonal_iff c).2 (b.inner_smul_self c i)

/-- The basis vectors are eigenvectors of a diagonal operator: `b.diagonal c (b i) = c i • b i`. -/
@[simp]
theorem diagonal_apply_self (i : ι) :
    b.diagonal c ⟨b i, b.self_mem_diagonal_domain c i⟩ = c i • b i :=
  (b.diagonal_apply_eq_iff c _).2 (b.inner_smul_self c i)

/-- **Restrictions of a diagonal operator.** A partial linear map `T` is a restriction of
`b.diagonal c` if and only if the coordinates of `T x` are those of `x` multiplied by `c`. -/
theorem le_diagonal_iff {T : E →ₗ.[𝕜] E} :
    T ≤ b.diagonal c ↔ ∀ (x : T.domain) (i : ι), ⟪b i, T x⟫_𝕜 = c i * ⟪b i, (x : E)⟫_𝕜 := by
  refine ⟨fun h x i ↦ by rw [apply_comp_inclusion h x, inner_diagonal_apply,
    Submodule.coe_inclusion], fun h ↦ le_of_le_graph ?_⟩
  rintro ⟨x, y⟩ hp
  obtain ⟨x', hx, hy⟩ := (mem_graph_iff T).1 hp
  simp only at hx hy
  subst hx hy
  exact (b.mem_graph_diagonal_iff c).2 (h x')

/-- The domain of a diagonal operator contains the span of the Hilbert basis. -/
theorem span_le_diagonal_domain : Submodule.span 𝕜 (Set.range b) ≤ (b.diagonal c).domain :=
  Submodule.span_le.2 <| Set.range_subset_iff.2 (b.self_mem_diagonal_domain c)

/-- A diagonal operator is densely defined. -/
theorem dense_diagonal_domain : Dense ((b.diagonal c).domain : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff, ← b.dense_span]
  exact Submodule.topologicalClosure_mono (b.span_le_diagonal_domain c)

/-- A diagonal operator with bounded coefficients is defined everywhere. -/
theorem diagonal_domain_eq_top {C : ℝ} (hc : ∀ i, ‖c i‖ ≤ C) : (b.diagonal c).domain = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x ↦ (b.mem_diagonal_domain_iff c).2 ?_
  refine ((b.summable_norm_sq_inner x).mul_left (C ^ 2)).of_nonneg_of_le (fun _ ↦ by positivity)
    fun i ↦ ?_
  rw [norm_mul, mul_pow]
  gcongr
  exact hc i

/-- The domain of a composite of diagonal operators: `b.diagonal d x` lies in the domain of
`b.diagonal c` if and only if `x` lies in the domain of `b.diagonal (c * d)`. -/
theorem diagonal_apply_mem_diagonal_domain_iff (x : (b.diagonal d).domain) :
    (b.diagonal d x : E) ∈ (b.diagonal c).domain ↔ (x : E) ∈ (b.diagonal (c * d)).domain := by
  simp only [mem_diagonal_domain_iff, inner_diagonal_apply, Pi.mul_apply, mul_assoc]

/-- **Composition of diagonal operators.** `b.diagonal c (b.diagonal d x) = b.diagonal (c * d) x`
whenever the left-hand side is defined. -/
theorem diagonal_apply_diagonal_apply (x : (b.diagonal d).domain)
    (hx : (b.diagonal d x : E) ∈ (b.diagonal c).domain) :
    b.diagonal c ⟨b.diagonal d x, hx⟩ =
      b.diagonal (c * d) ⟨x, (b.diagonal_apply_mem_diagonal_domain_iff c d x).1 hx⟩ := by
  rw [diagonal_apply_eq_iff]
  intro i
  simp [mul_assoc]

/-- **Sum of diagonal operators.** `b.diagonal c + b.diagonal d`, defined on the intersection of
the two domains, is a restriction of `b.diagonal (c + d)`. -/
theorem diagonal_add_diagonal_le : b.diagonal c + b.diagonal d ≤ b.diagonal (c + d) :=
  (b.le_diagonal_iff _).2 fun x i ↦ by
    rw [LinearPMap.add_apply, inner_add_right, inner_diagonal_apply, inner_diagonal_apply,
      Pi.add_apply, add_mul]

variable [CompleteSpace E]

/-- **The adjoint of a diagonal operator** is the diagonal operator of the conjugate coefficients.
-/
@[simp]
theorem adjoint_diagonal : (b.diagonal c)† = b.diagonal (star c) := by
  have hdense := b.dense_diagonal_domain c
  refine eq_of_eq_graph (Submodule.ext fun ⟨y, z⟩ ↦ ?_)
  rw [mem_graph_diagonal_iff, mem_graph_iff]
  constructor
  · -- Pair the adjoint with the basis vectors, which are eigenvectors of `b.diagonal c`.
    rintro ⟨y', hy, hz⟩ i
    have h := adjoint_isFormalAdjoint hdense y' ⟨b i, b.self_mem_diagonal_domain c i⟩
    rw [diagonal_apply_self, inner_smul_right, hz, hy] at h
    rw [← inner_conj_symm, h, map_mul, inner_conj_symm, Pi.star_apply, RCLike.star_def]
  · -- Conversely, Parseval's identity shows that `z` represents `x ↦ ⟪y, b.diagonal c x⟫`.
    intro h
    have key (x : (b.diagonal c).domain) : ⟪z, (x : E)⟫_𝕜 = ⟪y, b.diagonal c x⟫_𝕜 := by
      rw [← b.tsum_inner_mul_inner z, ← b.tsum_inner_mul_inner y]
      refine tsum_congr fun i ↦ ?_
      rw [inner_diagonal_apply, ← inner_conj_symm z, h, Pi.star_apply, RCLike.star_def,
        map_mul, RCLike.conj_conj, inner_conj_symm]
      ring
    have hy : y ∈ (b.diagonal c)†.domain := mem_adjoint_domain_of_exists y ⟨z, key⟩
    exact ⟨⟨y, hy⟩, rfl, adjoint_apply_eq hdense _ key⟩

/-- A diagonal operator is closed. -/
theorem isClosed_diagonal : (b.diagonal c).IsClosed := by
  have h := adjoint_isClosed (b.dense_diagonal_domain (star c))
  rwa [adjoint_diagonal, star_star] at h

/-- A diagonal operator with a self-adjoint coefficient family, that is, with real coefficients, is
self-adjoint. -/
theorem isSelfAdjoint_diagonal {c : ι → 𝕜} (hc : IsSelfAdjoint c) :
    IsSelfAdjoint (b.diagonal c) := by
  rw [isSelfAdjoint_def, adjoint_diagonal, hc.star_eq]

end HilbertBasis

namespace LinearPMap

variable {ι ι' 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {A : E →ₗ.[𝕜] E} {b : HilbertBasis ι 𝕜 E} {lam : ι → ℝ}

/-- The coordinates of `A x` in a Hilbert basis of eigenvectors of a symmetric operator `A` are
those of `x` multiplied by the eigenvalues. -/
theorem IsFormalAdjoint.inner_apply_eq_mul_inner (hA : A.IsFormalAdjoint A)
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : 𝕜) • b i) (x : A.domain) (i : ι) :
    ⟪b i, A x⟫_𝕜 = lam i * ⟪b i, (x : E)⟫_𝕜 := by
  obtain ⟨hi, hAi⟩ := hb i
  rw [← hA ⟨b i, hi⟩ x, hAi, inner_smul_left, RCLike.conj_ofReal]

/-- A symmetric operator with a Hilbert basis `b` of eigenvectors, with real eigenvalues `λ i`, is
contained in the diagonal operator `b.diagonal λ`. -/
theorem IsFormalAdjoint.le_diagonal (hA : A.IsFormalAdjoint A)
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : 𝕜) • b i) :
    A ≤ b.diagonal fun i ↦ (lam i : 𝕜) :=
  (b.le_diagonal_iff _).2 (hA.inner_apply_eq_mul_inner hb)

/-- **Eigenbasis expansion.** If `b` is a Hilbert basis of eigenvectors of a symmetric operator `A`,
with real eigenvalues `λ i`, then `A x = ∑ᵢ (λ i * ⟪b i, x⟫) • b i`. -/
theorem IsFormalAdjoint.hasSum_apply (hA : A.IsFormalAdjoint A)
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : 𝕜) • b i) (x : A.domain) :
    HasSum (fun i ↦ ((lam i : 𝕜) * ⟪b i, (x : E)⟫_𝕜) • b i) (A x) := by
  simpa only [b.repr_apply_apply, hA.inner_apply_eq_mul_inner hb x] using b.hasSum_repr (A x)

/-- **The graph norm in an eigenbasis.** If `b` is a Hilbert basis of eigenvectors of a symmetric
operator `A`, with real eigenvalues `λ i`, then `‖x‖² + ‖A x‖² = ∑ᵢ (1 + λ i ²) ‖⟪b i, x⟫‖²`. -/
theorem IsFormalAdjoint.hasSum_norm_sq_add_norm_apply_sq (hA : A.IsFormalAdjoint A)
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : 𝕜) • b i) (x : A.domain) :
    HasSum (fun i ↦ (1 + lam i ^ 2) * ‖⟪b i, (x : E)⟫_𝕜‖ ^ 2) (‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2) := by
  have h := (b.hasSum_norm_sq_inner (x : E)).add (b.hasSum_norm_sq_inner (A x))
  refine h.congr_fun fun i ↦ ?_
  rw [hA.inner_apply_eq_mul_inner hb x, norm_mul, RCLike.norm_ofReal, mul_pow, sq_abs]
  ring

/-- In the presence of two Hilbert bases of eigenvectors of a symmetric operator, the diagonal
operator `b.diagonal (f ∘ λ)` is contained in `b'.diagonal (f ∘ λ')`. -/
private theorem IsFormalAdjoint.diagonal_le_diagonal (hA : A.IsFormalAdjoint A)
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : 𝕜) • b i)
    {b' : HilbertBasis ι' 𝕜 E} {lam' : ι' → ℝ}
    (hb' : ∀ j, ∃ hj : b' j ∈ A.domain, A ⟨b' j, hj⟩ = (lam' j : 𝕜) • b' j) (f : ℝ → 𝕜) :
    b.diagonal (fun i ↦ f (lam i)) ≤ b'.diagonal fun j ↦ f (lam' j) := by
  refine (b'.le_diagonal_iff _).2 fun x j ↦ ?_
  -- Expand `x` and its image in the basis `b`, and pair the expansions with `b' j`.
  have h₁ := (b.hasSum_diagonal_apply _ x).mapL (innerSL 𝕜 (b' j))
  have h₂ := (b.hasSum_repr (x : E)).mapL (innerSL 𝕜 (b' j))
  simp only [innerSL_apply_apply, inner_smul_right, b.repr_apply_apply] at h₁ h₂
  refine h₁.unique ((h₂.mul_left (f (lam' j))).congr_fun fun i ↦ ?_)
  -- Only the basis vectors `b i` with eigenvalue `λ' j` are not orthogonal to `b' j`.
  by_cases hij : lam' j = lam i
  · rw [hij]
    ring
  · obtain ⟨hj, hAj⟩ := hb' j
    obtain ⟨hi, hAi⟩ := hb i
    rw [hA.inner_eq_zero_of_apply_eq_smul (x := ⟨b' j, hj⟩) (y := ⟨b i, hi⟩) hAj hAi
      (RCLike.ofReal_injective.ne hij)]
    ring

/-- **Independence of the eigenbasis.** If `b` and `b'` are Hilbert bases of eigenvectors of a
symmetric operator `A`, with real eigenvalues `λ` and `λ'`, then for every function `f : ℝ → 𝕜` the
diagonal operators `b.diagonal (f ∘ λ)` and `b'.diagonal (f ∘ λ')` coincide. So the eigenbasis
functional calculus `f(A)` is well defined. -/
theorem IsFormalAdjoint.diagonal_eq_diagonal (hA : A.IsFormalAdjoint A)
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : 𝕜) • b i)
    {b' : HilbertBasis ι' 𝕜 E} {lam' : ι' → ℝ}
    (hb' : ∀ j, ∃ hj : b' j ∈ A.domain, A ⟨b' j, hj⟩ = (lam' j : 𝕜) • b' j) (f : ℝ → 𝕜) :
    b.diagonal (fun i ↦ f (lam i)) = b'.diagonal fun j ↦ f (lam' j) :=
  le_antisymm (hA.diagonal_le_diagonal hb hb' f) (hA.diagonal_le_diagonal hb' hb f)

variable [CompleteSpace E]

/-- **A self-adjoint operator is diagonal in an eigenbasis.** If `b` is a Hilbert basis of
eigenvectors of a self-adjoint operator `A`, with real eigenvalues `λ i`, then `A` is the diagonal
operator `b.diagonal λ`. -/
theorem _root_.IsSelfAdjoint.eq_diagonal (hA : IsSelfAdjoint A)
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : 𝕜) • b i) :
    A = b.diagonal fun i ↦ (lam i : 𝕜) := by
  have hle := hA.isFormalAdjoint.le_diagonal hb
  -- The diagonal operator is symmetric, so it is a formal adjoint of its restriction `A`.
  have hD : (b.diagonal fun i ↦ (lam i : 𝕜)).IsFormalAdjoint (b.diagonal fun i ↦ (lam i : 𝕜)) :=
    (b.isSelfAdjoint_diagonal (funext fun i ↦ RCLike.conj_ofReal (lam i))).isFormalAdjoint
  have hAD : A.IsFormalAdjoint (b.diagonal fun i ↦ (lam i : 𝕜)) := fun x y ↦ by
    rw [apply_comp_inclusion hle x, hD, Submodule.coe_inclusion]
  refine le_antisymm hle ?_
  have h := hAD.le_adjoint hA.dense_domain
  rwa [isSelfAdjoint_def.mp hA] at h

/-- **The graph-domain criterion.** If `b` is a Hilbert basis of eigenvectors of a self-adjoint
operator `A`, with real eigenvalues `λ i`, then `x` lies in the domain of `A` if and only if
`∑ᵢ (1 + λ i ²) ‖⟪b i, x⟫‖²` is finite. The sum is then `‖x‖² + ‖A x‖²`
(`LinearPMap.IsFormalAdjoint.hasSum_norm_sq_add_norm_apply_sq`). -/
theorem _root_.IsSelfAdjoint.mem_domain_iff_summable (hA : IsSelfAdjoint A)
    (hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : 𝕜) • b i) {x : E} :
    x ∈ A.domain ↔ Summable fun i ↦ (1 + lam i ^ 2) * ‖⟪b i, x⟫_𝕜‖ ^ 2 := by
  refine ⟨fun hx ↦ (hA.isFormalAdjoint.hasSum_norm_sq_add_norm_apply_sq hb ⟨x, hx⟩).summable,
    fun h ↦ ?_⟩
  rw [hA.eq_diagonal hb, HilbertBasis.mem_diagonal_domain_iff]
  refine h.of_nonneg_of_le (fun _ ↦ by positivity) fun i ↦ ?_
  rw [norm_mul, RCLike.norm_ofReal, mul_pow, sq_abs]
  gcongr
  linarith

end LinearPMap
