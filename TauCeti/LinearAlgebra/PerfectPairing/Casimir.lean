/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Coevaluation
public import TauCeti.LinearAlgebra.PerfectPairing.TrilinearProduct

/-!
# The Casimir of a perfect pairing

Let `p : M × N → R` be a perfect pairing over a commutative semiring `R`, with `N` finite and free.
For a finite basis `e` of `N` with left dual basis `e^i` of `M`, characterised by
`p (e^i) (e_j) = δ_ij` (`LinearMap.leftDualBasis`), the **Casimir** of `p` is the tensor

`∑ᵢ eᵢ ⊗ eⁱ ∈ N ⊗ M`

(`LinearMap.casimir`). It does not depend on the basis
(`LinearMap.casimir_eq_sum_tmul_leftDualBasis`). It is the copairing of `p`: contracting its `N`
factor against `p x` gives back `x`, and contracting its `M` factor against `p (·) y` gives back
`y` (`LinearMap.lid_rTensor_casimir`, `LinearMap.rid_lTensor_casimir`). The first of these
identities characterises it (`LinearMap.eq_casimir_iff`). For the evaluation pairing of a
finite-dimensional vector space with its dual, the Casimir is Mathlib's canonical tensor
`coevaluation K V 1` (`LinearMap.casimir_id_eq_coevaluation`); a general perfect pairing
transports it along the identification of `M` with the dual of `N`.

**The Gram-matrix form.** For a pairing `g : M × M → R` of a module with itself and a finite
basis `Δ` of `M`, write `g_ab = g (Δ_a) (Δ_b)` for its Gram matrix and `g^ab` for the inverse
matrix, which exists because `g` is perfect. The left dual basis is `Δ^a = ∑_b g^ab Δ_b`
(`LinearMap.leftDualBasis_eq_sum_inv_toMatrix₂`), so the Casimir is

`∑_(a, b) g^ab Δ_a ⊗ Δ_b`

(`LinearMap.casimir_eq_sum_sum_inv_toMatrix₂_smul_tmul`), the order of the two factors being that
of the indices of `g^ab`. For the Poincaré pairing `g(x, y) = ∫_X x ⌣ y` on the rational cohomology
of a closed oriented manifold this is the ordered Casimir which, by the Künneth theorem and
Poincaré duality, represents the class of the diagonal in `H^*(X × X)`; through it the splitting
axiom of Gromov–Witten theory contracts the two branches at a node (Kontsevich–Manin, 2.2.6).
Only the algebra of the Casimir is developed here. For the anti-diagonal pairing of a basis
`1, H, …, Hⁿ` with `g(Hⁱ, Hʲ) = 1` exactly when `i + j = n`, as for the cohomology of `ℂPⁿ`, the
Casimir is `∑ᵢ Hⁱ ⊗ Hⁿ⁻ⁱ` (`LinearMap.casimir_eq_sum_tmul_rev`).

**The contraction of the Casimir.** Evaluating `g` on its own Casimir gives `∑_(a, b) g^ab g_ab`.
If exchanging the arguments of `g` on basis vectors multiplies by a factor depending on the first
index, `g (Δ_b) (Δ_a) = s_a g (Δ_a) (Δ_b)`, then this contraction is `∑_a s_a`
(`LinearMap.lift_casimir_eq_sum`). For a graded-symmetric pairing, with `Δ_a` of degree `d_a`,
`g (Δ_b) (Δ_a) = (-1)^(d_a d_b) g (Δ_a) (Δ_b)` and `g_ab = 0` unless `d_a + d_b` is even, as for the
Poincaré pairing of an even-dimensional manifold, it is the alternating count `∑_a (-1)^(d_a)`,
the Euler characteristic (`LinearMap.lift_casimir_eq_sum_neg_one_pow`). On the two-torus, with basis
`1, α, β, pt` of degrees `0, 1, 1, 2`, it is `1 + 1 - 1 - 1 = 0`, while the unsigned count of basis
vectors is `4`.

**Products from trilinear forms.** The product `a ⋆ b` defined by a trilinear form `I` through `p`
(`LinearMap.trilinearProduct`) is the contraction of the Casimir against `I(a, b, ·)`
(`LinearMap.trilinearProduct_apply_eq_lid_rTensor_casimir`). For the Gromov–Witten three-point
correlator this is the quantum product `a ⋆ b = ∑_j ⟨a, b, e_j⟩ e^j`: the product is the
three-point correlator with its third insertion joined to the output by the diagonal.

## Main definitions

* `LinearMap.casimir`: the Casimir `∑ᵢ eᵢ ⊗ eⁱ ∈ N ⊗ M` of a perfect pairing `p : M × N → R`.

## Main results

* `LinearMap.casimir_eq_sum_tmul_leftDualBasis`: the Casimir in any finite basis.
* `LinearMap.lid_rTensor_casimir`, `LinearMap.rid_lTensor_casimir`, `LinearMap.eq_casimir_iff`:
  the Casimir is the copairing of `p`, and is characterised by this.
* `LinearMap.casimir_flip`: the Casimir of the flipped pairing is the swapped Casimir.
* `LinearMap.casimir_id_eq_coevaluation`: for the evaluation pairing it is `coevaluation K V 1`.
* `LinearMap.casimir_eq_sum_sum_inv_toMatrix₂_smul_tmul`: the Gram-matrix form, in bases of `M`
  and `N`; for one basis of a module paired with itself this is the ordered Casimir.
* `LinearMap.lift_casimir_eq_sum`, `LinearMap.lift_casimir_eq_sum_neg_one_pow`: the contraction of
  a pairing with its Casimir, and the Euler characteristic of a graded-symmetric pairing.

## References

* M. Kontsevich and Yu. Manin, *Gromov–Witten classes, quantum cohomology, and enumerative
  geometry*, Comm. Math. Phys. 164 (1994), 525–562, §2.2.6 (the Casimir and the splitting axiom).
-/

public section

open Module TensorProduct

namespace LinearMap

section CommSemiring

variable {ι κ R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair]

/-- The tensor `∑ᵢ eᵢ ⊗ eⁱ` of a finite basis `e` and its left dual basis does not depend on `e`. -/
private theorem sum_tmul_leftDualBasis_eq [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : Basis ι R N) (f : Basis κ R N) :
    ∑ i, e i ⊗ₜ[R] p.leftDualBasis e i = ∑ j, f j ⊗ₜ[R] p.leftDualBasis f j := by
  calc ∑ i, e i ⊗ₜ[R] p.leftDualBasis e i
      = ∑ i, (∑ j, f.repr (e i) j • f j) ⊗ₜ[R] p.leftDualBasis e i := by
        simp only [f.sum_repr]
    _ = ∑ j, f j ⊗ₜ[R] ∑ i, p (p.leftDualBasis f j) (e i) • p.leftDualBasis e i := by
        simp only [sum_tmul, tmul_sum, smul_tmul, apply_leftDualBasis_eq_repr]
        exact Finset.sum_comm
    _ = ∑ j, f j ⊗ₜ[R] p.leftDualBasis f j := by
        simp only [sum_apply_smul_leftDualBasis]

variable [Module.Free R N] [Module.Finite R N]

/-- The **Casimir** of a perfect pairing `p : M × N → R` on a finite free module `N`: the tensor
`∑ᵢ eᵢ ⊗ eⁱ ∈ N ⊗ M` of a finite basis `e` of `N` and its left dual basis `eⁱ` of `M`, with
`p (eⁱ) (eⱼ) = δᵢⱼ`. It does not depend on `e` (`LinearMap.casimir_eq_sum_tmul_leftDualBasis`). -/
noncomputable def casimir : N ⊗[R] M :=
  ∑ i, Free.chooseBasis R N i ⊗ₜ[R] p.leftDualBasis (Free.chooseBasis R N) i

/-- **The Casimir in a basis.** For every finite basis `e` of `N`, the Casimir of `p` is
`∑ᵢ eᵢ ⊗ eⁱ`, for the left dual basis `eⁱ` of `e`. -/
theorem casimir_eq_sum_tmul_leftDualBasis [Fintype ι] [DecidableEq ι] (e : Basis ι R N) :
    p.casimir = ∑ i, e i ⊗ₜ[R] p.leftDualBasis e i :=
  sum_tmul_leftDualBasis_eq p _ e

/-- **The Casimir is a copairing**: contracting its `N` factor against `p x` gives back `x`. -/
@[simp]
theorem lid_rTensor_casimir (x : M) : TensorProduct.lid R M ((p x).rTensor M p.casimir) = x := by
  simp [casimir_eq_sum_tmul_leftDualBasis p (Free.chooseBasis R N),
    sum_apply_smul_leftDualBasis]

/-- **The Casimir is a copairing**: contracting its `M` factor against `p (·) y` gives back `y`. -/
@[simp]
theorem rid_lTensor_casimir (y : N) :
    TensorProduct.rid R N ((p.flip y).lTensor N p.casimir) = y := by
  simp [casimir_eq_sum_tmul_leftDualBasis p (Free.chooseBasis R N), apply_leftDualBasis_eq_repr,
    Basis.sum_repr]

/-- **The Casimir is the only copairing of `p`**: a tensor `t ∈ N ⊗ M` is the Casimir exactly when
contracting its `N` factor against `p x` gives back `x` for every `x`. -/
theorem eq_casimir_iff {t : N ⊗[R] M} :
    t = p.casimir ↔ ∀ x, TensorProduct.lid R M ((p x).rTensor M t) = x := by
  refine ⟨fun h x ↦ h ▸ p.lid_rTensor_casimir x, fun h ↦ ?_⟩
  let e := Free.chooseBasis R N
  -- The coordinates of a tensor along `e` are its contractions against the left dual basis.
  have key (u : N ⊗[R] M) (i) :
      equivFinsuppOfBasisLeft e u i =
        TensorProduct.lid R M ((p (p.leftDualBasis e i)).rTensor M u) := by
    have : Finsupp.lapply i ∘ₗ (equivFinsuppOfBasisLeft e).toLinearMap =
        (TensorProduct.lid R M).toLinearMap ∘ₗ (p (p.leftDualBasis e i)).rTensor M :=
      TensorProduct.ext' fun y m ↦ by simp [apply_leftDualBasis_eq_repr]
    exact LinearMap.congr_fun this u
  refine (equivFinsuppOfBasisLeft e).injective (Finsupp.ext fun i ↦ ?_)
  rw [key, key, h, lid_rTensor_casimir]

/-- **The Casimir of the flipped pairing is the swapped Casimir.** -/
theorem casimir_flip [Module.Free R M] [Module.Finite R M] :
    p.flip.casimir = TensorProduct.comm R N M p.casimir := by
  let e := Free.chooseBasis R N
  have hf : ⇑(p.flip.leftDualBasis (p.leftDualBasis e)) = e :=
    ((p.flip.eq_leftDualBasis_iff _).2 fun i j ↦ by
      rw [flip_apply, apply_leftDualBasis]
      exact if_congr eq_comm rfl rfl).symm
  simp [p.flip.casimir_eq_sum_tmul_leftDualBasis (p.leftDualBasis e), hf,
    p.casimir_eq_sum_tmul_leftDualBasis e]

/-- **The Casimir of an anti-diagonal pairing.** If `p (fᵢ) (eⱼ)` is `1` when `i + j = n` and `0`
otherwise, then the Casimir of `p` is `∑ᵢ eᵢ ⊗ fₙ₋ᵢ`. For the basis `1, H, …, Hⁿ` of the
cohomology of `ℂPⁿ` and the Poincaré pairing, this is `∑ᵢ Hⁱ ⊗ Hⁿ⁻ⁱ`. -/
theorem casimir_eq_sum_tmul_rev {n : ℕ} (e : Basis (Fin (n + 1)) R N) {f : Fin (n + 1) → M}
    (h : ∀ i j : Fin (n + 1), p (f i) (e j) = if (i : ℕ) + j = n then 1 else 0) :
    p.casimir = ∑ i, e i ⊗ₜ[R] f i.rev := by
  simp only [p.casimir_eq_sum_tmul_leftDualBasis e, p.coe_leftDualBasis_eq_comp_rev e h,
    Function.comp_apply]

/-- **Products from trilinear forms contract the Casimir.** The product `a ⋆ b` that a trilinear
form `I` defines through `p` is the contraction of the Casimir against `I(a, b, ·)`. -/
theorem trilinearProduct_apply_eq_lid_rTensor_casimir {V W : Type*} [AddCommMonoid V]
    [Module R V] [AddCommMonoid W] [Module R W] (I : V →ₗ[R] W →ₗ[R] N →ₗ[R] R) (a : V) (b : W) :
    p.trilinearProduct I a b = TensorProduct.lid R M ((I a b).rTensor M p.casimir) := by
  simp [casimir_eq_sum_tmul_leftDualBasis p (Free.chooseBasis R N),
    p.trilinearProduct_apply_eq_sum (Free.chooseBasis R N)]

end CommSemiring

/-- **The Casimir of the evaluation pairing is the coevaluation.** For a finite-dimensional vector
space `V`, the Casimir of the evaluation pairing `V* × V → K` is Mathlib's canonical tensor
`∑ᵢ bᵢ ⊗ bᵢ* = coevaluation K V 1`. -/
theorem casimir_id_eq_coevaluation (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] :
    (LinearMap.id : Dual K V →ₗ[K] V →ₗ[K] K).casimir = coevaluation K V 1 := by
  classical
  set b := Basis.ofVectorSpace K V
  have hb : ⇑(LinearMap.id.leftDualBasis b) = fun i ↦ b.coord i :=
    ((LinearMap.id.eq_leftDualBasis_iff b).2 fun i j ↦ by
      simp [Finsupp.single_apply]).symm
  rw [casimir_eq_sum_tmul_leftDualBasis _ b, coevaluation_apply_one, hb]

section CommRing

variable {ι R M N : Type*} [Fintype ι] [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (p : M →ₗ[R] N →ₗ[R] R)
  [p.IsPerfPair]

/-- **The Casimir through the inverse Gram matrix.** For finite bases `b` of `M` and `e` of `N`
indexed by the same type, with Gram matrix `G_ij = p (bᵢ) (eⱼ)`, the Casimir of `p` is
`∑_(i, j) (G⁻¹)ᵢⱼ eᵢ ⊗ bⱼ`. For a pairing `g` of `M` with itself and one basis `Δ` of `M`, with
Gram matrix `g_ab = g (Δ_a) (Δ_b)` and inverse matrix `g^ab`, this is the ordered Casimir
`∑_(a, b) g^ab Δ_a ⊗ Δ_b`. -/
theorem casimir_eq_sum_sum_inv_toMatrix₂_smul_tmul [DecidableEq ι] [Module.Free R N]
    [Module.Finite R N] (b : Basis ι R M) (e : Basis ι R N) :
    p.casimir = ∑ i, ∑ j, (toMatrix₂ b e p)⁻¹ i j • (e i ⊗ₜ[R] b j) := by
  simp only [p.casimir_eq_sum_tmul_leftDualBasis e, p.leftDualBasis_eq_sum_inv_toMatrix₂ b e,
    tmul_sum, tmul_smul]

/-- **The contraction of a pairing with its Casimir.** Let `g` be a perfect pairing of `M` with
itself and `Δ` a finite basis of `M`. If exchanging the arguments of `g` on basis vectors
multiplies by `s`, `g (Δ_b) (Δ_a) = s_a g (Δ_a) (Δ_b)`, then evaluating `g` on its Casimir,
`∑_(a, b) g^ab g_ab`, gives `∑_a s_a`. For a symmetric pairing it is the rank of `M`. -/
theorem lift_casimir_eq_sum [Module.Free R M] [Module.Finite R M] (g : M →ₗ[R] M →ₗ[R] R)
    [g.IsPerfPair] (Δ : Basis ι R M) (s : ι → R)
    (h : ∀ a b, g (Δ b) (Δ a) = s a * g (Δ a) (Δ b)) :
    TensorProduct.lift g g.casimir = ∑ a, s a := by
  classical
  set G := toMatrix₂ Δ Δ g
  have hG : G * G⁻¹ = 1 := G.mul_nonsing_inv (Basis.isUnit_det_of_isPerfPair Δ Δ g ‹_›)
  -- In matrix form the contraction is the trace of `G⁻¹ diag(s) G`, since `Gᵀ = diag(s) G`.
  calc TensorProduct.lift g g.casimir = (G⁻¹ * Matrix.diagonal s * G).trace := by
        simp only [g.casimir_eq_sum_sum_inv_toMatrix₂_smul_tmul Δ Δ, map_sum, map_smul, lift.tmul,
          Matrix.trace, Matrix.diag, Matrix.mul_apply (M := G⁻¹ * Matrix.diagonal s),
          Matrix.mul_diagonal, smul_eq_mul]
        refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
        simp only [G, toMatrix₂_apply, h b a]
        ring
    _ = ∑ a, s a := by
        rw [Matrix.trace_mul_cycle, hG, one_mul, Matrix.trace_diagonal]

/-- **The Casimir contraction of a graded-symmetric pairing is the Euler characteristic.** Let `g`
be a perfect pairing of `M` with itself and `Δ` a finite basis of `M`, with `Δ_a` of degree `d_a`.
If `g` is graded symmetric, `g (Δ_b) (Δ_a) = (-1)^(d_a d_b) g (Δ_a) (Δ_b)`, and pairs basis vectors
trivially unless the sum of their degrees is even, as the Poincaré pairing of a closed
even-dimensional manifold does, then evaluating `g` on its Casimir gives `∑_a (-1)^(d_a)`. -/
theorem lift_casimir_eq_sum_neg_one_pow [Module.Free R M] [Module.Finite R M]
    (g : M →ₗ[R] M →ₗ[R] R) [g.IsPerfPair] (Δ : Basis ι R M) (d : ι → ℕ)
    (hsymm : ∀ a b, g (Δ b) (Δ a) = (-1) ^ (d a * d b) * g (Δ a) (Δ b))
    (heven : ∀ a b, g (Δ a) (Δ b) ≠ 0 → Even (d a + d b)) :
    TensorProduct.lift g g.casimir = ∑ a, (-1) ^ d a :=
  lift_casimir_eq_sum g Δ _ fun a b ↦ by
    rw [hsymm]
    by_cases h0 : g (Δ a) (Δ b) = 0
    · simp [h0]
    · congr 1
      rcases Nat.even_or_odd (d a) with ha | ha
      · rw [ha.neg_one_pow, (ha.mul_right _).neg_one_pow]
      · have hb : Odd (d b) := Nat.not_even_iff_odd.1 fun hb ↦
          Nat.not_even_iff_odd.2 ha ((Nat.even_add.1 (heven a b h0)).2 hb)
        rw [ha.neg_one_pow, (ha.mul hb).neg_one_pow]

end CommRing

end LinearMap
