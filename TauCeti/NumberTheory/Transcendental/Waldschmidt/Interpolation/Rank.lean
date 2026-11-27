/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Transcendental.Waldschmidt.Interpolation.Matrix
import TauCeti.Algebra.MvPolynomial.PDeriv

/-!
# The rank of Waldschmidt's interpolation matrix

Waldschmidt's interpolation matrix `TauCeti.waldschmidtInterpolationMatrix` has a row for each
monomial `z^τ` of total degree at most `T₀` and each exponent `t` in a finite set `T` (in the
application `T = [-T₁, T₁]`), and a column for each differential operator `P(∂/∂z₀)` and grid point
`s · y`. If the grid points and the direction `e₀` of the derivatives lie in a subspace `W ⊆ Kᵐ`,
its rank is at most `L = (T₀ + dim W choose dim W) · #T`
(`TauCeti.rank_waldschmidtInterpolationMatrix_le_of_mem`): a row only depends on `t` and on the
restriction of `z^τ` to `W`.

In the rank argument of Waldschmidt's proof (W00 §9.2.3), this bound is attained because of a zero
estimate. This file proves the linear algebra connecting the two, when the field `K` is infinite:
the rank is exactly `L` if and only if the conclusion of the zero estimate holds, namely that
every family `(G_t)_{t ∈ T}` of polynomials of total degree at most `T₀` whose combined entries
`∑_{t ∈ T} waldschmidtOperatorEntry α b t (s c) (G t) (P c)` vanish on all columns `c` consists of
polynomials vanishing on `W`. In the language of the proof: no auxiliary polynomial
`∑_t G_t(z) Y^t` on `W × 𝔾ₘ` that is nonzero there vanishes to the prescribed order at the
points of the grid. The zero estimate itself, the torus and additive-group multiplicity
argument of W00 §9.2.3, is not proved here.

## Main results

* `TauCeti.rank_waldschmidtInterpolationMatrix_eq_iff_of_mem`: if the grid points and `e₀` lie
  in `W`, the rank is `(T₀ + dim W choose dim W) · #T` if and only if the conclusion of the zero
  estimate holds on `W`.
* `TauCeti.rank_waldschmidtInterpolationMatrix_eq_iff`: for column indices in a subspace `V`
  containing the coefficient vector, the rank is `L_d = (T₀ + d choose d) · #T` with
  `d = dim V` if and only if the conclusion of the zero estimate holds on `W = V · y + K e₀`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §9.2.3, Proposition 9.16.
-/

public section

open Finset Function MvPolynomial Module

namespace TauCeti

variable {n : ℕ} {K : Type*} [Field K]

/-- The rows of the interpolation matrix with the monomial rows span the image of the linear map
sending a family `(G_t)_{t ∈ T}` of polynomials of total degree at most `T₀` to its combined
entries `c ↦ ∑_{t ∈ T} waldschmidtOperatorEntry α b t (s c) (G t) (P c)`. -/
private theorem span_row_waldschmidtInterpolationMatrix_monomial {κ : Type*}
    (α b : Fin (n + 1) → K) (P : κ → Polynomial K) (s : κ → Fin (n + 1) → ℤ) (T₀ : ℕ)
    (T : Finset ℤ) :
    Submodule.span K (Set.range (waldschmidtInterpolationMatrix α b
        (fun r : {τ : Fin (n + 1) →₀ ℕ // τ.degree ≤ T₀} × T ↦ monomial r.1.val 1)
        (fun r ↦ r.2.val) P s).row) =
      LinearMap.range (∑ t : T,
        (LinearMap.pi fun c ↦ (waldschmidtOperatorEntry α b t (s c)).flip (P c)) ∘ₗ
          (restrictTotalDegree (Fin (n + 1)) K T₀).subtype ∘ₗ LinearMap.proj t) := by
  classical
  set Ψ : (T → restrictTotalDegree (Fin (n + 1)) K T₀) →ₗ[K] κ → K := ∑ t : T,
    (LinearMap.pi fun c ↦ (waldschmidtOperatorEntry α b t (s c)).flip (P c)) ∘ₗ
      (restrictTotalDegree (Fin (n + 1)) K T₀).subtype ∘ₗ LinearMap.proj t
  -- The row `(τ, t)` is the image of the basis vector `z^τ` in the `t`-th factor.
  let B := Pi.basis fun _ : T ↦ basisRestrictTotalDegree (Fin (n + 1)) K T₀
  have hrow (τ : {τ : Fin (n + 1) →₀ ℕ // τ.degree ≤ T₀}) (t : T) :
      (waldschmidtInterpolationMatrix α b
        (fun r : {τ : Fin (n + 1) →₀ ℕ // τ.degree ≤ T₀} × T ↦ monomial r.1.val 1)
        (fun r ↦ r.2.val) P s).row (τ, t) = Ψ (B ⟨t, τ⟩) := by
    ext c
    have hΨ : Ψ (B ⟨t, τ⟩) c =
        ∑ t' : T, waldschmidtOperatorEntry α b t' (s c) (B ⟨t, τ⟩ t') (P c) := by
      simp [Ψ]
    rw [hΨ, Finset.sum_eq_single t (fun t' _ ht' ↦ by simp [B, ht']) (by simp)]
    simp [B]
  rw [LinearMap.range_eq_map, ← B.span_eq, Submodule.map_span, ← Set.range_comp]
  congr 1
  ext v
  exact ⟨fun ⟨⟨τ, t⟩, h⟩ ↦ ⟨⟨t, τ⟩, (hrow τ t).symm.trans h⟩,
    fun ⟨⟨t, τ⟩, h⟩ ↦ ⟨(τ, t), (hrow τ t).trans h⟩⟩

/-- **The rank of the interpolation matrix and the zero estimate.** Take the monomial rows
`z^τ exp(t (z₀ + λ₁ z₁ + ⋯))`, `τ` of total degree at most `T₀` and `t ∈ T`, and columns
`(P c, s c)` whose grid points `s c · y` lie in a subspace `W ⊆ Kᵐ` containing the direction `e₀`
of the derivatives. Then the interpolation matrix has the largest possible rank
`(T₀ + dim W choose dim W) · #T` if and only if the conclusion of a zero estimate on `W` holds:
whenever polynomials `G_t` of total degree at most `T₀` have vanishing combined entries
`∑_{t ∈ T} waldschmidtOperatorEntry α b t (s c) (G t) (P c)` on every column `c`, each `G_t`
vanishes on `W`. -/
theorem rank_waldschmidtInterpolationMatrix_eq_iff_of_mem [Infinite K] {κ : Type*} [Finite κ]
    (α b : Fin (n + 1) → K) (P : κ → Polynomial K) {s : κ → Fin (n + 1) → ℤ} (T₀ : ℕ)
    (T : Finset ℤ) {W : Submodule K (Fin (n + 1) → K)} (hW : Pi.single 0 1 ∈ W)
    (hs : ∀ c, waldschmidtPoint b (s c) ∈ W) :
    (waldschmidtInterpolationMatrix α b
        (fun r : {τ : Fin (n + 1) →₀ ℕ // τ.degree ≤ T₀} × T ↦ monomial r.1.val 1)
        (fun r ↦ r.2.val) P s).rank = (T₀ + finrank K W).choose (finrank K W) * #T ↔
      ∀ G : T → MvPolynomial (Fin (n + 1)) K, (∀ t, G t ∈ restrictTotalDegree _ K T₀) →
        (∀ c, ∑ t : T, waldschmidtOperatorEntry α b t (s c) (G t) (P c) = 0) →
        ∀ t, ∀ w ∈ W, eval w (G t) = 0 := by
  set d := finrank K W
  set Pol := restrictTotalDegree (Fin (n + 1)) K T₀
  -- The combined entries of a family `(G_t)` of polynomials: the rows span their image.
  let Ψ : (T → Pol) →ₗ[K] κ → K := ∑ t : T,
    (LinearMap.pi fun c ↦ (waldschmidtOperatorEntry α b t (s c)).flip (P c)) ∘ₗ Pol.subtype ∘ₗ
      LinearMap.proj t
  have hΨ (G : T → Pol) (c : κ) :
      Ψ G c = ∑ t : T, waldschmidtOperatorEntry α b t (s c) (G t) (P c) := by
    simp [Ψ]
  have hrange : _ = LinearMap.range Ψ :=
    span_row_waldschmidtInterpolationMatrix_monomial α b P s T₀ T
  obtain ⟨R, hR, hRker⟩ := W.exists_surjective_linearMap_restrictTotalDegree T₀
  -- The componentwise restriction `RT` is onto, and its kernel lies in the kernel of `Ψ`.
  let RT : (T → Pol) →ₗ[K] T → restrictTotalDegree (Fin d) K T₀ :=
    LinearMap.pi fun t ↦ R ∘ₗ LinearMap.proj t
  have hRT : LinearMap.range RT = ⊤ := by
    refine LinearMap.range_eq_top.2 fun H ↦ ⟨fun t ↦ (hR (H t)).choose, funext fun t ↦ ?_⟩
    simp [RT, (hR (H t)).choose_spec]
  have hmemRT (G : T → Pol) : G ∈ LinearMap.ker RT ↔
      ∀ t, ∀ w ∈ W, eval w (G t : MvPolynomial (Fin (n + 1)) K) = 0 := by
    rw [LinearMap.mem_ker]
    exact ⟨fun h t ↦ (hRker (G t)).1 (congrFun h t),
      fun h ↦ funext fun t ↦ (hRker (G t)).2 (h t)⟩
  have hker : LinearMap.ker RT ≤ LinearMap.ker Ψ := by
    intro G hG
    refine LinearMap.mem_ker.2 (funext fun c ↦ ?_)
    rw [hΨ, Pi.zero_apply]
    refine Finset.sum_eq_zero fun t _ ↦ ?_
    rw [waldschmidtOperatorEntry_eq_sum_hasseDeriv]
    simp [eval_iterate_pderiv_eq_zero_of_forall_mem hW ((hmemRT G).1 hG t) _ _ (hs c)]
  -- Rank-nullity for `Ψ` and for `RT`: the rank is maximal iff the two kernels agree.
  have h₁ := LinearMap.finrank_range_add_finrank_ker Ψ
  have h₂ := LinearMap.finrank_range_add_finrank_ker RT
  have h₃ := Submodule.finrank_mono hker
  have h₄ : finrank K (LinearMap.range RT) = (T₀ + d).choose d * #T := by
    rw [hRT, finrank_top, Module.finrank_pi_fintype, finrank_restrictTotalDegree]
    simp [mul_comm]
  rw [← Matrix.finrank_span_range_row, hrange]
  constructor
  · intro hrank G hG hZ
    have heq : LinearMap.ker RT = LinearMap.ker Ψ :=
      Submodule.eq_of_le_of_finrank_eq hker (by lia)
    have hmem : (fun t ↦ ⟨G t, hG t⟩ : T → Pol) ∈ LinearMap.ker RT := by
      rw [heq]
      exact LinearMap.mem_ker.2 (funext fun c ↦ by simpa [hΨ] using hZ c)
    exact (hmemRT _).1 hmem
  · intro hZ
    have hle : LinearMap.ker Ψ ≤ LinearMap.ker RT := fun G hG ↦
      (hmemRT G).2 (hZ (fun t ↦ G t) (fun t ↦ (G t).property) fun c ↦ by
        simpa [hΨ] using congrFun (LinearMap.mem_ker.1 hG) c)
    have := Submodule.finrank_mono hle
    lia

/-- **Rank of the interpolation matrix on a residual subspace.** Take the monomial rows, `τ` of
total degree at most `T₀` and `t ∈ T`, and let the column indices `s c` lie in a subspace
`V ⊆ Kᵐ` containing the coefficient vector `(β₁, …, β_{m-1}, -1)` of the normalized linear form.
Then the interpolation matrix has rank `(T₀ + d choose d) · #T` with `d = dim V` (for
`T = [-T₁, T₁]` this is `L_d = (T₀ + d choose d) (2 T₁ + 1)`) if and only if the conclusion of a
zero estimate holds on `W = V · y + K e₀`, the subspace spanned by the grid points and the
direction of the derivatives. -/
theorem rank_waldschmidtInterpolationMatrix_eq_iff [Infinite K] {κ : Type*} [Finite κ]
    (α b : Fin (n + 1) → K) (P : κ → Polynomial K) {s : κ → Fin (n + 1) → ℤ} (T₀ : ℕ)
    (T : Finset ℤ) {V : Submodule K (Fin (n + 1) → K)}
    (hV : Fin.snoc (fun k : Fin n ↦ b k.succ) (-1) ∈ V) (hs : ∀ c, (fun i ↦ (s c i : K)) ∈ V) :
    (waldschmidtInterpolationMatrix α b
        (fun r : {τ : Fin (n + 1) →₀ ℕ // τ.degree ≤ T₀} × T ↦ monomial r.1.val 1)
        (fun r ↦ r.2.val) P s).rank = (T₀ + finrank K V).choose (finrank K V) * #T ↔
      ∀ G : T → MvPolynomial (Fin (n + 1)) K, (∀ t, G t ∈ restrictTotalDegree _ K T₀) →
        (∀ c, ∑ t : T, waldschmidtOperatorEntry α b t (s c) (G t) (P c) = 0) →
        ∀ t, ∀ w ∈ V.map (waldschmidtPointMap b) ⊔ K ∙ Pi.single 0 1, eval w (G t) = 0 := by
  rw [← finrank_map_waldschmidtPointMap_sup b hV]
  refine rank_waldschmidtInterpolationMatrix_eq_iff_of_mem α b P T₀ T
    (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)) fun c ↦ ?_
  rw [← waldschmidtPointMap_intCast]
  exact Submodule.mem_sup_left (Submodule.mem_map_of_mem (hs c))

end TauCeti
