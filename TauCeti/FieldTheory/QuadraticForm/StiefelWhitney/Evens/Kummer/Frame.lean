/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Evens.Kummer.Representation

/-!
# The frame of an orthogonal basis of the transferred plane

Let `L/K` be a separable quadratic extension, `σ : L → Kˢ` a `K`-embedding, `s ∈ G_K` outside
`G_L = galoisSubgroup K L σ`, `a ∈ Lˣ`, and `r ∈ Kˢ` a square root of `σ(a)`. The map
`φ(y) = (σ(y) r, s(σ(y) r))` (`TauCeti.kummerPoint`) realizes the transferred form `Tr_*⟨a⟩` inside
`(Kˢ)²`, and `g ∈ G_K` acts on its coordinates by `ρ_a(g)ᵀ`, where `ρ_a` is the signed-permutation
representation of `TauCeti.kummerInd`.

Let `(y₀, y₁)` be an orthogonal basis of `Tr_*⟨a⟩` with values `w_j = Tr_{L/K}(a y_j²)`, and choose
square roots `c_j ∈ Kˢ` of `w_j`. The matrix `P` whose `j`-th column is `φ(y_j)/c_j`
(`TauCeti.kummerFrame`) is orthogonal, and

```text
P⁻¹ ρ_a(g) g(P) = diag((−1)^{rootSign c₀ g}, (−1)^{rootSign c₁ g})
```

(`TauCeti.kummerFrame_conj`). In other words, in `Z¹(G_K, O₂(Kˢ))` the cocycle `ρ_a` is
cohomologous to the diagonal cocycle of the Kummer characters of `w₀` and `w₁`. This is the
diagonalization step of Serre's computation of the Evens norm of a Kummer class.

## Main definitions

* `TauCeti.kummerFrame`: the matrix whose `j`-th column is `φ(y_j)/c_j`.

## Main results

* `TauCeti.kummerFrame_mem_orthogonalGroup`: the frame of an orthogonal basis, normalized by
  square roots of its values, is an orthogonal matrix.
* `TauCeti.wreathSignedPerm_kummerInd_mul_map_kummerFrame`: `ρ_a(g) g(P) = P D(g)` for the
  diagonal sign matrix `D(g)` of the Kummer characters of the values.
* `TauCeti.kummerFrame_conj`: `P` is orthogonal and `P⁻¹ ρ_a(g) g(P) = D(g)`.

## References

* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. **59** (1984),
  651–676, second proof of Théorème 1′.
* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. **78** (1984), 223–256, Lemme II.2.1.
-/

public section

noncomputable section

namespace TauCeti

open Matrix

universe u v

variable {K : Type u} [Field K]

/-- **The frame of a basis of the transferred plane:** for `y : Fin 2 → L` and
`c : Fin 2 → Kˢ`, the matrix whose `j`-th column is `φ(y_j) / c_j`, where
`φ = kummerPoint σ r s`. -/
def kummerFrame {L : Type v} [Field L] [Algebra K L] (σ : L →ₐ[K] SeparableClosure K)
    (r : SeparableClosure K) (s : AbsoluteGaloisGroup K) (y : Fin 2 → L)
    (c : Fin 2 → SeparableClosure K) : Matrix (Fin 2) (Fin 2) (SeparableClosure K) :=
  Matrix.of fun i j => kummerPoint σ r s (y j) i / c j

/-- The `(i, j)` entry of the frame is the `i`-th coordinate of `φ(y_j) / c_j`. -/
@[simp]
theorem kummerFrame_apply {L : Type v} [Field L] [Algebra K L] (σ : L →ₐ[K] SeparableClosure K)
    (r : SeparableClosure K) (s : AbsoluteGaloisGroup K) (y : Fin 2 → L)
    (c : Fin 2 → SeparableClosure K) (i j : Fin 2) :
    kummerFrame σ r s y c i j = kummerPoint σ r s (y j) i / c j :=
  (rfl)

/-- **The frame of an orthogonal basis is orthogonal.** If `Tr_{L/K}(a y₀ y₁) = 0` and
`c_j² = Tr_{L/K}(a y_j²)` with `c_j ≠ 0`, then the columns `φ(y_j) / c_j` are orthonormal for the
unit form of `(Kˢ)²`. -/
theorem kummerFrame_mem_orthogonalGroup {L : Type v} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (σ : L →ₐ[K] SeparableClosure K)
    (hdeg : Module.finrank K L = 2) (a : L) (r : SeparableClosure K) (hr : r ^ 2 = σ a)
    (s : AbsoluteGaloisGroup K) (hs : s ∉ galoisSubgroup K L σ) {y : Fin 2 → L}
    (hy : Algebra.trace K L (a * y 0 * y 1) = 0) {c : Fin 2 → SeparableClosure K}
    (hc : ∀ i, c i ^ 2 = algebraMap K (SeparableClosure K) (Algebra.trace K L (a * y i ^ 2)))
    (hc0 : ∀ i, c i ≠ 0) :
    kummerFrame σ r s y c ∈ orthogonalGroup (Fin 2) (SeparableClosure K) := by
  rw [mem_orthogonalGroup_iff']
  -- The `(j, k)` entry of `Pᵀ P` is `φ(y_j) · φ(y_k) / (c_j c_k) = Tr(a y_j y_k) / (c_j c_k)`.
  have key (j k : Fin 2) : ((kummerFrame σ r s y c)ᵀ * kummerFrame σ r s y c) j k =
      algebraMap K (SeparableClosure K) (Algebra.trace K L (a * y j * y k)) / (c j * c k) := by
    rw [← kummerPoint_dotProduct σ hdeg a r hr s hs]
    simp [Matrix.mul_apply, dotProduct, Fin.sum_univ_two, div_mul_div_comm, add_div]
  have hy' : Algebra.trace K L (a * y 1 * y 0) = 0 := by rwa [mul_right_comm]
  ext j k
  rw [key]
  fin_cases j <;> fin_cases k
  · simp [← pow_two, mul_assoc, ← hc, hc0]
  · simp [hy]
  · simp [hy']
  · simp [← pow_two, mul_assoc, ← hc, hc0]

/-- **The frame turns `ρ_a` into a diagonal cocycle:** `ρ_a(g) g(P) = P D(g)`, where `P` is the
frame of `y` normalized by elements `c_j` whose squares lie in `K`, and
`D(g) = diag((−1)^{rootSign c₀ g}, (−1)^{rootSign c₁ g})`. No orthogonality of `y` and no
nonvanishing of `c` is needed for this identity. -/
theorem wreathSignedPerm_kummerInd_mul_map_kummerFrame {L : Type u}
    [Field L] [Algebra K L] [FiniteDimensional K L]
    (σ : L →ₐ[K] SeparableClosure K) (hdeg : Module.finrank K L = 2) (a : Lˣ)
    (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L)) (s : AbsoluteGaloisGroup K)
    (hs : s ∉ galoisSubgroup K L σ) (y : Fin 2 → L) {c : Fin 2 → SeparableClosure K}
    {w : Fin 2 → K} (hc : ∀ i, c i ^ 2 = algebraMap K (SeparableClosure K) (w i))
    (g : AbsoluteGaloisGroup K) :
    wreathSignedPerm (kummerInd σ hdeg a r hr s hs g) * (kummerFrame σ r s y c).map g =
      kummerFrame σ r s y c * diagonal fun i => (-1) ^ (rootSign (c i) g).val := by
  set ε : Fin 2 → SeparableClosure K := fun j => (-1) ^ (rootSign (c j) g).val
  have hε (j : Fin 2) : ε j * ε j = 1 := by simp [ε, ← mul_pow]
  -- `g` multiplies each normalizing element by its sign, since `g (c j) = ±c j`.
  have hgc (j : Fin 2) : g (c j) = ε j * c j := by
    exact apply_eq_neg_one_pow_rootSign_mul (g.apply_eq_or_eq_neg_of_sq_eq (hc j))
  -- By `kummerPoint_galois`, `g(P) = ρ_a(g)ᵀ P D(g)`; then `ρ_a(g) ρ_a(g)ᵀ = 1` concludes.
  have hmap : (kummerFrame σ r s y c).map g =
      (wreathSignedPerm (kummerInd σ hdeg a r hr s hs g))ᵀ * kummerFrame σ r s y c *
        diagonal ε := by
    refine Matrix.ext fun i j => ?_
    have hφ := congrFun (kummerPoint_galois σ hdeg a r hr s hs (y j) g) i
    rw [map_apply, kummerFrame_apply, map_div₀, hφ, hgc, mul_diagonal]
    simp only [Matrix.mul_apply, mulVec, dotProduct, Fin.sum_univ_two, kummerFrame_apply,
      div_eq_mul_inv, mul_inv, inv_eq_of_mul_eq_one_right (hε j)]
    ring
  rw [hmap, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    (mem_orthogonalGroup_iff _ _).1 (wreathSignedPerm_mem_orthogonalGroup _), Matrix.one_mul]

/-- **The diagonalization of `ρ_a`.** Let `y` be an orthogonal basis of `Tr_*⟨a⟩`, with values
`w_j = Tr_{L/K}(a y_j²)`, and let `c_j ∈ Kˢ` be nonzero with `c_j² = w_j`. Then the frame `P` of
`y` normalized by `c` is orthogonal and
`P⁻¹ ρ_a(g) g(P) = diag((−1)^{rootSign c₀ g}, (−1)^{rootSign c₁ g})`: in `Z¹(G_K, O₂(Kˢ))` the
cocycle `ρ_a = wreathSignedPerm ∘ kummerInd` is cohomologous to the diagonal cocycle of the Kummer
characters of `w₀` and `w₁`. -/
theorem kummerFrame_conj {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (σ : L →ₐ[K] SeparableClosure K)
    (hdeg : Module.finrank K L = 2) (a : Lˣ) (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L))
    (s : AbsoluteGaloisGroup K) (hs : s ∉ galoisSubgroup K L σ) (y : Fin 2 → L)
    (hy : Algebra.trace K L ((a : L) * y 0 * y 1) = 0) (c : Fin 2 → SeparableClosure K)
    (hc : ∀ i, c i ^ 2 = algebraMap K (SeparableClosure K) (Algebra.trace K L ((a : L) * y i ^ 2)))
    (hc0 : ∀ i, c i ≠ 0) (g : AbsoluteGaloisGroup K) :
    kummerFrame σ r s y c ∈ orthogonalGroup (Fin 2) (SeparableClosure K) ∧
      (kummerFrame σ r s y c)⁻¹ * wreathSignedPerm (kummerInd σ hdeg a r hr s hs g) *
          (kummerFrame σ r s y c).map g =
        diagonal fun i => (-1) ^ (rootSign (c i) g).val := by
  have hP := kummerFrame_mem_orthogonalGroup σ hdeg (a : L) r hr s hs hy hc hc0
  refine ⟨hP, ?_⟩
  rw [inv_eq_left_inv ((mem_orthogonalGroup_iff' _ _).1 hP), Matrix.mul_assoc,
    wreathSignedPerm_kummerInd_mul_map_kummerFrame σ hdeg a r hr s hs y hc g, ← Matrix.mul_assoc,
    (mem_orthogonalGroup_iff' _ _).1 hP, Matrix.one_mul]

end TauCeti
