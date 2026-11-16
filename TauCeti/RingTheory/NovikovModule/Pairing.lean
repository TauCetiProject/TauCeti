/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PerfectPairing.Basis
public import TauCeti.RingTheory.NovikovModule.Grading
public import TauCeti.RingTheory.NovikovModule.Topology
public import TauCeti.RingTheory.NovikovSeries.TopologicalRing

/-!
# Pairings of completed Novikov modules with constant Gram matrix

Let `V` and `W` be free modules over a commutative ring `R` with finite bases indexed by `ι₁`
and `ι₂`, and let `⟨·, ·⟩ : V × W → R` be a bilinear pairing with Gram matrix `G`. Over the
Novikov ring `Λ = NovikovSeries R H N` of an additive group `H` with period map `N`, the
completions `V ⊗̂ Λ` and `W ⊗̂ Λ` are the completed combinations `TauCeti.NovikovModule R F₁` and
`TauCeti.NovikovModule R F₂` of the generators `⟨i, p⟩`, with `p` in an `H`-torsor `P₁ i` (and
likewise for `W`), for potentials obeying `F (h +ᵥ p) = F p - N h`. Choosing a lift `r₁ i` in
each torsor identifies the basis vector `i` of `V` with the generator `⟨i, r₁ i⟩`, and the
generator `⟨i, h +ᵥ r₁ i⟩` with the monomial `e_i e^h`. The pairing extends `Λ`-bilinearly to

`⟨e_i e^h, f_j e^h'⟩ = G i j e^(h + h')`,

which is `TauCeti.NovikovModule.novikovPairingOfMatrix`: the `Λ`-bilinear map whose matrix in
the bases `TauCeti.NovikovModule.basis` of the lifts is `G`, read in `Λ` through the constant
series.
This is how the Poincaré pairing of a closed manifold extends to its quantum cohomology with
Novikov coefficients, where `H = H₂(X; ℤ)` and `N` is the symplectic area.

## Main results

* `TauCeti.NovikovModule.novikovPairingOfMatrix_apply`: in lift coordinates the pairing is
  `⟨a, b⟩ = ∑ i, ∑ j, G i j • (aᵢ * bⱼ)`.
* `TauCeti.NovikovModule.novikovPairingOfMatrix_single_single`: on generators the pairing is
  `⟨x ⟨i, p⟩, y ⟨j, q⟩⟩ = x y G i j e^((p -ᵥ r₁ i) + (q -ᵥ r₂ j))`.
* `TauCeti.NovikovModule.toMatrix₂_novikovPairingOfMatrix`: the matrix of the pairing in the
  bases of the lifts is the Gram matrix `G`, read in `Λ`.
* `TauCeti.NovikovModule.isPerfPair_novikovPairingOfMatrix_iff`: for `ι₁ = ι₂` the pairing is a
  perfect pairing of `Λ`-modules exactly when `G` has unit determinant over `R`. Over `R = ℚ`
  this says that a perfect rational pairing stays perfect over the Novikov ring, although `Λ`
  need not be a field or a domain.
* `TauCeti.NovikovModule.novikovPairingOfMatrix_mem_gradeBy`: if `G i j` vanishes unless the
  degrees of the lifts add up to `n`, the pairing maps homogeneous combinations of degrees `k`
  and `l` to a homogeneous series of degree `k + l - n`.
* `TauCeti.NovikovModule.continuous_novikovPairingOfMatrix`: the pairing is jointly continuous for
  the potential-cutoff and period topologies.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 11.1,
  on quantum cohomology with Novikov coefficients and its Poincaré pairing.
-/

public section

noncomputable section

open Matrix

namespace TauCeti.NovikovModule

variable {R H ι₁ ι₂ : Type*} [AddCommGroup H] {N : H →+ ℝ}
  {P₁ : ι₁ → Type*} [∀ i, AddTorsor H (P₁ i)] {F₁ : (Σ i, P₁ i) → ℝ}
  (hF₁ : ∀ i h (p : P₁ i), F₁ ⟨i, h +ᵥ p⟩ = F₁ ⟨i, p⟩ - N h)

section TwoModules

variable {P₂ : ι₂ → Type*} [∀ j, AddTorsor H (P₂ j)] {F₂ : (Σ j, P₂ j) → ℝ}
  (hF₂ : ∀ j h (p : P₂ j), F₂ ⟨j, h +ᵥ p⟩ = F₂ ⟨j, p⟩ - N h) (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j)

section CommSemiring

variable [CommSemiring R] [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
  (G : Matrix ι₁ ι₂ R)

/-- **The Novikov extension of a pairing with Gram matrix `G`.** The `Λ`-bilinear pairing of
completed combinations, for the Novikov module structures of `TauCeti.NovikovModule.module`,
whose value on the basis vectors of the lifts `r₁ i` and `r₂ j` is the constant series `G i j`.
On generators it is `⟨e_i e^h, f_j e^h'⟩ = G i j e^(h + h')`
(`TauCeti.NovikovModule.novikovPairingOfMatrix_single_single`). -/
def novikovPairingOfMatrix :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₂
    NovikovModule R F₁ →ₗ[NovikovSeries R H N] NovikovModule R F₂ →ₗ[NovikovSeries R H N]
      NovikovSeries R H N :=
  letI := module (R := R) hF₁
  letI := module (R := R) hF₂
  Matrix.toLinearMap₂ (basis hF₁ r₁) (basis hF₂ r₂) (G.map (algebraMap R (NovikovSeries R H N)))

/-- **The coordinate formula for the pairing.** In the coordinates relative to the lifts,
`⟨a, b⟩ = ∑ i, ∑ j, G i j • (aᵢ * bⱼ)`. -/
theorem novikovPairingOfMatrix_apply (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G a b =
      ∑ i, ∑ j, G i j • (coordinates hF₁ r₁ a i * coordinates hF₂ r₂ b j) := by
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  simp only [novikovPairingOfMatrix, Matrix.toLinearMap₂_apply, basis_repr_apply, map_apply,
    NovikovSeries.algebraMap_self_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← NovikovSeries.single_zero_mul_eq_smul]
  ring

/-- The pairing of the basis vectors of the lifts `r₁ i` and `r₂ j` is the constant series
`G i j`. -/
@[simp]
theorem novikovPairingOfMatrix_basis_basis (i : ι₁) (j : ι₂) :
    novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G (basis hF₁ r₁ i) (basis hF₂ r₂ j) =
      NovikovSeries.single 0 (G i j) := by
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  rw [novikovPairingOfMatrix, Matrix.toLinearMap₂_apply_basis, map_apply,
    NovikovSeries.algebraMap_self_apply]

/-- **The matrix of the pairing is the Gram matrix.** In the bases of the lifts, the matrix of
the pairing is `G`, read in `Λ` through the constant series. -/
theorem toMatrix₂_novikovPairingOfMatrix :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₂
    LinearMap.toMatrix₂ (basis hF₁ r₁) (basis hF₂ r₂) (novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G) =
      G.map (algebraMap R (NovikovSeries R H N)) := by
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  exact LinearMap.toMatrix₂_toLinearMap₂ _ _ _

/-- **The pairing on generators.** The pairing of the point masses `x` at a generator `p` of the
orbit `i` and `y` at a generator `q` of the orbit `j` is the monomial
`x y G i j e^((p -ᵥ r₁ i) + (q -ᵥ r₂ j))`. -/
theorem novikovPairingOfMatrix_single_single [DecidableEq (Σ i, P₁ i)] [DecidableEq (Σ j, P₂ j)]
    (i : ι₁) (p : P₁ i) (j : ι₂) (q : P₂ j) (x y : R) :
    novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G (single ⟨i, p⟩ x) (single ⟨j, q⟩ y) =
      NovikovSeries.single ((p -ᵥ r₁ i) + (q -ᵥ r₂ j)) (x * y * G i j) := by
  simp [novikovPairingOfMatrix_apply, Pi.single_apply, NovikovSeries.single_mul_single,
    NovikovSeries.smul_single, mul_comm]

/-- The flipped pairing is the pairing of the transposed Gram matrix. -/
theorem flip_novikovPairingOfMatrix :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₂
    (novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G).flip = novikovPairingOfMatrix hF₂ hF₁ r₂ r₁ Gᵀ := by
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  refine (basis hF₂ r₂).ext fun j => (basis hF₁ r₁).ext fun i => ?_
  rw [LinearMap.flip_apply, novikovPairingOfMatrix_basis_basis, novikovPairingOfMatrix_basis_basis,
    transpose_apply]

end CommSemiring

section Grading

variable [CommSemiring R] [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
  {D : Type*} [AddCommGroup D] (δ : H →+ D) {d₁ : (Σ i, P₁ i) → D} {d₂ : (Σ j, P₂ j) → D}
  (hd₁ : ∀ i h (p : P₁ i), d₁ ⟨i, h +ᵥ p⟩ = δ h + d₁ ⟨i, p⟩)
  (hd₂ : ∀ j h (p : P₂ j), d₂ ⟨j, h +ᵥ p⟩ = δ h + d₂ ⟨j, p⟩)

include hd₁ hd₂ in
/-- **The pairing lowers degree by `n`.** If the Gram matrix pairs only lifts whose degrees add
up to `n`, then the pairing maps combinations of degrees `k` and `l` to a series of degree
`k + l - n`, for the degree `δ` of the monomials. -/
theorem novikovPairingOfMatrix_mem_gradeBy {G : Matrix ι₁ ι₂ R} {n k l : D}
    (hG : ∀ i j, G i j ≠ 0 → d₁ ⟨i, r₁ i⟩ + d₂ ⟨j, r₂ j⟩ = n)
    {a : NovikovModule R F₁} {b : NovikovModule R F₂}
    (ha : a ∈ gradeBy R F₁ d₁ k) (hb : b ∈ gradeBy R F₂ d₂ l) :
    novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G a b ∈ NovikovSeries.gradeBy R N δ (k + l - n) := by
  rw [mem_gradeBy_iff_coordinates hF₁ δ hd₁ r₁] at ha
  rw [mem_gradeBy_iff_coordinates hF₂ δ hd₂ r₂] at hb
  rw [novikovPairingOfMatrix_apply]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  by_cases hij : G i j = 0
  · rw [hij, zero_smul]
    exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ ?_
    have hdeg : k - d₁ ⟨i, r₁ i⟩ + (l - d₂ ⟨j, r₂ j⟩) = k + l - n := by
      rw [← hG i j hij]
      abel
    rw [← hdeg]
    exact SetLike.mul_mem_graded (ha i) (hb j)

end Grading

section Topology

variable [CommRing R] [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
  (G : Matrix ι₁ ι₂ R)

/-- **The pairing is jointly continuous** for the potential-cutoff topologies of the completed
combinations and the period topology of the Novikov ring. -/
theorem continuous_novikovPairingOfMatrix :
    Continuous fun x : NovikovModule R F₁ × NovikovModule R F₂ =>
      novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G x.1 x.2 := by
  simp only [novikovPairingOfMatrix_apply]
  fun_prop

end Topology

end TwoModules

section Perfect

variable {P₂ : ι₁ → Type*} [∀ j, AddTorsor H (P₂ j)] {F₂ : (Σ j, P₂ j) → ℝ}
  (hF₂ : ∀ j h (p : P₂ j), F₂ ⟨j, h +ᵥ p⟩ = F₂ ⟨j, p⟩ - N h) (r₁ : ∀ i, P₁ i) (r₂ : ∀ j, P₂ j)
  [CommRing R] [Fintype ι₁] [DecidableEq ι₁]

/-- **The Novikov extension of a pairing is perfect exactly when the Gram matrix is invertible.**
For bases indexed by the same finite type, the `Λ`-bilinear pairing with Gram matrix `G` is a
perfect pairing exactly when `det G` is a unit of `R`. In particular a perfect pairing over a
field stays perfect over the Novikov ring, which need not be a field or a domain. -/
theorem isPerfPair_novikovPairingOfMatrix_iff (G : Matrix ι₁ ι₁ R) :
    letI := module (R := R) hF₁
    letI := module (R := R) hF₂
    (novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G).IsPerfPair ↔ IsUnit G.det := by
  let := module (R := R) hF₁
  let := module (R := R) hF₂
  have hdet : (LinearMap.toMatrix₂ (basis hF₁ r₁) (basis hF₂ r₂)
      (novikovPairingOfMatrix hF₁ hF₂ r₁ r₂ G)).det = NovikovSeries.single 0 G.det := by
    rw [toMatrix₂_novikovPairingOfMatrix, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      NovikovSeries.algebraMap_self_apply]
  rw [← NovikovSeries.isUnit_single_zero_iff (H := H) (N := N), ← hdet]
  exact ⟨Module.Basis.isUnit_det_of_isPerfPair _ _ _,
    Module.Basis.isPerfPair_of_isUnit_det _ _ _⟩

end Perfect

end TauCeti.NovikovModule
