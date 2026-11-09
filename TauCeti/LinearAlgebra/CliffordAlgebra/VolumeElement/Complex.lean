/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Complexification
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dual
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Oriented

/-!
# The normalized complex volume element of an oriented Euclidean space

Let `V` be an oriented real inner product space of dimension `n` and `Q` a quadratic form on `V`.
For the geometric convention `Q v = -‖v‖²`, so that `c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫`, the
**normalized complex volume element** is

  `Γ = i ^ ⌊(n + 1) / 2⌋ c(e₁) ⋯ c(eₙ)`

in the complexified Clifford algebra `Cℓ(ℂ ⊗ V, Q_ℂ)`, for any positively oriented orthonormal
basis `e`. It is defined without a frame, as `i ^ ⌊(n + 1) / 2⌋` times the image of the real
volume element `CliffordAlgebra.volumeElement Q o`, so the frame formula
`CliffordAlgebra.complexVolume_eq` is its independence under orientation-preserving orthonormal
changes of frame, and reversing the orientation changes its sign.

In even dimension `n = 2ℓ` this is `Γ = i ^ ℓ c(e₁) ⋯ c(e₂ₗ)`, the chirality operator: it
anticommutes with every vector, so its `±1` eigenspaces in a Clifford module are exchanged by
Clifford multiplication, and conjugation by `Γ` is the grade involution. In odd dimension
`n = 2ℓ + 1` it is `ω_ℂ = i ^ (ℓ + 1) c(e₁) ⋯ c(eₙ)`, a central element whose `±1` eigenspaces
separate the two irreducible Clifford modules. The power of `i` is chosen so that `Γ` squares to
`1` and is fixed by the conjugate-linear Clifford involution `CliffordAlgebra.conjStar`, so that
it acts as a self-adjoint involution in every `*`-representation. The complex-linear Clifford
conjugation `star` instead multiplies it by `(-1) ^ ⌊(n + 1) / 2⌋`. In rank zero, `Γ` is `1` for
the positive orientation and `-1` for the negative one.

## Main definitions

* `CliffordAlgebra.complexVolume Q o`: the normalized complex volume element `Γ` of
  `CliffordAlgebra (Q.baseChange ℂ)`.

## Main results

* `CliffordAlgebra.complexVolume_eq`: `Γ = i ^ ⌊(n + 1) / 2⌋ c(e₁) ⋯ c(eₙ)` for every positively
  oriented orthonormal basis `e` that is orthogonal for `Q`, and
  `CliffordAlgebra.complexVolume_eq_prod_pairs`: in dimension `2ℓ` it groups as
  `Γ = i ^ ℓ (c(e₁) c(e₂)) ⋯ (c(e₂ℓ₋₁) c(e₂ℓ))`, while
  `CliffordAlgebra.complexVolume_eq_prod_pairs_mul`: in dimension `2ℓ + 1` it groups as
  `ω_ℂ = i ^ (ℓ + 1) (c(e₁) c(e₂)) ⋯ (c(e₂ℓ₋₁) c(e₂ℓ)) c(e₂ℓ₊₁)`.
* `CliffordAlgebra.ofBaseChangeAux_volumeElement`: conversely, the real volume element is
  `(-i) ^ ⌊(n + 1) / 2⌋ Γ`.
* `CliffordAlgebra.complexVolume_neg_orientation`: reversing the orientation negates `Γ`, and
  `CliffordAlgebra.complexVolume_positiveOrientation`: in rank zero, `Γ = 1`.
* `CliffordAlgebra.map_complexVolume`: the complexification of an isometry of quadratic forms that
  also preserves the norms carries `Γ` to `Γ` for the transported orientation.
* `CliffordAlgebra.complexVolume_mul_self`: `Γ² = 1` for `Q v = -‖v‖²`.
* `CliffordAlgebra.complexVolume_smul_complexVolume_smul`,
  `CliffordAlgebra.lsmul_complexVolume_involutive`: `Γ` acts as an involution on every module.
* `CliffordAlgebra.conjStar_complexVolume`: `Γ` is fixed by the conjugate-linear Clifford
  involution, while `CliffordAlgebra.star_complexVolume` computes the complex-linear Clifford
  conjugation `star Γ = (-1) ^ ⌊(n + 1) / 2⌋ Γ`; in dimension `2ℓ` this is `(-1) ^ ℓ Γ`.
* `CliffordAlgebra.complexVolume_mul_eq_involute_mul`: in even dimension, `Γ x = involute x Γ`;
  hence `Γ` anticommutes with odd elements (`CliffordAlgebra.complexVolume_mul_of_mem_odd`), in
  particular with vectors (`CliffordAlgebra.complexVolume_mul_ι_of_even`). For `Q v = -‖v‖²`,
  conjugation by `Γ` is the grade involution
  (`CliffordAlgebra.complexVolume_mul_mul_complexVolume`).
* `CliffordAlgebra.complexVolume_mem_center`: in odd dimension, `Γ` is central.
* `CliffordAlgebra.commute_complexVolume_of_mem_even`: in every dimension, `Γ` commutes with even
  elements.

Only the statements involving `Γ²` assume `Q v = -‖v‖²`; the others hold for every `Q`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, the chapter on Clifford modules.
-/

public section

noncomputable section

open Module
open scoped TensorProduct ComplexConjugate

namespace CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)]

variable (Q : QuadraticForm ℝ V) (o : Orientation ℝ V (Fin n))

/-- The normalized complex volume element `Γ = i ^ ⌊(n + 1) / 2⌋ c(e₁) ⋯ c(eₙ)` of the
complexified Clifford algebra of an oriented real inner product space of dimension `n`, for any
positively oriented orthonormal basis `e` that is orthogonal for `Q`
(`CliffordAlgebra.complexVolume_eq`). It is fixed by `CliffordAlgebra.conjStar`; in even
dimension it anticommutes with every vector, and in odd dimension it is central. For
`Q v = -‖v‖²` it squares to `1`, so in even dimension it is the chirality operator. -/
def complexVolume : CliffordAlgebra (Q.baseChange ℂ) :=
  Complex.I ^ ((n + 1) / 2) • ofBaseChangeAux ℂ Q (volumeElement Q o)

/-- Unfolding lemma for `CliffordAlgebra.complexVolume`. -/
theorem complexVolume_def :
    complexVolume Q o = Complex.I ^ ((n + 1) / 2) • ofBaseChangeAux ℂ Q (volumeElement Q o) :=
  (rfl)

variable {Q}

/-- The real volume element is `(-i) ^ ⌊(n + 1) / 2⌋ Γ` in the complexified Clifford algebra; in
dimension two it is `-i Γ`. -/
theorem ofBaseChangeAux_volumeElement :
    ofBaseChangeAux ℂ Q (volumeElement Q o) = (-Complex.I) ^ ((n + 1) / 2) • complexVolume Q o := by
  rw [complexVolume_def, smul_smul, ← mul_pow, neg_mul, Complex.I_mul_I, neg_neg, one_pow,
    one_smul]

/-- Reversing the orientation negates the normalized complex volume element. -/
@[simp]
theorem complexVolume_neg_orientation : complexVolume Q (-o) = -complexVolume Q o := by
  simp [complexVolume_def]

/-- **Frame independence of `Γ`**: `Γ = i ^ ⌊(n + 1) / 2⌋ c(e₁) ⋯ c(eₙ)` for every positively
oriented orthonormal basis `e` that is orthogonal for `Q`, for instance for `Q v = -‖v‖²`
(`OrthonormalBasis.isOrthoᵢ_associated`). -/
theorem complexVolume_eq (b : OrthonormalBasis (Fin n) ℝ V) (hb : b.toBasis.orientation = o)
    (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis) :
    complexVolume Q o = Complex.I ^ ((n + 1) / 2) •
      (((List.finRange n).map b).map fun v ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ v)).prod := by
  simp [complexVolume_def, volumeElement_eq o b hb hQb, map_list_prod, Function.comp_def]

/-- **`Γ` as a product of adjacent pairs**: in dimension `2ℓ`,
`Γ = i ^ ℓ (c(e₁) c(e₂)) ⋯ (c(e₂ℓ₋₁) c(e₂ℓ))` for every positively oriented orthonormal basis `e`
that is orthogonal for `Q`. -/
theorem complexVolume_eq_prod_pairs {ℓ : ℕ} [Fact (finrank ℝ V = 2 * ℓ)]
    {o : Orientation ℝ V (Fin (2 * ℓ))} (b : OrthonormalBasis (Fin (2 * ℓ)) ℝ V)
    (hb : b.toBasis.orientation = o) (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis) :
    complexVolume Q o = Complex.I ^ ℓ • (List.ofFn fun k : Fin ℓ ↦
      ι (Q.baseChange ℂ) (1 ⊗ₜ b ⟨2 * k, by omega⟩) *
        ι (Q.baseChange ℂ) (1 ⊗ₜ b ⟨2 * k + 1, by omega⟩)).prod := by
  rw [complexVolume_eq o b hb hQb, List.map_map, ← List.ofFn_eq_map, List.ofFn_mul',
    List.prod_flatten, List.map_ofFn, show (2 * ℓ + 1) / 2 = ℓ by omega]
  simp [List.ofFn_succ, Function.comp_def]

/-- **`ω_ℂ` as a product of adjacent pairs and a last vector**: in dimension `2ℓ + 1`,
`ω_ℂ = i ^ (ℓ + 1) (c(e₁) c(e₂)) ⋯ (c(e₂ℓ₋₁) c(e₂ℓ)) c(e₂ℓ₊₁)` for every positively oriented
orthonormal basis `e` that is orthogonal for `Q`. -/
theorem complexVolume_eq_prod_pairs_mul {ℓ : ℕ} [Fact (finrank ℝ V = 2 * ℓ + 1)]
    {o : Orientation ℝ V (Fin (2 * ℓ + 1))} (b : OrthonormalBasis (Fin (2 * ℓ + 1)) ℝ V)
    (hb : b.toBasis.orientation = o) (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis) :
    complexVolume Q o = Complex.I ^ (ℓ + 1) • ((List.ofFn fun k : Fin ℓ ↦
      ι (Q.baseChange ℂ) (1 ⊗ₜ b ⟨2 * k, by omega⟩) *
        ι (Q.baseChange ℂ) (1 ⊗ₜ b ⟨2 * k + 1, by omega⟩)).prod *
      ι (Q.baseChange ℂ) (1 ⊗ₜ b (Fin.last (2 * ℓ)))) := by
  rw [complexVolume_eq o b hb hQb, List.finRange_succ_last,
    show (2 * ℓ + 1 + 1) / 2 = ℓ + 1 by omega]
  simp [List.prod_append, ← List.ofFn_eq_map, List.ofFn_mul', List.prod_flatten, List.ofFn_succ,
    Function.comp_def]

/-- **The normalized complex volume element in rank zero**: for the positive orientation of a
zero-dimensional space, `Γ = 1`. By `CliffordAlgebra.complexVolume_neg_orientation`, the negative
orientation gives `Γ = -1`. -/
@[simp]
theorem complexVolume_positiveOrientation [Fact (finrank ℝ V = 0)] :
    complexVolume Q (positiveOrientation : Orientation ℝ V (Fin 0)) = 1 := by
  rw [complexVolume_eq _ ((stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out))
    (Basis.orientation_isEmpty _) fun i ↦ i.elim0]
  simp

section Naturality

variable {V' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']
  [Fact (finrank ℝ V' = n)] {Q' : QuadraticForm ℝ V'}

/-- **Naturality of `Γ`**: the complexification of an isometric equivalence `e` of the quadratic
forms that also preserves the norms carries `Γ` for `o` to `Γ` for the transported orientation.
In particular an orientation-preserving isometry of `V` fixing `Q` fixes `Γ`, while an
orientation-reversing one negates it (`CliffordAlgebra.complexVolume_neg_orientation`). -/
theorem map_complexVolume (e : Q.IsometryEquiv Q') (he : ∀ v, ‖e v‖ = ‖v‖) :
    map (e.toIsometry.baseChange ℂ) (complexVolume Q o) =
      complexVolume Q' (o.map (Fin n) e.toLinearEquiv) := by
  rw [complexVolume_def, complexVolume_def, map_smul, ← QuadraticMap.Isometry.ofBaseChangeAux_map,
    map_volumeElement o e he]

end Naturality

/-- The grade involution multiplies `Γ` by `(-1) ^ n`. -/
@[simp]
theorem involute_complexVolume :
    involute (complexVolume Q o) = (-1 : ℂ) ^ n • complexVolume Q o := by
  rw [complexVolume_def, map_smul, ← ofBaseChangeAux_involute, involute_volumeElement, map_smul,
    smul_comm]
  norm_cast

/-- Reversal multiplies `Γ` by `(-1) ^ ⌊n / 2⌋`. -/
@[simp]
theorem reverse_complexVolume :
    reverse (complexVolume Q o) = (-1 : ℂ) ^ (n / 2) • complexVolume Q o := by
  rw [complexVolume_def, map_smul, ← ofBaseChangeAux_reverse, reverse_volumeElement, map_smul,
    smul_comm]
  norm_cast

/-- Complex-linear Clifford conjugation multiplies `Γ` by `(-1) ^ ⌊(n + 1) / 2⌋`; in dimension
`2ℓ` this is `star Γ = (-1) ^ ℓ Γ`. -/
@[simp]
theorem star_complexVolume :
    star (complexVolume Q o) = (-1 : ℂ) ^ ((n + 1) / 2) • complexVolume Q o := by
  rw [complexVolume_def, star_smul, ← ofBaseChangeAux_star, star_volumeElement, map_smul,
    smul_comm]
  norm_cast

/-- Complex conjugation of the coefficients multiplies `Γ` by `(-1) ^ ⌊(n + 1) / 2⌋`. -/
@[simp]
theorem complexConj_complexVolume :
    complexConj Q (complexVolume Q o) = (-1 : ℂ) ^ ((n + 1) / 2) • complexVolume Q o := by
  rw [complexVolume_def, complexConj_smul, complexConj_ofBaseChangeAux, map_pow, Complex.conj_I,
    neg_pow, mul_smul]

/-- **`Γ` is self-adjoint**: it is fixed by the conjugate-linear Clifford involution
`CliffordAlgebra.conjStar`, so it acts self-adjointly in every `*`-representation. -/
@[simp]
theorem conjStar_complexVolume : conjStar Q (complexVolume Q o) = complexVolume Q o := by
  simp [conjStar_apply, smul_smul, ← mul_pow]

/-- A relation `vol * c(v) = s • (c(v) * vol)` between the real volume element and every real
vector passes to `Γ` and every complex vector. -/
private theorem complexVolume_mul_ι_of_forall {s : ℂ}
    (h : ∀ v : V, ofBaseChangeAux ℂ Q (volumeElement Q o) * ι (Q.baseChange ℂ) (1 ⊗ₜ v) =
      s • (ι (Q.baseChange ℂ) (1 ⊗ₜ v) * ofBaseChangeAux ℂ Q (volumeElement Q o)))
    (w : ℂ ⊗[ℝ] V) :
    complexVolume Q o * ι (Q.baseChange ℂ) w = s • (ι (Q.baseChange ℂ) w * complexVolume Q o) := by
  induction w using TensorProduct.inductionOn with
  | tmul z v =>
    have hz : z ⊗ₜ[ℝ] v = z • ((1 : ℂ) ⊗ₜ[ℝ] v) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hz, map_smul, complexVolume_def, smul_mul_smul_comm, smul_mul_smul_comm, h,
      smul_comm _ s, mul_comm z]
  | add x y hx hy => rw [map_add, mul_add, add_mul, hx, hy, smul_add]

/-- **In even dimension `Γ` anticommutes with every vector**: `Γ c(w) = -c(w) Γ`. -/
theorem complexVolume_mul_ι_of_even (hn : Even n) (w : ℂ ⊗[ℝ] V) :
    complexVolume Q o * ι (Q.baseChange ℂ) w =
      -(ι (Q.baseChange ℂ) w * complexVolume Q o) := by
  rw [← neg_one_smul ℂ (_ * complexVolume Q o)]
  refine complexVolume_mul_ι_of_forall o (fun v ↦ ?_) w
  rw [neg_one_smul, ← ofBaseChangeAux_ι, ← map_mul, volumeElement_mul_ι_of_even o hn, map_neg,
    map_mul]

/-- **In even dimension `Γ` intertwines the grade involution**: `Γ x = involute x Γ`. -/
theorem complexVolume_mul_eq_involute_mul (hn : Even n) (x : CliffordAlgebra (Q.baseChange ℂ)) :
    complexVolume Q o * x = involute x * complexVolume Q o := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, Algebra.commutes]
  | ι w => rw [complexVolume_mul_ι_of_even o hn, involute_ι, neg_mul]
  | mul a b ha hb => rw [← mul_assoc, ha, mul_assoc, hb, map_mul, mul_assoc]
  | add a b ha hb => rw [mul_add, ha, hb, map_add, add_mul]

/-- In even dimension `Γ` anticommutes with every odd element. -/
theorem complexVolume_mul_of_mem_odd (hn : Even n) {x : CliffordAlgebra (Q.baseChange ℂ)}
    (hx : x ∈ evenOdd (Q.baseChange ℂ) 1) : complexVolume Q o * x = -(x * complexVolume Q o) := by
  rw [complexVolume_mul_eq_involute_mul o hn, involute_eq_of_mem_odd hx, neg_mul]

/-- In odd dimension `Γ` commutes with every vector. -/
theorem complexVolume_mul_ι_of_odd (hn : Odd n) (w : ℂ ⊗[ℝ] V) :
    complexVolume Q o * ι (Q.baseChange ℂ) w = ι (Q.baseChange ℂ) w * complexVolume Q o := by
  rw [← one_smul ℂ (_ * complexVolume Q o)]
  refine complexVolume_mul_ι_of_forall o (fun v ↦ ?_) w
  rw [one_smul, ← ofBaseChangeAux_ι, ← map_mul, volumeElement_mul_ι_of_odd o hn, map_mul]

/-- **In odd dimension `Γ` is central.** -/
theorem complexVolume_mem_center (hn : Odd n) :
    complexVolume Q o ∈ Subalgebra.center ℂ (CliffordAlgebra (Q.baseChange ℂ)) := by
  rw [Subalgebra.mem_center_iff]
  intro x
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact Algebra.commutes r _
  | ι w => exact (complexVolume_mul_ι_of_odd o hn w).symm
  | mul a b ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]

/-- `Γ` commutes with every even element, in every dimension: in even dimension `Γ` intertwines the
grade involution, and in odd dimension `Γ` is central. -/
theorem commute_complexVolume_of_mem_even {x : CliffordAlgebra (Q.baseChange ℂ)}
    (hx : x ∈ evenOdd (Q.baseChange ℂ) 0) : Commute (complexVolume Q o) x := by
  rcases Nat.even_or_odd n with hn | hn
  · rw [Commute, SemiconjBy, complexVolume_mul_eq_involute_mul o hn, involute_eq_of_mem_even hx]
  · exact ((Subalgebra.mem_center_iff.mp (complexVolume_mem_center o hn) x).symm)

section Form

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- **`Γ` is an involution**: `Γ² = 1`. -/
@[simp]
theorem complexVolume_mul_self : complexVolume Q o * complexVolume Q o = 1 := by
  rw [complexVolume_def, smul_mul_smul_comm, ← map_mul, volumeElement_mul_self o hQ, ← mul_pow,
    Complex.I_mul_I]
  simp [Algebra.smul_def, ← pow_add, ← two_mul]

/-- **`Γ` acts as an involution** on every module: `Γ • Γ • ψ = ψ`. -/
theorem complexVolume_smul_complexVolume_smul {M : Type*}
    [MulAction (CliffordAlgebra (Q.baseChange ℂ)) M] (ψ : M) :
    complexVolume Q o • complexVolume Q o • ψ = ψ := by
  rw [← mul_smul, complexVolume_mul_self o hQ, one_smul]

/-- Multiplication by `Γ` is an involution of every module. -/
theorem lsmul_complexVolume_involutive {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (CliffordAlgebra (Q.baseChange ℂ)) M]
    [IsScalarTower ℂ (CliffordAlgebra (Q.baseChange ℂ)) M] :
    Function.Involutive (Algebra.lsmul ℂ ℂ M (complexVolume Q o)) :=
  complexVolume_smul_complexVolume_smul o hQ

/-- **In even dimension, conjugation by `Γ` is the grade involution**: `Γ x Γ = involute x`. -/
theorem complexVolume_mul_mul_complexVolume (hn : Even n) (x : CliffordAlgebra (Q.baseChange ℂ)) :
    complexVolume Q o * x * complexVolume Q o = involute x := by
  rw [complexVolume_mul_eq_involute_mul o hn, mul_assoc, complexVolume_mul_self o hQ, mul_one]

end Form

end CliffordAlgebra
