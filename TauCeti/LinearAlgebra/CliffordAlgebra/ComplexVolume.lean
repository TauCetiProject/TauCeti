/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar
public import TauCeti.LinearAlgebra.CliffordAlgebra.Complexification
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
-- Private: the parity, orthogonal-basis and orthogonal-product computations are used only inside
-- proofs.
import TauCeti.Data.Nat.Choose.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthogonalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# The normalized complex volume element of an oriented Euclidean space

Let `V` be an oriented real inner product space of dimension `n` and `Q` a quadratic form on `V`.
The **volume element** `CliffordAlgebra.volumeElement Q o` is the quantization, under
`CliffordAlgebra.equivExterior`, of the unit volume element of `⋀ⁿ V`. For every positively
oriented orthonormal basis `e` it is the top Clifford basis vector `CliffordAlgebra.basis Q e univ`,
the quantization of `e₁ ∧ ⋯ ∧ eₙ`; this is the Clifford product `c(e₁) ⋯ c(eₙ)` when `e` is
moreover orthogonal for `Q`. For an arbitrary quadratic form the volume element is a multiple of
the top Clifford basis vector of every basis (`CliffordAlgebra.volumeElement_eq_inv_smul_basis`),
hence of the product of a `Q`-orthogonal basis, so in even dimension it anticommutes with every
vector and in odd dimension it commutes with every vector.

For the geometric convention `Q v = -‖v‖²`, so that `c(v) c(w) + c(w) c(v) = -2 ⟪v, w⟫`, the
**normalized complex volume element** is

  `Γ = i ^ ⌊(n + 1) / 2⌋ c(e₁) ⋯ c(eₙ)`

in the complexified Clifford algebra `Cℓ(ℂ ⊗ V, Q_ℂ)`. In even dimension `n = 2ℓ` this is
`Γ = i ^ ℓ c(e₁) ⋯ c(e₂ₗ)`, the chirality operator whose `±1` eigenspaces are the half-spin
modules; in odd dimension `n = 2ℓ + 1` it is `ω_ℂ = i ^ (ℓ + 1) c(e₁) ⋯ c(eₙ)`, the central
element separating the two irreducible Clifford modules. The power of `i` is chosen so that `Γ`
squares to `1` and is self-adjoint for the conjugate-linear Clifford involution
`CliffordAlgebra.conjStar`, that is, it acts as a self-adjoint involution in every
`*`-representation.

Both elements are defined without a frame. For `Q v = -‖v‖²` the frame formulas
`CliffordAlgebra.volumeElement_eq` and `CliffordAlgebra.complexVolume_eq` hold for every
positively oriented orthonormal basis, which is the independence of `Γ` under
orientation-preserving orthonormal changes of frame, while reversing the orientation changes the
sign of `Γ`. In rank zero, `Γ` is `1` for the positive
orientation and `-1` for the negative one.

## Main definitions

* `CliffordAlgebra.volumeElement Q o`: the volume element of `CliffordAlgebra Q`.
* `CliffordAlgebra.complexVolume Q o`: the normalized complex volume element `Γ` of
  `CliffordAlgebra (Q.baseChange ℂ)`.

## Main results

* `CliffordAlgebra.complexVolume_eq`: `Γ = i ^ ⌊(n + 1) / 2⌋ c(e₁) ⋯ c(eₙ)` for every positively
  oriented orthonormal basis `e` that is orthogonal for `Q`.
* `CliffordAlgebra.complexVolume_neg_orientation`: reversing the orientation negates `Γ`.
* `CliffordAlgebra.complexVolume_mul_self`: `Γ² = 1` for `Q v = -‖v‖²`.
* `CliffordAlgebra.conjStar_complexVolume`: `Γ` is fixed by the conjugate-linear Clifford
  involution, while `CliffordAlgebra.star_complexVolume` computes the complex-linear Clifford
  conjugation `star Γ = (-1) ^ ⌊(n + 1) / 2⌋ Γ`; in dimension `2ℓ` this is `(-1) ^ ℓ Γ`.
* `CliffordAlgebra.complexVolume_mul_eq_involute_mul`: in even dimension, `Γ x = involute x Γ`;
  hence `Γ` commutes with even elements (`CliffordAlgebra.commute_complexVolume_of_mem_even`) and
  anticommutes with odd ones (`CliffordAlgebra.complexVolume_mul_of_mem_odd`), and in particular
  with vectors (`CliffordAlgebra.complexVolume_mul_ι_of_even`). For `Q v = -‖v‖²`, conjugation by
  `Γ` is the grade involution (`CliffordAlgebra.complexVolume_mul_mul_complexVolume`).
* `CliffordAlgebra.complexVolume_mem_center`: in odd dimension, `Γ` is central.

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

/-! ### The real volume element -/

/-- The volume element of the Clifford algebra of an oriented real inner product space: the
quantization of the unit volume element of the top exterior power. It is the top Clifford basis
vector of every positively oriented orthonormal basis `e`
(`CliffordAlgebra.volumeElement_eq_basis`), and the product `c(e₁) ⋯ c(eₙ)` when `e` is moreover
orthogonal for `Q` (`CliffordAlgebra.volumeElement_eq`). -/
def volumeElement : CliffordAlgebra Q :=
  (equivExterior Q).symm (o.volumeEquiv.symm 1 : ExteriorAlgebra ℝ V)

/-- Unfolding lemma for `CliffordAlgebra.volumeElement`. -/
theorem volumeElement_def :
    volumeElement Q o = (equivExterior Q).symm (o.volumeEquiv.symm 1 : ExteriorAlgebra ℝ V) :=
  (rfl)

variable {Q}

/-- In terms of the Clifford basis of a positively oriented orthonormal basis `e`, the volume
element is the basis vector indexed by all of `Fin n`. -/
theorem volumeElement_eq_basis (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o) :
    volumeElement Q o = basis Q b.toBasis Finset.univ := by
  have h : o.volumeEquiv.symm 1 = b.toBasis.topVector := by
    rw [LinearEquiv.symm_apply_eq, o.volumeEquiv_topVector b hb]
  rw [volumeElement_def, h, Basis.coe_topVector, basis_apply]

/-- Reversing the orientation negates the volume element. -/
@[simp]
theorem volumeElement_neg_orientation : volumeElement Q (-o) = -volumeElement Q o := by
  rw [volumeElement_def, volumeElement_def, Orientation.volumeEquiv_symm_neg_orientation,
    Submodule.coe_neg, map_neg]

/-- For an arbitrary orthonormal basis `e`, the volume element is plus or minus the top Clifford
basis vector of `e`. -/
private theorem volumeElement_eq_basis_or_eq_neg (b : OrthonormalBasis (Fin n) ℝ V) :
    volumeElement Q o = basis Q b.toBasis Finset.univ ∨
      volumeElement Q o = -basis Q b.toBasis Finset.univ := by
  rcases b.toBasis.orientation_eq_or_eq_neg o with h | h
  · exact .inl (volumeElement_eq_basis o b h.symm)
  · rw [h, volumeElement_neg_orientation, volumeElement_eq_basis _ b rfl]
    exact .inr rfl

/-- An orthonormal basis of `V` indexed by `Fin n`. -/
private abbrev frame (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) [Fact (finrank ℝ V = n)] : OrthonormalBasis (Fin n) ℝ V :=
  (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)

/-- The volume element is fixed by reversal up to the sign `(-1) ^ (n.choose 2)`. -/
@[simp]
theorem reverse_volumeElement :
    reverse (volumeElement Q o) = (-1 : ℝ) ^ n.choose 2 • volumeElement Q o := by
  -- In the exterior algebra every pair of vectors is orthogonal for the zero form, so reversal
  -- multiplies the wedge of `n` vectors by `(-1) ^ (n.choose 2)`.
  have h : reverse (basis Q (frame V n).toBasis Finset.univ) =
      (-1 : ℝ) ^ n.choose 2 • basis Q (frame V n).toBasis Finset.univ := by
    apply (equivExterior Q).injective
    rw [equivExterior_reverse, basis_apply, LinearEquiv.apply_symm_apply,
      Module.Basis.exteriorAlgebra_eq_prod_map_sort, reverse_prod_map_ι_of_pairwise_isOrtho
        (List.pairwise_of_forall fun _ _ ↦ by simp [QuadraticMap.isOrtho_def]), map_smul,
      LinearEquiv.apply_symm_apply]
    simp
  rcases volumeElement_eq_basis_or_eq_neg (Q := Q) o (frame V n) with h' | h' <;>
    simp only [h', map_neg, h, smul_neg]

/-- The volume element is homogeneous of degree `n`: the grade involution multiplies it by
`(-1) ^ n`. -/
@[simp]
theorem involute_volumeElement :
    involute (volumeElement Q o) = (-1 : ℝ) ^ n • volumeElement Q o := by
  have h : involute (basis Q (frame V n).toBasis Finset.univ) =
      (-1 : ℝ) ^ n • basis Q (frame V n).toBasis Finset.univ := by
    apply (equivExterior Q).injective
    rw [equivExterior_involute, basis_apply, LinearEquiv.apply_symm_apply,
      Module.Basis.exteriorAlgebra_eq_prod_map_sort, involute_prod_map_ι, map_smul,
      LinearEquiv.apply_symm_apply]
    simp
  rcases volumeElement_eq_basis_or_eq_neg (Q := Q) o (frame V n) with h' | h' <;>
    simp only [h', map_neg, h, smul_neg]

/-- Clifford conjugation multiplies the volume element by `(-1) ^ ((n + 1).choose 2)`. -/
@[simp]
theorem star_volumeElement :
    star (volumeElement Q o) = (-1 : ℝ) ^ (n + 1).choose 2 • volumeElement Q o := by
  rw [star_def, involute_volumeElement, map_smul, reverse_volumeElement, smul_smul, ← pow_add,
    Nat.choose_succ_succ', Nat.choose_one_right, add_comm n]

/-- **Frame formula for the volume element**: `volumeElement Q o = c(e₁) ⋯ c(eₙ)` for every
positively oriented orthonormal basis `e` that is orthogonal for `Q`, for instance for
`Q v = -‖v‖²` (`OrthonormalBasis.isOrthoᵢ_associated`). -/
theorem volumeElement_eq (b : OrthonormalBasis (Fin n) ℝ V) (hb : b.toBasis.orientation = o)
    (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis) :
    volumeElement Q o = (((List.finRange n).map b).map (ι Q)).prod := by
  rw [volumeElement_eq_basis o b hb, basis_eq_prod_map_sort hQb, Fin.sort_univ,
    OrthonormalBasis.coe_toBasis]

/-- The volume element is a multiple of the top Clifford basis vector of every basis `f`: the
scalar is the inverse of the volume of `f₁ ∧ ⋯ ∧ fₙ`. For a positively oriented orthonormal basis
this scalar is `1` (`CliffordAlgebra.volumeElement_eq_basis`). -/
theorem volumeElement_eq_inv_smul_basis {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : Basis ι ℝ V) :
    volumeElement Q o = (o.volumeEquiv f.topVector)⁻¹ • basis Q f Finset.univ := by
  have hf := exteriorPower.isUnit_apply_topVector o.volumeEquiv f
  have h : o.volumeEquiv.symm 1 = (o.volumeEquiv f.topVector)⁻¹ • f.topVector := by
    rw [LinearEquiv.symm_apply_eq, map_smul, smul_eq_mul, inv_mul_cancel₀ hf.ne_zero]
  rw [volumeElement_def, h, Submodule.coe_smul, Basis.coe_topVector, map_smul, basis_apply]

/-- The volume element is a multiple of the ordered product of `n` pairwise `Q`-orthogonal vectors
spanning `V`, namely of a `Q`-orthogonal basis. -/
private theorem exists_volumeElement_eq_smul_prod :
    ∃ (l : List V) (c : ℝ), l.Pairwise Q.IsOrtho ∧ l.length = n ∧
      (∀ v, v ∈ Submodule.span ℝ {x | x ∈ l}) ∧ volumeElement Q o = c • (l.map (ι Q)).prod := by
  obtain ⟨f, hf⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm ℝ Q)
  refine ⟨Finset.univ.sort.map f, _, List.pairwise_map.mpr <| (Finset.univ.sort_nodup _).imp
    fun hij ↦ QuadraticMap.associated_isOrtho.mp (hf hij), by simp [Fact.out], fun v ↦ ?_,
    by rw [volumeElement_eq_inv_smul_basis o f, basis_eq_prod_map_sort hf]⟩
  simp only [List.mem_map, Finset.mem_sort, Finset.mem_univ, true_and]
  exact f.mem_span v

/-- In even dimension the volume element anticommutes with every vector. -/
theorem volumeElement_mul_ι_of_even (hn : Even n) (v : V) :
    volumeElement Q o * ι Q v = -(ι Q v * volumeElement Q o) := by
  obtain ⟨l, c, hl, hln, hspan, h⟩ := exists_volumeElement_eq_smul_prod (Q := Q) o
  rw [h, smul_mul_assoc, prod_map_ι_mul_ι_of_even_length hl (hln ▸ hn) (hspan v), mul_smul_comm,
    smul_neg]

/-- In odd dimension the volume element commutes with every vector. -/
theorem volumeElement_mul_ι_of_odd (hn : Odd n) (v : V) :
    volumeElement Q o * ι Q v = ι Q v * volumeElement Q o := by
  obtain ⟨l, c, hl, hln, hspan, h⟩ := exists_volumeElement_eq_smul_prod (Q := Q) o
  rw [h, smul_mul_assoc, prod_map_ι_mul_ι_of_odd_length hl (hln ▸ hn) (hspan v), mul_smul_comm]

/-- For `Q v = -‖v‖²`, the volume element squares to `(-1) ^ ((n + 1).choose 2)`. -/
@[simp]
theorem volumeElement_mul_self (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    volumeElement Q o * volumeElement Q o = (-1) ^ (n + 1).choose 2 := by
  have h := basis_mul_self_of_orthonormal hQ (frame V n) Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at h
  rcases volumeElement_eq_basis_or_eq_neg (Q := Q) o (frame V n) with h' | h' <;>
    simp only [h', neg_mul_neg, h]

/-! ### The normalized complex volume element -/

variable (Q)

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

/-- Reversing the orientation negates the normalized complex volume element. -/
@[simp]
theorem complexVolume_neg_orientation : complexVolume Q (-o) = -complexVolume Q o := by
  rw [complexVolume_def, complexVolume_def, volumeElement_neg_orientation, map_neg, smul_neg]

/-- **The normalized complex volume element in rank zero**: for the positive orientation of a
zero-dimensional space, `Γ = 1`. By `CliffordAlgebra.complexVolume_neg_orientation`, the negative
orientation gives `Γ = -1`. -/
theorem complexVolume_positiveOrientation [Fact (finrank ℝ V = 0)] :
    complexVolume Q (positiveOrientation : Orientation ℝ V (Fin 0)) = 1 := by
  rw [complexVolume_def, volumeElement_eq_basis _ (frame V 0) (Basis.orientation_isEmpty _),
    basis_eq_prod_map_sort (fun i ↦ i.elim0)]
  simp

/-- **Frame independence of `Γ`**: `Γ = i ^ ⌊(n + 1) / 2⌋ c(e₁) ⋯ c(eₙ)` for every positively
oriented orthonormal basis `e` that is orthogonal for `Q`, for instance for `Q v = -‖v‖²`
(`OrthonormalBasis.isOrthoᵢ_associated`). -/
theorem complexVolume_eq (b : OrthonormalBasis (Fin n) ℝ V) (hb : b.toBasis.orientation = o)
    (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis) :
    complexVolume Q o = Complex.I ^ ((n + 1) / 2) •
      (((List.finRange n).map b).map fun v ↦ ι (Q.baseChange ℂ) (1 ⊗ₜ v)).prod := by
  rw [complexVolume_def, volumeElement_eq o b hb hQb, map_list_prod, List.map_map, List.map_map]
  simp [Function.comp_def]

/-- The grade involution multiplies `Γ` by `(-1) ^ n`. -/
@[simp]
theorem involute_complexVolume :
    involute (complexVolume Q o) = (-1 : ℂ) ^ n • complexVolume Q o := by
  rw [complexVolume_def, map_smul, ← ofBaseChangeAux_involute, involute_volumeElement,
    ofBaseChangeAux_smul, smul_comm, map_pow, map_neg, map_one]

/-- Reversal multiplies `Γ` by `(-1) ^ (n.choose 2)`. -/
@[simp]
theorem reverse_complexVolume :
    reverse (complexVolume Q o) = (-1 : ℂ) ^ n.choose 2 • complexVolume Q o := by
  rw [complexVolume_def, map_smul, ← ofBaseChangeAux_reverse, reverse_volumeElement,
    ofBaseChangeAux_smul, smul_comm, map_pow, map_neg, map_one]

/-- Complex-linear Clifford conjugation multiplies `Γ` by `(-1) ^ ⌊(n + 1) / 2⌋`; in dimension
`2ℓ` this is `star Γ = (-1) ^ ℓ Γ`. -/
@[simp]
theorem star_complexVolume :
    star (complexVolume Q o) = (-1 : ℂ) ^ ((n + 1) / 2) • complexVolume Q o := by
  rw [complexVolume_def, star_smul, ← ofBaseChangeAux_star, star_volumeElement,
    ofBaseChangeAux_smul, smul_comm, map_pow, map_neg, map_one,
    neg_one_pow_eq_pow_mod_two ((n + 1).choose 2), Nat.choose_two_mod_two,
    ← neg_one_pow_eq_pow_mod_two]

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
  rw [conjStar_apply, star_complexVolume, complexConj_smul, complexConj_complexVolume, smul_smul,
    map_pow, map_neg, map_one, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

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

/-- In even dimension `Γ` commutes with every even element. -/
theorem commute_complexVolume_of_mem_even (hn : Even n) {x : CliffordAlgebra (Q.baseChange ℂ)}
    (hx : x ∈ evenOdd (Q.baseChange ℂ) 0) : Commute (complexVolume Q o) x := by
  rw [Commute, SemiconjBy, complexVolume_mul_eq_involute_mul o hn, involute_eq_of_mem_even hx]

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

section Form

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- **`Γ` is an involution**: `Γ² = 1`. -/
@[simp]
theorem complexVolume_mul_self : complexVolume Q o * complexVolume Q o = 1 := by
  rw [complexVolume_def, smul_mul_smul_comm, ← map_mul, volumeElement_mul_self o hQ, map_pow,
    map_neg, map_one, neg_one_pow_eq_pow_mod_two ((n + 1).choose 2), Nat.choose_two_mod_two,
    ← neg_one_pow_eq_pow_mod_two, ← mul_pow, Complex.I_mul_I, Algebra.smul_def, map_pow, map_neg,
    map_one, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩]

/-- **In even dimension, conjugation by `Γ` is the grade involution**: `Γ x Γ = involute x`. -/
theorem complexVolume_mul_mul_complexVolume (hn : Even n) (x : CliffordAlgebra (Q.baseChange ℂ)) :
    complexVolume Q o * x * complexVolume Q o = involute x := by
  rw [complexVolume_mul_eq_involute_mul o hn, mul_assoc, complexVolume_mul_self o hQ, mul_one]

end Form

end CliffordAlgebra
