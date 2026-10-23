/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
public import TauCeti.Analysis.InnerProductSpace.HodgeStar
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
-- Private: the parity, orthogonal-basis and orthogonal-product computations are used only inside
-- proofs.
import TauCeti.Data.Nat.Choose.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthogonalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Basic
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# The volume element of an oriented Euclidean space

Let `V` be an oriented real inner product space of dimension `n` and `Q` a quadratic form on `V`.
The **volume element** `CliffordAlgebra.volumeElement Q o` is the quantization, under
`CliffordAlgebra.equivExterior`, of the unit volume element of `⋀ⁿ V`. It is defined without a
frame. For every positively oriented orthonormal basis `e` it is the top Clifford basis vector
`CliffordAlgebra.basis Q e univ`, the quantization of `e₁ ∧ ⋯ ∧ eₙ`; when `e` is moreover
orthogonal for `Q`, for instance for the geometric form `Q v = -‖v‖²`, this is the Clifford
product `c(e₁) ⋯ c(eₙ)` (`CliffordAlgebra.volumeElement_eq`). That every such frame gives the same
product is the independence of the volume element under orientation-preserving orthonormal changes
of frame; reversing the orientation changes its sign.

For an arbitrary quadratic form the volume element is a multiple of the top Clifford basis vector
of every basis (`CliffordAlgebra.volumeElement_eq_inv_smul_basis`), hence of the ordered product of
a `Q`-orthogonal basis. The commutation rules of such products in
`TauCeti/LinearAlgebra/CliffordAlgebra/VolumeElement/Basic.lean` then show that in even dimension
it anticommutes with every vector and in odd dimension it commutes with every vector.

The volume element is the real input of the normalized complex volume element of
`TauCeti/LinearAlgebra/CliffordAlgebra/VolumeElement/Complex.lean`, and in dimension four it is
minus the chirality element `CliffordAlgebra.chirality` of
`TauCeti/LinearAlgebra/CliffordAlgebra/Chirality.lean`.

## Main definitions

* `CliffordAlgebra.volumeElement Q o`: the volume element of `CliffordAlgebra Q`.

## Main results

* `CliffordAlgebra.volumeElement_eq`: the volume element is `c(e₁) ⋯ c(eₙ)` for every positively
  oriented orthonormal basis `e` that is orthogonal for `Q`.
* `CliffordAlgebra.volumeElement_neg_orientation`: reversing the orientation negates it.
* `CliffordAlgebra.involute_volumeElement`, `CliffordAlgebra.reverse_volumeElement` and
  `CliffordAlgebra.star_volumeElement`: the grade involution, reversal and Clifford conjugation
  multiply it by `(-1) ^ n`, `(-1) ^ ⌊n / 2⌋` and `(-1) ^ ⌊(n + 1) / 2⌋`.
* `CliffordAlgebra.volumeElement_mul_ι_of_even` and `CliffordAlgebra.volumeElement_mul_ι_of_odd`:
  it anticommutes with every vector in even dimension and commutes with every vector in odd
  dimension.
* `CliffordAlgebra.volumeElement_mul_self`: for `Q v = -‖v‖²` it squares to
  `(-1) ^ ⌊(n + 1) / 2⌋`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

noncomputable section

open Module

namespace CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)]

variable (Q : QuadraticForm ℝ V) (o : Orientation ℝ V (Fin n))

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
  simp [volumeElement_def]

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

/-- The volume element is homogeneous of degree `n`: the grade involution multiplies it by
`(-1) ^ n`. -/
@[simp]
theorem involute_volumeElement :
    involute (volumeElement Q o) = (-1 : ℝ) ^ n • volumeElement Q o := by
  have hn : (-1 : ℝ) ^ finrank ℝ V = (-1) ^ n := by rw [Fact.out (p := finrank ℝ V = n)]
  apply (equivExterior Q).injective
  rw [equivExterior_involute, volumeElement_def, LinearEquiv.apply_symm_apply,
    TauCeti.ExteriorAlgebra.involute_of_mem_exteriorPower (o.volumeEquiv.symm 1).2, map_smul,
    LinearEquiv.apply_symm_apply, hn]

/-- Reversal multiplies the volume element by `(-1) ^ ⌊n / 2⌋`, the sign of the
order-reversing permutation of `n` letters. -/
@[simp]
theorem reverse_volumeElement :
    reverse (volumeElement Q o) = (-1 : ℝ) ^ (n / 2) • volumeElement Q o := by
  -- In the exterior algebra every pair of vectors is orthogonal for the zero form, so reversal
  -- multiplies the wedge of `n` vectors by `(-1) ^ (n.choose 2)`.
  have h : reverse (basis Q (frame V n).toBasis Finset.univ) =
      (-1 : ℝ) ^ (n / 2) • basis Q (frame V n).toBasis Finset.univ := by
    apply (equivExterior Q).injective
    rw [equivExterior_reverse, basis_apply, LinearEquiv.apply_symm_apply,
      Module.Basis.exteriorAlgebra_eq_prod_map_sort, reverse_prod_map_ι_of_pairwise_isOrtho
        (List.pairwise_of_forall fun _ _ ↦ by simp [QuadraticMap.isOrtho_def]), map_smul,
      LinearEquiv.apply_symm_apply]
    simp [Nat.neg_one_pow_choose_two]
  rcases volumeElement_eq_basis_or_eq_neg (Q := Q) o (frame V n) with h' | h' <;>
    simp only [h', map_neg, h, smul_neg]

/-- Clifford conjugation multiplies the volume element by `(-1) ^ ⌊(n + 1) / 2⌋`. -/
@[simp]
theorem star_volumeElement :
    star (volumeElement Q o) = (-1 : ℝ) ^ ((n + 1) / 2) • volumeElement Q o := by
  rw [star_def, involute_volumeElement, map_smul, reverse_volumeElement, smul_smul, ← pow_add]
  -- The sign identity is the parity fact `⌊n / 2⌋ + n ≡ ⌊(n + 1) / 2⌋ (mod 2)`.
  congr 1
  refine neg_one_pow_congr ?_
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩ <;> simp only [Nat.even_iff] <;> omega

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

/-- For `Q v = -‖v‖²`, the volume element squares to `(-1) ^ ⌊(n + 1) / 2⌋`. -/
@[simp]
theorem volumeElement_mul_self (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    volumeElement Q o * volumeElement Q o = (-1) ^ ((n + 1) / 2) := by
  have h := basis_mul_self_of_orthonormal hQ (frame V n) Finset.univ
  rw [Finset.card_univ, Fintype.card_fin, Nat.neg_one_pow_choose_two] at h
  rcases volumeElement_eq_basis_or_eq_neg (Q := Q) o (frame V n) with h' | h' <;>
    simp only [h', neg_mul_neg, h]

end CliffordAlgebra
