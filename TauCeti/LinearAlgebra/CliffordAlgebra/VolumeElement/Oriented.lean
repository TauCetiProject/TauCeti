/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Basic
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
* `CliffordAlgebra.map_volumeElement`: an isometry of quadratic forms that also preserves the norms
  carries the volume element to that of the transported orientation.
* `CliffordAlgebra.involute_volumeElement`, `CliffordAlgebra.reverse_volumeElement` and
  `CliffordAlgebra.star_volumeElement`: the grade involution, reversal and Clifford conjugation
  multiply it by `(-1) ^ n`, `(-1) ^ ⌊n / 2⌋` and `(-1) ^ ⌊(n + 1) / 2⌋`.
* `CliffordAlgebra.volumeElement_mul_ι_of_even` and `CliffordAlgebra.volumeElement_mul_ι_of_odd`:
  it anticommutes with every vector in even dimension and commutes with every vector in odd
  dimension.
* `CliffordAlgebra.volumeElement_mul_eq_involute_mul`: in even dimension the raw volume
  intertwines the grade involution.
* `CliffordAlgebra.volumeElement_mul_self`: for `Q v = -‖v‖²` it squares to
  `(-1) ^ ⌊(n + 1) / 2⌋`.
* `CliffordAlgebra.algebraMap_add_smul_volumeElement_inj`: in positive dimension, `r + s · vol`
  determines `r` and `s`. When the volume element squares to `-1`, for instance for an oriented
  plane with `Q v = -‖v‖²`, the elements `r + s · vol` multiply as the complex numbers `r + s i`
  (`CliffordAlgebra.algebraMap_add_smul_volumeElement_mul`), with spinor norm `r² + s²`
  (`CliffordAlgebra.algebraMap_add_smul_volumeElement_mul_star_self`).
* `CliffordAlgebra.volumeElement_eq_ι_mul_ι`: in dimension two the volume element is `c(e₀) c(e₁)`.
* `CliffordAlgebra.involute_eq_volumeElement_mul_mul`: in rank divisible by four, left and
  right multiplication by the negative-metric raw volume recover parity.
* `CliffordAlgebra.volumeElement_mul_basis`: for `Q v = -‖v‖²` it sends the Clifford basis vector
  `e_s` of a positively oriented orthonormal basis to a signed `e_{sᶜ}`.

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

section Naturality

variable {V' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']
  [Fact (finrank ℝ V' = n)] {Q' : QuadraticForm ℝ V'}

/-- **Naturality of the volume element**: an isometric equivalence `e` of the quadratic forms that
also preserves the norms carries the volume element of `o` to that of the transported orientation.
In particular an orientation-preserving isometry of `V` fixing `Q` fixes the volume element, while
an orientation-reversing one negates it (`CliffordAlgebra.volumeElement_neg_orientation`). -/
theorem map_volumeElement (e : Q.IsometryEquiv Q') (he : ∀ v, ‖e v‖ = ‖v‖) :
    map e.toIsometry (volumeElement Q o) = volumeElement Q' (o.map (Fin n) e.toLinearEquiv) := by
  let f : V ≃ₗᵢ[ℝ] V' := { e.toLinearEquiv with norm_map' := he }
  -- Both sides are signed by the orientation, so it suffices to treat the orientation of a frame.
  suffices h : ∀ b : OrthonormalBasis (Fin n) ℝ V, map e.toIsometry
      (volumeElement Q b.toBasis.orientation) =
        volumeElement Q' (b.toBasis.orientation.map (Fin n) e.toLinearEquiv) by
    rcases (frame V n).toBasis.orientation_eq_or_eq_neg o with ho | ho
    · rw [ho, h]
    · rw [ho, volumeElement_neg_orientation, map_neg, h, Orientation.map_neg,
        volumeElement_neg_orientation]
  intro b
  have hb : (b.map f).toBasis.orientation = b.toBasis.orientation.map (Fin n) e.toLinearEquiv := by
    rw [OrthonormalBasis.toBasis_map, Basis.orientation_map]
  rw [volumeElement_eq_basis _ b rfl, volumeElement_eq_basis _ (b.map f) hb, map_basis,
    OrthonormalBasis.toBasis_map]

end Naturality

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

/-- In even dimension the raw volume element intertwines the grade involution:
`ω x = involute x * ω`. -/
theorem volumeElement_mul_eq_involute_mul (hn : Even n) (x : CliffordAlgebra Q) :
    volumeElement Q o * x = involute x * volumeElement Q o := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp [Algebra.commutes]
  | ι v => simp [volumeElement_mul_ι_of_even o hn]
  | add x y hx hy => simp [mul_add, add_mul, hx, hy]
  | mul x y hx hy => rw [← mul_assoc, hx, mul_assoc, hy, map_mul, mul_assoc]

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

/-- **The coordinates of `r + s · vol`**: in positive dimension, the scalar `r` and the volume
coefficient `s` of `r + s · vol` are determined by the element. -/
theorem algebraMap_add_smul_volumeElement_inj (hn : n ≠ 0) {r s r' s' : ℝ} :
    algebraMap ℝ (CliffordAlgebra Q) r + s • volumeElement Q o =
        algebraMap ℝ _ r' + s' • volumeElement Q o ↔ r = r' ∧ s = s' := by
  have : NeZero n := ⟨hn⟩
  let B := basis Q ((frame V n).adjustToOrientation o).toBasis
  have hω : volumeElement Q o = B Finset.univ :=
    volumeElement_eq_basis o _ (OrthonormalBasis.orientation_adjustToOrientation _ _)
  have h₁ : (algebraMap ℝ (CliffordAlgebra Q) : ℝ → _) = fun t ↦ t • B ∅ := by
    ext t
    simp [B, Algebra.algebraMap_eq_smul_one]
  have hne : (∅ : Finset (Fin n)) ≠ Finset.univ := Finset.univ_nonempty.ne_empty.symm
  refine ⟨fun h ↦ ?_, fun ⟨hr, hs⟩ ↦ hr ▸ hs ▸ rfl⟩
  have h' := congrArg B.repr h
  rw [hω, h₁] at h'
  exact ⟨by simpa [Finsupp.single_apply, hne] using congrArg (· ∅) h',
    by simpa [Finsupp.single_apply, hne] using congrArg (· Finset.univ) h'⟩

/-- For `Q v = -‖v‖²` in a dimension `n` with `⌊(n + 1) / 2⌋` odd, for instance `n = 2`, the
volume element squares to `-1`, so the elements `r + s · vol` multiply as the complex numbers
`r + s i`. -/
theorem algebraMap_add_smul_volumeElement_mul (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hn : Odd ((n + 1) / 2)) (a b c d : ℝ) :
    (algebraMap ℝ (CliffordAlgebra Q) a + b • volumeElement Q o) *
        (algebraMap ℝ _ c + d • volumeElement Q o) =
      algebraMap ℝ _ (a * c - b * d) + (a * d + b * c) • volumeElement Q o := by
  have hsq : volumeElement Q o * volumeElement Q o = -1 := by
    rw [volumeElement_mul_self o hQ, hn.neg_one_pow]
  simp only [Algebra.algebraMap_eq_smul_one, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, hsq]
  module

/-- For `Q v = -‖v‖²` in a dimension `n` with `⌊(n + 1) / 2⌋` odd, for instance `n = 2`, the
spinor norm `x x⋆` of `x = r + s · vol` is the scalar `r² + s²`. -/
theorem algebraMap_add_smul_volumeElement_mul_star_self (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hn : Odd ((n + 1) / 2)) (r s : ℝ) :
    (algebraMap ℝ (CliffordAlgebra Q) r + s • volumeElement Q o) *
        star (algebraMap ℝ (CliffordAlgebra Q) r + s • volumeElement Q o) =
      algebraMap ℝ _ (r ^ 2 + s ^ 2) := by
  rw [star_add, star_algebraMap, CliffordAlgebra.star_smul, star_volumeElement, hn.neg_one_pow,
    smul_smul, algebraMap_add_smul_volumeElement_mul o hQ hn,
    show r * (s * -1) + s * r = 0 by ring, zero_smul, add_zero]
  congr 1
  ring

/-- **Frame formula in dimension two**: the volume element of an oriented plane is
`c(e₀) c(e₁)` for every positively oriented orthonormal basis `e` that is orthogonal for `Q`. -/
theorem volumeElement_eq_ι_mul_ι [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))
    (b : OrthonormalBasis (Fin 2) ℝ V) (hb : b.toBasis.orientation = o)
    (hQb : (QuadraticMap.associated Q).IsOrthoᵢ b.toBasis) :
    volumeElement Q o = ι Q (b 0) * ι Q (b 1) := by
  rw [volumeElement_eq o b hb hQb]
  simp [List.finRange_succ]

/-- In rank divisible by four, parity is left times right raw negative volume.
No orientation choice remains on the right, since reversing it changes both factors' signs. -/
theorem involute_eq_volumeElement_mul_mul (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hn : 4 ∣ n)
    (s : CliffordAlgebra Q) :
    involute s = volumeElement Q o * s * volumeElement Q o := by
  obtain ⟨k, rfl⟩ := hn
  have heven : Even (4 * k) := ⟨2 * k, by omega⟩
  have hexp : (4 * k + 1) / 2 = 2 * k := by omega
  rw [volumeElement_mul_eq_involute_mul o heven, mul_assoc,
    volumeElement_mul_self o hQ, hexp]
  simp [pow_mul]

open Set in
/-- For `Q v = -‖v‖²`, the Clifford product of the volume element with the basis vector `e_s` of a
positively oriented orthonormal basis is the signed basis vector
`(-1) ^ ((k + 1).choose 2) ε(sᶜ) e_{sᶜ}`, where `ε(sᶜ)` is the shuffle sign of the complement. -/
theorem volumeElement_mul_basis (hQ : ∀ v, Q v = -‖v‖ ^ 2) (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o) {k l : ℕ} (hcard : l + k = Fintype.card (Fin n))
    (s : powersetCard (Fin n) k) :
    volumeElement Q o * basis Q b.toBasis s =
      ((-1 : ℝ) ^ (k + 1).choose 2 * ((powersetCard.sign (powersetCard.compl hcard s) : ℤ) : ℝ))
        • basis Q b.toBasis (powersetCard.compl hcard s) := by
  set t := powersetCard.compl hcard s
  have hts : Disjoint t.val s.val := (powersetCard.disjoint_iff_eq_compl hcard).2 rfl
  have hunion : (powersetCard.disjUnion hts : Finset (Fin n)) = Finset.univ :=
    Finset.eq_univ_of_card _ <| by
      rw [powersetCard.coe_disjUnion, Finset.card_disjUnion, powersetCard.mem_iff.1 s.2,
        powersetCard.mem_iff.1 t.2]
      exact hcard
  -- `e_t e_s = ε(t) vol`, and `ε(t) ^ 2 = 1`.
  have hsq : ((powersetCard.sign t : ℤ) : ℝ) * ((powersetCard.sign t : ℤ) : ℝ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hvol : volumeElement Q o = ((powersetCard.sign t : ℤ) : ℝ) •
      (basis Q b.toBasis t * basis Q b.toBasis s) := by
    rw [basis_mul_basis_of_disjoint (b.isOrthoᵢ_associated hQ) hts,
      ← powersetCard.sign_eq_permOfDisjoint_sign (by omega) t s hts, hunion,
      ← volumeElement_eq_basis o b hb]
    simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, hsq, one_smul]
  have hss : basis Q b.toBasis s * basis Q b.toBasis s =
      algebraMap ℝ (CliffordAlgebra Q) ((-1) ^ (k + 1).choose 2) := by
    rw [basis_mul_self_of_orthonormal hQ, powersetCard.mem_iff.1 s.2]
    simp
  rw [hvol, smul_mul_assoc, mul_assoc, hss, ← Algebra.commutes, ← Algebra.smul_def, smul_smul,
    mul_comm]

end CliffordAlgebra
