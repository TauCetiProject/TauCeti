/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.Analysis.Complex.UpperHalfPlane.DiscCoordinate
public import TauCeti.Analysis.Complex.UpperHalfPlane.SmulDeriv
import Mathlib.RingTheory.IntegralDomain

/-!
# Point stabilizers of subgroups of `PSL(2, ℝ)`

The transformations fixing a point `z` of the upper half-plane are recorded by their derivative
there. By the chain rule that derivative is multiplicative on the stabilizer, so it is a
character `stabilizer Γ z →* ℂ` for any subgroup `Γ ≤ PSL(2, ℝ)`, and it is injective: a Möbius
transformation fixing `z` with derivative `1` there is the identity. Hence a point stabilizer is
commutative, and cyclic as soon as it is finite — a finite subgroup of the multiplicative monoid
of a field is cyclic.

The injectivity of the character turns the order of a generator into the order of its
derivative, so the derivative of a generator of a finite point stabilizer is a primitive root of
unity whose order is the order of the stabilizer, and the derivatives of a finite stabilizer of
order `m` are exactly the `m`-th roots of unity. In the disc coordinate centred at the point,
every element of the stabilizer is the rotation by its derivative. Finally, every nontrivial
element of a point stabilizer is an elliptic matrix.

The specialization to discrete subgroups, whose point stabilizers are finite, is
`TauCeti.Analysis.Complex.Fuchsian.Stabilizer`.

## Main declarations

* `Subgroup.stabilizerDeriv`: the derivative character of a point stabilizer, and
  `Subgroup.stabilizerDeriv_injective`.
* `Subgroup.isCyclic_stabilizer`: a finite point stabilizer is cyclic.
* `Subgroup.exists_isPrimitiveRoot_stabilizerDeriv`: a generator of a finite point
  stabilizer has a primitive root of unity of the stabilizer's order as its derivative, and
  `Subgroup.range_stabilizerDeriv`: the derivatives are exactly the roots of unity of that order.
* `Matrix.ProjectiveSpecialLinearGroup.discCoordinate_smul_of_smul_eq_self`: a transformation
  fixing `z` multiplies the disc coordinate centred at `z` by its derivative at `z`, and
  `Subgroup.discCoordinate_smul_stabilizer`: its form for the stabilizer of `z` in `Γ`.
* `Matrix.SpecialLinearGroup.isElliptic_of_smul_eq_self_of_ne_one`: a matrix fixing a point of
  `ℍ` and nontrivial in `PSL(2, ℝ)` is elliptic.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, Chapters 7–8.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of
  Chicago Press, 1992, §§2.1–2.4.
-/

public section

noncomputable section

open Matrix Matrix.SpecialLinearGroup MulAction UpperHalfPlane

open scoped MatrixGroups ComplexConjugate

namespace Matrix.SpecialLinearGroup

/-- An element of `SL(2, ℝ)` that fixes `z : ℍ` and whose automorphy factor at `z` is a real
number `e` is the scalar matrix `e`. -/
theorem coe_eq_scalar_of_smul_eq_self_of_denom_eq {g : SL(2, ℝ)} {z : ℍ} {e : ℝ}
    (hz : g • z = z)
    (hd : denom (mapGL ℝ g) (z : ℂ) = (e : ℂ)) :
    (g : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.scalar (Fin 2) e := by
  have hdet : (0 : ℝ) < (mapGL ℝ g).det.val := by simp
  have hne : (e : ℂ) ≠ 0 := hd ▸ denom_ne_zero (mapGL ℝ g) z
  have hn : num (mapGL ℝ g) (z : ℂ) = (e : ℂ) * (z : ℂ) := by
    have h1 : ((mapGL ℝ g) • z : ℍ) = z := hz
    have h2 := coe_smul_of_det_pos hdet z
    rw [h1, hd, eq_div_iff hne] at h2
    rw [← h2]
    ring
  simp only [num, denom, mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    RingHom.id_apply, Algebra.algebraMap_self, Complex.ext_iff, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero] at hd hn
  have him : (z : ℂ).im ≠ 0 := z.im_ne_zero
  have h10 : g 1 0 = 0 := (mul_eq_zero.mp hd.2).resolve_right him
  have h00 : g 0 0 = e := mul_right_cancel₀ him hn.2
  have h11 : g 1 1 = e := by
    have h := hd.1
    rw [h10] at h
    linarith
  have h01 : g 0 1 = 0 := by
    have h := hn.1
    rw [h00] at h
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h00, h01, h10, h11]

/-- An element of `SL(2, ℝ)` fixing `z : ℍ` whose automorphy factor at `z` squares to one is
central, that is, `±1`. -/
theorem mem_center_of_smul_eq_self_of_denom_sq_eq_one {g : SL(2, ℝ)} {z : ℍ}
    (hz : g • z = z)
    (hd : denom (mapGL ℝ g) (z : ℂ) ^ 2 = 1) : g ∈ Subgroup.center SL(2, ℝ) := by
  rw [mem_center_iff_eq_one_or_eq_neg_one]
  have hd' : denom (mapGL ℝ g) (z : ℂ) * denom (mapGL ℝ g) (z : ℂ) = 1 := by rw [← sq]; exact hd
  rcases mul_self_eq_one_iff.mp hd' with h | h
  · exact Or.inl (Subtype.ext (by
      rw [coe_eq_scalar_of_smul_eq_self_of_denom_eq hz (e := 1) (by simpa using h)]; simp))
  · refine Or.inr (Subtype.ext ?_)
    rw [coe_eq_scalar_of_smul_eq_self_of_denom_eq hz (e := -1) (by simpa using h)]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]

end Matrix.SpecialLinearGroup

namespace Matrix.ProjectiveSpecialLinearGroup

/-- **The derivative of the action detects the identity**: a Möbius transformation of `ℍ` fixing
`z` whose derivative at `z` is `1` is the identity of `PSL(2, ℝ)`. -/
theorem eq_one_of_smul_eq_self_of_smulDeriv_eq_one {q : PSL(2, ℝ)} {z : ℍ}
    (hz : q • z = z)
    (h : smulDeriv q z = 1) : q = 1 := by
  induction q using QuotientGroup.induction_on with | _ g =>
  rw [smulDeriv_coe, inv_eq_one] at h
  refine (QuotientGroup.eq_one_iff g).mpr
    (Matrix.SpecialLinearGroup.mem_center_of_smul_eq_self_of_denom_sq_eq_one ?_ h)
  rwa [pslMk_smul] at hz

/-- **A Möbius transformation fixing `z` is a rotation in the disc coordinate centred at `z`**,
by its derivative at `z`: the disc coordinate linearizes the transformation near its fixed
point. -/
theorem discCoordinate_smul_of_smul_eq_self {q : PSL(2, ℝ)} {z : ℍ} (hq : q • z = z)
    (τ : ℍ) : discCoordinate z (q • τ) = smulDeriv q z * discCoordinate z τ := by
  induction q using QuotientGroup.induction_on with | _ g =>
  rw [pslMk_smul, MulAction.compHom_smul_def] at hq ⊢
  have hdet : (0 : ℝ) < (mapGL ℝ g).det.val := by simp
  have hd := denom_ne_zero (mapGL ℝ g) z
  -- a transformation of determinant one fixing `z` has an automorphy factor of modulus one there
  have hn : conj (denom (mapGL ℝ g) z) * denom (mapGL ℝ g) z = 1 := by
    have h := im_smul_eq_div_normSq (mapGL ℝ g) z
    rw [hq] at h
    simp only [Matrix.SpecialLinearGroup.det_mapGL, Units.val_one, abs_one, one_mul] at h
    rw [eq_div_iff (Complex.normSq_pos.mpr hd).ne', mul_eq_left₀ z.im_ne_zero] at h
    rw [mul_comm, Complex.mul_conj, h, Complex.ofReal_one]
  rw [UpperHalfPlane.discCoordinate_smul_of_smul_eq_self hdet hq, smulDeriv_coe,
    eq_inv_of_mul_eq_one_left hn]
  field_simp

end Matrix.ProjectiveSpecialLinearGroup

namespace Subgroup

/-- The derivative character of the stabilizer of `z : ℍ` in a subgroup `Γ ≤ PSL(2, ℝ)`: it
sends an element fixing `z` to its derivative
`Matrix.ProjectiveSpecialLinearGroup.smulDeriv` at `z`. -/
def stabilizerDeriv (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) : stabilizer Γ z →* ℂ where
  toFun q := Matrix.ProjectiveSpecialLinearGroup.smulDeriv ((q : Γ) : PSL(2, ℝ)) z
  map_one' := by simp
  map_mul' q₁ q₂ := by
    have h₂ : (((q₂ : Γ) : PSL(2, ℝ)) • z) = z := q₂.2
    simp only [Subgroup.coe_mul, Matrix.ProjectiveSpecialLinearGroup.smulDeriv_mul, h₂]

/-- The derivative character evaluated on an element of the stabilizer. -/
@[simp]
theorem stabilizerDeriv_apply (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (q : stabilizer Γ z) :
    stabilizerDeriv Γ z q =
      Matrix.ProjectiveSpecialLinearGroup.smulDeriv ((q : Γ) : PSL(2, ℝ)) z := (rfl)

/-- **The derivative character of a point stabilizer is injective**: a transformation fixing `z`
is determined by its derivative at `z`. -/
theorem stabilizerDeriv_injective (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    Function.Injective (stabilizerDeriv Γ z) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  exact Subtype.ext (Subtype.ext
    (Matrix.ProjectiveSpecialLinearGroup.eq_one_of_smul_eq_self_of_smulDeriv_eq_one q.2 hq))

/-- **An element of the stabilizer of `z` is a rotation in the disc coordinate centred at `z`**,
by its derivative character. -/
@[simp]
theorem discCoordinate_smul_stabilizer (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (q : stabilizer Γ z)
    (τ : ℍ) : discCoordinate z (q • τ) = stabilizerDeriv Γ z q * discCoordinate z τ := by
  rw [Subgroup.smul_def, Subgroup.smul_def]
  exact Matrix.ProjectiveSpecialLinearGroup.discCoordinate_smul_of_smul_eq_self q.2 τ

/-- A point stabilizer in a subgroup of `PSL(2, ℝ)` is commutative. -/
instance instIsMulCommutativeStabilizer (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    IsMulCommutative (stabilizer Γ z) where
  is_comm := ⟨fun q₁ q₂ ↦ stabilizerDeriv_injective Γ z (by rw [map_mul, map_mul, mul_comm])⟩

/-- **A finite point stabilizer is cyclic.** For a discrete subgroup of `PSL(2, ℝ)`, where the
finiteness hypothesis is automatic, see `Subgroup.instIsCyclicStabilizer`. -/
theorem isCyclic_stabilizer (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) [Finite (stabilizer Γ z)] :
    IsCyclic (stabilizer Γ z) :=
  isCyclic_of_injective_ringHom _ (stabilizerDeriv_injective Γ z)

/-- The order of an element of a point stabilizer is the order of its derivative at that
point. -/
theorem orderOf_stabilizerDeriv (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (q : stabilizer Γ z) :
    orderOf (stabilizerDeriv Γ z q) = orderOf q :=
  orderOf_injective _ (stabilizerDeriv_injective Γ z) q

/-- **A finite point stabilizer is generated by a transformation whose derivative at the point
is a primitive root of unity** of order the stabilizer's order — the elliptic order of the
point. -/
theorem exists_isPrimitiveRoot_stabilizerDeriv (Γ : Subgroup PSL(2, ℝ)) (z : ℍ)
    [Finite (stabilizer Γ z)] :
    ∃ q : stabilizer Γ z, Subgroup.zpowers q = ⊤ ∧
      IsPrimitiveRoot (stabilizerDeriv Γ z q) (Nat.card (stabilizer Γ z)) := by
  obtain ⟨q, hq⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (isCyclic_stabilizer Γ z)
  refine ⟨q, hq, ?_⟩
  have hcard : orderOf q = Nat.card (stabilizer Γ z) := by
    rw [← Nat.card_zpowers, hq, Subgroup.card_top]
  rw [← hcard, ← orderOf_stabilizerDeriv]
  exact IsPrimitiveRoot.orderOf _

/-- The derivative of an element of a point stabilizer is a root of unity of order dividing the
stabilizer's order (vacuously so, with `Nat.card = 0`, when the stabilizer is infinite). -/
@[simp]
theorem stabilizerDeriv_pow_card (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (q : stabilizer Γ z) :
    stabilizerDeriv Γ z q ^ Nat.card (stabilizer Γ z) = 1 := by
  rw [← map_pow, pow_card_eq_one', map_one]

/-- **The derivatives of a finite point stabilizer of order `m` are exactly the `m`-th roots of
unity.** In the disc coordinate centred at the point, the stabilizer therefore acts as the full
group of rotations by `m`-th roots of unity. -/
theorem range_stabilizerDeriv (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) [Finite (stabilizer Γ z)] :
    Set.range (stabilizerDeriv Γ z) = {ζ | ζ ^ Nat.card (stabilizer Γ z) = 1} := by
  refine Set.Subset.antisymm (Set.range_subset_iff.mpr (stabilizerDeriv_pow_card Γ z))
    fun ζ hζ ↦ ?_
  have : NeZero (Nat.card (stabilizer Γ z)) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨q, -, hq⟩ := exists_isPrimitiveRoot_stabilizerDeriv Γ z
  obtain ⟨k, -, hk⟩ := hq.eq_pow_of_pow_eq_one hζ
  exact ⟨q ^ k, by rw [map_pow, hk]⟩

end Subgroup

namespace Matrix.SpecialLinearGroup

/-- **A nonidentity element fixing a point of `ℍ` is elliptic.** -/
theorem isElliptic_of_smul_eq_self_of_ne_one {g : SL(2, ℝ)} {z : ℍ} (hz : g • z = z)
    (hg : (g : PSL(2, ℝ)) ≠ 1) : Matrix.GeneralLinearGroup.IsElliptic (mapGL ℝ g) := by
  refine isElliptic_of_exists_smul_eq_self (by simp) (fun hc ↦ hg ?_) ⟨z, hz⟩
  have h := forall_smul_eq_self_iff_mem_center.mpr hc
  exact eq_of_smul_eq_smul fun w : ℍ ↦ by rw [one_smul, pslMk_smul]; exact h w

end Matrix.SpecialLinearGroup
