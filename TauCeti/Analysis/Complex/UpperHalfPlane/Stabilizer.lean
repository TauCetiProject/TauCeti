/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.Analysis.Complex.UpperHalfPlane.DiscCoordinate
public import TauCeti.RingTheory.RootsOfUnity.PowFiber
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
unity whose order is the order of the stabilizer. Consequently the character identifies a finite
point stabilizer of order `m` with the group of `m`-th roots of unity, and in the disc coordinate
centred at the fixed point the stabilizer acts by exactly those rotations. Finally, every
nontrivial element of a point stabilizer is an elliptic matrix.

The specialization to discrete subgroups, whose point stabilizers are finite, is
`TauCeti.Analysis.Complex.Fuchsian.Stabilizer`.

## Main declarations

* `Subgroup.stabilizerDeriv`: the derivative character of a point stabilizer, and
  `Subgroup.stabilizerDeriv_injective`.
* `Subgroup.isCyclic_stabilizer`: a finite point stabilizer is cyclic.
* `Subgroup.exists_isPrimitiveRoot_stabilizerDeriv`: a generator of a finite point
  stabilizer has a primitive root of unity of the stabilizer's order as its derivative.
* `Subgroup.stabilizerRotation` and `Subgroup.stabilizerRotationEquiv`: the derivative character
  of a point stabilizer, and, for a finite stabilizer of order `m`, the isomorphism it gives onto
  the `m`-th roots of unity.
* `Subgroup.discCoordinate_stabilizer_smul` and `Subgroup.discCoordinate_smul_eq_rotation_smul`:
  in the disc coordinate centred at the fixed point, an element of the stabilizer acts by
  multiplication by its derivative, that is, by its rotation.
* `Subgroup.mem_orbit_stabilizer_iff_discCoordinate_pow_eq_pow`: two points lie in the same
  orbit of a finite stabilizer of order `m` exactly when their disc coordinates have the same
  `m`-th power.
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

open scoped MatrixGroups

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

/-- A point stabilizer in a subgroup of `PSL(2, ℝ)` is commutative. -/
instance instIsMulCommutativeStabilizer (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    IsMulCommutative (stabilizer Γ z) where
  is_comm := ⟨fun q₁ q₂ ↦ stabilizerDeriv_injective Γ z (by rw [map_mul, map_mul, mul_comm])⟩

/-- **A finite point stabilizer is cyclic.** For a discrete subgroup of `PSL(2, ℝ)`, where the
finiteness hypothesis is automatic, see `Subgroup.instIsCyclicStabilizer`. -/
theorem isCyclic_stabilizer (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) [Finite (stabilizer Γ z)] :
    IsCyclic (stabilizer Γ z) :=
  isCyclic_of_injective_ringHom _ (stabilizerDeriv_injective Γ z)

/-- **The disc coordinate linearizes a point stabilizer**: an element of the stabilizer of `z`
acts, in the disc coordinate centred at `z`, by multiplication by its derivative at `z`. -/
theorem discCoordinate_stabilizer_smul (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (q : stabilizer Γ z)
    (τ : ℍ) :
    discCoordinate z (q • τ) = stabilizerDeriv Γ z q * discCoordinate z τ := by
  have hq : ((q : Γ) : PSL(2, ℝ)) • z = z := by
    have h := q.2
    rwa [MulAction.mem_stabilizer_iff, Subgroup.smul_def] at h
  rw [Subgroup.smul_def, Subgroup.smul_def, stabilizerDeriv_apply]
  exact discCoordinate_psl_smul_of_smul_eq_self hq τ

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

/-- The rotation character of a point stabilizer: its derivative character at the fixed point,
which lands in the group of `m`-th roots of unity for `m = Nat.card (stabilizer Γ z)`. For a
finite stabilizer — the case of interest, and the only one in which `m` is the order of the
stabilizer — that is Lagrange's theorem, and the character is moreover an isomorphism, by
`Subgroup.stabilizerRotationEquiv`. For an infinite stabilizer `m = 0`, so the codomain is the
whole unit group and the roots-of-unity condition is vacuous. -/
def stabilizerRotation (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    stabilizer Γ z →* rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ :=
  (stabilizerDeriv Γ z).toHomUnits.codRestrict _ fun q ↦ by
    rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]

@[simp]
theorem coe_stabilizerRotation (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) (q : stabilizer Γ z) :
    ((stabilizerRotation Γ z q : ℂˣ) : ℂ) = stabilizerDeriv Γ z q :=
  (rfl)

theorem stabilizerRotation_injective (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) :
    Function.Injective (stabilizerRotation Γ z) := fun q₁ q₂ h ↦
  stabilizerDeriv_injective Γ z <| by
    rw [← coe_stabilizerRotation, ← coe_stabilizerRotation, h]

theorem stabilizerRotation_bijective (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) [Finite (stabilizer Γ z)] :
    Function.Bijective (stabilizerRotation Γ z) := by
  have : NeZero (Nat.card (stabilizer Γ z)) := ⟨Nat.card_pos.ne'⟩
  exact (Nat.bijective_iff_injective_and_card _).mpr
    ⟨stabilizerRotation_injective Γ z, (Complex.card_rootsOfUnity _).symm⟩

/-- **A finite point stabilizer of order `m` is the group of `m`-th roots of unity**, identified
by the derivative character at the fixed point. Together with
`Subgroup.discCoordinate_stabilizer_smul` this conjugates the stabilizer action on the upper
half-plane to the rotation action of the `m`-th roots of unity on the unit disc. -/
noncomputable def stabilizerRotationEquiv (Γ : Subgroup PSL(2, ℝ)) (z : ℍ)
    [Finite (stabilizer Γ z)] :
    stabilizer Γ z ≃* rootsOfUnity (Nat.card (stabilizer Γ z)) ℂ :=
  MulEquiv.ofBijective _ (stabilizerRotation_bijective Γ z)

@[simp]
theorem coe_stabilizerRotationEquiv (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) [Finite (stabilizer Γ z)] :
    ⇑(stabilizerRotationEquiv Γ z) = stabilizerRotation Γ z :=
  (rfl)

/-- **The disc coordinate conjugates a point stabilizer into the roots of unity**: an element of
the stabilizer of `z` acts, in the disc coordinate centred at `z`, by its rotation. -/
@[simp]
theorem discCoordinate_smul_eq_rotation_smul (Γ : Subgroup PSL(2, ℝ)) (z : ℍ)
    (q : stabilizer Γ z) (τ : ℍ) :
    discCoordinate z (q • τ) = stabilizerRotation Γ z q • discCoordinate z τ := by
  rw [rootsOfUnity.smul_eq_mul, coe_stabilizerRotation, discCoordinate_stabilizer_smul]

/-- Two points of `ℍ` lie in the same orbit of a finite stabilizer of `z` of order `m` exactly
when their disc coordinates centred at `z` have the same `m`-th power. -/
@[simp]
theorem mem_orbit_stabilizer_iff_discCoordinate_pow_eq_pow (Γ : Subgroup PSL(2, ℝ)) (z : ℍ)
    [Finite (stabilizer Γ z)] {τ σ : ℍ} :
    τ ∈ orbit (stabilizer Γ z) σ ↔
      discCoordinate z τ ^ Nat.card (stabilizer Γ z) =
        discCoordinate z σ ^ Nat.card (stabilizer Γ z) := by
  have : NeZero (Nat.card (stabilizer Γ z)) := ⟨Nat.card_pos.ne'⟩
  rw [TauCeti.pow_eq_pow_iff_exists_rootsOfUnity_smul (NeZero.ne _)]
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨stabilizerRotation Γ z q⁻¹, ?_⟩
    simp only [discCoordinate_smul_eq_rotation_smul, map_inv, inv_smul_smul]
  · rintro ⟨ζ, hζ⟩
    let q := (stabilizerRotationEquiv Γ z).symm ζ
    have hq : stabilizerRotation Γ z q = ζ := by
      rw [← coe_stabilizerRotationEquiv]
      exact (stabilizerRotationEquiv Γ z).apply_symm_apply ζ
    refine ⟨q⁻¹, discCoordinate_injective z ?_⟩
    simpa only [discCoordinate_smul_eq_rotation_smul, map_inv, hq, inv_smul_eq_iff] using hζ.symm

end Subgroup

namespace Matrix.SpecialLinearGroup

/-- **A nonidentity element fixing a point of `ℍ` is elliptic.** -/
theorem isElliptic_of_smul_eq_self_of_ne_one {g : SL(2, ℝ)} {z : ℍ} (hz : g • z = z)
    (hg : (g : PSL(2, ℝ)) ≠ 1) : Matrix.GeneralLinearGroup.IsElliptic (mapGL ℝ g) := by
  refine isElliptic_of_exists_smul_eq_self (by simp) (fun hc ↦ hg ?_) ⟨z, hz⟩
  have h := forall_smul_eq_self_iff_mem_center.mpr hc
  exact eq_of_smul_eq_smul fun w : ℍ ↦ by rw [one_smul, pslMk_smul]; exact h w

end Matrix.SpecialLinearGroup
