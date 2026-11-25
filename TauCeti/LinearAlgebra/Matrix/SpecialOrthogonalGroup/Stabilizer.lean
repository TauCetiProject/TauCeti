/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.DotProduct
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.FinTwo.Cyclic
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Frame
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block

/-!
# Stabilizers of vectors in `SO(3)`

The rotations of `R³` fixing a vector `p` are the rotations of the plane orthogonal to `p`. In
coordinates: the image of the block embedding `B ↦ diag(1, B)` of `SO(m, R)` in `SO(1 + m, R)`
(`Matrix.SpecialOrthogonalGroup.fromBlocksOne`) is the stabilizer of the first standard basis
vector `e₀`, over any commutative ring. If `p` is a unit vector with a unit vector `u` orthogonal
to it, the rotation `ofFrame p u` with columns `p`, `u` and `p ⨯₃ u` carries `e₀` to `p`, and
conjugating by it identifies `SO(2, R)` with the stabilizer of `p`.

Over a field in which `2 ≠ 0` every unit vector has an orthogonal unit vector
(`TauCeti.exists_dotProduct_self_eq_one_dotProduct_eq_zero`), and over an integral domain in which
`2 ≠ 0` the finite subgroups of `SO(2)` are cyclic
(`TauCeti.Matrix.SpecialOrthogonalGroup.isCyclic_of_injective_specialOrthogonalGroup_fin_two`).
After passing to the algebraic closure of the fraction field and normalizing, the identification
above applies to any `p` with `p ⬝ᵥ p ≠ 0`, so every finite group of rotations fixing such a vector
is cyclic. Over `ℝ`, or any linearly ordered commutative ring, this holds for every nonzero `p`.
These stabilizers are the pole stabilizers in Klein's classification of the finite rotation groups
of `ℝ³`.

## Main declarations

* `TauCeti.Matrix.SpecialOrthogonalGroup.range_fromBlocksOne_eq_stabilizer`: the block-diagonal
  rotations `diag(1, B)` are the stabilizer of `e₀`.
* `TauCeti.Matrix.SpecialOrthogonalGroup.equivFirstStabilizer`: `SO(m, R)` is the stabilizer of
  the first standard basis vector in `SO(1 + m, R)`, through `B ↦ diag(1, B)`.
* `TauCeti.Matrix.SpecialOrthogonalGroup.equivStabilizer`: `SO(2, R)` is the stabilizer of a unit
  vector `p` with an orthogonal unit vector `u`, through conjugation by the frame `(p, u, p ⨯₃ u)`.
* `TauCeti.Matrix.SpecialOrthogonalGroup.isCyclic_stabilizer`: a finite stabilizer of a vector `p`
  with `p ⬝ᵥ p ≠ 0` in a group of rotations is cyclic.
* `TauCeti.Matrix.SpecialOrthogonalGroup.isCyclic_stabilizer_of_ne_zero`: over a linearly ordered
  commutative ring, such as `ℝ`, a finite stabilizer of a nonzero vector is cyclic.

## References

* M. Artin, *Algebra*, second edition, Pearson, 2011, Section 6.12 (the stabilizer of a pole is a
  cyclic group of rotations about its axis).
-/

public section

open Matrix MulAction

namespace TauCeti.Matrix.SpecialOrthogonalGroup

attribute [local instance] starRingOfComm

variable {R : Type*} [CommRing R]

/-! ### The stabilizer of the first standard basis vector -/

variable (R) in
/-- **The block-diagonal rotations `diag(1, B)` are the stabilizer of the first standard basis
vector `e₀`**: the image of the block embedding of `SO(m)` in `SO(1 + m)` is the subgroup fixing
`e₀`. -/
theorem range_fromBlocksOne_eq_stabilizer (m : ℕ) :
    (Matrix.SpecialOrthogonalGroup.fromBlocksOne R 1 m).range =
      stabilizer (specialOrthogonalGroup (Fin (1 + m)) R) (Pi.single 0 1 : Fin (1 + m) → R) := by
  ext A
  rw [Matrix.SpecialOrthogonalGroup.mem_range_fromBlocksOne_iff, Fin.forall_fin_one,
    Matrix.SpecialOrthogonalGroup.mem_stabilizer_iff_mulVec_eq_self,
    show (Fin.castAdd m 0 : Fin (1 + m)) = 0 from Fin.ext (by simp)]

variable (R) in
/-- **`SO(m, R)` is the stabilizer of the first standard basis vector `e₀` in `SO(1 + m, R)`**, over
any commutative ring: a rotation `B` corresponds to the block matrix `diag(1, B)`
(`Matrix.SpecialOrthogonalGroup.fromBlocksOne`). -/
noncomputable def equivFirstStabilizer (m : ℕ) :
    specialOrthogonalGroup (Fin m) R ≃* stabilizer (specialOrthogonalGroup (Fin (1 + m)) R)
      (Pi.single 0 1 : Fin (1 + m) → R) :=
  (MonoidHom.ofInjective (Matrix.SpecialOrthogonalGroup.fromBlocksOne_injective R 1)).trans
    (MulEquiv.subgroupCongr (range_fromBlocksOne_eq_stabilizer R m))

/-- The rotation attached to `B ∈ SO(m, R)` is the block matrix `diag(1, B)`. -/
@[simp]
theorem coe_equivFirstStabilizer_apply {m : ℕ} (B : specialOrthogonalGroup (Fin m) R) :
    (equivFirstStabilizer R m B : specialOrthogonalGroup (Fin (1 + m)) R) =
      Matrix.SpecialOrthogonalGroup.fromBlocksOne R 1 m B :=
  (rfl)

/-- The rotation of `Rᵐ` attached to a rotation of `R¹⁺ᵐ` fixing `e₀` is its lower right `m × m`
block. -/
@[simp]
theorem coe_equivFirstStabilizer_symm_apply {m : ℕ}
    (g : stabilizer (specialOrthogonalGroup (Fin (1 + m)) R) (Pi.single 0 1 : Fin (1 + m) → R))
    (k l : Fin m) :
    ((equivFirstStabilizer R m).symm g : Matrix (Fin m) (Fin m) R) k l =
      ((g : specialOrthogonalGroup (Fin (1 + m)) R) : Matrix (Fin (1 + m)) (Fin (1 + m)) R)
        (Fin.natAdd 1 k) (Fin.natAdd 1 l) := by
  conv_rhs => rw [← (equivFirstStabilizer R m).apply_symm_apply g]
  rw [coe_equivFirstStabilizer_apply,
    Matrix.SpecialOrthogonalGroup.fromBlocksOne_apply_natAdd_natAdd]

/-! ### The stabilizer of a unit vector -/

section Frame

variable {p u : Fin 3 → R}

/-- **`SO(2, R)` is the stabilizer of a unit vector `p` in `SO(3, R)`**, given a unit vector `u`
orthogonal to `p`: a rotation `A` of the plane corresponds to the rotation acting by `A` in the
oriented orthonormal basis `(u, p ⨯₃ u)` of the plane orthogonal to `p`. It conjugates
`equivFirstStabilizer` by the rotation `ofFrame p u`, which carries `e₀` to `p`. -/
noncomputable def equivStabilizer (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1) (hpu : p ⬝ᵥ u = 0) :
    specialOrthogonalGroup (Fin 2) R ≃* stabilizer (specialOrthogonalGroup (Fin 3) R) p :=
  (equivFirstStabilizer R 2).trans <|
    stabilizerEquivStabilizer (g := ⟨ofFrame p u, ofFrame_mem_iff.mpr ⟨hp, hu, hpu⟩⟩) <| by
      rw [Submonoid.smul_def, smul_eq_mulVec, mulVec_single_one, ofFrame_col_zero]

/-- The rotation attached to `A ∈ SO(2, R)` is `F * diag(1, A) * Fᵀ`, where `F` is the frame
matrix with columns `p`, `u` and `p ⨯₃ u`. -/
@[simp]
theorem coe_equivStabilizer_apply (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1) (hpu : p ⬝ᵥ u = 0)
    (A : specialOrthogonalGroup (Fin 2) R) :
    ((equivStabilizer hp hu hpu A : specialOrthogonalGroup (Fin 3) R) :
      Matrix (Fin 3) (Fin 3) R) =
      ofFrame p u * (Matrix.SpecialOrthogonalGroup.fromBlocksOne R 1 2 A :
        Matrix (Fin 3) (Fin 3) R) * (ofFrame p u)ᵀ := by
  rw [equivStabilizer, MulEquiv.trans_apply, stabilizerEquivStabilizer_apply, MulAut.conj_apply,
    Submonoid.coe_mul, Submonoid.coe_mul, coe_specialOrthogonalGroup_inv,
    coe_equivFirstStabilizer_apply]

/-- The rotation of the plane attached to a rotation `g` fixing `p` is the matrix whose columns
are the coordinates of `g u` and `g (p ⨯₃ u)` in the orthonormal basis `(u, p ⨯₃ u)`. -/
@[simp]
theorem coe_equivStabilizer_symm_apply (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1) (hpu : p ⬝ᵥ u = 0)
    (g : stabilizer (specialOrthogonalGroup (Fin 3) R) p) :
    ((equivStabilizer hp hu hpu).symm g : Matrix (Fin 2) (Fin 2) R) =
      !![u ⬝ᵥ (g : Matrix (Fin 3) (Fin 3) R) *ᵥ u,
        u ⬝ᵥ (g : Matrix (Fin 3) (Fin 3) R) *ᵥ (p ⨯₃ u);
        (p ⨯₃ u) ⬝ᵥ (g : Matrix (Fin 3) (Fin 3) R) *ᵥ u,
        (p ⨯₃ u) ⬝ᵥ (g : Matrix (Fin 3) (Fin 3) R) *ᵥ (p ⨯₃ u)] := by
  ext i j
  simp only [equivStabilizer, MulEquiv.symm_trans_apply, coe_equivFirstStabilizer_symm_apply,
    stabilizerEquivStabilizer_symm_apply, MulAut.conj_apply, Submonoid.coe_mul,
    coe_specialOrthogonalGroup_inv, inv_inv]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, mulVec, dotProduct, Fin.sum_univ_three, ofFrame_apply] <;> ring

end Frame

/-- **A finite stabilizer of a vector `p` with `p ⬝ᵥ p ≠ 0` in a group of rotations is cyclic**,
over an integral domain in which `2 ≠ 0`. After passing to an algebraically closed field and
normalizing `p`, the stabilizer embeds into `SO(2)` (`equivStabilizer`). -/
theorem isCyclic_stabilizer [IsDomain R] [NeZero (2 : R)]
    (H : Subgroup (specialOrthogonalGroup (Fin 3) R)) {p : Fin 3 → R} (hp : p ⬝ᵥ p ≠ 0)
    [Finite (stabilizer H p)] : IsCyclic (stabilizer H p) := by
  let L := AlgebraicClosure (FractionRing R)
  have hφ : Function.Injective (algebraMap R L) := FaithfulSMul.algebraMap_injective R L
  set φ := algebraMap R L
  have : NeZero (2 : L) := NeZero.of_faithfulSMul R L 2
  -- Normalize the image `p'` of `p` in `L³` to a unit vector `q`, and choose `u` orthogonal to it.
  set p' : Fin 3 → L := φ ∘ p
  have hp' : p' ⬝ᵥ p' ≠ 0 := by
    rw [← RingHom.map_dotProduct]
    exact (map_ne_zero_iff φ hφ).mpr hp
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (p' ⬝ᵥ p')⁻¹ two_pos
  have hq : (c • p') ⬝ᵥ (c • p') = 1 := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq, hc,
      inv_mul_cancel₀ hp']
  obtain ⟨u, hu, hqu⟩ := TauCeti.exists_dotProduct_self_eq_one_dotProduct_eq_zero hq
  -- An element of the stabilizer, with entries mapped to `L`, fixes `q`.
  have hfix (g : stabilizer H p) : Matrix.SpecialOrthogonalGroup.map φ (g : H) ∈
      stabilizer (specialOrthogonalGroup (Fin 3) L) (c • p') := by
    have hg : ((g : H) : Matrix (Fin 3) (Fin 3) R) *ᵥ p = p := by
      rw [← Matrix.SpecialOrthogonalGroup.mem_stabilizer_iff_mulVec_eq_self, mem_stabilizer_iff,
        ← Subgroup.smul_def]
      exact mem_stabilizer_iff.mp g.property
    rw [Matrix.SpecialOrthogonalGroup.mem_stabilizer_iff_mulVec_eq_self, mulVec_smul,
      Matrix.SpecialOrthogonalGroup.coe_map]
    congr 1
    ext j
    simp only [p', Function.comp_apply, ← RingHom.map_mulVec, hg]
  let F : stabilizer H p →* stabilizer (specialOrthogonalGroup (Fin 3) L) (c • p') :=
    ((Matrix.SpecialOrthogonalGroup.map φ).comp
      (H.subtype.comp (stabilizer H p).subtype)).codRestrict _ hfix
  refine isCyclic_of_injective_specialOrthogonalGroup_fin_two
    ((equivStabilizer hq hu hqu).symm.toMonoidHom.comp F) ?_
  refine (equivStabilizer hq hu hqu).symm.injective.comp fun g h hgh ↦ ?_
  exact Subtype.ext <| Subtype.ext <| Matrix.SpecialOrthogonalGroup.map_injective hφ <|
    congrArg Subtype.val hgh

/-- Over a linearly ordered commutative ring, such as `ℝ`, **a finite stabilizer of a nonzero
vector in a group of rotations is cyclic.** -/
theorem isCyclic_stabilizer_of_ne_zero [LinearOrder R] [IsStrictOrderedRing R]
    (H : Subgroup (specialOrthogonalGroup (Fin 3) R)) {p : Fin 3 → R} (hp : p ≠ 0)
    [Finite (stabilizer H p)] : IsCyclic (stabilizer H p) :=
  isCyclic_stabilizer H (dotProduct_self_eq_zero.not.mpr hp)

end TauCeti.Matrix.SpecialOrthogonalGroup
