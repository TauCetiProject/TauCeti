/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.DotProduct
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.FinTwo.Cyclic
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Frame

/-!
# Stabilizers of vectors in `SO(3)`

The rotations of `R³` fixing a vector `p` are the rotations of the plane orthogonal to `p`. In
coordinates: a rotation fixing the last standard basis vector `e₂` has the block form `diag(A, 1)`
with `A ∈ SO(2, R)`, and this identifies `SO(2, R)` with the stabilizer of `e₂`, over any
commutative ring. If `p` is a unit vector with a unit vector `u` orthogonal to it, the rotation
with columns `u`, `p ⨯₃ u` and `p` carries `e₂` to `p`, and conjugating by it identifies `SO(2, R)`
with the stabilizer of `p`.

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

* `TauCeti.Matrix.SpecialOrthogonalGroup.mem_stabilizer_single_two_iff`: a rotation fixes the last
  standard basis vector `e₂` exactly when its third column and third row are `e₂`.
* `TauCeti.Matrix.SpecialOrthogonalGroup.equivLastStabilizer`: `SO(2, R)` is the stabilizer of the
  last standard basis vector in `SO(3, R)`, through `A ↦ diag(A, 1)`.
* `TauCeti.Matrix.SpecialOrthogonalGroup.equivStabilizer`: `SO(2, R)` is the stabilizer of a unit
  vector `p` with an orthogonal unit vector `u`, through conjugation by the frame `(u, p ⨯₃ u, p)`.
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

/-! ### The stabilizer of the last standard basis vector -/

/-- The block matrix `diag(A, 1)` of a rotation `A` of `R²` is a rotation of `R³`. -/
private theorem blockDiag_mem (A : specialOrthogonalGroup (Fin 2) R) :
    !![(A : Matrix (Fin 2) (Fin 2) R) 0 0, (A : Matrix (Fin 2) (Fin 2) R) 0 1, 0;
      (A : Matrix (Fin 2) (Fin 2) R) 1 0, (A : Matrix (Fin 2) (Fin 2) R) 1 1, 0; 0, 0, 1] ∈
      specialOrthogonalGroup (Fin 3) R := by
  have := mem_specialOrthogonalGroup_fin_two_iff.mp A.2
  simp [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff, ← Matrix.ext_iff,
    Fin.forall_fin_succ, vecHead, vecTail, det_fin_three]
  grind

/-- **A rotation of `R³` fixes `e₂` exactly when its third column and third row are `e₂`.** -/
theorem mem_stabilizer_single_two_iff {g : specialOrthogonalGroup (Fin 3) R} :
    g ∈ stabilizer (specialOrthogonalGroup (Fin 3) R) (Pi.single 2 1 : Fin 3 → R) ↔
      (g : Matrix (Fin 3) (Fin 3) R) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) R) 1 2 = 0 ∧
        (g : Matrix (Fin 3) (Fin 3) R) 2 2 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) R) 2 0 = 0 ∧
        (g : Matrix (Fin 3) (Fin 3) R) 2 1 = 0 := by
  rw [Matrix.SpecialOrthogonalGroup.mem_stabilizer_iff_mulVec_eq_self]
  refine ⟨fun hcol ↦ ?_, fun ⟨h02, h12, h22, _, _⟩ ↦ ?_⟩
  · -- An orthogonal matrix fixing a vector has transpose fixing it too.
    have hrow : (g : Matrix (Fin 3) (Fin 3) R)ᵀ *ᵥ Pi.single 2 1 = Pi.single 2 1 := by
      conv_lhs => rw [← hcol]
      rw [mulVec_mulVec, (mem_orthogonalGroup_iff' _ _).mp
        (mem_specialOrthogonalGroup_iff.mp g.2).1, one_mulVec]
    rw [mulVec_single_one] at hcol hrow
    exact ⟨by simpa using congrFun hcol 0, by simpa using congrFun hcol 1,
      by simpa using congrFun hcol 2, by simpa using congrFun hrow 0,
      by simpa using congrFun hrow 1⟩
  · rw [mulVec_single_one]
    ext i
    fin_cases i <;> simp [h02, h12, h22]

/-- The upper left `2 × 2` block of a rotation of `R³` fixing `e₂` is a rotation of `R²`. -/
private theorem block_mem {g : specialOrthogonalGroup (Fin 3) R}
    (hg : g ∈ stabilizer (specialOrthogonalGroup (Fin 3) R) (Pi.single 2 1 : Fin 3 → R)) :
    !![(g : Matrix (Fin 3) (Fin 3) R) 0 0, (g : Matrix (Fin 3) (Fin 3) R) 0 1;
      (g : Matrix (Fin 3) (Fin 3) R) 1 0, (g : Matrix (Fin 3) (Fin 3) R) 1 1] ∈
      specialOrthogonalGroup (Fin 2) R := by
  obtain ⟨h02, h12, h22, -, -⟩ := mem_stabilizer_single_two_iff.mp hg
  obtain ⟨hO, hdet⟩ := mem_specialOrthogonalGroup_iff.mp g.2
  have hO' := (mem_orthogonalGroup_iff _ _).mp hO
  -- The first two rows are orthonormal, and the block has determinant one.
  have e00 := Matrix.ext_iff.mpr hO' 0 0
  have e01 := Matrix.ext_iff.mpr hO' 0 1
  have e11 := Matrix.ext_iff.mpr hO' 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_three, transpose_apply, h02, h12, zero_mul, add_zero,
    one_apply_eq, one_apply_ne (show (0 : Fin 3) ≠ 1 by decide)] at e00 e01 e11
  rw [det_fin_three, h02, h12, h22] at hdet
  rw [of_mem_specialOrthogonalGroup_fin_two_iff]
  refine ⟨?_, ?_, by linear_combination e00⟩
  · linear_combination (-(g : Matrix (Fin 3) (Fin 3) R) 0 0) * e11 +
      (g : Matrix (Fin 3) (Fin 3) R) 1 0 * e01 + (g : Matrix (Fin 3) (Fin 3) R) 1 1 * hdet
  · linear_combination (-(g : Matrix (Fin 3) (Fin 3) R) 0 1) * e11 +
      (g : Matrix (Fin 3) (Fin 3) R) 1 1 * e01 - (g : Matrix (Fin 3) (Fin 3) R) 1 0 * hdet

/-- **`SO(2, R)` is the stabilizer of the last standard basis vector `e₂` in `SO(3, R)`**, over any
commutative ring: a rotation `A` of `R²` corresponds to the block matrix `diag(A, 1)`. -/
def equivLastStabilizer :
    specialOrthogonalGroup (Fin 2) R ≃* stabilizer (specialOrthogonalGroup (Fin 3) R)
      (Pi.single 2 1 : Fin 3 → R) where
  toFun A := ⟨⟨_, blockDiag_mem A⟩, mem_stabilizer_single_two_iff.mpr <| by simp⟩
  invFun g := ⟨_, block_mem g.2⟩
  left_inv A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  right_inv g := by
    obtain ⟨h02, h12, h22, h20, h21⟩ := mem_stabilizer_single_two_iff.mp g.2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h02, h12, h22, h20, h21]
  map_mul' A B := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The rotation attached to `A ∈ SO(2, R)` is the block matrix `diag(A, 1)`. -/
@[simp]
theorem coe_equivLastStabilizer_apply (A : specialOrthogonalGroup (Fin 2) R) :
    ((equivLastStabilizer A : specialOrthogonalGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      !![(A : Matrix (Fin 2) (Fin 2) R) 0 0, (A : Matrix (Fin 2) (Fin 2) R) 0 1, 0;
        (A : Matrix (Fin 2) (Fin 2) R) 1 0, (A : Matrix (Fin 2) (Fin 2) R) 1 1, 0; 0, 0, 1] :=
  (rfl)

/-- The rotation of `R²` attached to a rotation of `R³` fixing `e₂` is its upper left `2 × 2`
block. -/
@[simp]
theorem coe_equivLastStabilizer_symm_apply
    (g : stabilizer (specialOrthogonalGroup (Fin 3) R) (Pi.single 2 1 : Fin 3 → R)) :
    (equivLastStabilizer.symm g : Matrix (Fin 2) (Fin 2) R) =
      !![((g : specialOrthogonalGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 0 0,
        ((g : specialOrthogonalGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 0 1;
        ((g : specialOrthogonalGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 1 0,
        ((g : specialOrthogonalGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) 1 1] :=
  (rfl)

/-! ### The stabilizer of a unit vector -/

section Frame

variable {p u : Fin 3 → R}

/-- **`SO(2, R)` is the stabilizer of a unit vector `p` in `SO(3, R)`**, given a unit vector `u`
orthogonal to `p`: a rotation `A` of the plane corresponds to the rotation acting by `A` in the
oriented orthonormal basis `(u, p ⨯₃ u)` of the plane orthogonal to `p`. -/
noncomputable def equivStabilizer (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1) (hpu : p ⬝ᵥ u = 0) :
    specialOrthogonalGroup (Fin 2) R ≃* stabilizer (specialOrthogonalGroup (Fin 3) R) p :=
  equivLastStabilizer.trans <| stabilizerEquivStabilizer (g := ⟨_, ofFrame_cross_mem hp hu hpu⟩) <|
    by rw [Submonoid.smul_def, smul_eq_mulVec, ofFrame_cross_mulVec_single_two hu hpu]

/-- The rotation attached to `A ∈ SO(2, R)` is `F * diag(A, 1) * Fᵀ`, where `F` is the frame
matrix with columns `u`, `p ⨯₃ u` and `p`. -/
@[simp]
theorem coe_equivStabilizer_apply (hp : p ⬝ᵥ p = 1) (hu : u ⬝ᵥ u = 1) (hpu : p ⬝ᵥ u = 0)
    (A : specialOrthogonalGroup (Fin 2) R) :
    ((equivStabilizer hp hu hpu A : specialOrthogonalGroup (Fin 3) R) :
      Matrix (Fin 3) (Fin 3) R) =
      ofFrame u (p ⨯₃ u) *
        ((equivLastStabilizer A : specialOrthogonalGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) *
        (ofFrame u (p ⨯₃ u))ᵀ := by
  simp [equivStabilizer, stabilizerEquivStabilizer_apply, Matrix.SpecialOrthogonalGroup.coe_inv]

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
  simp only [equivStabilizer, MulEquiv.symm_trans_apply, coe_equivLastStabilizer_symm_apply,
    stabilizerEquivStabilizer_symm_apply, MulAut.conj_apply, Submonoid.coe_mul,
    Matrix.SpecialOrthogonalGroup.coe_inv, inv_inv]
  ext i j
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
  have hφ : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R (FractionRing R)]
    exact (algebraMap (FractionRing R) L).injective.comp (IsFractionRing.injective R _)
  set φ := algebraMap R L
  have : NeZero (2 : L) := ⟨by
    rw [← map_ofNat φ 2, ← map_zero φ]
    exact hφ.ne two_ne_zero⟩
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
      have := MulAction.mem_stabilizer_iff.mp g.2
      rwa [Subgroup.smul_def, Submonoid.smul_def, smul_eq_mulVec] at this
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
