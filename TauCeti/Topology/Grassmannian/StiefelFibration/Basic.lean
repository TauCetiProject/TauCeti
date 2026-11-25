/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.StiefelFibration.SpecialUnitary

/-!
# The Stiefel fibration `SO(m) → SO(r + m) → V_r(ℝ^(r + m))`

Applying a special orthogonal matrix to the standard frame `(e₀, …, e_{r-1})` gives the map
`SO(r + m) → V_r(ℝ^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`, to the orthonormal `r`-frames
(`TauCeti.specialOrthogonalFrameMap`): it reads off the first `r` columns of `A`. Its fibre over
the standard frame is the block subgroup `diag(1_r, SO(m))`, the image of
`Matrix.SpecialOrthogonalGroup.fromBlocksOne ℝ r m`, and its fibres are the left cosets of that
subgroup. For `m ≥ 1` the map is surjective and a locally trivial bundle with fibre `SO(m)`, and
hence a Serre fibration. For `r = 2` this is the bundle `SO(n) → SO(n + 2) → V₂(ℝ^(n + 2))` whose
homotopy sequence compares `π_(n-1)(SO(n))` with the stable groups.

Since `Matrix.specialOrthogonalGroup` is `Matrix.specialUnitaryGroup` for the trivial star of `ℝ`,
this is the special unitary Stiefel fibration `TauCeti.specialUnitaryFrameMap` over `ℝ`
(`TauCeti.Topology.Grassmannian.StiefelFibration.SpecialUnitary`), and every statement here is
its specialization. Its charts come from the Gram–Schmidt local sections of the unitary Stiefel
fibration (`TauCeti.exists_unitaryFrameMap_localSection`), corrected to determinant `1` in a
column outside the first `r`.

The case `r = 1`, where frames are unit vectors, is
`TauCeti.Topology.Grassmannian.SphereBundle.Basic`, with charts from explicit rotations.

## Main definitions

* `TauCeti.specialOrthogonalFrameMap`: the map `SO(r + m) → V_r(ℝ^(r + m))`,
  `A ↦ (A e₀, …, A e_{r-1})`.
* `TauCeti.specialOrthogonalFrameFiberHomeomorph`: `SO(m)` is homeomorphic to the fibre of this
  map over the standard frame, through `B ↦ diag(1_r, B)`.

## Main results

* `TauCeti.specialOrthogonalFrameMap_eq_specialOrthogonalFrameMap_iff`: the fibres are the left
  cosets of the stabilizer of the standard frame.
* `TauCeti.specialOrthogonalFrameMap_eq_specialOrthogonalFrameMap_one_iff`: the fibre over the
  standard frame is the image of `SO(m)`.
* `TauCeti.exists_trivialization_specialOrthogonalFrameMap`: a chart with fibre `SO(m)` around each
  frame.
* `TauCeti.specialOrthogonalFrameMap_mem_serreFibrations`: `SO(r + m) → V_r(ℝ^(r + m))` is a Serre
  fibration.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2 (Stiefel manifolds and
  the fibrations `SO(n - k) → SO(n) → V_k(ℝⁿ)`).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Lemma 6.35, which compares
  `π_(n-1)(SO(n))` with the stable groups through `V₂(ℝ^(n + 2))`.
-/

public section

open Matrix Set Topology

noncomputable section

namespace TauCeti

open finiteOrthonormalFrame

variable {r m : ℕ}

/-! ### The frame map `SO(r + m) → V_r(ℝ^(r + m))` -/

variable (r m) in
/-- The Stiefel map `SO(r + m) → V_r(ℝ^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`, sending a special
orthogonal matrix to its first `r` columns: the special unitary frame map over `ℝ`. -/
def specialOrthogonalFrameMap (A : specialOrthogonalGroup (Fin (r + m)) ℝ) :
    finiteOrthonormalFrame ℝ r (r + m) :=
  specialUnitaryFrameMap r m A

/-- In coordinates, the `i`-th vector of `specialOrthogonalFrameMap r m A` is the column
`A e_i` of `A`. -/
@[simp]
theorem coe_specialOrthogonalFrameMap (A : specialOrthogonalGroup (Fin (r + m)) ℝ) :
    (specialOrthogonalFrameMap r m A : Fin r → Fin (r + m) → ℝ) =
      fun i ↦ (A : Matrix (Fin (r + m)) (Fin (r + m)) ℝ) *ᵥ Pi.single (Fin.castAdd m i) 1 :=
  coe_specialUnitaryFrameMap A

variable (r m) in
/-- The frame map `SO(r + m) → V_r(ℝ^(r + m))` is continuous. -/
theorem continuous_specialOrthogonalFrameMap : Continuous (specialOrthogonalFrameMap r m) :=
  continuous_specialUnitaryFrameMap ℝ r m

/-- The frame map is equivariant: `(A B) • e = A • (B • e)`. -/
theorem specialOrthogonalFrameMap_mul (A B : specialOrthogonalGroup (Fin (r + m)) ℝ) :
    specialOrthogonalFrameMap r m (A * B) =
      unitaryMap ⟨A.val, A.property.1⟩ (specialOrthogonalFrameMap r m B) :=
  specialUnitaryFrameMap_mul A B

/-- The frame map of the identity is the standard frame. -/
@[simp]
theorem specialOrthogonalFrameMap_one :
    specialOrthogonalFrameMap r m 1 = standard ℝ (Nat.le_add_right r m) :=
  specialUnitaryFrameMap_one

/-- The frame map is the orbit map `A ↦ A • e` of the standard frame `e` under
`specialOrthogonalMulAction`. -/
theorem specialOrthogonalFrameMap_eq_smul_standard (A : specialOrthogonalGroup (Fin (r + m)) ℝ) :
    letI := specialOrthogonalMulAction r (r + m)
    specialOrthogonalFrameMap r m A = A • standard ℝ (Nat.le_add_right r m) :=
  specialUnitaryFrameMap_eq_smul_standard A

/-- The fibres of the frame map are the left cosets of the stabilizer of the standard frame. -/
theorem specialOrthogonalFrameMap_eq_specialOrthogonalFrameMap_iff
    {A B : specialOrthogonalGroup (Fin (r + m)) ℝ} :
    specialOrthogonalFrameMap r m A = specialOrthogonalFrameMap r m B ↔
      A⁻¹ * B ∈ specialOrthogonalStabilizer (Nat.le_add_right r m) := by
  rw [specialOrthogonalStabilizer_eq_specialUnitaryStabilizer]
  exact specialUnitaryFrameMap_eq_specialUnitaryFrameMap_iff

/-- The fibre of the frame map over the standard frame is the block subgroup `diag(1_r, SO(m))`. -/
theorem specialOrthogonalFrameMap_eq_specialOrthogonalFrameMap_one_iff
    {A : specialOrthogonalGroup (Fin (r + m)) ℝ} :
    specialOrthogonalFrameMap r m A = specialOrthogonalFrameMap r m 1 ↔
      A ∈ (SpecialOrthogonalGroup.fromBlocksOne ℝ r m).range := by
  rw [SpecialOrthogonalGroup.fromBlocksOne_eq_specialUnitaryGroup_fromBlocksOne]
  exact specialUnitaryFrameMap_eq_specialUnitaryFrameMap_one_iff

/-- For `m ≥ 1`, every orthonormal `r`-frame of `ℝ^(r + m)` consists of the first `r` columns of a
special orthogonal matrix. -/
theorem surjective_specialOrthogonalFrameMap [NeZero m] :
    Function.Surjective (specialOrthogonalFrameMap r m) :=
  surjective_specialUnitaryFrameMap

/-! ### The fibre over the standard frame -/

variable (r m) in
/-- The fibre of the frame map over the standard frame is `SO(m)`: the block embedding
`B ↦ diag(1_r, B)` is a homeomorphism of `SO(m)` onto the special orthogonal matrices fixing the
standard frame. -/
def specialOrthogonalFrameFiberHomeomorph :
    specialOrthogonalGroup (Fin m) ℝ ≃ₜ
      specialOrthogonalFrameMap r m ⁻¹' {specialOrthogonalFrameMap r m 1} :=
  specialUnitaryFrameFiberHomeomorph ℝ r m

@[simp]
theorem coe_specialOrthogonalFrameFiberHomeomorph_apply (B : specialOrthogonalGroup (Fin m) ℝ) :
    (specialOrthogonalFrameFiberHomeomorph r m B : specialOrthogonalGroup (Fin (r + m)) ℝ) =
      SpecialOrthogonalGroup.fromBlocksOne ℝ r m B := by
  rw [SpecialOrthogonalGroup.fromBlocksOne_eq_specialUnitaryGroup_fromBlocksOne]
  exact coe_specialUnitaryFrameFiberHomeomorph_apply B

/-- A special orthogonal matrix fixing the standard frame is the block matrix `diag(1_r, B)` of its
image `B` in `SO(m)`. -/
@[simp]
theorem fromBlocksOne_specialOrthogonalFrameFiberHomeomorph_symm_apply
    (A : specialOrthogonalFrameMap r m ⁻¹' {specialOrthogonalFrameMap r m 1}) :
    SpecialOrthogonalGroup.fromBlocksOne ℝ r m
        ((specialOrthogonalFrameFiberHomeomorph r m).symm A) = A := by
  rw [SpecialOrthogonalGroup.fromBlocksOne_eq_specialUnitaryGroup_fromBlocksOne]
  exact fromBlocksOne_specialUnitaryFrameFiberHomeomorph_symm_apply A

/-- The identity of `SO(m)` corresponds to the identity of `SO(r + m)` in the fibre. -/
@[simp]
theorem specialOrthogonalFrameFiberHomeomorph_one :
    specialOrthogonalFrameFiberHomeomorph r m 1 = ⟨1, rfl⟩ :=
  specialUnitaryFrameFiberHomeomorph_one

/-! ### Local triviality -/

/-- For `m ≥ 1`, the frame map `SO(r + m) → V_r(ℝ^(r + m))` has a chart with fibre `SO(m)` around
each orthonormal frame. -/
theorem exists_trivialization_specialOrthogonalFrameMap [NeZero m]
    (b : finiteOrthonormalFrame ℝ r (r + m)) :
    ∃ e : Bundle.Trivialization (specialOrthogonalGroup (Fin m) ℝ) (specialOrthogonalFrameMap r m),
      b ∈ e.baseSet :=
  exists_trivialization_specialUnitaryFrameMap b

/-- For `m ≥ 1`, the frame map `SO(r + m) → V_r(ℝ^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`, is a
Serre fibration: it is locally trivial with fibre `SO(m)`. -/
theorem specialOrthogonalFrameMap_mem_serreFibrations [NeZero m] :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom ⟨specialOrthogonalFrameMap r m,
          continuous_specialOrthogonalFrameMap r m⟩ :
        _root_.TopCat.of (specialOrthogonalGroup (Fin (r + m)) ℝ) ⟶
          _root_.TopCat.of (finiteOrthonormalFrame ℝ r (r + m))) :=
  specialUnitaryFrameMap_mem_serreFibrations

end TauCeti
