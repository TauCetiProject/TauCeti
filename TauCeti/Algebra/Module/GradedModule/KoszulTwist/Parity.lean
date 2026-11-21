/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DirectSum.Component
public import TauCeti.Algebra.Module.GradedModule.Coarsen
import TauCeti.Algebra.DirectSum.Internal

/-!
# The parity involution on `ZMod 2`-graded modules and nonunital rings

On an internally `ZMod 2`-graded module, the parity involution
`TauCeti.InternalGrading.parityTwist` fixes the even piece and negates the odd piece. This is the
`ZMod 2`-graded counterpart of `TauCeti.InternalGrading.koszulTwist G 1`, and agrees with it on the
parity reduction of any integer grading (`TauCeti.InternalGrading.parityTwist_parity`). For unital
internally `ZMod 2`-graded algebras, `TauCeti.gradeInvolution` in
`TauCeti.RingTheory.GradedAlgebra.GradeInvolution` supplies the corresponding involutive algebra
automorphism.

## Main definitions

* `TauCeti.InternalGrading.parityTwist`: the parity involution fixing the even piece and negating
  the odd piece of a `ZMod 2`-graded module.

## Main results

* `TauCeti.InternalGrading.parityTwist_apply_of_mem`,
  `TauCeti.InternalGrading.isHomogeneous_parityTwist`,
  `TauCeti.InternalGrading.parityTwist_comp_self`, and
  `TauCeti.InternalGrading.parityTwist_ofDecomposition_mul`: action on homogeneous elements,
  degree preservation, involutivity, and multiplicativity of the parity involution.
* `TauCeti.InternalGrading.parityTwist_parity`: compatibility with `InternalGrading.koszulTwist 1`
  under parity reduction.
-/

public section

namespace TauCeti.InternalGrading

section ParityTwist

variable {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M]

/-- The parity involution on an internally `ZMod 2`-graded module, fixing the even piece and
negating the odd piece (`parityTwist_apply_of_mem`). This is the `ZMod 2`-graded counterpart of
`InternalGrading.koszulTwist G 1`. -/
noncomputable def parityTwist (G : InternalGrading R M (ZMod 2)) : M →ₗ[R] M :=
  homogeneousComponent G.piece 0 - homogeneousComponent G.piece 1

/-- `parityTwist` is the difference of the even and odd homogeneous projections. -/
theorem parityTwist_apply (G : InternalGrading R M (ZMod 2)) (x : M) :
    G.parityTwist x = homogeneousComponent G.piece 0 x - homogeneousComponent G.piece 1 x :=
  (rfl)

/-- On an element of parity `i`, `parityTwist` acts as multiplication by `(-1) ^ i`. -/
theorem parityTwist_apply_of_mem (G : InternalGrading R M (ZMod 2)) {i : ZMod 2} {x : M}
    (hx : x ∈ G.piece i) : G.parityTwist x = ((-1 : ℤˣ) ^ i) • x := by
  rw [parityTwist_apply]
  match i with
  | 0 =>
    rw [homogeneousComponent_apply_of_mem G.piece hx,
      homogeneousComponent_apply_of_mem_ne G.piece hx (by decide : (0 : ZMod 2) ≠ 1)]
    simp
  | 1 =>
    rw [homogeneousComponent_apply_of_mem_ne G.piece hx (by decide : (1 : ZMod 2) ≠ 0),
      homogeneousComponent_apply_of_mem G.piece hx]
    simp

/-- The parity involution preserves both parity pieces. -/
theorem parityTwist_mem_piece (G : InternalGrading R M (ZMod 2)) {i : ZMod 2} {x : M}
    (hx : x ∈ G.piece i) : G.parityTwist x ∈ G.piece i := by
  rw [G.parityTwist_apply_of_mem hx, Units.smul_def]
  exact DirectSum.Decomposition.zsmul_mem hx _

/-- The parity involution is homogeneous of parity `0`. -/
theorem isHomogeneous_parityTwist (G : InternalGrading R M (ZMod 2)) :
    LinearMap.IsHomogeneous G.parityTwist G.piece G.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    simpa only [add_zero] using G.parityTwist_mem_piece hx

/-- The parity involution squares to the identity. -/
@[simp]
theorem parityTwist_comp_self (G : InternalGrading R M (ZMod 2)) :
    G.parityTwist ∘ₗ G.parityTwist = LinearMap.id := by
  refine G.linearMap_ext fun i x hx ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [G.parityTwist_apply_of_mem (G.parityTwist_mem_piece hx), G.parityTwist_apply_of_mem hx,
    smul_smul, ← uzpow_add, CharTwo.add_self_eq_zero, uzpow_zero, one_smul]

/-- The parity involution is involutive pointwise. -/
@[simp]
theorem parityTwist_parityTwist (G : InternalGrading R M (ZMod 2)) (x : M) :
    G.parityTwist (G.parityTwist x) = x :=
  LinearMap.congr_fun G.parityTwist_comp_self x

/-- On an element of parity `i` of a decomposition `ℳ`, `parityTwist` acts as `(-1) ^ i`. -/
theorem parityTwist_ofDecomposition_apply_of_mem (ℳ : ZMod 2 → Submodule R M)
    [DirectSum.Decomposition ℳ] {i : ZMod 2} {x : M} (hx : x ∈ ℳ i) :
    (ofDecomposition ℳ).parityTwist x = ((-1 : ℤˣ) ^ i) • x :=
  parityTwist_apply_of_mem _ (by rwa [ofDecomposition_piece])

/-- **The parity involution of a `ZMod 2`-graded ring is multiplicative.** -/
theorem parityTwist_ofDecomposition_mul {A : Type*} [NonUnitalNonAssocRing A] [Module R A]
    {𝒜 : ZMod 2 → Submodule R A} [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜] (a b : A) :
    (ofDecomposition 𝒜).parityTwist (a * b) =
      (ofDecomposition 𝒜).parityTwist a * (ofDecomposition 𝒜).parityTwist b := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a a' ha ha' => rw [add_mul, map_add, ha, ha', map_add, add_mul]
  | @homogeneous i a =>
    obtain ⟨a, hai⟩ := a
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add b b' hb hb' => rw [mul_add, map_add, hb, hb', map_add, mul_add]
    | @homogeneous j b =>
      obtain ⟨b, hbj⟩ := b
      rw [parityTwist_ofDecomposition_apply_of_mem 𝒜 (SetLike.GradedMul.mul_mem hai hbj),
        parityTwist_ofDecomposition_apply_of_mem 𝒜 hai,
        parityTwist_ofDecomposition_apply_of_mem 𝒜 hbj]
      match i, j with
      | 0, 0 => simp
      | 0, 1 => simp
      | 1, 0 => simp
      | 1, 1 => simp [(by decide : (1 : ZMod 2) + 1 = 0)]

/-- The parity involution fixes `1` whenever `1` lies in the even piece. -/
@[simp]
theorem parityTwist_ofDecomposition_one {A : Type*} [AddCommGroup A] [One A] [Module R A]
    {𝒜 : ZMod 2 → Submodule R A} [SetLike.GradedOne 𝒜] [DirectSum.Decomposition 𝒜] :
    (ofDecomposition 𝒜).parityTwist 1 = 1 := by
  simpa using parityTwist_ofDecomposition_apply_of_mem 𝒜 (SetLike.GradedOne.one_mem (A := 𝒜))

/-- On the parity reduction of an integer grading, `parityTwist` agrees with `koszulTwist` at
parameter `1`. -/
theorem parityTwist_parity {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (G : InternalGrading R M ℤ) : G.parity.parityTwist = G.koszulTwist 1 := by
  refine G.linearMap_ext fun p x hx ↦ ?_
  have hxp : x ∈ G.parity.piece (p : ZMod 2) := by
    simpa only [parity_piece] using mem_parityGrading_of_mem hx
  rw [G.parity.parityTwist_apply_of_mem hxp, G.koszulTwist_one_apply_of_mem hx,
    uzpow_intCast, ← Int.negOnePow_def, Units.smul_def, Int.cast_smul_eq_zsmul]

end ParityTwist

end TauCeti.InternalGrading
