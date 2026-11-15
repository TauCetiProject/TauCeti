/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.KoszulTwist.Algebra
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Parity.Grading
import Mathlib.GroupTheory.GroupAction.Ring
import TauCeti.Algebra.CharP.Invertible
import TauCeti.Data.ZMod.IntUnitsPower

/-!
# Supercommutativity and grade involution of `ParitySignedSym`

Homogeneous elements of `TauCeti.ParitySignedSym G`, not just its generators, obey the parity
Koszul commutation rule `a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a)` for `a` of parity `i` and `b`
of parity `j`. Even elements lie in the center of `TauCeti.ParitySignedSym G`, while odd
homogeneous elements anticommute, square to their own negatives over any commutative ring, and
square to zero whenever `2` is invertible in `R`.

This file also constructs the grade involution `TauCeti.ParitySignedSym.gradeInvolution G`, the
involutive algebra automorphism scaling parity-`i` elements by `(-1 : ℤˣ) ^ i` (fixing the even
piece and negating the odd piece). When `G` comes from an integer grading, `SignedSym.parityEquiv`
intertwines `InternalGrading.koszulTwistAlgEquiv (signedSymPiece G) 1` with
`ParitySignedSym.gradeInvolution G.parity`.

## Main definitions

* `TauCeti.ParitySignedSym.gradeInvolution`: the involutive algebra automorphism scaling
  `paritySignedSymPiece G i` by `(-1 : ℤˣ) ^ i`.

## Main results

* `TauCeti.ParitySignedSym.mul_eq_uzpow_smul_mul`: parity supercommutativity for arbitrary
  homogeneous elements.
* `TauCeti.ParitySignedSym.commute_of_mem_zero`,
  `TauCeti.ParitySignedSym.mul_comm_of_mem_zero_left`, and
  `TauCeti.ParitySignedSym.mem_center_of_mem_zero`: even elements are central.
* `TauCeti.ParitySignedSym.mul_anticomm_of_mem_one`, `TauCeti.ParitySignedSym.sq_eq_neg`, and
  `TauCeti.ParitySignedSym.sq_eq_zero`: anticommutativity and nilpotence of odd elements.
* `TauCeti.ParitySignedSym.gradeInvolution_apply_of_mem`: the grade involution acts by
  `(-1 : ℤˣ) ^ i` on parity `i`.
* `TauCeti.SignedSym.parityEquiv_koszulTwistAlgEquiv_one`: `parityEquiv` intertwines the integer
  degree-one Koszul twist with `gradeInvolution`.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1) and Definition 2.48.
-/

public section

namespace TauCeti

universe u v

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

namespace ParitySignedSym

variable (G : InternalGrading R V (ZMod 2))

/-! ### Supercommutativity -/

/-- Homogeneous elements of `ParitySignedSym G` supercommute with the sign determined by their
parities, over any commutative ring. -/
theorem mul_eq_uzpow_smul_mul {i j : ZMod 2} {a b : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G i) (hb : b ∈ paritySignedSymPiece G j) :
    a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a) := by
  -- Share the product step between the algebra and its opposite.
  have hmul {A : Type (max u v)} [Ring A] {x b c : A} {s t : ℤˣ}
      (hb : x * b = s • (b * x)) (hc : x * c = t • (c * x)) :
      x * (b * c) = (s * t) • ((b * c) * x) := by
    calc
      x * (b * c) = (x * b) * c := (mul_assoc _ _ _).symm
      _ = s • (b * (x * c)) := by
        rw [hb, Units.smul_def, smul_mul_assoc, mul_assoc, ← Units.smul_def]
      _ = (s * t) • ((b * c) * x) := by
        rw [hc]
        simp only [Units.smul_def, Units.val_mul, mul_smul_comm, smul_smul, mul_assoc]
  -- First commute a homogeneous generator past a homogeneous expression, then induct on `a`.
  have hgen : ∀ (i : ZMod 2) (x : V), x ∈ G.piece i →
      ∀ (j : ZMod 2) (b : ParitySignedSym G), b ∈ paritySignedSymPiece G j →
        generator G x * b = ((-1 : ℤˣ) ^ (i * j)) • (b * generator G x) := by
    intro i x hx j b hb
    refine homogeneous_induction G (P := fun j b ↦
      generator G x * b = ((-1 : ℤˣ) ^ (i * j)) • (b * generator G x))
      (by simp) (fun j y hy ↦ generator_mul_generator G hx hy)
      (fun j k b c hb hc ↦ by simpa only [mul_add, uzpow_add] using hmul hb hc)
      (by simp [Units.smul_def])
      (fun j b c hb hc ↦ by
        simp only [mul_add, add_mul, Units.smul_def, zsmul_add, hb, hc])
      (fun j r b hb ↦ by
        rw [mul_smul_comm, hb, Units.smul_def, smul_mul_assoc, smul_comm r, ← Units.smul_def]) hb
  refine homogeneous_induction G (P := fun i a ↦
    a * b = ((-1 : ℤˣ) ^ (i * j)) • (b * a))
    (by simp) (fun i x hx ↦ hgen i x hx j b hb)
    (fun i k a c ha hc ↦ ?_) (by simp [Units.smul_def])
    (fun i a c ha hc ↦ by
      simp only [add_mul, mul_add, Units.smul_def, zsmul_add, ha, hc])
    (fun i r a ha ↦ by
      rw [smul_mul_assoc, ha, Units.smul_def, mul_smul_comm, smul_comm r, ← Units.smul_def]) ha
  simpa only [MulOpposite.unop_mul, MulOpposite.unop_smul, MulOpposite.unop_op,
    add_mul, uzpow_add, mul_comm ((-1 : ℤˣ) ^ (k * j))] using
    congrArg MulOpposite.unop
      (hmul (x := MulOpposite.op b) (b := MulOpposite.op c) (c := MulOpposite.op a)
        (s := (-1 : ℤˣ) ^ (k * j)) (t := (-1 : ℤˣ) ^ (i * j))
        (by simpa only [MulOpposite.op_mul, MulOpposite.op_smul] using
          congrArg MulOpposite.op hc)
        (by simpa only [MulOpposite.op_mul, MulOpposite.op_smul] using
          congrArg MulOpposite.op ha))

/-- Every even element commutes with all of `ParitySignedSym G`. -/
theorem commute_of_mem_zero {a : ParitySignedSym G} (ha : a ∈ paritySignedSymPiece G 0)
    (b : ParitySignedSym G) : Commute a b :=
  TauCeti.commute_of_mul_eq_uzpow_smul_mul_of_mem_zero (mul_eq_uzpow_smul_mul G) ha b

/-- An even element commutes on the left with every element of `ParitySignedSym G`. -/
theorem mul_comm_of_mem_zero_left {a : ParitySignedSym G} (ha : a ∈ paritySignedSymPiece G 0)
    (b : ParitySignedSym G) : a * b = b * a :=
  (commute_of_mem_zero G ha b).eq

/-- An even element commutes on the right with every element of `ParitySignedSym G`. -/
theorem mul_comm_of_mem_zero_right {b : ParitySignedSym G} (hb : b ∈ paritySignedSymPiece G 0)
    (a : ParitySignedSym G) : a * b = b * a :=
  (mul_comm_of_mem_zero_left G hb a).symm

/-- Every even element lies in the center of `ParitySignedSym G`. -/
theorem mem_center_of_mem_zero {a : ParitySignedSym G} (ha : a ∈ paritySignedSymPiece G 0) :
    a ∈ Subalgebra.center R (ParitySignedSym G) :=
  Subalgebra.mem_center_iff.2 fun b ↦ mul_comm_of_mem_zero_right G ha b

/-- Odd homogeneous elements anticommute in `ParitySignedSym G`. -/
theorem mul_anticomm_of_mem_one {a b : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G 1) (hb : b ∈ paritySignedSymPiece G 1) :
    a * b = -(b * a) := by
  simpa using mul_eq_uzpow_smul_mul G ha hb

/-- Every odd homogeneous element squares to its own negative, over any commutative ring. -/
theorem sq_eq_neg {a : ParitySignedSym G} (ha : a ∈ paritySignedSymPiece G 1) :
    a ^ 2 = -(a ^ 2) := by
  simpa only [pow_two] using mul_anticomm_of_mem_one G ha ha

/-- Every odd homogeneous element has square zero when `2` is invertible in `R`. -/
theorem sq_eq_zero [Invertible (2 : R)] {a : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G 1) : a ^ 2 = 0 :=
  eq_zero_of_eq_neg_of_invertible_two (R := R) (sq_eq_neg G ha)

/-! ### The grade involution -/

/-- Auxiliary linear involution of `V` scaling each parity-`i` piece by `(-1 : ℤˣ) ^ i`. -/
private noncomputable def generatorParityTwist : V →ₗ[R] V :=
  (DirectSum.toModule R (ZMod 2) V fun i ↦ ((-1 : ℤˣ) ^ i) • (G.piece i).subtype) ∘ₗ
    (DirectSum.decomposeLinearEquiv G.piece).toLinearMap

private theorem generatorParityTwist_of_mem {i : ZMod 2} {x : V} (hx : x ∈ G.piece i) :
    generatorParityTwist G x = ((-1 : ℤˣ) ^ i) • x := by
  simp only [generatorParityTwist, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_of_mem G.piece hx,
    ← DirectSum.lof_eq_of R, DirectSum.toModule_lof, LinearMap.smul_apply,
    Submodule.coe_subtype]

private theorem generatorParityTwist_involutive :
    Function.Involutive (generatorParityTwist G) := by
  have hsq : generatorParityTwist G ∘ₗ generatorParityTwist G = LinearMap.id :=
    G.linearMap_ext fun i x hx ↦ by
      have hx' : ((-1 : ℤˣ) ^ i) • x ∈ G.piece i := by
        rw [Units.smul_def]; exact zsmul_mem hx _
      rw [LinearMap.comp_apply, generatorParityTwist_of_mem G hx,
        generatorParityTwist_of_mem G hx', smul_smul, Int.units_mul_self, one_smul,
        LinearMap.id_apply]
  exact fun x ↦ LinearMap.congr_fun hsq x

private noncomputable def generatorParityTwistEquiv : V ≃ₗ[R] V :=
  LinearEquiv.ofInvolutive (generatorParityTwist G) (generatorParityTwist_involutive G)

private theorem isHomogeneous_generatorParityTwist :
    LinearMap.IsHomogeneous (generatorParityTwistEquiv G).toLinearMap G.piece G.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun i x hx ↦ by
    simp only [generatorParityTwistEquiv, LinearEquiv.coe_coe, LinearEquiv.coe_ofInvolutive,
      add_zero, generatorParityTwist_of_mem G hx]
    rw [Units.smul_def]
    exact zsmul_mem hx _

/-- The grade involution of `ParitySignedSym G`: the involutive algebra automorphism scaling
elements of parity `i` by `(-1 : ℤˣ) ^ i` (`gradeInvolution_apply_of_mem`), fixing the even piece
and negating the odd piece. -/
noncomputable def gradeInvolution : ParitySignedSym G ≃ₐ[R] ParitySignedSym G :=
  congr G G (generatorParityTwistEquiv G) (isHomogeneous_generatorParityTwist G)

/-- On a generator of parity `i`, `gradeInvolution` acts by `(-1 : ℤˣ) ^ i`. -/
theorem gradeInvolution_generator_of_mem {i : ZMod 2} {x : V} (hx : x ∈ G.piece i) :
    gradeInvolution G (generator G x) = ((-1 : ℤˣ) ^ i) • generator G x := by
  rw [gradeInvolution, congr_generator]
  simp only [generatorParityTwistEquiv, LinearEquiv.coe_ofInvolutive,
    generatorParityTwist_of_mem G hx, Units.smul_def, map_zsmul]

/-- On an element of parity `i`, `gradeInvolution` multiplies by `(-1 : ℤˣ) ^ i`. -/
theorem gradeInvolution_apply_of_mem {i : ZMod 2} {a : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G i) :
    gradeInvolution G a = ((-1 : ℤˣ) ^ i) • a := by
  refine homogeneous_induction G
    (P := fun i a ↦ gradeInvolution G a = ((-1 : ℤˣ) ^ i) • a)
    (by simp) (fun i x hx ↦ gradeInvolution_generator_of_mem G hx)
    (fun i j a b ha hb ↦ by
      rw [map_mul, ha, hb, uzpow_add, mul_comm ((-1 : ℤˣ) ^ i)]
      simp only [Units.smul_def, Units.val_mul, smul_mul_assoc, mul_smul_comm, smul_smul])
    (fun i ↦ by simp [Units.smul_def])
    (fun i a b ha hb ↦ by simp only [map_add, ha, hb, Units.smul_def, zsmul_add])
    (fun i r a ha ↦ by rw [map_smul, ha, Units.smul_def, smul_comm r, ← Units.smul_def]) ha

/-- `gradeInvolution` fixes every even element. -/
theorem gradeInvolution_apply_of_mem_zero {a : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G 0) : gradeInvolution G a = a := by
  simpa using gradeInvolution_apply_of_mem G ha

/-- `gradeInvolution` negates every odd element. -/
theorem gradeInvolution_apply_of_mem_one {a : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G 1) : gradeInvolution G a = -a := by
  simpa using gradeInvolution_apply_of_mem G ha

/-- `gradeInvolution` is an involution. -/
@[simp]
theorem gradeInvolution_gradeInvolution (a : ParitySignedSym G) :
    gradeInvolution G (gradeInvolution G a) = a := by
  induction a using DirectSum.Decomposition.inductionOn (paritySignedSymPiece G) with
  | zero => simp
  | homogeneous a =>
    rw [gradeInvolution_apply_of_mem G a.2, Units.smul_def, map_zsmul,
      gradeInvolution_apply_of_mem G a.2, Units.smul_def, smul_smul, ← Units.val_mul,
      Int.units_mul_self, Units.val_one, one_smul]
  | add a b ha hb => simp [ha, hb]

/-- `gradeInvolution` is its own inverse. -/
@[simp]
theorem gradeInvolution_symm : (gradeInvolution G).symm = gradeInvolution G := by
  ext a
  exact (gradeInvolution G).symm_apply_eq.2 (gradeInvolution_gradeInvolution G a).symm

/-- `gradeInvolution` preserves the parity pieces. -/
theorem isHomogeneous_gradeInvolution :
    LinearMap.IsHomogeneous (gradeInvolution G).toLinearMap
      (paritySignedSymPiece G) (paritySignedSymPiece G) 0 :=
  LinearMap.isHomogeneous_def.2 fun i a ha ↦ by
    rw [add_zero, AlgEquiv.toLinearMap_apply, gradeInvolution_apply_of_mem G ha, Units.smul_def]
    exact zsmul_mem ha _

/-- `gradeInvolution` detects membership in each parity piece. -/
@[simp]
theorem gradeInvolution_mem_paritySignedSymPiece_iff {i : ZMod 2} {a : ParitySignedSym G} :
    gradeInvolution G a ∈ paritySignedSymPiece G i ↔ a ∈ paritySignedSymPiece G i := by
  refine ⟨fun h ↦ ?_, fun h ↦ by
    simpa only [add_zero, AlgEquiv.toLinearMap_apply] using
      (isHomogeneous_gradeInvolution G).map_mem h⟩
  simpa only [gradeInvolution_gradeInvolution, add_zero, AlgEquiv.toLinearMap_apply] using
    (isHomogeneous_gradeInvolution G).map_mem h

/-- The parity-`i` projection after `gradeInvolution` is `(-1 : ℤˣ) ^ i` times the parity-`i`
projection. -/
@[simp]
theorem decompose_gradeInvolution (a : ParitySignedSym G) (i : ZMod 2) :
    (DirectSum.decompose (paritySignedSymPiece G) (gradeInvolution G a) i : ParitySignedSym G) =
      ((-1 : ℤˣ) ^ i) • (DirectSum.decompose (paritySignedSymPiece G) a i : ParitySignedSym G) := by
  have h := (isHomogeneous_gradeInvolution G).map_decompose i a
  rw [add_zero, AlgEquiv.toLinearMap_apply,
    gradeInvolution_apply_of_mem G (DirectSum.decompose (paritySignedSymPiece G) a i).2] at h
  exact h.symm

/-- On any element, `gradeInvolution` is the difference of its even and odd projections. -/
theorem gradeInvolution_eq_sub_decompose (a : ParitySignedSym G) :
    gradeInvolution G a =
      (DirectSum.decompose (paritySignedSymPiece G) a 0 : ParitySignedSym G) -
        (DirectSum.decompose (paritySignedSymPiece G) a 1 : ParitySignedSym G) := by
  induction a using DirectSum.Decomposition.inductionOn (paritySignedSymPiece G) with
  | zero => simp
  | @homogeneous i a =>
    rcases (by decide : ∀ j : ZMod 2, j = 0 ∨ j = 1) i with rfl | rfl
    · rw [gradeInvolution_apply_of_mem_zero G a.2,
        DirectSum.decompose_of_mem_same _ a.2,
        DirectSum.decompose_of_mem_ne _ a.2 (by decide), sub_zero]
    · rw [gradeInvolution_apply_of_mem_one G a.2,
        DirectSum.decompose_of_mem_ne _ a.2 (by decide),
        DirectSum.decompose_of_mem_same _ a.2, zero_sub]
  | add a b ha hb =>
    simp only [map_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, ha, hb]
    abel

end ParitySignedSym

namespace SignedSym

variable (G : InternalGrading R V ℤ)

/-- `SignedSym.parityEquiv` intertwines the degree-one Koszul twist equivalence of `SignedSym G`
with `ParitySignedSym.gradeInvolution G.parity`. -/
theorem parityEquiv_koszulTwistAlgEquiv_one (a : SignedSym G) :
    parityEquiv G (InternalGrading.koszulTwistAlgEquiv (signedSymPiece G) 1 a) =
      ParitySignedSym.gradeInvolution G.parity (parityEquiv G a) := by
  have hhom : (parityEquiv G).toAlgHom.comp
      (InternalGrading.koszulTwistAlgEquiv (signedSymPiece G) 1).toAlgHom =
      (ParitySignedSym.gradeInvolution G.parity).toAlgHom.comp (parityEquiv G).toAlgHom := by
    apply hom_ext
    have hlin : ((parityEquiv G).toAlgHom.comp
        (InternalGrading.koszulTwistAlgEquiv (signedSymPiece G) 1).toAlgHom).toLinearMap ∘ₗ
          generator G =
        ((ParitySignedSym.gradeInvolution G.parity).toAlgHom.comp
          (parityEquiv G).toAlgHom).toLinearMap ∘ₗ generator G :=
      G.linearMap_ext fun p x hx ↦ by
        have hxpar : x ∈ G.parity.piece p := by
          rw [InternalGrading.parity_piece]
          exact mem_parityGrading_of_mem hx
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
          AlgEquiv.coe_toAlgHom,
          InternalGrading.koszulTwistAlgEquiv_apply_of_mem (signedSymPiece G) 1
            (generator_mem_signedSymPiece G hx),
          one_mul, Units.smul_def, map_zsmul, parityEquiv_generator,
          ParitySignedSym.gradeInvolution_generator_of_mem G.parity hxpar,
          uzpow_intCast_eq_negOnePow]
    exact fun x ↦ LinearMap.congr_fun hlin x
  exact AlgHom.congr_fun hhom a

/-- `SignedSym.parityEquiv` intertwines the degree-one Koszul twist of `SignedSym G` with
`ParitySignedSym.gradeInvolution G.parity`. -/
@[simp]
theorem parityEquiv_koszulTwist_one (a : SignedSym G) :
    parityEquiv G ((InternalGrading.ofDecomposition (signedSymPiece G)).koszulTwist 1 a) =
      ParitySignedSym.gradeInvolution G.parity (parityEquiv G a) := by
  rw [← InternalGrading.koszulTwistAlgEquiv_apply, parityEquiv_koszulTwistAlgEquiv_one]

end SignedSym

end TauCeti
