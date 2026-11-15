/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Derivation
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Parity.Supercommutativity
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.GroupAction.Ring
import TauCeti.Algebra.Homology.DG.Algebra.Parity

/-!
# Odd derivations of the parity-presented signed symmetric algebra

A linear assignment `δ : V → ParitySignedSym G` of parity `1 : ZMod 2` extends uniquely to a
linear endomorphism `d` of `TauCeti.ParitySignedSym G` satisfying the parity signed Leibniz rule

`d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b)` for `a` of parity `i`.

This extension `TauCeti.ParitySignedSym.liftDerivation` flips parity (`i ↦ i + 1`) without
requiring any integer lift of `G`. Its square is an unsigned derivation, so an odd signed Leibniz
endomorphism squares to zero if and only if its square vanishes on generators. When an integer
grading `H : InternalGrading R V ℤ` is present, `TauCeti.SignedSym.parityEquiv H` intertwines
`TauCeti.SignedSym.liftDerivation` with `TauCeti.ParitySignedSym.liftDerivation`.

The API and construction parallel `TauCeti.SignedSym.liftDerivation` in
`TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Derivation`.

## Main definitions

* `TauCeti.ParitySignedSym.liftDerivation`: the odd derivation extending a parity-`1` assignment on
  generators.

## Main results

* `TauCeti.ParitySignedSym.liftDerivation_mul` and
  `TauCeti.ParitySignedSym.isHomogeneous_liftDerivation`: the parity Leibniz rule and odd degree
  law.
* `TauCeti.ParitySignedSym.eq_liftDerivation` and
  `TauCeti.ParitySignedSym.existsUnique_odd_extension`: odd derivations are uniquely determined by
  generators.
* `TauCeti.ParitySignedSym.comp_self_eq_zero_iff` and
  `TauCeti.ParitySignedSym.liftDerivation_comp_self_eq_zero_iff`: square-zero reduces to
  generators.
* `TauCeti.SignedSym.parityEquiv_liftDerivation` and
  `TauCeti.SignedSym.isDGAlgebra_liftDerivation_iff_parity`: compatibility with integer-graded odd
  derivations under `SignedSym.parityEquiv`.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1) and Definition 2.48.
* Y. Eliashberg, A. Givental, and H. Hofer, *Introduction to symplectic field theory*, Section 1.9.
-/

public section

namespace TauCeti

universe u v

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

namespace ParitySignedSym

variable {G : InternalGrading R V (ZMod 2)}

/-- A linear endomorphism of `ParitySignedSym G` satisfying a Leibniz rule with an arbitrary sign
`s i` on left factors of parity `i`, and vanishing on generators, is zero. -/
private theorem eq_zero_of_leibniz (s : ZMod 2 → ℤˣ)
    {D : ParitySignedSym G →ₗ[R] ParitySignedSym G}
    (hD : ∀ {i : ZMod 2} {a : ParitySignedSym G}, a ∈ paritySignedSymPiece G i →
      ∀ b : ParitySignedSym G, D (a * b) = D a * b + s i • (a * D b))
    (hgen : ∀ x, D (generator G x) = 0) : D = 0 := by
  have hone : D 1 = 0 := by
    have h := hD (SetLike.GradedOne.one_mem (A := paritySignedSymPiece G)) 1
    simp only [mul_one, one_mul, left_eq_add] at h
    exact (smul_eq_zero_iff_eq (s 0)).1 h
  have hhom : ∀ {i : ZMod 2} {a : ParitySignedSym G},
      a ∈ paritySignedSymPiece G i → D a = 0 := by
    intro i a ha
    refine (homogeneous_induction G
      (P := fun i a => a ∈ paritySignedSymPiece G i ∧ D a = 0)
      ⟨SetLike.GradedOne.one_mem, hone⟩
      (fun i x hx => ⟨generator_mem_paritySignedSymPiece G hx, hgen x⟩)
      (fun i j a b ha hb => ⟨SetLike.mul_mem_graded ha.1 hb.1, by
        rw [hD ha.1, ha.2, hb.2, zero_mul, mul_zero, zero_add, Units.smul_def, zsmul_zero]⟩)
      (fun _ => ⟨zero_mem _, map_zero D⟩)
      (fun _ a b ha hb => ⟨add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2, add_zero]⟩)
      (fun _ r a ha => ⟨Submodule.smul_mem _ r ha.1, by rw [map_smul, ha.2, smul_zero]⟩)
      ha).2
  ext a
  induction a using DirectSum.Decomposition.inductionOn (paritySignedSymPiece G) with
  | zero => simp
  | homogeneous a => exact hhom a.2
  | add a b ha hb => simp_all

section Lift

private noncomputable def generatorTwist (G : InternalGrading R V (ZMod 2)) : V →ₗ[R] V :=
  let π (i : ZMod 2) : V →ₗ[R] V :=
    (G.piece i).subtype ∘ₗ DirectSum.component R (ZMod 2) (fun j => G.piece j) i ∘ₗ
      (DirectSum.decomposeLinearEquiv G.piece).toLinearMap
  π 0 - π 1

private theorem generatorTwist_of_mem {i : ZMod 2} {x : V} (hx : x ∈ G.piece i) :
    generatorTwist G x = ((-1 : ℤˣ) ^ i) • x := by
  change (DirectSum.decompose G.piece x 0 : V) - (DirectSum.decompose G.piece x 1 : V) = _
  match i with
  | 0 =>
    rw [DirectSum.decompose_of_mem_same _ hx,
      DirectSum.decompose_of_mem_ne _ hx (by decide : (0 : ZMod 2) ≠ 1)]
    simp
  | 1 =>
    rw [DirectSum.decompose_of_mem_ne _ hx (by decide : (1 : ZMod 2) ≠ 0),
      DirectSum.decompose_of_mem_same _ hx]
    simp

private theorem isHomogeneous_generatorTwist (G : InternalGrading R V (ZMod 2)) :
    LinearMap.IsHomogeneous (generatorTwist G) G.piece G.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun i x hx => by
    rw [add_zero, generatorTwist_of_mem hx, Units.smul_def]
    exact zsmul_mem hx _

/-- The parity involution `a ↦ (-1) ^ i • a` of `ParitySignedSym G` as an algebra endomorphism. -/
private noncomputable def twist : ParitySignedSym G →ₐ[R] ParitySignedSym G :=
  map G G (generatorTwist G) (isHomogeneous_generatorTwist G)

private theorem twist_of_mem {i : ZMod 2} {a : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G i) :
    twist (G := G) a = ((-1 : ℤˣ) ^ i) • a := by
  refine homogeneous_induction G (P := fun i a => twist a = ((-1 : ℤˣ) ^ i) • a)
    (by simp [twist])
    (fun j x hx => by
      simp only [twist, map_generator, generatorTwist_of_mem hx, Units.smul_def, map_zsmul])
    (fun j k b c hb hc => by
      simp only [map_mul, hb, hc, uzpow_add, Units.smul_def, mul_smul,
        smul_mul_assoc, mul_smul_comm]
      exact smul_comm _ _ _)
    (fun _ => by simp [Units.smul_def])
    (fun _ b c hb hc => by simp only [map_add, hb, hc, Units.smul_def, zsmul_add])
    (fun _ r b hb => by
      simp only [Units.smul_def] at hb ⊢
      rw [map_smul, hb, smul_comm r])
    ha

/-- The parity Koszul sign identity for the lower-left entry of a `2 × 2` triangular product:
for `a`, `b` of parities `i`, `j` and `a'`, `b'` of parities `i + 1`, `j + 1`,
`a' * b + σ a * b' = (-1) ^ (i * j) • (b' * a + σ b * a')`. -/
private theorem mul_add_twist_mul_comm {i j : ZMod 2} {a b a' b' : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G i) (hb : b ∈ paritySignedSymPiece G j)
    (ha' : a' ∈ paritySignedSymPiece G (i + 1)) (hb' : b' ∈ paritySignedSymPiece G (j + 1)) :
    a' * b + twist a * b' = ((-1 : ℤˣ) ^ (i * j)) • (b' * a + twist b * a') := by
  have h₁ : (-1 : ℤˣ) ^ ((i + 1) * j) = (-1 : ℤˣ) ^ (i * j) * (-1 : ℤˣ) ^ j := by
    rw [add_mul, one_mul, uzpow_add]
  have h₂ : (-1 : ℤˣ) ^ i * (-1 : ℤˣ) ^ (i * (j + 1)) = (-1 : ℤˣ) ^ (i * j) := by
    rw [← uzpow_add, mul_add, mul_one, ← add_assoc, add_comm i (i * j), add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  rw [twist_of_mem ha, twist_of_mem hb, smul_mul_assoc, smul_mul_assoc,
    mul_eq_uzpow_smul_mul G ha' hb, mul_eq_uzpow_smul_mul G ha hb', h₁, ← h₂]
  simp only [Units.smul_def, mul_smul]
  module

variable (δ : V →ₗ[R] ParitySignedSym G)

/-- The lower-triangular matrix `[[x, 0], [δ x, σ x]]` attached to a generator `x`. -/
private noncomputable def triangular :
    V →ₗ[R] Matrix (Fin 2) (Fin 2) (ParitySignedSym G) where
  toFun x := !![generator G x, 0; δ x, twist (generator G x)]
  map_add' x y := by
    ext r c
    fin_cases r <;> fin_cases c <;> simp
  map_smul' r x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

variable {δ}
variable (hδ : LinearMap.IsHomogeneous δ G.piece (paritySignedSymPiece G) 1)

include hδ in
private theorem triangular_mul_triangular {i j : ZMod 2} {x y : V}
    (hx : x ∈ G.piece i) (hy : y ∈ G.piece j) :
    triangular δ x * triangular δ y =
      ((-1 : ℤˣ) ^ (i * j)) • (triangular δ y * triangular δ x) := by
  have hgx := generator_mem_paritySignedSymPiece G hx
  have hgy := generator_mem_paritySignedSymPiece G hy
  have hdx := hδ.map_mem hx
  have hdy := hδ.map_mem hy
  ext r c
  fin_cases r <;> fin_cases c
  · simpa [triangular, Matrix.mul_apply] using mul_eq_uzpow_smul_mul G hgx hgy
  · simp [triangular, Matrix.mul_apply, Units.smul_def]
  · simpa [triangular, Matrix.mul_apply, Fin.sum_univ_two] using
      mul_add_twist_mul_comm hgx hgy hdx hdy
  · have key : twist (generator G x) * twist (generator G y) =
        ((-1 : ℤˣ) ^ (i * j)) • (twist (generator G y) * twist (generator G x)) := by
      rw [← map_mul (twist (G := G)), ← map_mul (twist (G := G)),
        generator_mul_generator G hx hy, Units.smul_def, map_zsmul, map_mul, Units.smul_def]
    simpa [triangular, Matrix.mul_apply, Fin.sum_univ_two] using key

private noncomputable def triangularLift :
    ParitySignedSym G →ₐ[R] Matrix (Fin 2) (Fin 2) (ParitySignedSym G) :=
  lift G (triangular δ) fun _ _ _ _ hx hy => triangular_mul_triangular hδ hx hy

private theorem triangularLift_apply (a : ParitySignedSym G) :
    triangularLift hδ a 0 0 = a ∧ triangularLift hδ a 0 1 = 0 ∧
      triangularLift hδ a 1 1 = twist a := by
  induction a using ParitySignedSym.induction with
  | algebraMap r => simp [Matrix.algebraMap_matrix_apply]
  | generator x => simp [triangularLift, triangular]
  | mul a b ha hb =>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]
  | add a b ha hb => simp [ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]

variable (δ) in
/-- The odd derivation of `ParitySignedSym G` extending a parity-`1` linear map
`δ : V → ParitySignedSym G`. It satisfies `TauCeti.ParitySignedSym.liftDerivation_mul`, flips
parity (`i ↦ i + 1`), and is the unique such extension of `δ`
(`TauCeti.ParitySignedSym.eq_liftDerivation`). -/
noncomputable def liftDerivation : ParitySignedSym G →ₗ[R] ParitySignedSym G :=
  Matrix.entryLinearMap R (ParitySignedSym G) (1 : Fin 2) (0 : Fin 2) ∘ₗ
    (triangularLift hδ).toLinearMap

private theorem liftDerivation_apply (a : ParitySignedSym G) :
    liftDerivation δ hδ a = triangularLift hδ a 1 0 := (rfl)

/-- The odd derivation extends the assignment on generators. -/
@[simp]
theorem liftDerivation_generator (x : V) : liftDerivation δ hδ (generator G x) = δ x := by
  simp [liftDerivation_apply, triangularLift, triangular]

/-- **The parity signed Leibniz rule**: for a left factor `a` of parity `i`,
`d (a * b) = d a * b + (-1) ^ i • (a * d b)`. -/
theorem liftDerivation_mul {i : ZMod 2} {a : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G i) (b : ParitySignedSym G) :
    liftDerivation δ hδ (a * b) =
      liftDerivation δ hδ a * b + ((-1 : ℤˣ) ^ i) • (a * liftDerivation δ hδ b) := by
  simp only [liftDerivation_apply, map_mul, Matrix.mul_apply, Fin.sum_univ_two,
    (triangularLift_apply hδ a).2.2, (triangularLift_apply hδ b).1, twist_of_mem ha]
  rw [Units.smul_def, Units.smul_def, smul_mul_assoc]

/-- The odd derivation annihilates the coefficients. -/
@[simp]
theorem liftDerivation_algebraMap (r : R) :
    liftDerivation δ hδ (algebraMap R _ r) = 0 := by
  simp [liftDerivation_apply, Matrix.algebraMap_matrix_apply]

/-- The odd derivation annihilates the unit. -/
@[simp]
theorem liftDerivation_one : liftDerivation δ hδ 1 = 0 := by
  simpa only [map_one] using liftDerivation_algebraMap hδ 1

/-- The odd derivation has parity `1`, mapping `paritySignedSymPiece G i` into
`paritySignedSymPiece G (i + 1)`. -/
theorem isHomogeneous_liftDerivation :
    LinearMap.IsHomogeneous (liftDerivation δ hδ)
      (paritySignedSymPiece G) (paritySignedSymPiece G) 1 := by
  refine LinearMap.isHomogeneous_def.2 fun i a ha => ?_
  refine (homogeneous_induction G
    (P := fun i a => a ∈ paritySignedSymPiece G i ∧
      liftDerivation δ hδ a ∈ paritySignedSymPiece G (i + 1))
    ⟨SetLike.GradedOne.one_mem, by simp⟩
    (fun i x hx => ⟨generator_mem_paritySignedSymPiece G hx, by simpa using hδ.map_mem hx⟩)
    (fun i j a b ha hb => ⟨SetLike.mul_mem_graded ha.1 hb.1, by
      rw [liftDerivation_mul hδ ha.1]
      refine add_mem ?_ (Submodule.smul_of_tower_mem _ _ ?_)
      · simpa [add_right_comm] using SetLike.mul_mem_graded ha.2 hb.1
      · simpa [add_assoc] using SetLike.mul_mem_graded ha.1 hb.2⟩)
    (fun _ => ⟨zero_mem _, by simp⟩)
    (fun _ a b ha hb => ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩)
    (fun _ r a ha => ⟨Submodule.smul_mem _ r ha.1, by
      rw [map_smul]; exact Submodule.smul_mem _ r ha.2⟩)
    ha).2

/-- **Uniqueness of parity odd derivations**: a linear endomorphism of `ParitySignedSym G`
satisfying the parity signed Leibniz rule and agreeing with `δ` on generators equals
`liftDerivation δ hδ`. No parity homogeneity assumption on `d` is needed. -/
theorem eq_liftDerivation {d : ParitySignedSym G →ₗ[R] ParitySignedSym G}
    (hleibniz : ∀ {i : ZMod 2} {a : ParitySignedSym G}, a ∈ paritySignedSymPiece G i →
      ∀ b : ParitySignedSym G, d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b))
    (hgen : ∀ x, d (generator G x) = δ x) : d = liftDerivation δ hδ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_leibniz (fun i => (-1 : ℤˣ) ^ i) (fun {i a} ha b => ?_) fun x => ?_
  · simp only [LinearMap.sub_apply, hleibniz ha, liftDerivation_mul hδ ha, sub_mul, mul_sub,
      Units.smul_def, zsmul_sub]
    abel
  · simp [hgen]

end Lift

/-- **Parity odd derivations are free on generators**: a parity-`1` linear map
`δ : V → ParitySignedSym G` extends uniquely to a linear endomorphism satisfying the parity signed
Leibniz rule. -/
theorem existsUnique_odd_extension {δ : V →ₗ[R] ParitySignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (paritySignedSymPiece G) 1) :
    ∃! d : ParitySignedSym G →ₗ[R] ParitySignedSym G, d ∘ₗ generator G = δ ∧
      ∀ {i : ZMod 2} {a : ParitySignedSym G}, a ∈ paritySignedSymPiece G i →
        ∀ b : ParitySignedSym G, d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b) :=
  ⟨liftDerivation δ hδ, ⟨LinearMap.ext (liftDerivation_generator hδ), liftDerivation_mul hδ⟩,
    fun _ hd => eq_liftDerivation hδ hd.2 fun x => LinearMap.congr_fun hd.1 x⟩

/-- **The square of a parity odd derivation is determined by generators**: a parity-`1` linear
endomorphism of `ParitySignedSym G` satisfying the parity signed Leibniz rule squares to zero if
and only if its square vanishes on generators. -/
theorem comp_self_eq_zero_iff {d : ParitySignedSym G →ₗ[R] ParitySignedSym G}
    (hdeg : LinearMap.IsHomogeneous d (paritySignedSymPiece G) (paritySignedSymPiece G) 1)
    (hleibniz : ∀ {i : ZMod 2} {a : ParitySignedSym G}, a ∈ paritySignedSymPiece G i →
      ∀ b : ParitySignedSym G, d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b)) :
    d ∘ₗ d = 0 ↔ ∀ x, d (d (generator G x)) = 0 := by
  refine ⟨fun h x => LinearMap.congr_fun h (generator G x), fun h => ?_⟩
  refine eq_zero_of_leibniz 1 (fun {i a} ha b => ?_) h
  have hda := hdeg.map_mem ha
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, hleibniz ha, map_add,
    map_zsmul_unit, hleibniz hda, hleibniz ha, uzpow_add, uzpow_one]
  simp only [Units.smul_def, Units.val_neg, Units.val_one, mul_neg, mul_one,
    neg_zsmul, zsmul_add, smul_smul, ← Units.val_mul, Int.units_mul_self, one_zsmul, Pi.one_apply]
  abel

/-- The odd derivation `liftDerivation δ hδ` squares to zero if and only if it annihilates `δ x`
for every `x : V`. -/
theorem liftDerivation_comp_self_eq_zero_iff {δ : V →ₗ[R] ParitySignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (paritySignedSymPiece G) 1) :
    liftDerivation δ hδ ∘ₗ liftDerivation δ hδ = 0 ↔
      ∀ x, liftDerivation δ hδ (δ x) = 0 := by
  simpa only [liftDerivation_generator] using
    comp_self_eq_zero_iff (isHomogeneous_liftDerivation hδ) (liftDerivation_mul hδ)

end ParitySignedSym

namespace SignedSym

variable {G : InternalGrading R V ℤ}

/-- Pushing a degree-`1` assignment `δ : V → SignedSym G` forward along `SignedSym.parityEquiv G`
produces a parity-`1` assignment into `ParitySignedSym G.parity`. -/
theorem isHomogeneous_parityEquiv_comp {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) :
    LinearMap.IsHomogeneous ((parityEquiv G).toLinearMap ∘ₗ δ)
      G.parity.piece (paritySignedSymPiece G.parity) 1 := by
  refine LinearMap.isHomogeneous_def.2 fun i x hx => ?_
  rw [InternalGrading.parity_piece] at hx
  have h1 : Int.castAddHom (ZMod 2) 1 = 1 := Int.cast_one
  have hmem := (hδ.coarsenGrading (Int.castAddHom (ZMod 2))).map_mem hx
  rw [h1] at hmem
  simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    mem_paritySignedSymPiece_parityEquiv_iff] using hmem

/-- `SignedSym.parityEquiv G` intertwines `SignedSym.liftDerivation` with
`ParitySignedSym.liftDerivation`. -/
theorem parityEquiv_liftDerivation {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) (a : SignedSym G) :
    parityEquiv G (liftDerivation δ hδ a) =
      ParitySignedSym.liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
        (isHomogeneous_parityEquiv_comp hδ) (parityEquiv G a) := by
  let d' : ParitySignedSym G.parity →ₗ[R] ParitySignedSym G.parity :=
    (parityEquiv G).toLinearMap ∘ₗ liftDerivation δ hδ ∘ₗ (parityEquiv G).symm.toLinearMap
  have hd' : d' = ParitySignedSym.liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
      (isHomogeneous_parityEquiv_comp hδ) := by
    refine ParitySignedSym.eq_liftDerivation (isHomogeneous_parityEquiv_comp hδ)
      (fun {i b} hb c => ?_) fun x => ?_
    · have hb' : (parityEquiv G).symm b ∈ parityGrading (signedSymPiece G) i :=
        (mem_parityGrading_parityEquiv_symm_iff G).2 hb
      have hl := leibniz_parityGrading_of_leibniz (liftDerivation_mul hδ) hb'
        ((parityEquiv G).symm c)
      simpa only [d', LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul, map_add,
        Units.smul_def, map_zsmul, AlgEquiv.apply_symm_apply] using congrArg (parityEquiv G) hl
    · simp [d']
  simpa only [d', LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.symm_apply_apply] using LinearMap.congr_fun hd' (parityEquiv G a)

/-- The inverse of `SignedSym.parityEquiv G` intertwines `ParitySignedSym.liftDerivation` with
`SignedSym.liftDerivation`. -/
theorem parityEquiv_symm_liftDerivation {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1)
    (b : ParitySignedSym G.parity) :
    (parityEquiv G).symm
      (ParitySignedSym.liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
        (isHomogeneous_parityEquiv_comp hδ) b) =
      liftDerivation δ hδ ((parityEquiv G).symm b) := by
  apply (parityEquiv G).injective
  simpa only [AlgEquiv.apply_symm_apply] using
    (parityEquiv_liftDerivation hδ ((parityEquiv G).symm b)).symm

/-- For a degree-`1` assignment `δ : V → SignedSym G`, `SignedSym.liftDerivation δ hδ` makes
`SignedSym G` a differential graded algebra if and only if the induced parity odd derivation on
`ParitySignedSym G.parity` squares to zero. -/
theorem isDGAlgebra_liftDerivation_iff_parity {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) :
    IsDGAlgebra (signedSymPiece G) (liftDerivation δ hδ) ↔
      ParitySignedSym.liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
        (isHomogeneous_parityEquiv_comp hδ) ∘ₗ
      ParitySignedSym.liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
        (isHomogeneous_parityEquiv_comp hδ) = 0 := by
  rw [isDGAlgebra_liftDerivation_iff, ParitySignedSym.liftDerivation_comp_self_eq_zero_iff]
  refine forall_congr' fun x => ?_
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, ← parityEquiv_liftDerivation hδ]
  exact ⟨fun h => by rw [h, map_zero], fun h => (parityEquiv G).injective (by rwa [map_zero])⟩

end SignedSym

end TauCeti
