/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Parity
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Derivation
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Parity.Supercommutativity
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.GroupAction.Ring

/-!
# Odd derivations of `ParitySignedSym`

A linear map `δ : V → ParitySignedSym G` that shifts generator parity by `1` extends uniquely to
an `R`-linear endomorphism `d` of `ParitySignedSym G` satisfying the parity-signed Leibniz rule

`d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b)` for `a` of parity `i : ZMod 2`,

or equivalently `d (a * b) = d a * b + gradeInvolution G a * d b` for every `a` and `b`. No
integer lift of the parity grading is required. This extension
`TauCeti.ParitySignedSym.liftDerivation` again shifts parity by `1` and anticommutes with
`TauCeti.ParitySignedSym.gradeInvolution`. Its square is an unsigned derivation of
`ParitySignedSym G`, so `d ∘ₗ d = 0` holds if and only if `d (d (generator G x)) = 0` for every
`x : V`. This provides the native `ZMod 2`-graded differential calculus for the contact homology
algebra when no global integer Conley–Zehnder lift exists.

When `G` is an internal `ℤ`-grading, `TauCeti.SignedSym.parityEquiv G` conjugates every
degree-one signed Leibniz map on `SignedSym G` to an odd signed Leibniz map on
`ParitySignedSym G.parity`, carries `TauCeti.SignedSym.liftDerivation` to
`TauCeti.ParitySignedSym.liftDerivation`, and identifies `IsDGAlgebra` for an integer-lifted
derivation with `d ∘ₗ d = 0` for its parity reduction.

## Main definitions

* `TauCeti.ParitySignedSym.liftDerivation`: the odd derivation of `ParitySignedSym G` extending a
  parity-shifting linear map `δ : V →ₗ[R] ParitySignedSym G`.

## Main results

* `TauCeti.ParitySignedSym.liftDerivation_mul` and
  `TauCeti.ParitySignedSym.liftDerivation_mul_gradeInvolution`: the homogeneous and unconditional
  parity-signed Leibniz rules.
* `TauCeti.ParitySignedSym.isHomogeneous_liftDerivation`: the extension shifts parity by `1`.
* `TauCeti.ParitySignedSym.eq_liftDerivation` and
  `TauCeti.ParitySignedSym.existsUnique_odd_extension`: odd derivations are free on generators.
* `TauCeti.ParitySignedSym.apply_apply_mul_of_leibniz`,
  `TauCeti.ParitySignedSym.comp_self_eq_zero_iff`, and
  `TauCeti.ParitySignedSym.liftDerivation_comp_self_eq_zero_iff`: the square of an odd derivation
  is an unsigned derivation, so `d ∘ₗ d = 0` reduces to generators.
* `TauCeti.SignedSym.parityEquiv_liftDerivation` and
  `TauCeti.SignedSym.isDGAlgebra_liftDerivation_iff_parity`: compatibility of integer-graded and
  parity-graded odd derivations across `SignedSym.parityEquiv`.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1) and Definition 2.48.
-/

public section

namespace TauCeti

universe u v

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

namespace ParitySignedSym

variable {G : InternalGrading R V (ZMod 2)}

/-- A linear endomorphism of `ParitySignedSym G` satisfying a Leibniz rule with an arbitrary sign
`s i` on a left factor of parity `i`, and vanishing on generators, is zero. This covers both the
difference of two odd derivations and the square of an odd derivation. -/
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
    refine (homogeneous_induction G (P := fun i a ↦ a ∈ paritySignedSymPiece G i ∧ D a = 0)
      ⟨SetLike.GradedOne.one_mem, hone⟩
      (fun i x hx ↦ ⟨generator_mem_paritySignedSymPiece G hx, hgen x⟩)
      (fun i j a b ha hb ↦ ⟨SetLike.mul_mem_graded ha.1 hb.1, by
        rw [hD ha.1, ha.2, hb.2, zero_mul, mul_zero, zero_add, Units.smul_def, zsmul_zero]⟩)
      (fun i ↦ ⟨zero_mem _, map_zero D⟩)
      (fun i a b ha hb ↦ ⟨add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2, add_zero]⟩)
      (fun i r a ha ↦ ⟨Submodule.smul_mem _ r ha.1, by rw [map_smul, ha.2, smul_zero]⟩)
      ha).2
  ext a
  induction a using DirectSum.Decomposition.inductionOn (paritySignedSymPiece G) with
  | zero => simp
  | homogeneous a => exact hhom a.2
  | add a b ha hb => simp_all

section Lift

variable (δ : V →ₗ[R] ParitySignedSym G)

/-- The parity Koszul sign identity behind the lower-left entry of a product of `2 × 2` triangular
matrices: for `a`, `b` of parities `i`, `j` and `a'`, `b'` of parities `i + 1`, `j + 1`,
`a' * b + gradeInvolution G a * b' = ((-1 : ℤˣ) ^ (i * j)) • (b' * a + gradeInvolution G b * a')`.
-/
private theorem mul_add_gradeInvolution_mul_comm {i j : ZMod 2}
    {a b a' b' : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G i) (hb : b ∈ paritySignedSymPiece G j)
    (ha' : a' ∈ paritySignedSymPiece G (i + 1)) (hb' : b' ∈ paritySignedSymPiece G (j + 1)) :
    a' * b + gradeInvolution G a * b' =
      ((-1 : ℤˣ) ^ (i * j)) • (b' * a + gradeInvolution G b * a') := by
  have h₁ : (-1 : ℤˣ) ^ ((i + 1) * j) = ((-1 : ℤˣ) ^ (i * j)) * ((-1 : ℤˣ) ^ j) := by
    rw [add_mul, one_mul, uzpow_add]
  have hii : ∀ k : ZMod 2, k + k = 0 := by decide
  have h₂ : ((-1 : ℤˣ) ^ i) * ((-1 : ℤˣ) ^ (i * (j + 1))) = (-1 : ℤˣ) ^ (i * j) := by
    rw [← uzpow_add, mul_add, mul_one, ← add_assoc, add_right_comm i (i * j) i, hii i, zero_add]
  simp only [gradeInvolution_apply_of_mem G ha, gradeInvolution_apply_of_mem G hb,
    Units.smul_def, smul_mul_assoc]
  rw [mul_eq_uzpow_smul_mul G ha' hb, mul_eq_uzpow_smul_mul G ha hb']
  simp only [Units.smul_def, zsmul_add, smul_smul, ← Units.val_mul, h₁, h₂]
  exact add_comm _ _

/-- The lower-triangular matrix `[[generator G x, 0], [δ x, gradeInvolution G (generator G x)]]`
attached to a generator `x : V`. -/
private noncomputable def triangular :
    V →ₗ[R] Matrix (Fin 2) (Fin 2) (ParitySignedSym G) where
  toFun x := !![generator G x, 0; δ x, gradeInvolution G (generator G x)]
  map_add' x y := by
    ext r c
    fin_cases r <;> fin_cases c <;> simp
  map_smul' c x := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp

variable {δ}
variable (hδ : LinearMap.IsHomogeneous δ G.piece (paritySignedSymPiece G) 1)

include hδ in
/-- The triangular matrices of homogeneous generators obey the parity swap relation. -/
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
  · simpa [triangular, Matrix.mul_apply, Units.smul_def] using
      mul_eq_uzpow_smul_mul G hgx hgy
  · simp [triangular, Matrix.mul_apply, Units.smul_def]
  · simpa [triangular, Matrix.mul_apply, Fin.sum_univ_two, Units.smul_def] using
      mul_add_gradeInvolution_mul_comm hgx hgy hdx hdy
  · have key : gradeInvolution G (generator G x) * gradeInvolution G (generator G y) =
        ((-1 : ℤˣ) ^ (i * j)) •
          (gradeInvolution G (generator G y) * gradeInvolution G (generator G x)) := by
      rw [← map_mul (gradeInvolution G), ← map_mul (gradeInvolution G),
        generator_mul_generator G hx hy, Units.smul_def, map_zsmul, ← Units.smul_def]
    simpa [triangular, Matrix.mul_apply, Fin.sum_univ_two, Units.smul_def] using key

/-- The algebra map `a ↦ [[a, 0], [d a, gradeInvolution G a]]` extending `triangular δ`. -/
private noncomputable def triangularLift :
    ParitySignedSym G →ₐ[R] Matrix (Fin 2) (Fin 2) (ParitySignedSym G) :=
  lift G (triangular δ) fun _ _ _ _ hx hy ↦ triangular_mul_triangular hδ hx hy

/-- The diagonal and upper-right entries of `triangularLift` are `a`, `gradeInvolution G a`,
and `0`. -/
private theorem triangularLift_apply (a : ParitySignedSym G) :
    triangularLift hδ a 0 0 = a ∧ triangularLift hδ a 0 1 = 0 ∧
      triangularLift hδ a 1 1 = gradeInvolution G a := by
  induction a using ParitySignedSym.induction with
  | algebraMap r => simp [Matrix.algebraMap_matrix_apply]
  | generator x => simp [triangularLift, triangular]
  | mul a b ha hb =>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]
  | add a b ha hb => simp [ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]

variable (δ) in
/-- The odd derivation of `ParitySignedSym G` extending a parity-shifting linear map
`δ : V →ₗ[R] ParitySignedSym G`. It satisfies the parity-signed Leibniz rule
`TauCeti.ParitySignedSym.liftDerivation_mul`, shifts parity by `1`, and is the unique such
extension of `δ` (`TauCeti.ParitySignedSym.eq_liftDerivation`). -/
noncomputable def liftDerivation : ParitySignedSym G →ₗ[R] ParitySignedSym G :=
  Matrix.entryLinearMap R (ParitySignedSym G) (1 : Fin 2) (0 : Fin 2) ∘ₗ
    (triangularLift hδ).toLinearMap

private theorem liftDerivation_apply (a : ParitySignedSym G) :
    liftDerivation δ hδ a = triangularLift hδ a 1 0 :=
  (rfl)

/-- The odd derivation extends the assignment on generators. -/
@[simp]
theorem liftDerivation_generator (x : V) : liftDerivation δ hδ (generator G x) = δ x := by
  simp [liftDerivation_apply, triangularLift, triangular]

/-- **Unconditional Leibniz rule**: on any two elements of `ParitySignedSym G`,
`d (a * b) = d a * b + gradeInvolution G a * d b`. -/
theorem liftDerivation_mul_gradeInvolution (a b : ParitySignedSym G) :
    liftDerivation δ hδ (a * b) =
      liftDerivation δ hδ a * b + gradeInvolution G a * liftDerivation δ hδ b := by
  simp only [liftDerivation_apply, map_mul, Matrix.mul_apply, Fin.sum_univ_two,
    (triangularLift_apply hδ a).2.2, (triangularLift_apply hδ b).1]

/-- **The parity-signed Leibniz rule**: for a left factor of parity `i`,
`d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b)`. -/
theorem liftDerivation_mul {i : ZMod 2} {a : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G i) (b : ParitySignedSym G) :
    liftDerivation δ hδ (a * b) =
      liftDerivation δ hδ a * b + ((-1 : ℤˣ) ^ i) • (a * liftDerivation δ hδ b) := by
  rw [liftDerivation_mul_gradeInvolution, gradeInvolution_apply_of_mem G ha,
    Units.smul_def, smul_mul_assoc, ← Units.smul_def]

/-- On an even left factor, `liftDerivation` satisfies the unsigned Leibniz rule. -/
theorem liftDerivation_mul_of_mem_zero {a : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G 0) (b : ParitySignedSym G) :
    liftDerivation δ hδ (a * b) = liftDerivation δ hδ a * b + a * liftDerivation δ hδ b := by
  simpa using liftDerivation_mul hδ ha b

/-- On an odd left factor, `liftDerivation` satisfies `d (a * b) = d a * b - a * d b`. -/
theorem liftDerivation_mul_of_mem_one {a : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G 1) (b : ParitySignedSym G) :
    liftDerivation δ hδ (a * b) = liftDerivation δ hδ a * b - a * liftDerivation δ hδ b := by
  simpa [sub_eq_add_neg] using liftDerivation_mul hδ ha b

/-- The odd derivation annihilates the unit. -/
@[simp]
theorem liftDerivation_one : liftDerivation δ hδ 1 = 0 := by
  have h := liftDerivation_mul_of_mem_zero hδ
    (SetLike.GradedOne.one_mem (A := paritySignedSymPiece G)) 1
  simp only [mul_one, one_mul] at h
  exact left_eq_add.mp h

/-- The odd derivation annihilates the image of the coefficient ring. -/
@[simp]
theorem liftDerivation_algebraMap (r : R) : liftDerivation δ hδ (algebraMap R _ r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, liftDerivation_one, smul_zero]

/-- The odd derivation shifts parity by `1`. -/
theorem isHomogeneous_liftDerivation :
    LinearMap.IsHomogeneous (liftDerivation δ hδ)
      (paritySignedSymPiece G) (paritySignedSymPiece G) 1 := by
  refine LinearMap.isHomogeneous_def.2 fun i a ha ↦ ?_
  refine (homogeneous_induction G
    (P := fun i a ↦ a ∈ paritySignedSymPiece G i ∧
      liftDerivation δ hδ a ∈ paritySignedSymPiece G (i + 1))
    ⟨SetLike.GradedOne.one_mem, by simp⟩
    (fun i x hx ↦ ⟨generator_mem_paritySignedSymPiece G hx, by simpa using hδ.map_mem hx⟩)
    (fun i j a b ha hb ↦ ⟨SetLike.mul_mem_graded ha.1 hb.1, by
      rw [liftDerivation_mul hδ ha.1]
      refine add_mem ?_ ?_
      · simpa [add_right_comm] using SetLike.mul_mem_graded ha.2 hb.1
      · rw [Units.smul_def]
        exact zsmul_mem (by simpa [add_assoc] using SetLike.mul_mem_graded ha.1 hb.2) _⟩)
    (fun i ↦ ⟨zero_mem _, by simp⟩)
    (fun i a b ha hb ↦ ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩)
    (fun i r a ha ↦ ⟨Submodule.smul_mem _ r ha.1, by
      rw [map_smul]; exact Submodule.smul_mem _ r ha.2⟩)
    ha).2

/-- `liftDerivation` commutes with parity projections up to the parity shift by `1`. -/
@[simp]
theorem liftDerivation_decompose (a : ParitySignedSym G) (i : ZMod 2) :
    liftDerivation δ hδ (DirectSum.decompose (paritySignedSymPiece G) a i : ParitySignedSym G) =
      (DirectSum.decompose (paritySignedSymPiece G) (liftDerivation δ hδ a) (i + 1) :
        ParitySignedSym G) :=
  (isHomogeneous_liftDerivation hδ).map_decompose i a

/-- `liftDerivation` anticommutes with `gradeInvolution`. -/
theorem gradeInvolution_liftDerivation (a : ParitySignedSym G) :
    gradeInvolution G (liftDerivation δ hδ a) =
      -liftDerivation δ hδ (gradeInvolution G a) := by
  induction a using DirectSum.Decomposition.inductionOn (paritySignedSymPiece G) with
  | zero => simp
  | @homogeneous i a =>
    have hda := (isHomogeneous_liftDerivation hδ).map_mem a.2
    rw [gradeInvolution_apply_of_mem G hda, gradeInvolution_apply_of_mem G a.2,
      map_zsmul_unit, uzpow_add, uzpow_one]
    simp only [Units.smul_def, Units.val_neg, mul_neg_one, neg_zsmul]
  | add a b ha hb => simp only [map_add, neg_add_rev, ha, hb]; abel

/-- **Uniqueness of odd derivations**: a linear endomorphism of `ParitySignedSym G` satisfying the
parity-signed Leibniz rule and agreeing with `δ` on generators equals `liftDerivation δ hδ`. No
parity-homogeneity hypothesis on `d` is needed. -/
theorem eq_liftDerivation {d : ParitySignedSym G →ₗ[R] ParitySignedSym G}
    (hleibniz : ∀ {i : ZMod 2} {a : ParitySignedSym G}, a ∈ paritySignedSymPiece G i →
      ∀ b : ParitySignedSym G, d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b))
    (hgen : ∀ x, d (generator G x) = δ x) : d = liftDerivation δ hδ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_leibniz (fun i ↦ (-1 : ℤˣ) ^ i) (fun {i a} ha b ↦ ?_) fun x ↦ ?_
  · simp only [LinearMap.sub_apply, hleibniz ha, liftDerivation_mul hδ ha, sub_mul, mul_sub,
      Units.smul_def, zsmul_sub]
    abel
  · simp [hgen]

end Lift

/-- **Odd derivations are free on generators**: a parity-shifting linear map
`δ : V →ₗ[R] ParitySignedSym G` extends uniquely to a linear endomorphism satisfying the
parity-signed Leibniz rule. -/
theorem existsUnique_odd_extension {δ : V →ₗ[R] ParitySignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (paritySignedSymPiece G) 1) :
    ∃! d : ParitySignedSym G →ₗ[R] ParitySignedSym G, d ∘ₗ generator G = δ ∧
      ∀ {i : ZMod 2} {a : ParitySignedSym G}, a ∈ paritySignedSymPiece G i →
        ∀ b : ParitySignedSym G, d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b) :=
  ⟨liftDerivation δ hδ, ⟨LinearMap.ext (liftDerivation_generator hδ), liftDerivation_mul hδ⟩,
    fun _ hd ↦ eq_liftDerivation hδ hd.2 fun x ↦ LinearMap.congr_fun hd.1 x⟩

/-- **The square of an odd derivation is an unsigned derivation**: for any parity-shifting linear
endomorphism `d` of `ParitySignedSym G` satisfying the parity-signed Leibniz rule,
`d (d (a * b)) = d (d a) * b + a * d (d b)` for all `a` and `b`. -/
theorem apply_apply_mul_of_leibniz {d : ParitySignedSym G →ₗ[R] ParitySignedSym G}
    (hdeg : LinearMap.IsHomogeneous d (paritySignedSymPiece G) (paritySignedSymPiece G) 1)
    (hleibniz : ∀ {i : ZMod 2} {a : ParitySignedSym G}, a ∈ paritySignedSymPiece G i →
      ∀ b : ParitySignedSym G, d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b))
    (a b : ParitySignedSym G) :
    d (d (a * b)) = d (d a) * b + a * d (d b) := by
  induction a using DirectSum.Decomposition.inductionOn (paritySignedSymPiece G) with
  | zero => simp
  | @homogeneous i a =>
    have hda := hdeg.map_mem a.2
    rw [hleibniz a.2, map_add, map_zsmul_unit, hleibniz hda, hleibniz a.2, uzpow_add, uzpow_one]
    simp only [Units.smul_def, Units.val_neg, Units.val_one, mul_neg_one, neg_zsmul,
      zsmul_add, smul_smul, ← Units.val_mul, Int.units_mul_self, one_zsmul]
    abel
  | add a c ha hc =>
    simp only [add_mul, map_add, ha, hc]
    abel

/-- **The square of an odd derivation is determined by generators**: a parity-shifting linear
endomorphism of `ParitySignedSym G` satisfying the parity-signed Leibniz rule squares to zero if
and only if its square vanishes on generators. -/
theorem comp_self_eq_zero_iff {d : ParitySignedSym G →ₗ[R] ParitySignedSym G}
    (hdeg : LinearMap.IsHomogeneous d (paritySignedSymPiece G) (paritySignedSymPiece G) 1)
    (hleibniz : ∀ {i : ZMod 2} {a : ParitySignedSym G}, a ∈ paritySignedSymPiece G i →
      ∀ b : ParitySignedSym G, d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b)) :
    d ∘ₗ d = 0 ↔ ∀ x, d (d (generator G x)) = 0 := by
  refine ⟨fun h x ↦ LinearMap.congr_fun h (generator G x), fun h ↦ ?_⟩
  refine eq_zero_of_leibniz 1 (fun {i a} _ b ↦ ?_) h
  simpa only [LinearMap.comp_apply, Pi.one_apply, one_smul] using
    apply_apply_mul_of_leibniz hdeg hleibniz a b

/-- **Generator criterion for `d ∘ₗ d = 0`**: `liftDerivation δ hδ` squares to zero if and only if
it annihilates `δ x` for every `x : V`. -/
theorem liftDerivation_comp_self_eq_zero_iff {δ : V →ₗ[R] ParitySignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (paritySignedSymPiece G) 1) :
    liftDerivation δ hδ ∘ₗ liftDerivation δ hδ = 0 ↔
      ∀ x, liftDerivation δ hδ (δ x) = 0 := by
  simpa only [liftDerivation_generator] using
    comp_self_eq_zero_iff (isHomogeneous_liftDerivation hδ) (liftDerivation_mul hδ)

end ParitySignedSym

/-! ### Comparison with integer-graded derivations -/

namespace SignedSym

variable (G : InternalGrading R V ℤ)

/-- Conjugating a degree-one endomorphism of `SignedSym G` by `parityEquiv G` gives a
parity-shifting endomorphism of `ParitySignedSym G.parity`. -/
theorem isHomogeneous_conj_parityEquiv {d : SignedSym G →ₗ[R] SignedSym G}
    (hd : LinearMap.IsHomogeneous d (signedSymPiece G) (signedSymPiece G) 1) :
    LinearMap.IsHomogeneous
      ((parityEquiv G).toLinearMap ∘ₗ d ∘ₗ (parityEquiv G).symm.toLinearMap)
      (paritySignedSymPiece G.parity) (paritySignedSymPiece G.parity) 1 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hb ↦ by
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      parityEquiv_mem_paritySignedSymPiece_iff]
    exact map_mem_parityGrading_of_map_mem (fun ha ↦ hd.map_mem ha)
      ((parityEquiv_symm_mem_parityGrading_iff G).2 hb)

/-- Conjugating a signed Leibniz endomorphism of `SignedSym G` by `parityEquiv G` gives a
parity-signed Leibniz endomorphism of `ParitySignedSym G.parity`. -/
theorem leibniz_conj_parityEquiv {d : SignedSym G →ₗ[R] SignedSym G}
    (hl : ∀ {p : ℤ} {a : SignedSym G}, a ∈ signedSymPiece G p → ∀ b : SignedSym G,
      d (a * b) = d a * b + p.negOnePow • (a * d b))
    {i : ZMod 2} {a : ParitySignedSym G.parity} (ha : a ∈ paritySignedSymPiece G.parity i)
    (b : ParitySignedSym G.parity) :
    parityEquiv G (d ((parityEquiv G).symm (a * b))) =
      parityEquiv G (d ((parityEquiv G).symm a)) * b +
        ((-1 : ℤˣ) ^ i) • (a * parityEquiv G (d ((parityEquiv G).symm b))) := by
  have ha' : (parityEquiv G).symm a ∈ parityGrading (signedSymPiece G) i :=
    (parityEquiv_symm_mem_parityGrading_iff G).2 ha
  rw [map_mul, leibniz_parityGrading_of_leibniz hl ha' ((parityEquiv G).symm b),
    map_add, map_mul, Units.smul_def, map_zsmul, map_mul, AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply, ← Units.smul_def]

/-- Post-composing a degree-one generator assignment `δ : V →ₗ[R] SignedSym G` with
`parityEquiv G` produces a parity-shifting assignment into `ParitySignedSym G.parity`. -/
theorem isHomogeneous_parityEquiv_comp {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) :
    LinearMap.IsHomogeneous ((parityEquiv G).toLinearMap ∘ₗ δ)
      G.parity.piece (paritySignedSymPiece G.parity) 1 := by
  refine LinearMap.isHomogeneous_def.2 fun i x hx ↦ ?_
  rw [InternalGrading.parity_piece] at hx
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    parityEquiv_mem_paritySignedSymPiece_iff]
  have hle : parityGrading G.piece i ≤ (parityGrading (signedSymPiece G) (i + 1)).comap δ :=
    parityGrading_le_iff.2 fun n hn y hy ↦ by
      simpa [hn] using mem_parityGrading_of_mem (hδ.map_mem hy)
  exact hle hx

/-- `SignedSym.parityEquiv` intertwines `SignedSym.liftDerivation` with
`ParitySignedSym.liftDerivation`. -/
@[simp]
theorem parityEquiv_liftDerivation {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) (a : SignedSym G) :
    parityEquiv G (liftDerivation δ hδ a) =
      ParitySignedSym.liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
        (isHomogeneous_parityEquiv_comp G hδ) (parityEquiv G a) := by
  let dPar : ParitySignedSym G.parity →ₗ[R] ParitySignedSym G.parity :=
    (parityEquiv G).toLinearMap ∘ₗ liftDerivation δ hδ ∘ₗ (parityEquiv G).symm.toLinearMap
  have hdPar : dPar = ParitySignedSym.liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
      (isHomogeneous_parityEquiv_comp G hδ) := by
    refine ParitySignedSym.eq_liftDerivation (isHomogeneous_parityEquiv_comp G hδ)
      (fun {i b} hb c ↦ ?_) fun x ↦ ?_
    · exact leibniz_conj_parityEquiv G (liftDerivation_mul hδ) hb c
    · simp [dPar]
  simpa [dPar] using LinearMap.congr_fun hdPar (parityEquiv G a)

/-- `(SignedSym.parityEquiv G).symm` intertwines `ParitySignedSym.liftDerivation` with
`SignedSym.liftDerivation`. -/
@[simp]
theorem parityEquiv_symm_liftDerivation {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1)
    (b : ParitySignedSym G.parity) :
    (parityEquiv G).symm
      (ParitySignedSym.liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
        (isHomogeneous_parityEquiv_comp G hδ) b) =
      liftDerivation δ hδ ((parityEquiv G).symm b) := by
  apply (parityEquiv G).injective
  simp

/-- An integer-graded derivation `SignedSym.liftDerivation δ hδ` makes `SignedSym G` a
differential graded algebra if and only if its parity reduction squares to zero on
`ParitySignedSym G.parity`. -/
theorem isDGAlgebra_liftDerivation_iff_parity {δ : V →ₗ[R] SignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (signedSymPiece G) 1) :
    IsDGAlgebra (signedSymPiece G) (liftDerivation δ hδ) ↔
      ParitySignedSym.liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
        (isHomogeneous_parityEquiv_comp G hδ) ∘ₗ
        ParitySignedSym.liftDerivation ((parityEquiv G).toLinearMap ∘ₗ δ)
          (isHomogeneous_parityEquiv_comp G hδ) = 0 := by
  rw [isDGAlgebra_liftDerivation_iff hδ, ParitySignedSym.liftDerivation_comp_self_eq_zero_iff]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, parityEquiv_liftDerivation,
      map_zero] using congrArg (parityEquiv G) (h x)
  · apply (parityEquiv G).injective
    simpa only [parityEquiv_liftDerivation, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      map_zero] using h x

end SignedSym

end TauCeti
