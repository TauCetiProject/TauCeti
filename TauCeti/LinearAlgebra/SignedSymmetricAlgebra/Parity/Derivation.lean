/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Parity
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Derivation
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Parity.Grading
public import TauCeti.RingTheory.GradedAlgebra.GradeInvolution
import Mathlib.Data.Matrix.Basic
import Mathlib.GroupTheory.GroupAction.Ring
import TauCeti.Data.ZMod.IntUnitsPower

/-!
# Odd derivations of the parity signed algebra

For an internal `ZMod 2`-grading `G` of an `R`-module `V`, an odd linear map
`δ : V →ₗ[R] ParitySignedSym G` extends uniquely to a linear endomorphism
`d = TauCeti.ParitySignedSym.liftDerivation δ hδ` satisfying the parity Leibniz rule

`d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b)` for `a ∈ paritySignedSymPiece G i`.

No lift of `G` to an integer grading is used. Instead, the grade involution
`σ = TauCeti.gradeInvolution (paritySignedSymPiece G)` acts by `(-1 : ℤˣ) ^ i` on each homogeneous
piece, and the lower triangular matrices `[[x, 0], [δ x, σ x]]` obey the parity Koszul relation in
`Matrix (Fin 2) (Fin 2) (ParitySignedSym G)`. Applying `ParitySignedSym.lift` produces an algebra
map `a ↦ [[a, 0], [d a, σ a]]` whose lower-left entry satisfies
`d (a * b) = d a * b + σ a * d b` on arbitrary elements.

The extension flips parity (`isHomogeneous_liftDerivation`). Because the square of any odd
parity-Leibniz map is an unsigned derivation (`TauCeti.comp_self_mul_of_parity_leibniz`), `d ∘ₗ d`
vanishes on the whole algebra if and only if it vanishes on generators (`comp_self_eq_zero_iff`).
When `V` carries an internal integer grading `H`, the presentation equivalence
`TauCeti.SignedSym.parityEquiv H` intertwines `SignedSym.liftDerivation` with
`ParitySignedSym.liftDerivation` (`SignedSym.parityEquiv_liftDerivation`).

## Main definitions

* `TauCeti.ParitySignedSym.liftDerivation`: the odd derivation of `ParitySignedSym G` extending an
  odd linear map on generators.

## Main results

* `TauCeti.ParitySignedSym.liftDerivation_mul_gradeInvolution` and
  `TauCeti.ParitySignedSym.liftDerivation_mul`: the parity Leibniz rule, in global
  grade-involution form and on homogeneous left factors.
* `TauCeti.ParitySignedSym.isHomogeneous_liftDerivation`: the extension flips parity.
* `TauCeti.ParitySignedSym.eq_liftDerivation` and
  `TauCeti.ParitySignedSym.existsUnique_odd_extension`: odd derivations are free on generators.
* `TauCeti.ParitySignedSym.comp_self_eq_zero_iff` and
  `TauCeti.ParitySignedSym.liftDerivation_comp_self_eq_zero_iff`: `d ∘ₗ d = 0` reduces to
  generators.
* `TauCeti.SignedSym.isHomogeneous_parityEquiv_comp_of_degree_one`,
  `TauCeti.SignedSym.parityEquiv_liftDerivation`, and
  `TauCeti.SignedSym.parityEquiv_comp_liftDerivation`: compatibility of `SignedSym.liftDerivation`
  with `ParitySignedSym.liftDerivation` across `SignedSym.parityEquiv`.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1) and Definition 2.48,
  where the contact homology differential is defined as an odd derivation of the free
  supercommutative algebra even when no canonical integer grading is fixed.
-/

public section

namespace TauCeti

universe u v

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

namespace ParitySignedSym

variable {G : InternalGrading R V (ZMod 2)}

/-- A linear endomorphism of `ParitySignedSym G` satisfying the parity Leibniz rule and vanishing
on generators is zero. -/
private theorem eq_zero_of_parity_leibniz {D : ParitySignedSym G →ₗ[R] ParitySignedSym G}
    (hD : ∀ {i : ZMod 2} {a : ParitySignedSym G}, a ∈ paritySignedSymPiece G i →
      ∀ b : ParitySignedSym G, D (a * b) = D a * b + ((-1 : ℤˣ) ^ i) • (a * D b))
    (hgen : ∀ x, D (generator G x) = 0) : D = 0 := by
  have hone : D 1 = 0 := map_one_eq_zero_of_parity_leibniz hD
  have hhom : ∀ {i : ZMod 2} {a : ParitySignedSym G}, a ∈ paritySignedSymPiece G i → D a = 0 := by
    intro i a ha
    refine (homogeneous_induction G (P := fun j b ↦ b ∈ paritySignedSymPiece G j ∧ D b = 0)
      ⟨SetLike.GradedOne.one_mem, hone⟩
      (fun j x hx ↦ ⟨generator_mem_paritySignedSymPiece G hx, hgen x⟩)
      (fun j k u v hu hv ↦ ⟨SetLike.mul_mem_graded hu.1 hv.1, by
        rw [hD hu.1, hu.2, hv.2, zero_mul, mul_zero, zero_add]
        exact smul_zero _⟩)
      (fun _ ↦ ⟨zero_mem _, map_zero D⟩)
      (fun _ u v hu hv ↦ ⟨add_mem hu.1 hv.1, by rw [map_add, hu.2, hv.2, add_zero]⟩)
      (fun _ r u hu ↦ ⟨Submodule.smul_mem _ r hu.1, by rw [map_smul, hu.2, smul_zero]⟩)
      ha).2
  ext a
  induction a using DirectSum.Decomposition.inductionOn (paritySignedSymPiece G) with
  | zero => simp
  | homogeneous a => exact hhom a.2
  | add u v hu hv => simp_all

section Lift

variable (δ : V →ₗ[R] ParitySignedSym G)

/-- The parity Koszul sign identity behind the lower-left entry of a product of triangular
matrices: for `a, b` of parities `i, j` and `a', b'` of parities `i + 1, j + 1`,
`a' * b + σ a * b' = ((-1 : ℤˣ) ^ (i * j)) • (b' * a + σ b * a')`. -/
private theorem mul_add_gradeInvolution_mul_comm {i j : ZMod 2} {a b a' b' : ParitySignedSym G}
    (ha : a ∈ paritySignedSymPiece G i) (hb : b ∈ paritySignedSymPiece G j)
    (ha' : a' ∈ paritySignedSymPiece G (i + 1)) (hb' : b' ∈ paritySignedSymPiece G (j + 1)) :
    a' * b + gradeInvolution (paritySignedSymPiece G) a * b' =
      ((-1 : ℤˣ) ^ (i * j)) • (b' * a + gradeInvolution (paritySignedSymPiece G) b * a') := by
  have h₁ : (-1 : ℤˣ) ^ ((i + 1) * j) = (-1 : ℤˣ) ^ (i * j) * (-1 : ℤˣ) ^ j := by
    rw [← uzpow_add]
    congr 1
    ring
  have h₂ : (-1 : ℤˣ) ^ i * (-1 : ℤˣ) ^ (i * (j + 1)) = (-1 : ℤˣ) ^ (i * j) := by
    rw [← uzpow_add]
    congr 1
    rcases (by decide : ∀ k : ZMod 2, k = 0 ∨ k = 1) i with rfl | rfl <;>
    rcases (by decide : ∀ k : ZMod 2, k = 0 ∨ k = 1) j with rfl | rfl <;> decide
  rw [gradeInvolution_apply_of_mem ha, gradeInvolution_apply_of_mem hb,
    smul_mul_assoc, smul_mul_assoc, mul_eq_uzpow_smul_mul G ha' hb,
    mul_eq_uzpow_smul_mul G ha hb', h₁, ← mul_smul, h₂, mul_smul]
  simp only [Units.smul_def]
  module

/-- The lower triangular matrix `[[x, 0], [δ x, σ x]]` attached to a generator `x`. -/
private noncomputable def triangular : V →ₗ[R] Matrix (Fin 2) (Fin 2) (ParitySignedSym G) where
  toFun x := !![generator G x, 0; δ x, gradeInvolution (paritySignedSymPiece G) (generator G x)]
  map_add' x y := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp
  map_smul' c x := by
    ext r s
    fin_cases r <;> fin_cases s <;> simp

variable {δ}
variable (hδ : LinearMap.IsHomogeneous δ G.piece (paritySignedSymPiece G) 1)

include hδ in
/-- The triangular matrices of homogeneous generators obey the parity Koszul relation. -/
private theorem triangular_mul_triangular {i j : ZMod 2} {x y : V}
    (hx : x ∈ G.piece i) (hy : y ∈ G.piece j) :
    triangular δ x * triangular δ y =
      ((-1 : ℤˣ) ^ (i * j)) • (triangular δ y * triangular δ x) := by
  have hgx := generator_mem_paritySignedSymPiece G hx
  have hgy := generator_mem_paritySignedSymPiece G hy
  have hdx := hδ.map_mem hx
  have hdy := hδ.map_mem hy
  ext r s
  fin_cases r <;> fin_cases s
  · simpa [triangular, Matrix.mul_apply, Units.smul_def] using
      mul_eq_uzpow_smul_mul G hgx hgy
  · simp [triangular, Matrix.mul_apply, Units.smul_def]
  · simpa [triangular, Matrix.mul_apply, Fin.sum_univ_two, Units.smul_def] using
      mul_add_gradeInvolution_mul_comm hgx hgy hdx hdy
  · have key : gradeInvolution (paritySignedSymPiece G) (generator G x) *
        gradeInvolution (paritySignedSymPiece G) (generator G y) =
          ((-1 : ℤˣ) ^ (i * j)) •
            (gradeInvolution (paritySignedSymPiece G) (generator G y) *
              gradeInvolution (paritySignedSymPiece G) (generator G x)) := by
      rw [← map_mul (gradeInvolution (paritySignedSymPiece G)),
        ← map_mul (gradeInvolution (paritySignedSymPiece G)),
        generator_mul_generator G hx hy, Units.smul_def, Units.smul_def, map_zsmul]
    simpa [triangular, Matrix.mul_apply, Fin.sum_univ_two, Units.smul_def] using key

/-- The algebra map `a ↦ [[a, 0], [d a, σ a]]` whose lower-left entry is the odd derivation. -/
private noncomputable def triangularLift :
    ParitySignedSym G →ₐ[R] Matrix (Fin 2) (Fin 2) (ParitySignedSym G) :=
  lift G (triangular δ) fun _ _ _ _ hx hy ↦ triangular_mul_triangular hδ hx hy

/-- The diagonal and upper-right entries of `triangularLift` are `a`, `σ a`, and `0`. -/
private theorem triangularLift_apply (a : ParitySignedSym G) :
    triangularLift hδ a 0 0 = a ∧ triangularLift hδ a 0 1 = 0 ∧
      triangularLift hδ a 1 1 = gradeInvolution (paritySignedSymPiece G) a := by
  induction a using ParitySignedSym.induction with
  | algebraMap r => simp [Matrix.algebraMap_matrix_apply]
  | generator x => simp [triangularLift, triangular]
  | mul a b ha hb =>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]
  | add a b ha hb => simp [ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]

variable (δ) in
/-- The odd derivation of `ParitySignedSym G` extending an odd linear map `δ : V →ₗ[R]
ParitySignedSym G`. It satisfies the parity Leibniz rule (`liftDerivation_mul`), flips parity
(`isHomogeneous_liftDerivation`), and is the unique such extension (`eq_liftDerivation`). -/
noncomputable def liftDerivation : ParitySignedSym G →ₗ[R] ParitySignedSym G :=
  Matrix.entryLinearMap R (ParitySignedSym G) (1 : Fin 2) (0 : Fin 2) ∘ₗ
    (triangularLift hδ).toLinearMap

private theorem liftDerivation_apply (a : ParitySignedSym G) :
    liftDerivation δ hδ a = triangularLift hδ a 1 0 := (rfl)

/-- The odd derivation extends the assignment on generators. -/
@[simp]
theorem liftDerivation_generator (x : V) : liftDerivation δ hδ (generator G x) = δ x := by
  simp [liftDerivation_apply, triangularLift, triangular]

/-- On arbitrary elements, `liftDerivation` satisfies the Leibniz rule twisted by the grade
involution on the left factor. -/
theorem liftDerivation_mul_gradeInvolution (a b : ParitySignedSym G) :
    liftDerivation δ hδ (a * b) =
      liftDerivation δ hδ a * b +
        gradeInvolution (paritySignedSymPiece G) a * liftDerivation δ hδ b := by
  simp only [liftDerivation_apply, map_mul, Matrix.mul_apply, Fin.sum_univ_two,
    (triangularLift_apply hδ a).2.2, (triangularLift_apply hδ b).1]

/-- **The parity Leibniz rule**: for a left factor of parity `i`,
`d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b)`. -/
theorem liftDerivation_mul {i : ZMod 2} {a : ParitySignedSym G} (ha : a ∈ paritySignedSymPiece G i)
    (b : ParitySignedSym G) :
    liftDerivation δ hδ (a * b) =
      liftDerivation δ hδ a * b + ((-1 : ℤˣ) ^ i) • (a * liftDerivation δ hδ b) := by
  rw [liftDerivation_mul_gradeInvolution, gradeInvolution_apply_of_mem ha, smul_mul_assoc]

/-- The odd derivation annihilates the ground ring. -/
@[simp]
theorem liftDerivation_algebraMap (r : R) :
    liftDerivation δ hδ (algebraMap R (ParitySignedSym G) r) = 0 :=
  map_algebraMap_of_parity_leibniz (liftDerivation_mul hδ) r

/-- The odd derivation annihilates the unit. -/
@[simp]
theorem liftDerivation_one : liftDerivation δ hδ 1 = 0 :=
  map_one_eq_zero_of_parity_leibniz (liftDerivation_mul hδ)

/-- The odd derivation flips parity. -/
theorem isHomogeneous_liftDerivation :
    LinearMap.IsHomogeneous (liftDerivation δ hδ)
      (paritySignedSymPiece G) (paritySignedSymPiece G) 1 := by
  refine LinearMap.isHomogeneous_def.2 fun i a ha ↦ ?_
  refine (homogeneous_induction G
    (P := fun j b ↦ b ∈ paritySignedSymPiece G j ∧
      liftDerivation δ hδ b ∈ paritySignedSymPiece G (j + 1))
    ⟨SetLike.GradedOne.one_mem, by simp⟩
    (fun j x hx ↦ ⟨generator_mem_paritySignedSymPiece G hx, by simpa using hδ.map_mem hx⟩)
    (fun j k u v hu hv ↦ ⟨SetLike.mul_mem_graded hu.1 hv.1, by
      rw [liftDerivation_mul hδ hu.1]
      refine add_mem ?_ (Submodule.smul_of_tower_mem _ _ ?_)
      · simpa [add_right_comm] using SetLike.mul_mem_graded hu.2 hv.1
      · simpa [add_assoc] using SetLike.mul_mem_graded hu.1 hv.2⟩)
    (fun _ ↦ ⟨zero_mem _, by simp⟩)
    (fun _ u v hu hv ↦ ⟨add_mem hu.1 hv.1, by rw [map_add]; exact add_mem hu.2 hv.2⟩)
    (fun _ r u hu ↦ ⟨Submodule.smul_mem _ r hu.1, by
      rw [map_smul]; exact Submodule.smul_mem _ r hu.2⟩)
    ha).2

/-- **Uniqueness of odd derivations**: a linear endomorphism of `ParitySignedSym G` satisfying the
parity Leibniz rule and agreeing with `δ` on generators equals `liftDerivation δ hδ`. No parity
condition on `d` is needed. -/
theorem eq_liftDerivation {d : ParitySignedSym G →ₗ[R] ParitySignedSym G}
    (hleibniz : ∀ {i : ZMod 2} {a : ParitySignedSym G}, a ∈ paritySignedSymPiece G i →
      ∀ b : ParitySignedSym G, d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b))
    (hgen : ∀ x, d (generator G x) = δ x) : d = liftDerivation δ hδ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_parity_leibniz (fun {i a} ha b ↦ ?_) fun x ↦ ?_
  · simp only [LinearMap.sub_apply, hleibniz ha, liftDerivation_mul hδ ha, sub_mul, mul_sub,
      Units.smul_def, zsmul_sub]
    abel
  · simp [hgen]

end Lift

/-- **Odd derivations are free on generators**: an odd linear map `δ : V →ₗ[R] ParitySignedSym G`
extends uniquely to a linear endomorphism satisfying the parity Leibniz rule. -/
theorem existsUnique_odd_extension {δ : V →ₗ[R] ParitySignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (paritySignedSymPiece G) 1) :
    ∃! d : ParitySignedSym G →ₗ[R] ParitySignedSym G, d ∘ₗ generator G = δ ∧
      ∀ {i : ZMod 2} {a : ParitySignedSym G}, a ∈ paritySignedSymPiece G i →
        ∀ b : ParitySignedSym G, d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b) :=
  ⟨liftDerivation δ hδ, ⟨LinearMap.ext (liftDerivation_generator hδ), liftDerivation_mul hδ⟩,
    fun _ hd ↦ eq_liftDerivation hδ hd.2 fun x ↦ LinearMap.congr_fun hd.1 x⟩

/-- **The square of an odd parity-Leibniz map is determined on generators**: an odd linear
endomorphism of `ParitySignedSym G` satisfying the parity Leibniz rule squares to zero if and only
if its square vanishes on generators. -/
theorem comp_self_eq_zero_iff {d : ParitySignedSym G →ₗ[R] ParitySignedSym G}
    (hdeg : LinearMap.IsHomogeneous d (paritySignedSymPiece G) (paritySignedSymPiece G) 1)
    (hleibniz : ∀ {i : ZMod 2} {a : ParitySignedSym G}, a ∈ paritySignedSymPiece G i →
      ∀ b : ParitySignedSym G, d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b)) :
    d ∘ₗ d = 0 ↔ ∀ x, d (d (generator G x)) = 0 := by
  refine ⟨fun h x ↦ LinearMap.congr_fun h (generator G x), fun h ↦ ?_⟩
  ext a
  induction a using ParitySignedSym.induction with
  | algebraMap r => simp [map_algebraMap_of_parity_leibniz hleibniz]
  | generator x => exact h x
  | mul u v hu hv =>
    have hmul := comp_self_mul_of_parity_leibniz (fun hx ↦ hdeg.map_mem hx) hleibniz u v
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hu hv ⊢
    rw [hmul, hu, hv, zero_mul, mul_zero, add_zero]
  | add u v hu hv => simp_all

/-- The odd derivation extending `δ` squares to zero if and only if it annihilates `δ x` for every
generator `x : V`. -/
theorem liftDerivation_comp_self_eq_zero_iff {δ : V →ₗ[R] ParitySignedSym G}
    (hδ : LinearMap.IsHomogeneous δ G.piece (paritySignedSymPiece G) 1) :
    liftDerivation δ hδ ∘ₗ liftDerivation δ hδ = 0 ↔ ∀ x, liftDerivation δ hδ (δ x) = 0 := by
  simpa using comp_self_eq_zero_iff (isHomogeneous_liftDerivation hδ) (liftDerivation_mul hδ)

end ParitySignedSym

/-! ### Comparison with integer-graded odd derivations -/

namespace SignedSym

variable (H : InternalGrading R V ℤ)

/-- Composing a degree-one generator assignment into `SignedSym H` with `parityEquiv H` yields an
odd generator assignment into `ParitySignedSym H.parity`. -/
theorem isHomogeneous_parityEquiv_comp_of_degree_one {δ : V →ₗ[R] SignedSym H}
    (hδ : LinearMap.IsHomogeneous δ H.piece (signedSymPiece H) 1) :
    LinearMap.IsHomogeneous ((parityEquiv H).toLinearMap ∘ₗ δ)
      H.parity.piece (paritySignedSymPiece H.parity) 1 := by
  refine LinearMap.isHomogeneous_def.2 fun i x hx ↦ ?_
  rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, parityEquiv_mem_paritySignedSymPiece_iff]
  rw [InternalGrading.parity_piece] at hx
  exact map_mem_parityGrading_of_map_mem (fun hy ↦ hδ.map_mem hy) hx

/-- `SignedSym.parityEquiv H` intertwines the integer-graded odd derivation `liftDerivation δ hδ`
with the parity-only odd derivation extending `(parityEquiv H).toLinearMap ∘ₗ δ`. -/
theorem parityEquiv_liftDerivation {δ : V →ₗ[R] SignedSym H}
    (hδ : LinearMap.IsHomogeneous δ H.piece (signedSymPiece H) 1) (a : SignedSym H) :
    parityEquiv H (liftDerivation δ hδ a) =
      ParitySignedSym.liftDerivation ((parityEquiv H).toLinearMap ∘ₗ δ)
        (isHomogeneous_parityEquiv_comp_of_degree_one H hδ) (parityEquiv H a) := by
  let d' : ParitySignedSym H.parity →ₗ[R] ParitySignedSym H.parity :=
    (parityEquiv H).toLinearMap ∘ₗ liftDerivation δ hδ ∘ₗ (parityEquiv H).symm.toLinearMap
  have hd' : d' = ParitySignedSym.liftDerivation ((parityEquiv H).toLinearMap ∘ₗ δ)
      (isHomogeneous_parityEquiv_comp_of_degree_one H hδ) := by
    refine ParitySignedSym.eq_liftDerivation _ (fun {i u} hu v ↦ ?_) fun x ↦ ?_
    · have ha : (parityEquiv H).symm u ∈ parityGrading (signedSymPiece H) i :=
        (parityEquiv_symm_mem_parityGrading_iff H).2 hu
      have hl := leibniz_parityGrading_of_leibniz (liftDerivation_mul hδ) ha
        ((parityEquiv H).symm v)
      simpa only [d', LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul, map_add,
        Units.smul_def, map_zsmul, AlgEquiv.apply_symm_apply] using congrArg (parityEquiv H) hl
    · simp [d']
  simpa only [d', LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.symm_apply_apply] using LinearMap.congr_fun hd' (parityEquiv H a)

/-- Linear-map form of `parityEquiv_liftDerivation`: `parityEquiv H` intertwines
`SignedSym.liftDerivation` with `ParitySignedSym.liftDerivation`. -/
theorem parityEquiv_comp_liftDerivation {δ : V →ₗ[R] SignedSym H}
    (hδ : LinearMap.IsHomogeneous δ H.piece (signedSymPiece H) 1) :
    (parityEquiv H).toLinearMap ∘ₗ liftDerivation δ hδ =
      ParitySignedSym.liftDerivation ((parityEquiv H).toLinearMap ∘ₗ δ)
        (isHomogeneous_parityEquiv_comp_of_degree_one H hδ) ∘ₗ (parityEquiv H).toLinearMap := by
  ext a
  exact parityEquiv_liftDerivation H hδ a

end SignedSym

end TauCeti
