/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Derivation
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Parity.Grading
public import TauCeti.RingTheory.GradedAlgebra.GradeInvolution
import Mathlib.GroupTheory.GroupAction.Ring
import TauCeti.Algebra.Homology.DG.Algebra.Parity

/-!
# Odd derivations of the parity signed algebra

For an internal `ZMod 2`-grading `G` of an `R`-module `V`, an odd linear map
`δ : V →ₗ[R] ParitySignedSym G` extends uniquely to a linear endomorphism
`d = TauCeti.ParitySignedSym.liftDerivation δ hδ` satisfying the parity Leibniz rule

`d (a * b) = d a * b + ((-1 : ℤˣ) ^ i) • (a * d b)` for `a ∈ paritySignedSymPiece G i`.

No lift of `G` to an integer grading is used. Instead, the grade involution
`σ = TauCeti.gradeInvolution (paritySignedSymPiece G)` acts by `(-1 : ℤˣ) ^ i` on each homogeneous
piece, and instantiating the shared lower-triangular matrix construction
(`TauCeti.triangularDerivationMap`, `TauCeti.triangularDerivation`) with `σ` lifts
`x ↦ [[x, 0], [δ x, σ x]]` via `ParitySignedSym.lift` to an algebra map whose lower-left entry
satisfies `d (a * b) = d a * b + σ a * d b` on arbitrary elements.

The extension flips parity (`isHomogeneous_liftDerivation`). Because the square of any odd
parity-Leibniz map is an unsigned derivation (`TauCeti.map_map_mul_of_parity_leibniz`), `d ∘ₗ d`
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
* `TauCeti.SignedSym.isHomogeneous_parityEquiv_comp_of_isHomogeneous_one`,
  `TauCeti.SignedSym.parityEquiv_liftDerivation`, and
  `TauCeti.SignedSym.parityEquiv_comp_liftDerivation`: compatibility of `SignedSym.liftDerivation`
  with `ParitySignedSym.liftDerivation` across `SignedSym.parityEquiv`.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1) and Definition 2.48,
  where the contact homology differential is defined as an odd derivation of the free
  supercommutative algebra even when no canonical integer grading is fixed.
* This file instantiates the shared lower-triangular `2 × 2` matrix derivation construction from
  `TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Derivation` with `TauCeti.gradeInvolution`, and
  adapts the uniqueness and square-zero proof architecture of `TauCeti.SignedSym.liftDerivation`.
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
  ext a
  induction a using ParitySignedSym.induction with
  | algebraMap r => simp [map_algebraMap_of_leibniz (𝒜 := paritySignedSymPiece G) hD]
  | generator x => exact hgen x
  | mul u v hu hv =>
    simp only [LinearMap.zero_apply] at hu hv ⊢
    rw [map_mul_of_leibniz_of_map_eq_zero (𝒜 := paritySignedSymPiece G) hD u hv, hu, zero_mul]
  | add u v hu hv => simp_all

section Lift

variable (δ : V →ₗ[R] ParitySignedSym G)
variable {δ}
variable (hδ : LinearMap.IsHomogeneous δ G.piece (paritySignedSymPiece G) 1)

variable (δ) in
/-- The odd derivation of `ParitySignedSym G` extending an odd linear map `δ : V →ₗ[R]
ParitySignedSym G`. It satisfies the parity Leibniz rule (`liftDerivation_mul`), flips parity
(`isHomogeneous_liftDerivation`), and is the unique such extension (`eq_liftDerivation`). -/
noncomputable def liftDerivation : ParitySignedSym G →ₗ[R] ParitySignedSym G :=
  triangularDerivation <|
    lift G
      (triangularDerivationMap (generator G)
        (gradeInvolution (paritySignedSymPiece G)).toAlgHom δ)
      fun i j x y hx hy ↦ by
        have hgx := generator_mem_paritySignedSymPiece G hx
        have hgy := generator_mem_paritySignedSymPiece G hy
        exact triangularDerivationMap_mul_eq_smul_mul (generator G)
          (gradeInvolution (paritySignedSymPiece G)).toAlgHom δ
          (s₁ := (-1 : ℤˣ) ^ i) (s₂ := (-1 : ℤˣ) ^ j) (c := (-1 : ℤˣ) ^ (i * j))
          (generator_mul_generator G hx hy)
          (by
            rw [show (-1 : ℤˣ) ^ (i * j) * (-1 : ℤˣ) ^ j = (-1 : ℤˣ) ^ ((i + 1) * j) by
              rw [add_mul, one_mul, uzpow_add]]
            exact mul_eq_uzpow_smul_mul G (hδ.map_mem hx) hgy)
          (by
            rw [show (-1 : ℤˣ) ^ (i * j) * (-1 : ℤˣ) ^ i = (-1 : ℤˣ) ^ (i * (j + 1)) by
              rw [mul_add, mul_one, uzpow_add]]
            exact mul_eq_uzpow_smul_mul G hgx (hδ.map_mem hy))
          (gradeInvolution_apply_of_mem hgx) (gradeInvolution_apply_of_mem hgy)

/-- The odd derivation extends the assignment on generators. -/
@[simp]
theorem liftDerivation_generator (x : V) : liftDerivation δ hδ (generator G x) = δ x := by
  simp [liftDerivation]

/-- On arbitrary elements, `liftDerivation` satisfies the Leibniz rule twisted by the grade
involution on the left factor. -/
theorem liftDerivation_mul_gradeInvolution (a b : ParitySignedSym G) :
    liftDerivation δ hδ (a * b) =
      liftDerivation δ hδ a * b +
        gradeInvolution (paritySignedSymPiece G) a * liftDerivation δ hδ b := by
  have htop : Algebra.adjoin R (Set.range (generator G)) = ⊤ :=
    top_unique fun x _ ↦ ParitySignedSym.induction G (algebraMap_mem _)
      (fun m ↦ Algebra.subset_adjoin ⟨m, rfl⟩) (fun _ _ ↦ mul_mem) (fun _ _ ↦ add_mem) x
  rw [liftDerivation, triangularDerivation_mul (gradeInvolution (paritySignedSymPiece G)).toAlgHom
    htop (by rintro _ ⟨x, rfl⟩; simp), AlgEquiv.coe_toAlgHom]

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
  map_algebraMap_of_leibniz (𝒜 := paritySignedSymPiece G) (liftDerivation_mul hδ) r

/-- The odd derivation annihilates the unit. -/
@[simp]
theorem liftDerivation_one : liftDerivation δ hδ 1 = 0 :=
  map_one_eq_zero_of_leibniz (𝒜 := paritySignedSymPiece G) (liftDerivation_mul hδ)

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
  | algebraMap r => simp [map_algebraMap_of_leibniz (𝒜 := paritySignedSymPiece G) hleibniz]
  | generator x => exact h x
  | mul u v hu hv =>
    have hmul := map_map_mul_of_parity_leibniz (fun hx ↦ hdeg.map_mem hx) hleibniz u v
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
theorem isHomogeneous_parityEquiv_comp_of_isHomogeneous_one {δ : V →ₗ[R] SignedSym H}
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
        (isHomogeneous_parityEquiv_comp_of_isHomogeneous_one H hδ) (parityEquiv H a) := by
  let d' : ParitySignedSym H.parity →ₗ[R] ParitySignedSym H.parity :=
    (parityEquiv H).toLinearMap ∘ₗ liftDerivation δ hδ ∘ₗ (parityEquiv H).symm.toLinearMap
  have hd' : d' = ParitySignedSym.liftDerivation ((parityEquiv H).toLinearMap ∘ₗ δ)
      (isHomogeneous_parityEquiv_comp_of_isHomogeneous_one H hδ) := by
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
        (isHomogeneous_parityEquiv_comp_of_isHomogeneous_one H hδ) ∘ₗ
          (parityEquiv H).toLinearMap := by
  ext a
  exact parityEquiv_liftDerivation H hδ a

end SignedSym

end TauCeti
