/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Loop
public import TauCeti.Algebra.Lie.Presentation.Basic

/-!
# Word-length grading of a free Lie algebra

The homogeneous piece of length `n` is spanned by bracketed words with `n` leaves.
These pieces form an internal Lie grading over any commutative ring, without a
basis or a characteristic-zero hypothesis.

The grading identifies lower central terms by word length and supports degree
truncations of free Lie algebras.

Adapted from `Mei/Algebra/Lie/Free/Grading.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`68536122a97fed8e87bc6870b9427151971b9ab2` (Apache 2.0).

## References

* `LieAlgebra.loopAlgebra` and `LieAlgebra.LoopAlgebra.toFinsupp`: loop algebras and
  their coefficients.
* `TauCeti.FreeLieAlgebra.lieSpan_range_of_eq_top`: Lie generation by the canonical generators.
-/

public section

open scoped TensorProduct

namespace TauCeti.FreeLieAlgebra

variable (R : Type*) [CommRing R] {S : Type*}

local notation "F" => _root_.FreeLieAlgebra R S

-- Supply the endomorphism Lie ring required by `LieAlgebra.ad`.
attribute [local instance] LieRing.ofAssociativeRing

/-- Evaluate a bracketed word in the canonical generators of the free Lie algebra. -/
noncomputable def word : FreeMagma S → F
  | .of s => _root_.FreeLieAlgebra.of R s
  | .mul u v => ⁅word u, word v⁆

/-- A single-leaf word is the corresponding free generator. -/
@[simp]
theorem word_of (s : S) : word R (FreeMagma.of s) = _root_.FreeLieAlgebra.of R s := (rfl)

/-- Combining two bracketed words evaluates to their Lie bracket. -/
@[simp]
theorem word_mul (u v : FreeMagma S) : word R (u * v) = ⁅word R u, word R v⁆ := (rfl)

/-- The span of bracketed words of prescribed length. -/
noncomputable def homogeneousSubmodule (S : Type*) (n : ℕ) :
    Submodule R (_root_.FreeLieAlgebra R S) :=
  Submodule.span R (word R '' {w : FreeMagma S | w.length = n})

/-- The word-span description of a homogeneous piece. -/
theorem homogeneousSubmodule_def (S : Type*) (n : ℕ) :
    homogeneousSubmodule R S n =
      Submodule.span R (word R '' {w : FreeMagma S | w.length = n}) := (rfl)

/-- A bracketed word lies in the piece given by its number of leaves. -/
theorem word_mem_homogeneousSubmodule (w : FreeMagma S) :
    word R w ∈ homogeneousSubmodule R S w.length :=
  Submodule.subset_span ⟨w, rfl, rfl⟩

/-- Bracketed words span the free Lie algebra as a module. -/
theorem span_range_word (S : Type*) :
    Submodule.span R (Set.range (word R : FreeMagma S → _root_.FreeLieAlgebra R S)) = ⊤ := by
  let P := Submodule.span R (Set.range (word R : FreeMagma S → _root_.FreeLieAlgebra R S))
  have hlie (x : _root_.FreeLieAlgebra R S) (hx : x ∈ P)
      (y : _root_.FreeLieAlgebra R S) (hy : y ∈ P) : ⁅x, y⁆ ∈ P := by
    refine LinearMap.BilinMap.apply_apply_mem_of_mem_span P _ _
      (LieAlgebra.ad R (_root_.FreeLieAlgebra R S)).toLinearMap ?_ x y hx hy
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    rw [LieHom.coe_toLinearMap, LieAlgebra.ad_apply, ← word_mul]
    exact Submodule.subset_span ⟨u * v, rfl⟩
  let K : LieSubalgebra R (_root_.FreeLieAlgebra R S) :=
    { P with lie_mem' := fun {x y} hx hy => hlie x hx y hy }
  have hK : LieSubalgebra.lieSpan R (_root_.FreeLieAlgebra R S)
      (Set.range (_root_.FreeLieAlgebra.of R)) ≤ K := by
    rw [LieSubalgebra.lieSpan_le]
    rintro _ ⟨s, rfl⟩
    exact Submodule.subset_span ⟨FreeMagma.of s, word_of R s⟩
  rw [TauCeti.FreeLieAlgebra.lieSpan_range_of_eq_top] at hK
  apply top_unique
  exact fun x _ => hK (LieSubalgebra.mem_top x)

/-- The homogeneous word spans together generate the whole free Lie algebra. -/
theorem iSup_homogeneousSubmodule_eq_top (S : Type*) :
    (⨆ n : ℕ, homogeneousSubmodule R S n) = ⊤ := by
  apply top_unique
  rw [← span_range_word R S, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  exact le_iSup (homogeneousSubmodule R S) w.length (word_mem_homogeneousSubmodule R w)

/-- Bracketing homogeneous words adds their lengths. -/
instance homogeneousSubmodule_gradedBracket :
    SetLike.GradedBracket (homogeneousSubmodule R S) (homogeneousSubmodule R S) where
  bracket_mem := by
    intro i j x y hx hy
    refine LinearMap.BilinMap.apply_apply_mem_of_mem_span
      (homogeneousSubmodule R S (i + j)) _ _ (LieAlgebra.ad R F).toLinearMap ?_ x y hx hy
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [LieHom.coe_toLinearMap, LieAlgebra.ad_apply, ← word_mul]
    have h := word_mem_homogeneousSubmodule R (u * v)
    have hu' : u.length = i := hu
    have hv' : v.length = j := hv
    simpa only [FreeMagma.length, hu', hv', vadd_eq_add] using h

private noncomputable def loopLift :
    F →ₗ⁅R⁆ LieAlgebra.loopAlgebra R ℕ F :=
  _root_.FreeLieAlgebra.lift R fun s =>
    AddMonoidAlgebra.single 1 1 ⊗ₜ[R] _root_.FreeLieAlgebra.of R s

private theorem loopLift_word (w : FreeMagma S) :
    loopLift R (word R w) = AddMonoidAlgebra.single w.length 1 ⊗ₜ[R] word R w := by
  induction w with
  | ih1 s => simp [loopLift]
  | ih2 u v hu hv =>
    rw [word_mul, LieHom.map_lie, hu, hv, LieAlgebra.ExtendScalars.bracket_tmul]
    simp only [AddMonoidAlgebra.single_mul_single, one_mul, FreeMagma.length]

private theorem loopLift_homogeneous_coeff (n : ℕ) {x : F}
    (hx : x ∈ homogeneousSubmodule R S n) :
    LieAlgebra.LoopAlgebra.toFinsupp R ℕ F (loopLift R x) = Finsupp.single n x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    have hw' : w.length = n := hw
    rw [loopLift_word, LieAlgebra.LoopAlgebra.toFinsupp_single_tmul, hw']
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, Finsupp.single_add]
  | smul r x _ hx => simp only [map_smul, hx, Finsupp.smul_single]

variable (S)

/-- Word spans of distinct lengths are independent over any commutative coefficient ring. -/
theorem homogeneousSubmodule_iSupIndep : iSupIndep (homogeneousSubmodule R S) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum i hi
  have h := congrArg (fun x => LieAlgebra.LoopAlgebra.toFinsupp R ℕ F (loopLift R x)) hsum
  simp only [map_sum, map_zero] at h
  have hsingle : (∑ j ∈ s, Finsupp.single j (v j)) = 0 := by
    calc (∑ j ∈ s, Finsupp.single j (v j)) =
        ∑ j ∈ s, LieAlgebra.LoopAlgebra.toFinsupp R ℕ F (loopLift R (v j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact (loopLift_homogeneous_coeff R j (hv j hj)).symm
      _ = 0 := h
  have hcoeff := congrArg (fun f : ℕ →₀ F => f i) hsingle
  simpa [Finsupp.single_apply, hi] using hcoeff

/-- The word-length pieces give an internal direct sum of the free Lie algebra. -/
theorem isInternal_homogeneousSubmodule :
    _root_.DirectSum.IsInternal (homogeneousSubmodule R S) :=
  _root_.DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (homogeneousSubmodule_iSupIndep R S) (iSup_homogeneousSubmodule_eq_top R S)

/-- Word length grades the free Lie algebra over any commutative ring. -/
noncomputable instance gradedLieAlgebra : GradedLieAlgebra (homogeneousSubmodule R S) where
  toGradedBracket := inferInstance
  toDecomposition := (isInternal_homogeneousSubmodule R S).chooseDecomposition

/-- There are no bracketed words of length zero. -/
@[simp]
theorem homogeneousSubmodule_zero : homogeneousSubmodule R S 0 = ⊥ := by
  rw [homogeneousSubmodule_def, Submodule.span_eq_bot]
  rintro x ⟨w, hw, rfl⟩
  have hw' : w.length = 0 := hw
  exact False.elim ((Nat.ne_of_gt w.length_pos) hw')

/-- The piece of length one is spanned by the canonical free generators. -/
@[simp]
theorem homogeneousSubmodule_one :
    homogeneousSubmodule R S 1 = Submodule.span R (Set.range (_root_.FreeLieAlgebra.of R)) := by
  rw [homogeneousSubmodule_def]
  congr 1
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    cases w with
    | of s => exact ⟨s, word_of R s⟩
    | mul u v =>
      have hu := u.length_pos
      have hv := v.length_pos
      simp only [Set.mem_ofPred_eq, FreeMagma.length] at hw
      omega
  · rintro ⟨s, rfl⟩
    exact ⟨FreeMagma.of s, rfl, word_of R s⟩

end TauCeti.FreeLieAlgebra
