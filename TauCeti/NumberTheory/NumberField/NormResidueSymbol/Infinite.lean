/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Archimedean.ArtinMap
import TauCeti.FieldTheory.Kummer.Degree
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Norm

/-!
# Norm-residue symbols at infinite places

For an infinite place `w`, `w.normResidueSymbol n a b` is the root of unity by which the
archimedean Artin symbol of `a` moves an `n`-th root of `b`. The first argument enters the
Artin map, just as for the nonarchimedean norm-residue symbol. No primitive root is chosen
as a coordinate. The characterization works with every radical and every representative
of the Artin symbol.

The symbol is bimultiplicative, trivial on `n`-th powers, and trivial at complex places.
At a real place its quadratic value is `-1` exactly when both arguments are negative.
These are the infinite factors needed for norm-residue symbols over number fields.

## References

* J. S. Milne, *Class Field Theory*, Chapter VIII, §5, paragraph after Theorem 5.11,
  for the archimedean values. Our Artin argument comes first, transposing Milne's convention.
-/

public section

noncomputable section

namespace NumberField.InfinitePlace

open TauCeti TauCeti.ClassFieldTheory

variable {K : Type} [Field K] (w : InfinitePlace K) (n : ℕ) [NeZero n]
  [HasEnoughRootsOfUnity w.Completion n]

/-- The unique representative of the archimedean Artin symbol in the absolute Galois group. -/
private def symbolAut (a : w.Completionˣ) : Gal(AlgebraicClosure w.Completion/w.Completion) :=
  (QuotientGroup.mk_surjective (infiniteArtinAt w a)).choose

private theorem symbolAut_spec (a : w.Completionˣ) :
    (symbolAut w a : TopologicalAbelianization Gal(AlgebraicClosure w.Completion/w.Completion)) =
      infiniteArtinAt w a :=
  (QuotientGroup.mk_surjective (infiniteArtinAt w a)).choose_spec

private theorem symbolAut_eq (a : w.Completionˣ)
    (σ : Gal(AlgebraicClosure w.Completion/w.Completion))
    (hσ : (σ : TopologicalAbelianization Gal(AlgebraicClosure w.Completion/w.Completion)) =
      infiniteArtinAt w a) :
    symbolAut w a = σ := by
  exact (injective_iff_map_eq_one
    (QuotientGroup.mk' (commutator (Field.absoluteGaloisGroup w.Completion)).topologicalClosure)).2
    (fun _ h ↦ eq_one_of_mk_eq_one w h) ((symbolAut_spec w a).trans hσ.symm)

/-- An auxiliary radical, used only to construct the symbol. -/
private def symbolRoot (b : w.Completionˣ) : AlgebraicClosure w.Completion :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap w.Completion (AlgebraicClosure w.Completion)
    (b : w.Completion)) (NeZero.pos n)).choose

omit [HasEnoughRootsOfUnity w.Completion n] in
private theorem symbolRoot_pow (b : w.Completionˣ) :
    symbolRoot w n b ^ n =
      algebraMap w.Completion (AlgebraicClosure w.Completion) (b : w.Completion) :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap w.Completion (AlgebraicClosure w.Completion)
    (b : w.Completion)) (NeZero.pos n)).choose_spec

/-- The norm-residue symbol at an infinite place. The first argument enters the archimedean
Artin map and the second supplies an `n`-th root. -/
def normResidueSymbol (a b : w.Completionˣ) : rootsOfUnity n w.Completion :=
  (rootsOfUnityEquivOfPrimitiveRoots
    (algebraMap w.Completion (AlgebraicClosure w.Completion)).injective (by
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot w.Completion n
      exact ⟨ζ, (mem_primitiveRoots (NeZero.pos n)).2 hζ⟩)).symm
    (rootsOfUnity.mkOfPowEq (symbolAut w a (symbolRoot w n b) / symbolRoot w n b) (by
      rw [div_pow, ← map_pow, symbolRoot_pow, AlgEquiv.commutes, div_self (by simp)]))

variable {n}

/-- Read in the algebraic closure, the symbol is `σ β / β` for every lift of the Artin symbol
and every `n`-th root of the second argument. -/
theorem algebraMap_normResidueSymbol (a b : w.Completionˣ)
    (σ : Gal(AlgebraicClosure w.Completion/w.Completion))
    (hσ : (σ : TopologicalAbelianization Gal(AlgebraicClosure w.Completion/w.Completion)) =
      infiniteArtinAt w a)
    {β : AlgebraicClosure w.Completion}
    (hβ : β ^ n = algebraMap w.Completion (AlgebraicClosure w.Completion) (b : w.Completion)) :
    algebraMap w.Completion (AlgebraicClosure w.Completion)
      ((w.normResidueSymbol n a b : w.Completionˣ) : w.Completion) = σ β / β := by
  rw [normResidueSymbol, rootsOfUnityEquivOfPrimitiveRoots_symm_apply,
    rootsOfUnity.coe_mkOfPowEq, symbolAut_eq w a σ hσ]
  exact σ.apply_div_self_eq_of_pow_eq ((symbolRoot_pow w n b).trans hβ.symm)

/-- The archimedean Artin symbol moves every radical by the norm-residue symbol. -/
theorem normResidueSymbol_spec (a b : w.Completionˣ)
    (σ : Gal(AlgebraicClosure w.Completion/w.Completion))
    (hσ : (σ : TopologicalAbelianization Gal(AlgebraicClosure w.Completion/w.Completion)) =
      infiniteArtinAt w a)
    {β : AlgebraicClosure w.Completion}
    (hβ : β ^ n = algebraMap w.Completion (AlgebraicClosure w.Completion) (b : w.Completion)) :
    σ β = algebraMap w.Completion (AlgebraicClosure w.Completion)
      ((w.normResidueSymbol n a b : w.Completionˣ) : w.Completion) * β := by
  rw [algebraMap_normResidueSymbol w a b σ hσ hβ,
    div_mul_cancel₀ _ (ne_zero_of_pow_eq_algebraMap hβ)]

/-- A trivial Artin symbol pairs trivially with every radical. -/
theorem normResidueSymbol_eq_one_of_artin_eq_one (a b : w.Completionˣ)
    (ha : infiniteArtinAt w a = 1) : w.normResidueSymbol n a b = 1 := by
  apply Subtype.ext
  apply Units.ext
  apply (algebraMap w.Completion (AlgebraicClosure w.Completion)).injective
  rw [algebraMap_normResidueSymbol w a b 1 (by
    exact (QuotientGroup.mk_one _).trans ha.symm) (symbolRoot_pow w n b)]
  simp only [AlgEquiv.one_apply, div_self (ne_zero_of_pow_eq_algebraMap
    (symbolRoot_pow w n b)), Subgroup.coe_one, Units.val_one, map_one]

/-- At a complex place every norm-residue symbol is trivial. -/
@[simp]
theorem normResidueSymbol_eq_one_of_isComplex (hw : w.IsComplex) (a b : w.Completionˣ) :
    w.normResidueSymbol n a b = 1 :=
  w.normResidueSymbol_eq_one_of_artin_eq_one a b (infiniteArtinAt_eq_one_of_isComplex w hw a)

/-- The symbol is multiplicative in the Artin argument. -/
theorem normResidueSymbol_mul_left (a a' b : w.Completionˣ) :
    w.normResidueSymbol n (a * a') b =
      w.normResidueSymbol n a b * w.normResidueSymbol n a' b := by
  apply Subtype.ext
  apply Units.ext
  apply (algebraMap w.Completion (AlgebraicClosure w.Completion)).injective
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
  rw [algebraMap_normResidueSymbol w (a * a') b (symbolAut w a * symbolAut w a')
      (by
        rw [QuotientGroup.mk_mul, symbolAut_spec, symbolAut_spec]
        exact (map_mul (infiniteArtinAt w) a a').symm)
      (symbolRoot_pow w n b),
    algebraMap_normResidueSymbol w a b (symbolAut w a) (symbolAut_spec w a)
      (symbolRoot_pow w n b),
    algebraMap_normResidueSymbol w a' b (symbolAut w a') (symbolAut_spec w a')
      (symbolRoot_pow w n b)]
  exact (symbolAut w a).mul_apply_div_self_of_pow_eq (symbolAut w a') (symbolRoot_pow w n b)

/-- The symbol is multiplicative in the radical argument. -/
theorem normResidueSymbol_mul_right (a b b' : w.Completionˣ) :
    w.normResidueSymbol n a (b * b') =
      w.normResidueSymbol n a b * w.normResidueSymbol n a b' := by
  apply Subtype.ext
  apply Units.ext
  apply (algebraMap w.Completion (AlgebraicClosure w.Completion)).injective
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
  rw [algebraMap_normResidueSymbol w a (b * b') (symbolAut w a) (symbolAut_spec w a)
      (β := symbolRoot w n b * symbolRoot w n b') (by
        rw [mul_pow, symbolRoot_pow, symbolRoot_pow, Units.val_mul, map_mul]),
    algebraMap_normResidueSymbol w a b (symbolAut w a) (symbolAut_spec w a)
      (symbolRoot_pow w n b),
    algebraMap_normResidueSymbol w a b' (symbolAut w a) (symbolAut_spec w a)
      (symbolRoot_pow w n b'), map_mul, mul_div_mul_comm]

/-- An `n`-th power in the radical argument has trivial symbol. -/
@[simp]
theorem normResidueSymbol_pow_right_eq_one (a b : w.Completionˣ) :
    w.normResidueSymbol n a (b ^ n) = 1 := by
  apply Subtype.ext
  apply Units.ext
  apply (algebraMap w.Completion (AlgebraicClosure w.Completion)).injective
  rw [algebraMap_normResidueSymbol w a (b ^ n) (symbolAut w a) (symbolAut_spec w a)
    (β := algebraMap w.Completion (AlgebraicClosure w.Completion) (b : w.Completion)) (by simp)]
  simp

/-- The symbol of the identity in the Artin argument is trivial. -/
@[simp]
theorem normResidueSymbol_one_left (b : w.Completionˣ) :
    w.normResidueSymbol n 1 b = 1 :=
  w.normResidueSymbol_eq_one_of_artin_eq_one 1 b (map_one _)

/-- The symbol of the identity in the radical argument is trivial. -/
@[simp]
theorem normResidueSymbol_one_right (a : w.Completionˣ) :
    w.normResidueSymbol n a 1 = 1 := by
  simpa only [one_pow] using w.normResidueSymbol_pow_right_eq_one (n := n) a 1

/-- Powers in the Artin argument become powers of the symbol. -/
theorem normResidueSymbol_pow_left (a b : w.Completionˣ) (k : ℕ) :
    w.normResidueSymbol n (a ^ k) b = w.normResidueSymbol n a b ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, normResidueSymbol_mul_left, ih, pow_succ]

/-- Powers in the radical argument become powers of the symbol. -/
theorem normResidueSymbol_pow_right (a b : w.Completionˣ) (k : ℕ) :
    w.normResidueSymbol n a (b ^ k) = w.normResidueSymbol n a b ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, normResidueSymbol_mul_right, ih, pow_succ]

/-- An `n`-th power in the Artin argument has trivial symbol. -/
@[simp]
theorem normResidueSymbol_pow_left_eq_one (a b : w.Completionˣ) :
    w.normResidueSymbol n (a ^ n) b = 1 := by
  rw [normResidueSymbol_pow_left]
  exact Subtype.ext ((mem_rootsOfUnity n _).mp (w.normResidueSymbol n a b).property)

/-- In degree one every archimedean norm-residue symbol is trivial. -/
@[simp]
theorem normResidueSymbol_degree_one (a b : w.Completionˣ) :
    w.normResidueSymbol 1 a b = 1 := by
  simpa only [pow_one] using w.normResidueSymbol_pow_right_eq_one (n := 1) a b

/-- The symbol is trivial precisely when the Artin symbol is trivial or the radical is
already an `n`-th power in the completion. -/
theorem normResidueSymbol_eq_one_iff (a b : w.Completionˣ) :
    w.normResidueSymbol n a b = 1 ↔ infiniteArtinAt w a = 1 ∨
      b ∈ (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_cases ha : infiniteArtinAt w a = 1
    · exact Or.inl ha
    have hσ : symbolAut w a ≠ 1 := by
      intro h1
      exact ha ((symbolAut_spec w a).symm.trans (h1 ▸ QuotientGroup.mk_one _))
    have hfix : symbolAut w a (symbolRoot w n b) = symbolRoot w n b := by
      simpa only [h, Subgroup.coe_one, Units.val_one, map_one, one_mul] using
        w.normResidueSymbol_spec a b (symbolAut w a) (symbolAut_spec w a) (symbolRoot_pow w n b)
    obtain ⟨c, hc⟩ := mem_range_algebraMap_of_fieldAbsoluteGaloisGroup_apply_eq w hσ hfix
    have hc0 : c ≠ 0 := by
      intro h0
      exact ne_zero_of_pow_eq_algebraMap (symbolRoot_pow w n b) (by rw [← hc, h0, map_zero])
    refine Or.inr ⟨Units.mk0 c hc0, Units.ext ?_⟩
    apply (algebraMap w.Completion (AlgebraicClosure w.Completion)).injective
    simpa only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, hc] using
      symbolRoot_pow w n b
  · rintro (ha | ⟨c, rfl⟩)
    · exact w.normResidueSymbol_eq_one_of_artin_eq_one a b ha
    · exact w.normResidueSymbol_pow_right_eq_one a c

/-- At a real place the quadratic symbol is trivial exactly when at least one argument is
positive. -/
@[simp]
theorem normResidueSymbol_two_eq_one_iff (hw : w.IsReal) (a b : w.Completionˣ) :
    w.normResidueSymbol 2 a b = 1 ↔
      0 < Completion.extensionEmbeddingOfIsReal hw a ∨
      0 < Completion.extensionEmbeddingOfIsReal hw b := by
  rw [normResidueSymbol_eq_one_iff, infiniteArtinAt_eq_one_iff_of_isReal w hw]
  refine or_congr_right ⟨?_, fun hb ↦ Completion.mem_range_powMonoidHom (by decide) b ?_⟩
  · rintro ⟨c, hc⟩
    have hc' := congrArg (fun u : w.Completionˣ ↦ Completion.extensionEmbeddingOfIsReal hw u) hc
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, map_pow] at hc'
    exact hc' ▸ sq_pos_of_ne_zero ((map_ne_zero _).2 c.ne_zero)
  · intro _
    exact hb

/-- At a real place the quadratic norm-residue symbol is `-1` exactly when both arguments
are negative. -/
@[simp]
theorem coe_normResidueSymbol_two_eq_neg_one_iff (hw : w.IsReal) (a b : w.Completionˣ) :
    (w.normResidueSymbol 2 a b : w.Completionˣ) = -1 ↔
      Completion.extensionEmbeddingOfIsReal hw a < 0 ∧
      Completion.extensionEmbeddingOfIsReal hw b < 0 := by
  rw [← Units.val_eq_neg_one]
  have hζ := (mem_rootsOfUnity 2 _).mp (w.normResidueSymbol 2 a b).property
  have hsq : (((w.normResidueSymbol 2 a b : w.Completionˣ) : w.Completion)) ^ 2 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hζ
  have h1 : ((w.normResidueSymbol 2 a b : w.Completionˣ) : w.Completion) = 1 ↔
      w.normResidueSymbol 2 a b = 1 := by
    constructor
    · intro h
      exact Subtype.ext (Units.ext h)
    · intro h
      simp only [h, Subgroup.coe_one, Units.val_one]
  have ha0 := (map_ne_zero (Completion.extensionEmbeddingOfIsReal hw)).2 a.ne_zero
  have hb0 := (map_ne_zero (Completion.extensionEmbeddingOfIsReal hw)).2 b.ne_zero
  rw [← not_iff_not, not_and_or]
  have hcases := sq_eq_one_iff.mp hsq
  have heq : ¬ ((w.normResidueSymbol 2 a b : w.Completionˣ) : w.Completion) = -1 ↔
      ((w.normResidueSymbol 2 a b : w.Completionˣ) : w.Completion) = 1 := by
    grind
  rw [heq, h1, normResidueSymbol_two_eq_one_iff w hw]
  exact or_congr (by grind) (by grind)

example (hw : w.IsReal) :
    (w.normResidueSymbol 2 (-1) (-1) : w.Completionˣ) = -1 := by
  apply (w.coe_normResidueSymbol_two_eq_neg_one_iff hw _ _).2
  simp

end NumberField.InfinitePlace
