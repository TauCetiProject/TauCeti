/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Archimedean.ArtinMap
import TauCeti.FieldTheory.Kummer.AbsoluteGalois
import TauCeti.FieldTheory.Kummer.Degree
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Norm
import TauCeti.RingTheory.RootsOfUnity.Basic

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

/-- The norm-residue symbol at an infinite place. The first argument enters the archimedean
Artin map and the second supplies an `n`-th root. -/
def normResidueSymbol (a b : w.Completionˣ) : rootsOfUnity n w.Completion :=
  abelianizedKummerPairing w.Completion n b (infiniteArtinAt w a)

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
  rw [normResidueSymbol, ← hσ]
  exact algebraMap_abelianizedKummerPairing b σ hβ

/-- The archimedean Artin symbol moves every radical by the norm-residue symbol. -/
theorem normResidueSymbol_spec (a b : w.Completionˣ)
    (σ : Gal(AlgebraicClosure w.Completion/w.Completion))
    (hσ : (σ : TopologicalAbelianization Gal(AlgebraicClosure w.Completion/w.Completion)) =
      infiniteArtinAt w a)
    {β : AlgebraicClosure w.Completion}
    (hβ : β ^ n = algebraMap w.Completion (AlgebraicClosure w.Completion) (b : w.Completion)) :
    σ β = algebraMap w.Completion (AlgebraicClosure w.Completion)
      ((w.normResidueSymbol n a b : w.Completionˣ) : w.Completion) * β := by
  rw [normResidueSymbol, ← hσ]
  exact abelianizedKummerPairing_spec b σ hβ

/-- A trivial Artin symbol pairs trivially with every radical. -/
theorem normResidueSymbol_eq_one_of_infiniteArtinAt_eq_one (a b : w.Completionˣ)
    (ha : infiniteArtinAt w a = 1) : w.normResidueSymbol n a b = 1 := by
  rw [normResidueSymbol, ha]
  exact map_one (abelianizedKummerPairing w.Completion n b)

/-- At a complex place every norm-residue symbol is trivial. -/
@[simp]
theorem normResidueSymbol_eq_one_of_isComplex (hw : w.IsComplex) (a b : w.Completionˣ) :
    w.normResidueSymbol n a b = 1 :=
  w.normResidueSymbol_eq_one_of_infiniteArtinAt_eq_one a b
    (infiniteArtinAt_eq_one_of_isComplex w hw a)

/-- The symbol is multiplicative in the Artin argument. -/
theorem normResidueSymbol_mul_left (a a' b : w.Completionˣ) :
    w.normResidueSymbol n (a * a') b =
      w.normResidueSymbol n a b * w.normResidueSymbol n a' b :=
  map_mul ((abelianizedKummerPairing w.Completion n b).comp (infiniteArtinAt w)) a a'

/-- The symbol is multiplicative in the radical argument. -/
theorem normResidueSymbol_mul_right (a b b' : w.Completionˣ) :
    w.normResidueSymbol n a (b * b') =
      w.normResidueSymbol n a b * w.normResidueSymbol n a b' :=
  map_mul ((abelianizedKummerPairing w.Completion n).flip (infiniteArtinAt w a)) b b'

/-- The symbol of the identity in the Artin argument is trivial. -/
@[simp]
theorem normResidueSymbol_one_left (b : w.Completionˣ) :
    w.normResidueSymbol n 1 b = 1 :=
  w.normResidueSymbol_eq_one_of_infiniteArtinAt_eq_one 1 b (map_one _)

/-- The symbol of the identity in the radical argument is trivial. -/
@[simp]
theorem normResidueSymbol_one_right (a : w.Completionˣ) : w.normResidueSymbol n a 1 = 1 :=
  map_one ((abelianizedKummerPairing w.Completion n).flip (infiniteArtinAt w a))

/-- Inversion in the Artin argument inverts the norm-residue symbol. -/
@[simp]
theorem normResidueSymbol_inv_left (a b : w.Completionˣ) :
    w.normResidueSymbol n a⁻¹ b = (w.normResidueSymbol n a b)⁻¹ :=
  map_inv ((abelianizedKummerPairing w.Completion n b).comp (infiniteArtinAt w)) a

/-- Inversion in the radical argument inverts the norm-residue symbol. -/
@[simp]
theorem normResidueSymbol_inv_right (a b : w.Completionˣ) :
    w.normResidueSymbol n a b⁻¹ = (w.normResidueSymbol n a b)⁻¹ :=
  map_inv ((abelianizedKummerPairing w.Completion n).flip (infiniteArtinAt w a)) b

/-- Powers in the Artin argument become powers of the symbol. -/
theorem normResidueSymbol_pow_left (a b : w.Completionˣ) (k : ℕ) :
    w.normResidueSymbol n (a ^ k) b = w.normResidueSymbol n a b ^ k :=
  map_pow ((abelianizedKummerPairing w.Completion n b).comp (infiniteArtinAt w)) a k

/-- Powers in the radical argument become powers of the symbol. -/
theorem normResidueSymbol_pow_right (a b : w.Completionˣ) (k : ℕ) :
    w.normResidueSymbol n a (b ^ k) = w.normResidueSymbol n a b ^ k :=
  map_pow ((abelianizedKummerPairing w.Completion n).flip (infiniteArtinAt w a)) b k

/-- An `n`-th power in the Artin argument has trivial symbol. -/
@[simp]
theorem normResidueSymbol_pow_left_eq_one (a b : w.Completionˣ) :
    w.normResidueSymbol n (a ^ n) b = 1 := by
  rw [normResidueSymbol_pow_left]
  exact Subtype.ext ((mem_rootsOfUnity n _).mp (w.normResidueSymbol n a b).property)

/-- An `n`-th power in the radical argument has trivial symbol. -/
@[simp]
theorem normResidueSymbol_pow_right_eq_one (a b : w.Completionˣ) :
    w.normResidueSymbol n a (b ^ n) = 1 := by
  rw [normResidueSymbol_pow_right]
  exact Subtype.ext ((mem_rootsOfUnity n _).mp (w.normResidueSymbol n a b).property)

/-- In degree one every archimedean norm-residue symbol is trivial. -/
@[simp]
theorem normResidueSymbol_degree_one (a b : w.Completionˣ) :
    w.normResidueSymbol 1 a b = 1 :=
  Subsingleton.elim _ _

/-- The symbol is trivial precisely when the Artin symbol is trivial or the second argument is
an `n`-th power in the completion. -/
theorem normResidueSymbol_eq_one_iff (a b : w.Completionˣ) :
    w.normResidueSymbol n a b = 1 ↔ infiniteArtinAt w a = 1 ∨
      b ∈ (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_cases ha : infiniteArtinAt w a = 1
    · exact Or.inl ha
    let q : TopologicalAbelianization Gal(AlgebraicClosure w.Completion/w.Completion) :=
      infiniteArtinAt w a
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective q
    change (σ : TopologicalAbelianization Gal(AlgebraicClosure w.Completion/w.Completion)) =
      infiniteArtinAt w a at hσ
    have hσ' : σ ≠ 1 := fun h1 ↦ ha (hσ.symm.trans (h1 ▸ QuotientGroup.mk_one _))
    obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq
      (algebraMap w.Completion (AlgebraicClosure w.Completion) (b : w.Completion)) (NeZero.pos n)
    have hfix : σ β = β := by
      simpa only [h, Subgroup.coe_one, Units.val_one, map_one, one_mul] using
        w.normResidueSymbol_spec a b σ hσ hβ
    obtain ⟨c, hc⟩ := mem_range_algebraMap_of_fieldAbsoluteGaloisGroup_apply_eq w hσ' hfix
    have hc0 : c ≠ 0 := by
      intro h0
      exact ne_zero_of_pow_eq_algebraMap hβ (by rw [← hc, h0, map_zero])
    refine Or.inr ⟨Units.mk0 c hc0, Units.ext ?_⟩
    apply (algebraMap w.Completion (AlgebraicClosure w.Completion)).injective
    simpa only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, hc] using hβ
  · rintro (ha | ⟨c, rfl⟩)
    · exact w.normResidueSymbol_eq_one_of_infiniteArtinAt_eq_one a b ha
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
  rw [← coe_negOneRootsOfUnity, Subtype.coe_inj]
  have hζ : w.normResidueSymbol 2 a b = negOneRootsOfUnity ↔ w.normResidueSymbol 2 a b ≠ 1 :=
    ⟨fun h h1 ↦ negOneRootsOfUnity_ne_one two_ne_zero (h.symm.trans h1),
      fun h ↦ (rootsOfUnity.eq_one_or_eq_negOneRootsOfUnity _).resolve_left h⟩
  rw [hζ, ne_eq, normResidueSymbol_two_eq_one_iff w hw, not_or, not_lt, not_lt]
  have ha := (map_ne_zero (Completion.extensionEmbeddingOfIsReal hw)).2 a.ne_zero
  have hb := (map_ne_zero (Completion.extensionEmbeddingOfIsReal hw)).2 b.ne_zero
  exact and_congr (le_iff_lt_or_eq.trans (or_iff_left ha))
    (le_iff_lt_or_eq.trans (or_iff_left hb))

example (hw : w.IsReal) :
    (w.normResidueSymbol 2 (-1) (-1) : w.Completionˣ) = -1 := by
  apply (w.coe_normResidueSymbol_two_eq_neg_one_iff hw _ _).2
  simp

end NumberField.InfinitePlace
