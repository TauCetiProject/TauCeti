/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.FormationClosed

/-!
# The first-order image fragment

The images of first-order formulas in `L_{ω₁ω}` form a formation-closed fragment. This is the
least formation-closed fragment: every such fragment contains the images of all first-order
formulas, by induction on their construction. It is countable precisely when the language has
countably many function and relation symbols.

This fragment allows results about formation-closed infinitary fragments to be specialized to
first-order logic, in particular when transferring omission of types. Membership is syntactic:
even a countable conjunction of copies of a first-order formula is outside the first-order image,
although it is semantically equivalent to that formula.

The bound-renaming lemma is generic in the branching carrier and free variables. It constructs
a first-order preimage by induction without choosing a presentation of an infinitary formula.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Cambridge University Press, 2016, Chapter 1,
  for fragments containing the first-order formulas.
-/

public section

universe u v u' uι

namespace FirstOrder.Language

variable {L : Language.{u, v}}

namespace BoundedFormula

/-- An embedded first-order formula has no countable or infinitary conjunction at its root. -/
@[simp]
theorem toInf_ne_iInf {ι : Type uι} {α : Type u'} {n : ℕ} (φ : L.BoundedFormula α n)
    (φs : ι → L.BoundedFormulaInf ι α n) : φ.toInf ≠ BoundedFormulaInf.iInf φs := by
  cases φ <;> simp

/-- An embedded first-order formula has no countable or infinitary disjunction at its root. -/
@[simp]
theorem toInf_ne_iSup {ι : Type uι} {α : Type u'} {n : ℕ} (φ : L.BoundedFormula α n)
    (φs : ι → L.BoundedFormulaInf ι α n) : φ.toInf ≠ BoundedFormulaInf.iSup φs := by
  cases φ <;> simp

end BoundedFormula

namespace BoundedFormulaInf

/-- Renaming bound positions preserves the image of first-order syntax, at any branching
carrier and with arbitrary free variables. -/
theorem mapBound_mem_range_toInf {ι : Type uι} {α : Type u'} {m n : ℕ}
    (φ : L.BoundedFormulaInf ι α m)
    (hφ : φ ∈ Set.range (BoundedFormula.toInf (ι := ι))) (f : Fin m → Fin n) :
    φ.mapBound f ∈ Set.range (BoundedFormula.toInf (ι := ι)) := by
  obtain ⟨ψ, rfl⟩ := hφ
  induction ψ generalizing n with
  | falsum => exact ⟨.falsum, by simp⟩
  | equal t₁ t₂ =>
    exact ⟨.equal (t₁.relabel (Sum.map id f)) (t₂.relabel (Sum.map id f)), by simp⟩
  | rel R ts => exact ⟨.rel R (fun i => (ts i).relabel (Sum.map id f)), by simp⟩
  | imp ψ θ ihψ ihθ =>
    obtain ⟨ψ', hψ'⟩ := ihψ f
    obtain ⟨θ', hθ'⟩ := ihθ f
    exact ⟨ψ'.imp θ', by simp [hψ', hθ']⟩
  | all ψ ih =>
    obtain ⟨ψ', hψ'⟩ := ih (Fin.snoc (fun i => (f i).castSucc) (Fin.last n))
    exact ⟨ψ'.all, by simp [hψ']⟩

end BoundedFormulaInf

namespace Fragment

/-- The fragment consisting exactly of the images of first-order formulas in `L_{ω₁ω}`. -/
def firstOrderImage (L : Language.{u, v}) : Fragment L where
  toSet := {p | ∃ φ : L.BoundedFormula Empty p.1, φ.toOmega = p.2}
  imp_left_mem' := by
    rintro n φ ψ ⟨χ, hχ⟩
    cases χ with
    | imp χ θ =>
      simp only [BoundedFormula.toInf_imp, BoundedFormulaInf.imp.injEq] at hχ
      exact ⟨χ, hχ.1⟩
    | _ => simp at hχ
  imp_right_mem' := by
    rintro n φ ψ ⟨χ, hχ⟩
    cases χ with
    | imp χ θ =>
      simp only [BoundedFormula.toInf_imp, BoundedFormulaInf.imp.injEq] at hχ
      exact ⟨θ, hχ.2⟩
    | _ => simp at hχ
  all_mem' := by
    rintro n φ ⟨χ, hχ⟩
    cases χ with
    | all χ =>
      simp only [BoundedFormula.toInf_all, BoundedFormulaInf.all.injEq] at hχ
      exact ⟨χ, hχ⟩
    | _ => simp at hχ
  iInf_mem' := by
    rintro n φs ⟨χ, hχ⟩ k
    exact (χ.toInf_ne_iInf φs hχ).elim
  iSup_mem' := by
    rintro n φs ⟨χ, hχ⟩ k
    exact (χ.toInf_ne_iSup φs hχ).elim

/-- A formula is in the first-order image exactly when it has a first-order preimage. -/
@[simp]
theorem mem_firstOrderImage {n : ℕ} {φ : L.BoundedFormulaω Empty n} :
    (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ firstOrderImage L ↔
      ∃ ψ : L.BoundedFormula Empty n, ψ.toOmega = φ :=
  Iff.rfl

/-- The first-order image contains the atomic formulas and is closed under first-order
formation and renaming of bound positions. -/
theorem formationClosed_firstOrderImage : (firstOrderImage L).FormationClosed where
  bot_mem _ := ⟨.falsum, by simp [BoundedFormulaInf.bot_def]⟩
  atomic_mem h := by
    cases h with
    | equal t₁ t₂ => exact ⟨.equal t₁ t₂, BoundedFormula.toInf_equal t₁ t₂⟩
    | rel R ts => exact ⟨.rel R ts, BoundedFormula.toInf_rel R ts⟩
  imp_mem := by
    intro n φ ψ hφ hψ
    obtain ⟨χ, hχ⟩ := mem_firstOrderImage.1 hφ
    obtain ⟨θ, hθ⟩ := mem_firstOrderImage.1 hψ
    exact ⟨χ.imp θ, by simp [hχ, hθ]⟩
  all_mem := by
    intro n φ hφ
    obtain ⟨χ, hχ⟩ := mem_firstOrderImage.1 hφ
    exact ⟨χ.all, by simp [hχ]⟩
  mapBound_mem f h := BoundedFormulaInf.mapBound_mem_range_toInf _ h f

/-- Every formation-closed fragment contains the image of every first-order formula. -/
theorem FormationClosed.toOmega_mem {A : Fragment L} (hA : A.FormationClosed) {n : ℕ}
    (φ : L.BoundedFormula Empty n) : (⟨n, φ.toOmega⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ A := by
  induction φ with
  | falsum => simpa [BoundedFormulaInf.bot_def] using hA.bot_mem _
  | equal t₁ t₂ => simpa using hA.atomic_mem (.equal t₁ t₂)
  | rel R ts => simpa using hA.atomic_mem (.rel R ts)
  | imp φ ψ ihφ ihψ => simpa using hA.imp_mem ihφ ihψ
  | all φ ih => simpa using hA.all_mem ih

/-- The first-order image is the least formation-closed fragment. -/
theorem FormationClosed.firstOrderImage_le {A : Fragment L} (hA : A.FormationClosed) :
    firstOrderImage L ≤ A := by
  rintro ⟨n, φ⟩ hφ
  obtain ⟨ψ, rfl⟩ := mem_firstOrderImage.1 hφ
  exact hA.toOmega_mem ψ

/-- Forming the formation closure of the empty set gives exactly the first-order image. -/
@[simp]
theorem formationClosure_empty : formationClosure (L := L) ∅ = firstOrderImage L :=
  le_antisymm ((formationClosure_le_iff formationClosed_firstOrderImage).2 (Set.empty_subset _))
    (formationClosed_formationClosure ∅).firstOrderImage_le

/-- Over a countable language, the first-order image fragment is countable. -/
theorem firstOrderImage_countable [Countable (Σ n, L.Functions n)]
    [Countable (Σ n, L.Relations n)] :
    (firstOrderImage L : Set (Σ n, L.BoundedFormulaω Empty n)).Countable := by
  rw [← formationClosure_empty]
  exact formationClosure_countable Set.countable_empty

/-- The first-order image is countable precisely when each sort of symbols is countable. -/
theorem firstOrderImage_countable_iff :
    (firstOrderImage L : Set (Σ n, L.BoundedFormulaω Empty n)).Countable ↔
      Countable (Σ n, L.Functions n) ∧ Countable (Σ n, L.Relations n) := by
  refine ⟨fun h => ⟨formationClosed_firstOrderImage.countable_functions h,
    formationClosed_firstOrderImage.countable_relations h⟩, fun ⟨hF, hR⟩ => ?_⟩
  exact firstOrderImage_countable

end Fragment

/-- The image of a first-order formula belongs to the first-order image fragment. -/
theorem BoundedFormula.toOmega_mem_firstOrderImage {n : ℕ} (φ : L.BoundedFormula Empty n) :
    (⟨n, φ.toOmega⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ Fragment.firstOrderImage L :=
  ⟨φ, rfl⟩

end FirstOrder.Language
