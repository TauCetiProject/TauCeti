/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.LanguageMap

/-!
# Separating analytic classes in a countable sublanguage

Two disjoint analytic classes of relational configurations can be distinguished using only
countably many relation symbols, even when neither class depends on countably many symbols.
The coordinate disagreements give an open cover of a product of Polish parameter spaces;
second countability supplies the countable subcover. No countability assumption on the carrier
or relationality assumption on the language is needed.

On a countable carrier, analyticity of saturation under the logic action upgrades this reduction:
if the original classes share no orbit, their reducts can be chosen to share no orbit either.
This uses `analyticSet_iUnion_smul` and the equivariance of `LHom.reductConfiguration`.
-/

public section

universe u v w

open FirstOrder FirstOrder.Language MeasureTheory Set TopologicalSpace
open scoped Pointwise

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} {V : Type w}

/-- Disjoint analytic classes of configurations have disjoint images in some countable relational
symbol sublanguage. The language and the carrier can both be uncountable. -/
theorem exists_countable_sublanguage_separating
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hAB : Disjoint A B) :
    ∃ R : Set (Σ n, L.Relations n), R.Countable ∧
      Disjoint ((symbSublangIncl ∅ R).reductConfiguration '' A)
        ((symbSublangIncl ∅ R).reductConfiguration '' B) := by
  obtain ⟨X, _, _, f, hf, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hA
  obtain ⟨Y, _, _, g, hg, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hB
  let U : Atom L V → Set (X × Y) := fun p =>
    {z | (f z.1).eval p ≠ (g z.2).eval p}
  have hU_open (p : Atom L V) : IsOpen (U p) :=
    isOpen_ne_fun ((continuous_eval _).comp (hf.comp continuous_fst))
      ((continuous_eval _).comp (hg.comp continuous_snd))
  have hU_cover : (⋃ p, U p) = univ := by
    refine eq_univ_iff_forall.2 fun ⟨x, y⟩ => ?_
    have hne : f x ≠ g y := fun h =>
      disjoint_left.1 hAB (h ▸ mem_range_self x) (mem_range_self y)
    obtain ⟨a, ha⟩ : ∃ a : Atom L V, (f x).eval a ≠ (g y).eval a := by
      by_contra! hall
      exact hne (RelationalConfiguration.ext hall)
    exact mem_iUnion.2 ⟨a, ha⟩
  obtain ⟨S, hS, hS_eq⟩ := isOpen_iUnion_countable U hU_open
  rw [hU_cover] at hS_eq
  refine ⟨Atom.symbol '' S, hS.image _, disjoint_left.2 ?_⟩
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩ ⟨_, ⟨y, rfl⟩, hxy⟩
  have hz : (x, y) ∈ ⋃ p ∈ S, U p := hS_eq.symm ▸ mem_univ (x, y)
  obtain ⟨p, hpS, hzp⟩ := mem_iUnion₂.1 hz
  induction p using Atom.induction_atom with
  | h R t =>
    let r : (symbSublang ∅ (Atom.symbol '' S)).Relations _ :=
      ⟨R, ⟨atom R t, hpS, Atom.symbol_atom R t⟩⟩
    have heval := congrArg (fun c => c.eval (atom r t)) hxy
    simp only [LHom.eval_reductConfiguration, LHom.onAtom_atom, symbSublangIncl_onRelation, r]
      at heval
    exact hzp heval.symm

/-- On a countable carrier, analytic classes sharing no orbit have reducts to a countable
relational symbol sublanguage that still share no orbit. Neither class need be invariant. -/
theorem exists_countable_sublanguage_separating_orbits [Countable V]
    {A B : Set (RelationalConfiguration L V)} (hA : AnalyticSet A) (hB : AnalyticSet B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B,
      ¬ MulAction.orbitRel (Equiv.Perm V) (RelationalConfiguration L V) a b) :
    ∃ R : Set (Σ n, L.Relations n), R.Countable ∧
      ∀ a ∈ A, ∀ b ∈ B,
        ¬ MulAction.orbitRel (Equiv.Perm V) (RelationalConfiguration (symbSublang ∅ R) V)
          ((symbSublangIncl ∅ R).reductConfiguration a)
          ((symbSublangIncl ∅ R).reductConfiguration b) := by
  have hdisj : Disjoint A (⋃ σ : Equiv.Perm V, σ • B) := by
    refine disjoint_left.2 fun a ha hb => ?_
    obtain ⟨σ, hσ⟩ := mem_iUnion.1 hb
    obtain ⟨b, hbB, rfl⟩ := mem_smul_set.1 hσ
    exact hAB _ ha b hbB (MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨σ, rfl⟩))
  obtain ⟨R, hR, hsep⟩ :=
    exists_countable_sublanguage_separating hA (analyticSet_iUnion_smul hB) hdisj
  refine ⟨R, hR, fun a ha b hb hab => ?_⟩
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hab)
  exact disjoint_left.1 hsep ⟨a, ha, rfl⟩
    ⟨σ • b, mem_iUnion.2 ⟨σ, smul_mem_smul_set hb⟩,
      ((symbSublangIncl ∅ R).reductConfiguration_perm_smul σ b).trans hσ⟩

end TauCeti.RelationalConfiguration
