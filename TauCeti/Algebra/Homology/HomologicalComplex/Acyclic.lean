/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Functors preserving acyclicity of complexes in an adapted class

Let `F : C ⥤ D` be an additive functor between abelian categories and `P` a class of objects of
`C`, closed under isomorphisms, such that in a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` with `A`
and `B` in `P` also `C` lies in `P`, and `F` sends such a sequence to a short exact sequence. Then
`F` sends acyclic complexes `0 ⟶ Q⁰ ⟶ Q¹ ⟶ ⋯` with terms in `P` to acyclic complexes
(`HomologicalComplex.Acyclic.map_of_shortExact`). The cycles `Zⁿ` lie in `P` by induction, using
the short exact sequences `0 ⟶ Zⁿ ⟶ Qⁿ ⟶ Zⁿ⁺¹ ⟶ 0`, and `F` keeps these exact.

## References

* The Stacks Project, Derived Categories, Lemma 13.15.6 (tag 05T8).
* M. Kashiwara, P. Schapira, *Categories and Sheaves*, Grundlehren 332, Springer, 2006,
  Definition 13.3.4, where such classes are called `F`-injective.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe v₁ v₂ u₁ u₂

namespace HomologicalComplex.Acyclic

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
  (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)

variable {Q : CochainComplex C ℕ}

/-- The sequence `Zⁿ ⟶ Qⁿ ⟶ Zⁿ⁺¹` of the cycles of `Q`, which is
`HomologicalComplex.cyclesShortComplex` spelled out so that its terms can be computed. -/
private abbrev cyclesSequence (Q : CochainComplex C ℕ) (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (Q.iCycles n) (Q.toCycles n (n + 1)) (Q.iCycles_toCycles n (n + 1))

private lemma cyclesSequence_shortExact (n : ℕ) (hQ : Q.ExactAt (n + 1)) :
    (cyclesSequence Q n).ShortExact := by
  rw [cyclesSequence, ← cyclesShortComplex_def]
  exact Q.cyclesShortComplex_shortExact n (n + 1) (by simp) hQ

include hP in
private lemma prop_cycles_succ (hQ : Q.Acyclic) (hQP : ∀ n, P (Q.X n)) (n : ℕ) :
    P (Q.cycles (n + 1)) := by
  induction n with
  | zero =>
    have := Q.isIso_toCycles_zero_of_exactAt (hQ 0) (hQ 1)
    exact P.prop_of_iso (asIso (Q.toCycles 0 1)) (hQP 0)
  | succ n ih => exact hP _ (cyclesSequence_shortExact (n + 1) (hQ _)) ih (hQP _)

include hP hF in
private lemma shortExact_map_cyclesSequence (hQ : Q.Acyclic) (hQP : ∀ n, P (Q.X n)) (n : ℕ) :
    ((cyclesSequence Q (n + 1)).map F).ShortExact :=
  hF _ (cyclesSequence_shortExact (n + 1) (hQ _)) (prop_cycles_succ P hP hQ hQP n) (hQP _)

include hP hF in
private lemma epi_map_toCycles (hQ : Q.Acyclic) (hQP : ∀ n, P (Q.X n)) (n : ℕ) :
    Epi (F.map (Q.toCycles n (n + 1))) := by
  rcases n with _ | n
  · have := Q.isIso_toCycles_zero_of_exactAt (hQ 0) (hQ 1)
    infer_instance
  · exact (shortExact_map_cyclesSequence F P hP hF hQ hQP n).epi_g

include hP hF in
/-- **`F` preserves acyclicity of complexes in an adapted class.** Let `P` be a class of objects
closed under isomorphisms and under cokernels of monomorphisms, on whose short exact sequences
`F` is exact. Then `F` sends every acyclic complex `0 ⟶ Q⁰ ⟶ Q¹ ⟶ ⋯` with terms in `P` to an
acyclic complex. -/
theorem map_of_shortExact (hQ : Q.Acyclic) (hQP : ∀ n, P (Q.X n)) :
    ((F.mapHomologicalComplex _).obj Q).Acyclic := by
  have hmono (n : ℕ) : Mono (F.map (Q.iCycles (n + 1))) :=
    (shortExact_map_cyclesSequence F P hP hF hQ hQP n).mono_f
  rintro (_ | n)
  · -- in degree `0`, `F(Q⁰ ⟶ Q¹)` is the composite of `F(Q⁰ ≅ Z¹)` and `F(Z¹ ⟶ Q¹)`
    rw [HomologicalComplex.exactAt_iff' _ 0 0 1 (by simp) (by simp),
      ShortComplex.exact_iff_mono _ (by simp)]
    have := Q.isIso_toCycles_zero_of_exactAt (hQ 0) (hQ 1)
    have h : F.map (Q.d 0 1) = F.map (Q.toCycles 0 1) ≫ F.map (Q.iCycles 1) := by
      rw [← F.map_comp, toCycles_i]
    dsimp
    rw [h]
    infer_instance
  · -- in degree `n + 1`, compare with `F(Zⁿ⁺¹) ⟶ F(Qⁿ⁺¹) ⟶ F(Zⁿ⁺²)`
    rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
      (by simp only [CochainComplex.next]; rfl)]
    have := epi_map_toCycles F P hP hF hQ hQP n
    have := hmono (n + 1)
    let S₃ := ShortComplex.mk (F.map (Q.d n (n + 1))) (F.map (Q.toCycles (n + 1) (n + 2)))
      (by rw [← F.map_comp, d_toCycles, F.map_zero])
    let φ : S₃ ⟶ (cyclesSequence Q (n + 1)).map F :=
      { τ₁ := F.map (Q.toCycles n (n + 1)), τ₂ := 𝟙 _, τ₃ := 𝟙 _
        comm₁₂ := by simp [S₃, ← F.map_comp]
        comm₂₃ := by simp [S₃] }
    let φ' : S₃ ⟶ ((shortComplexFunctor' C _ n (n + 1) (n + 2)).obj Q).map F :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := F.map (Q.iCycles (n + 2))
        comm₁₂ := by simp [S₃]
        comm₂₃ := by simp [S₃, ← F.map_comp] }
    have : Epi φ.τ₁ := inferInstanceAs (Epi (F.map (Q.toCycles n (n + 1))))
    have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
    have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 _))
    have : Epi φ'.τ₁ := inferInstanceAs (Epi (𝟙 _))
    have : IsIso φ'.τ₂ := inferInstanceAs (IsIso (𝟙 _))
    have : Mono φ'.τ₃ := inferInstanceAs (Mono (F.map (Q.iCycles (n + 1 + 1))))
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ').1
      ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
        (shortExact_map_cyclesSequence F P hP hF hQ hQP n).exact)

end HomologicalComplex.Acyclic
