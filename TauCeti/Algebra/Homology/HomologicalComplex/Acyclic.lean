/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Functors preserving acyclicity of complexes in an adapted class

Let `F : C ⥤ D` be an additive functor between abelian categories and `P` a class of objects of
`C`, closed under isomorphisms, such that in a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` with `A`
and `B` in `P` also `C` lies in `P`, and `F` sends such a sequence to a short exact sequence. Then
`F` sends acyclic complexes `0 ⟶ Q⁰ ⟶ Q¹ ⟶ ⋯` with terms in `P` to acyclic complexes
(`HomologicalComplex.Acyclic.map_of_shortExact`), and likewise acyclic complexes indexed by `ℤ`
with terms in `P` which vanish below some degree
(`HomologicalComplex.Acyclic.map_of_shortExact_of_isStrictlyGE`). The cycles `Zⁿ` lie in `P` by
induction, using the short exact sequences `0 ⟶ Zⁿ ⟶ Qⁿ ⟶ Zⁿ⁺¹ ⟶ 0`, and `F` keeps these exact;
this gives exactness of `F(Q)` degree by degree
(`HomologicalComplex.mapHomologicalComplex_obj_exactAt_of_exact_map`).

## References

* The Stacks Project, Derived Categories, Lemma 13.15.6 (tag 05T8).
* M. Kashiwara, P. Schapira, *Categories and Sheaves*, Grundlehren 332, Springer, 2006,
  Definition 13.3.4, where such classes are called `F`-injective.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe v₁ v₂ u₁ u₂

namespace HomologicalComplex

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]

/-- Let `i ⟶ j ⟶ k` be consecutive degrees of a complex `Q`, with cycles `Zⱼ` and `Zₖ`. If `F`
keeps the cycle sequence `Zⱼ ⟶ Qⱼ ⟶ Zₖ` exact, sends `Qᵢ ⟶ Zⱼ` to an epimorphism and `Zₖ ⟶ Qₖ` to
a monomorphism, then `F(Q)` is exact in degree `j`. -/
theorem mapHomologicalComplex_obj_exactAt_of_exact_map {ι : Type*} {c : ComplexShape ι}
    (Q : HomologicalComplex C c) {i j k : ι} (hi : c.prev j = i) (hk : c.next j = k)
    [Epi (F.map (Q.toCycles i j))] [Mono (F.map (Q.iCycles k))]
    (h : ((ShortComplex.mk (Q.iCycles j) (Q.toCycles j k) (Q.iCycles_toCycles j k)).map F).Exact) :
    ((F.mapHomologicalComplex c).obj Q).ExactAt j := by
  rw [HomologicalComplex.exactAt_iff' _ i j k hi hk]
  -- compare `F(Qᵢ) ⟶ F(Qⱼ) ⟶ F(Zₖ)` with the image of the cycle sequence and with `F(Q)`
  let S₃ := ShortComplex.mk (F.map (Q.d i j)) (F.map (Q.toCycles j k))
    (by rw [← F.map_comp, d_toCycles, F.map_zero])
  let φ : S₃ ⟶ (ShortComplex.mk (Q.iCycles j) (Q.toCycles j k) (Q.iCycles_toCycles j k)).map F :=
    { τ₁ := F.map (Q.toCycles i j), τ₂ := 𝟙 _, τ₃ := 𝟙 _
      comm₁₂ := by simp [S₃, ← F.map_comp]
      comm₂₃ := by simp [S₃] }
  let φ' : S₃ ⟶ ((shortComplexFunctor' C _ i j k).obj Q).map F :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := F.map (Q.iCycles k)
      comm₁₂ := by simp [S₃]
      comm₂₃ := by simp [S₃, ← F.map_comp] }
  have : Epi φ.τ₁ := inferInstanceAs (Epi (F.map (Q.toCycles i j)))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 _))
  have : Epi φ'.τ₁ := inferInstanceAs (Epi (𝟙 _))
  have : IsIso φ'.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono φ'.τ₃ := inferInstanceAs (Mono (F.map (Q.iCycles k)))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ').1
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 h)

end HomologicalComplex

namespace HomologicalComplex.Acyclic

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
  (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)

section Nat

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
  · -- in degree `n + 1`, use the cycle sequences in degrees `n`, `n + 1` and `n + 2`
    have := epi_map_toCycles F P hP hF hQ hQP n
    have := hmono (n + 1)
    exact mapHomologicalComplex_obj_exactAt_of_exact_map F Q (i := n) (k := n + 2) (by simp)
      (by simp only [CochainComplex.next]; rfl)
      (shortExact_map_cyclesSequence F P hP hF hQ hQP n).exact

end Nat

section Int

variable {K : CochainComplex C ℤ}

include hP in
/-- In an acyclic complex `K` which vanishes below degree `b` and has terms in `P`, all cycles lie
in `P`. -/
private lemma prop_cycles_of_isStrictlyGE (b : ℤ) [K.IsStrictlyGE b] (hK : K.Acyclic)
    (hKP : ∀ n, P (K.X n)) (n : ℤ) : P (K.cycles n) := by
  -- up to degree `b`, the cycles vanish, as `Kⁿ⁻¹ = 0` maps onto `Zⁿ` by exactness
  have h₀ (n : ℤ) (hn : n ≤ b) : P (K.cycles n) := by
    have := epi_toCycles_of_exactAt (hK n) (CochainComplex.prev ℤ n)
    exact P.prop_of_iso ((K.isZero_of_isStrictlyGE b (n - 1)).iso
      ((K.isZero_of_isStrictlyGE b (n - 1)).of_epi (K.toCycles (n - 1) n))) (hKP _)
  -- above degree `b`, `Zⁿ⁺¹` is the cokernel of the monomorphism `Zⁿ ⟶ Kⁿ`
  rcases le_total n b with hn | hn
  · exact h₀ n hn
  · obtain ⟨k, rfl⟩ := Int.exists_add_of_le hn
    induction k with
    | zero => simpa using h₀ b le_rfl
    | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc]
      exact hP _ (K.shortExact_mk_iCycles_toCycles _ _ (by simp) (hK _)) (ih (by lia)) (hKP _)

include hP hF in
/-- **`F` preserves acyclicity of bounded below complexes in an adapted class.** Let `P` be a class
of objects closed under isomorphisms and under cokernels of monomorphisms, on whose short exact
sequences `F` is exact. Then `F` sends every acyclic complex `K` with terms in `P` which vanishes
below some degree `b` to an acyclic complex. -/
theorem map_of_shortExact_of_isStrictlyGE (b : ℤ) [K.IsStrictlyGE b] (hK : K.Acyclic)
    (hKP : ∀ n, P (K.X n)) : ((F.mapHomologicalComplex _).obj K).Acyclic := by
  intro n
  -- `F` keeps the cycle sequences `Zᵐ ⟶ Kᵐ ⟶ Zᵐ⁺¹` short exact
  have hS (m m' : ℤ) (h : m + 1 = m') :=
    hF _ (K.shortExact_mk_iCycles_toCycles m m' (by simpa using h) (hK _))
      (prop_cycles_of_isStrictlyGE P hP b hK hKP m) (hKP m)
  have : Epi (F.map (K.toCycles (n - 1) n)) := (hS (n - 1) n (by lia)).epi_g
  have : Mono (F.map (K.iCycles (n + 1))) := (hS (n + 1) (n + 1 + 1) rfl).mono_f
  exact mapHomologicalComplex_obj_exactAt_of_exact_map F K (CochainComplex.prev ℤ n)
    (CochainComplex.next ℤ n) (hS n (n + 1) rfl).exact

end Int

end HomologicalComplex.Acyclic
