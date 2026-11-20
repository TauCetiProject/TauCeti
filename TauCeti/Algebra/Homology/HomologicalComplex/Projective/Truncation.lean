/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.Algebra.Homology.Embedding.Regrade
public import TauCeti.Algebra.Homology.Embedding.Restriction.Homotopy
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Removing an exact lower tail of a complex of projectives

An integer-indexed chain complex of projectives that vanishes in sufficiently low degrees and
has no homology below `k` has a homotopy-equivalent model with no terms below `k`. In cochain
notation the model is the good truncation `CochainComplex.truncLE`. Its cutoff term is a direct
summand of the original term, so truncation preserves finite generation for complexes of modules.
It introduces no terms beyond an existing upper bound in chain notation.

This is the one-sided shortening argument of Calmès et al., *Hermitian K-theory for stable
∞-categories III: Grothendieck–Witt groups of rings*, Lemma 1.1.6 and Remark 1.1.7.
-/

public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CochainComplex

/-- In a complex strictly bounded above and exact in degrees `> k`, projectivity of the terms
in degrees `> k` makes the inclusion of cycles at `k` split. -/
theorem isSplitMono_iCycles_of_isLE (K : CochainComplex C ℤ) (k b : ℤ) [K.IsStrictlyLE b]
    [K.IsLE k] (hP : ∀ i, k < i → Projective (K.X i)) : IsSplitMono (K.iCycles k) := by
  have step (i : ℤ) (hi : k ≤ i) (h : IsSplitMono (K.iCycles (i + 1))) :
      IsSplitMono (K.iCycles i) := by
    have : Projective (K.X (i + 1)) := hP _ (by omega)
    have : Projective (K.cycles (i + 1)) :=
      (Retract.mk _ _ (IsSplitMono.id (K.iCycles (i + 1)))).projective
    -- Exactness one degree up identifies the quotient by cycles with the next cycles.
    have hS := K.shortExact_mk_iCycles_toCycles i (i + 1) (by simp)
      (K.exactAt_of_isLE k _ (by omega))
    exact hS.splittingOfProjective.isSplitMono_f
  have split (n : ℕ) : ∀ i, k ≤ i → b - i ≤ (n : ℤ) → IsSplitMono (K.iCycles i) := by
    induction n with
    | zero =>
      intro i _ hi
      have : IsIso (K.iCycles i) := K.isIso_iCycles i (i + 1) (by simp)
        ((K.isZero_of_isStrictlyLE b (i + 1) (by omega)).eq_of_tgt _ _)
      infer_instance
    | succ n ih =>
      intro i hi hib
      exact step i hi (ih (i + 1) (by omega) (by omega))
  exact split (b - k).toNat k le_rfl (by omega)

/-- Every term of good truncation is a retract of the corresponding original term if the
cutoff cycles split off. In particular no upper homological degree is added by truncation. -/
noncomputable def retractTruncLEX (K : CochainComplex C ℤ) (k i : ℤ)
    [IsSplitMono (K.iCycles k)] : Retract ((K.truncLE k).X i) (K.X i) := by
  -- Away from the cutoff the truncation term is the unchanged term or zero.
  by_cases hi : i < k
  · exact Retract.ofIso (K.truncLEXIso k i hi)
  by_cases he : i = k
  · subst i
    exact (Retract.ofIso (K.truncLEXIsoCycles k)).trans
      ⟨K.iCycles k, retraction (K.iCycles k), IsSplitMono.id _⟩
  · exact ⟨0, 0, ((K.truncLE k).isZero_of_isStrictlyLE k i (by omega)).eq_of_src _ _⟩

/-- The inclusion of good truncation is a homotopy equivalence for a bounded-above complex of
projectives whose homology vanishes above the cutoff. -/
theorem homotopyEquivalences_ιTruncLE (K : CochainComplex C ℤ) (k b : ℤ)
    [K.IsStrictlyLE b] [K.IsLE k] (hP : ∀ i, Projective (K.X i)) :
    homotopyEquivalences C (.up ℤ) (K.ιTruncLE k) := by
  have := K.isSplitMono_iCycles_of_isLE k b (fun i _ ↦ hP i)
  have hT (i : ℤ) : Projective ((K.truncLE k).X i) := (K.retractTruncLEX k i).projective
  have := CochainComplex.isKProjective_of_projective K b
  have := CochainComplex.isKProjective_of_projective (K.truncLE k) k
  exact (IsKProjective.quasiIso_iff _).mp inferInstance

end CochainComplex

namespace ChainComplex

open ComplexShape

/-- If a bounded-below complex of projectives is exact below `k`, it is homotopy equivalent to a
complex supported in degrees `≥ k` whose terms are retracts of the original terms. -/
theorem exists_homotopyEquiv_of_exactAt_below (K : ChainComplex C ℤ) (k a : ℤ)
    (ha : ∀ i < a, IsZero (K.X i)) (hP : ∀ i, Projective (K.X i))
    (hK : ∀ i < k, K.ExactAt i) :
    ∃ L : ChainComplex C ℤ, (∀ i < k, IsZero (L.X i)) ∧
      (∀ i, Nonempty (Retract (L.X i) (K.X i))) ∧ Nonempty (HomotopyEquiv L K) := by
  let E := regradeEquivalence C k
  let M := E.functor.obj K
  have : M.IsStrictlyLE (k - a) := (M.isStrictlyLE_iff _).2 (fun i hi ↦ ha (k - i) (by omega))
  have : M.IsLE 0 := (M.isLE_iff 0).2 (fun i hi ↦ by
    rw [exactAt_iff_isZero_homology]
    exact (hK (k - i) (by omega)).isZero_homology.of_iso (regradeHomologyIso k K i))
  have hMP (i : ℤ) : Projective (M.X i) := hP (k - i)
  let L := E.inverse.obj (M.truncLE 0)
  refine ⟨L, fun i hi ↦ (M.truncLE 0).isZero_of_isStrictlyLE 0 (k - i) (by omega), ?_, ?_⟩
  · have := M.isSplitMono_iCycles_of_isLE 0 (k - a) (fun i _ ↦ hMP i)
    intro i
    exact ⟨(M.retractTruncLEX 0 (k - i)).trans
      (Retract.ofIso ((HomologicalComplex.eval C _ i).mapIso (E.unitIso.app K).symm))⟩
  · obtain ⟨e, -⟩ := M.homotopyEquivalences_ιTruncLE 0 (k - a) hMP
    exact ⟨(e.restriction (embeddingDownIntUpIntSub k)).trans
      (HomotopyEquiv.ofIso (E.unitIso.app K).symm)⟩

/-- A bounded complex of finitely generated projective left modules has a finite-projective
model supported in `[k, b]` up to homotopy equivalence exactly when its homology vanishes below
`k`, where `b` is any upper bound on the terms of the original complex. -/
theorem exists_homotopyEquiv_finite_projective_iff {R : Type u} [Ring R]
    (K : ChainComplex (ModuleCat.{v} R) ℤ) (k a b : ℤ)
    (ha : ∀ i < a, IsZero (K.X i)) (hb : ∀ i > b, IsZero (K.X i))
    (hF : ∀ i, Module.Finite R (K.X i)) (hP : ∀ i, Module.Projective R (K.X i)) :
    (∃ L : ChainComplex (ModuleCat.{v} R) ℤ,
      (∀ i, i < k ∨ b < i → IsZero (L.X i)) ∧
      (∀ i, Module.Finite R (L.X i) ∧ Module.Projective R (L.X i)) ∧
      Nonempty (HomotopyEquiv L K)) ↔ ∀ i < k, IsZero (K.homology i) := by
  constructor
  · rintro ⟨L, hL, -, ⟨e⟩⟩ i hi
    exact ((ExactAt.of_isZero (hL i (.inl hi))).isZero_homology).of_iso
      (asIso (homologyMap e.hom i)).symm
  · intro hK
    have hProj (i : ℤ) : Projective (K.X i) :=
      have := hP i
      inferInstance
    obtain ⟨L, hL, hR, he⟩ := K.exists_homotopyEquiv_of_exactAt_below k a ha hProj
      (fun i hi ↦ (exactAt_iff_isZero_homology _ _).mpr (hK i hi))
    refine ⟨L, fun i hi ↦ ?_, fun i ↦ ?_, he⟩
    · rcases hi with hi | hi
      · exact hL i hi
      · obtain ⟨r⟩ := hR i
        exact (IsZero.iff_id_eq_zero _).mpr (r.retract.symm.trans
          (by rw [(hb i hi).eq_of_tgt r.i 0, zero_comp]))
    · obtain ⟨r⟩ := hR i
      have := hF i
      have := hP i
      exact ⟨Module.Finite.of_surjective r.r.hom ((ModuleCat.epi_iff_surjective _).mp
        r.instIsSplitEpiR.epi), Module.Projective.of_split r.i.hom r.r.hom
          (ModuleCat.hom_ext_iff.mp r.retract)⟩

end ChainComplex
