/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Nilpotent
public import TauCeti.Algebra.Lie.Basic

/-!
# The nilradical of a Lie algebra

The **nilradical** of a Lie algebra `L` is the supremum of its ideals that are nilpotent *as Lie
algebras*, built here as `TauCeti.LieAlgebra.nilradical R L`, the supremum of the ideals `I` with
`LieRing.IsNilpotent I`.  As soon as `L` is Noetherian that supremum is itself nilpotent, so it is
then a largest element: the largest nilpotent ideal.  It sits between the centre and the solvable
radical, and, again for Noetherian `L`, every one of its elements is `ad`-nilpotent.

Mathlib's `LieAlgebra.maxNilpotentIdeal R L` is a *different* ideal: the largest ideal on which the
ambient algebra `L` acts nilpotently.  It is contained in the nilradical
(`TauCeti.LieAlgebra.maxNilpotentIdeal_le_nilradical`), and the containment is strict in general.
The standard example is the two-dimensional nonabelian Lie algebra spanned by `x` and `y` with
`⁅x, y⁆ = y`: the span of `y` is an abelian, hence nilpotent, ideal, so it lies in the nilradical,
while `⁅L, span y⁆ = span y` says that `L` does not act nilpotently on it, and indeed no nonzero
ideal of that algebra is acted on nilpotently, so its `maxNilpotentIdeal` is `⊥`.  That algebra is
built in `TauCeti.Algebra.Lie.AffineLine`, where both ideals are computed and the containment is
witnessed to be strict by `TauCeti.LieAlgebra.AffineLine.maxNilpotentIdeal_lt_nilradical`.

## Nilpotency of an ideal, read inside the ambient algebra

Nilpotency of an ideal `I` as a Lie algebra is awkward to manipulate through the type `↥I`, so the
work below is done with Mathlib's `LieIdeal.lcs I L`, the descending series
`L ≥ ⁅I, L⁆ ≥ ⁅I, ⁅I, L⁆⁆ ≥ ⋯` of ideals of `L`.  The two readings agree:
`LieIdeal.isNilpotent_iff_exists_lcs_eq_bot` says that `I` is nilpotent as a Lie algebra exactly
when that series reaches `⊥`, equivalently (`LieIdeal.isNilpotent_iff_isNilpotent_ambient`) exactly
when `I` acts nilpotently on the whole of `L`.  From that description the sum of two nilpotent
ideals is nilpotent, which is what makes the supremum defining the nilradical well behaved.

These ambient readings all take a `LieIdeal` as their receiver, so they live in the root `LieIdeal`
namespace, where dot notation on that Mathlib type elaborates.

## Main definitions

* `TauCeti.LieAlgebra.nilradical`: the supremum of the ideals of `L` that are nilpotent as Lie
  algebras, the largest such ideal as soon as `L` is Noetherian.

## Main statements

* `LieIdeal.isNilpotent_iff_exists_lcs_eq_bot` and `LieIdeal.isNilpotent_iff_isNilpotent_ambient`:
  the two ambient readings of nilpotency of an ideal.
* `LieIdeal.isNilpotentSup`: a sum of nilpotent ideals is nilpotent.
* `LieIdeal.le_nilradical` and `TauCeti.LieAlgebra.nilradical_le_iff`: the two halves of the
  universal property of the supremum, neither needing a Noetherian assumption.
* `TauCeti.LieAlgebra.nilradicalIsNilpotent`: over a Noetherian Lie algebra the nilradical is
  nilpotent, so `LieIdeal.isNilpotent_iff_le_nilradical` characterises it.
* `TauCeti.LieAlgebra.maxNilpotentIdeal_le_nilradical`, `TauCeti.LieAlgebra.center_le_nilradical`
  and `TauCeti.LieAlgebra.nilradical_le_radical`: the standard containments.
* `TauCeti.LieAlgebra.isNilpotent_ad_of_mem_nilradical`: elements of the nilradical are
  `ad`-nilpotent.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1-3*][bourbaki1975], Chapter I, §4.
* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter II.
* The construction of `nilradical`, `nilradicalIsNilpotent`, and the largest-ideal API adapts
  Mathlib's `LieAlgebra.radical` development in `Mathlib.Algebra.Lie.Solvable`.
-/

public section

namespace LieIdeal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

section Module

variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M]

/-- The series `M ≥ ⁅I, M⁆ ≥ ⁅I, ⁅I, M⁆⁆ ≥ ⋯` attached to an ideal is antitone. -/
theorem lcs_antitone (I : LieIdeal R L) : Antitone (I.lcs M) :=
  antitone_nat_of_succ_le fun k ↦ by
    rw [lcs_succ]; exact LieSubmodule.lie_le_right _ _

/-- The series `M ≥ ⁅I, M⁆ ≥ ⁅I, ⁅I, M⁆⁆ ≥ ⋯` attached to an ideal is monotone in that ideal. -/
theorem lcs_mono {I J : LieIdeal R L} (h : I ≤ J) (k : ℕ) : I.lcs M k ≤ J.lcs M k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [lcs_succ, lcs_succ]
    exact LieSubmodule.mono_lie h ih

end Module

/-- The `k + 1`-st term of `⁅I, ⁅I, … ⁅I, L⁆…⁆⁆` lies in the image of the `k`-th term of the lower
central series of `I` as a module over itself.  This is the step that reads nilpotency of the Lie
algebra `↥I` back inside the ambient algebra. -/
theorem lcs_succ_le_map_lcs (I : LieIdeal R L) (k : ℕ) :
    I.lcs L (k + 1) ≤ LieSubmodule.map (LieSubmodule.incl I) (I.lcs ↥I k) := by
  induction k with
  | zero =>
    rw [lcs_zero, LieSubmodule.map_incl_top, lcs_succ, lcs_zero]
    exact LieSubmodule.lie_le_left _ _
  | succ k ih =>
    rw [lcs_succ I ↥I k, LieSubmodule.map_bracket_eq, lcs_succ I L (k + 1)]
    exact LieSubmodule.mono_lie_right _ ih

/-- The series `⁅I, ⁅I, … ⁅I, M⁆…⁆⁆` of submodules of `M`, read inside the ambient algebra, reaches
`⊥` exactly when the lower central series of `M` as a module over `I` does. -/
theorem lcs_eq_bot_iff (I : LieIdeal R L) (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule L M] [LieModule R L M] (k : ℕ) :
    I.lcs M k = ⊥ ↔ LieModule.lowerCentralSeries R (↥I) M k = ⊥ := by
  constructor
  · intro h
    rw [← LieSubmodule.toSubmodule_eq_bot, ← coe_lcs_eq, h]
    simp
  · intro h
    rw [← LieSubmodule.toSubmodule_eq_bot, coe_lcs_eq, h]
    simp

/-- **An ideal is nilpotent as a Lie algebra exactly when the series `⁅I, ⁅I, … ⁅I, L⁆…⁆⁆` of
ideals of the ambient algebra reaches `⊥`.** -/
theorem isNilpotent_iff_exists_lcs_eq_bot (I : LieIdeal R L) :
    LieRing.IsNilpotent I ↔ ∃ k, I.lcs L k = ⊥ := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := (LieModule.isNilpotent_iff R (↥I) (↥I)).1 h
    have hk' : I.lcs ↥I k = ⊥ := (lcs_eq_bot_iff I ↥I k).2 hk
    exact ⟨k + 1, le_bot_iff.1 (by simpa [hk'] using lcs_succ_le_map_lcs I k)⟩
  · rintro ⟨k, hk⟩
    have : LieModule.IsNilpotent (↥I) L :=
      (LieModule.isNilpotent_iff R (↥I) L).2 ⟨k, (lcs_eq_bot_iff I L k).1 hk⟩
    -- `↥I` acts on the submodule `↥I` through its action on `L`, so the two brackets are the
    -- same function and the comparison map is the inclusion.
    exact Function.Injective.lieModuleIsNilpotent
      (f := (LieHom.id : ↥I →ₗ⁅R⁆ ↥I)) (g := (LieSubmodule.incl I).toLinearMap)
      (fun _ _ ↦ rfl) (LieSubmodule.injective_incl I)

/-- **An ideal is nilpotent as a Lie algebra exactly when it acts nilpotently on the whole of the
ambient algebra.** -/
theorem isNilpotent_iff_isNilpotent_ambient (I : LieIdeal R L) :
    LieRing.IsNilpotent I ↔ LieModule.IsNilpotent (↥I) L := by
  rw [isNilpotent_iff_exists_lcs_eq_bot, LieModule.isNilpotent_iff R]
  exact exists_congr fun k ↦ lcs_eq_bot_iff I L k

/-- An ideal contained in a nilpotent ideal is itself nilpotent as a Lie algebra.  This is the
nilpotent counterpart of Mathlib's `LieAlgebra.le_solvable_ideal_solvable`. -/
theorem isNilpotent_of_le {I J : LieIdeal R L} (h : I ≤ J) (_ : LieRing.IsNilpotent J) :
    LieRing.IsNilpotent I :=
  (inclusion_injective h).lieAlgebra_isNilpotent

/-- A surjective Lie algebra homomorphism maps a nilpotent ideal to a nilpotent ideal. -/
theorem isNilpotent_map_of_surjective {L' : Type*} [LieRing L'] [LieAlgebra R L']
    (I : LieIdeal R L) (g : L →ₗ⁅R⁆ L') (hg : Function.Surjective g)
    (hI : LieRing.IsNilpotent I) : LieRing.IsNilpotent (I.map g) := by
  let _ : LieRing.IsNilpotent I := hI
  let f : I →ₗ⁅R⁆ I.map g :=
    { toFun := fun x ↦ ⟨g x, LieIdeal.mem_map x.property⟩
      map_add' := fun _ _ ↦ by ext; exact map_add g _ _
      map_smul' := fun _ _ ↦ by ext; exact map_smul g _ _
      map_lie' := fun {_ _} ↦ by ext; exact g.map_lie _ _ }
  apply Function.Surjective.lieAlgebra_isNilpotent (f := f)
  intro y
  obtain ⟨x, hx⟩ := LieIdeal.mem_map_of_surjective hg y.property
  exact ⟨x, Subtype.ext hx⟩

/-- A Lie algebra equivalence maps a nilpotent ideal to a nilpotent ideal. -/
theorem isNilpotent_map_equiv {L' : Type*} [LieRing L'] [LieAlgebra R L']
    (I : LieIdeal R L) (e : L ≃ₗ⁅R⁆ L') (hI : LieRing.IsNilpotent I) :
    LieRing.IsNilpotent (I.map e.toLieHom) :=
  isNilpotent_map_of_surjective I e.toLieHom e.surjective hI

/-- Every element of a nilpotent ideal acts nilpotently in the adjoint representation. -/
theorem isNilpotent_ad_of_mem (I : LieIdeal R L) [LieRing.IsNilpotent I] {x : L} (hx : x ∈ I) :
    IsNilpotent (LieAlgebra.ad R L x) := by
  let xI : I := ⟨x, hx⟩
  let _ : LieModule.IsNilpotent (↥I) L :=
    (isNilpotent_iff_isNilpotent_ambient I).mp inferInstance
  have haction : LieModule.toEnd R (↥I) L xI = LieAlgebra.ad R L x := by
    ext y
    rfl
  rw [← haction]
  exact LieModule.isNilpotent_toEnd_of_isNilpotent R (↥I) L xI

instance isNilpotentBot : LieRing.IsNilpotent (⊥ : LieIdeal R L) :=
  (isNilpotent_iff_exists_lcs_eq_bot _).2 ⟨1, by simp⟩

/-- The series of a supremum of two ideals is caught between the series of the two summands: after
`n` steps every summand of the bound has spent `i` steps inside `I` and `n - i` steps inside `J`.
This is the combinatorial heart of `LieIdeal.isNilpotentSup`. -/
theorem lcs_sup_le_iSup_inf (I J : LieIdeal R L) (n : ℕ) :
    (I ⊔ J).lcs L n ≤ ⨆ i : ℕ, I.lcs L i ⊓ J.lcs L (n - i) := by
  induction n with
  | zero => exact le_iSup_of_le 0 (by simp)
  | succ n ih =>
    rw [lcs_succ]
    refine (LieSubmodule.mono_lie_right _ ih).trans ?_
    rw [LieSubmodule.lie_iSup]
    refine iSup_le fun i ↦ ?_
    rw [LieSubmodule.sup_lie]
    refine sup_le ?_ ?_
    · refine le_iSup_of_le (i + 1) (le_inf ?_ ?_)
      · rw [lcs_succ]
        exact LieSubmodule.mono_lie_right _ inf_le_left
      · rw [Nat.succ_sub_succ]
        exact (LieSubmodule.lie_le_right _ _).trans inf_le_right
    · refine le_iSup_of_le i (le_inf ((LieSubmodule.lie_le_right _ _).trans inf_le_left) ?_)
      rcases le_or_gt i n with hi | hi
      · have : n + 1 - i = (n - i) + 1 := by omega
        rw [this, lcs_succ]
        exact LieSubmodule.mono_lie_right _ inf_le_right
      · have : n + 1 - i = 0 := by omega
        rw [this, lcs_zero]
        exact le_top

/-- **A supremum of two nilpotent ideals is nilpotent.** -/
instance isNilpotentSup (I J : LieIdeal R L) [LieRing.IsNilpotent I] [LieRing.IsNilpotent J] :
    LieRing.IsNilpotent (I ⊔ J : LieIdeal R L) := by
  obtain ⟨k, hk⟩ := (isNilpotent_iff_exists_lcs_eq_bot I).1 ‹_›
  obtain ⟨l, hl⟩ := (isNilpotent_iff_exists_lcs_eq_bot J).1 ‹_›
  refine (isNilpotent_iff_exists_lcs_eq_bot _).2 ⟨k + l, le_bot_iff.1 ?_⟩
  refine (lcs_sup_le_iSup_inf I J (k + l)).trans (iSup_le fun i ↦ ?_)
  rcases le_or_gt k i with h | h
  · exact inf_le_left.trans ((lcs_antitone L I h).trans hk.le)
  · exact inf_le_right.trans ((lcs_antitone L J (by omega)).trans hl.le)

end LieIdeal

namespace TauCeti

namespace LieAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- **The nilradical of a Lie algebra**: the supremum of the ideals that are nilpotent as Lie
algebras.  Over a Noetherian Lie algebra it is itself nilpotent, hence the largest nilpotent
ideal.

This is not Mathlib's `LieAlgebra.maxNilpotentIdeal`, which is the largest ideal on which the
ambient algebra acts nilpotently, and is in general smaller. -/
def nilradical : LieIdeal R L :=
  sSup { I : LieIdeal R L | LieRing.IsNilpotent I }

/-- The nilradical of a Noetherian Lie algebra is nilpotent. -/
instance nilradicalIsNilpotent [IsNoetherian R L] : LieRing.IsNilpotent (nilradical R L) := by
  have hwf := LieSubmodule.wellFoundedGT_of_noetherian R L L
  rw [← CompleteLattice.isSupClosedCompact_iff_wellFoundedGT] at hwf
  refine hwf { I : LieIdeal R L | LieRing.IsNilpotent I } ⟨⊥, ?_⟩ fun I hI J hJ ↦ ?_
  · exact LieIdeal.isNilpotentBot
  · rw [Set.mem_ofPred_eq] at hI hJ ⊢
    exact LieIdeal.isNilpotentSup I J

/-- An ideal that is nilpotent as a Lie algebra is contained in the nilradical.  This is the `→`
direction of `LieIdeal.isNilpotent_iff_le_nilradical`, which needs no Noetherian assumption. -/
theorem _root_.LieIdeal.le_nilradical (I : LieIdeal R L) (h : LieRing.IsNilpotent I) :
    I ≤ nilradical R L :=
  le_sSup h

/-- The nilradical is below an ideal `J` exactly when every nilpotent ideal is.  This is the
elimination half of the universal property of the supremum defining the nilradical, dual to
`LieIdeal.le_nilradical`, and like it needs no Noetherian assumption. -/
theorem nilradical_le_iff {J : LieIdeal R L} :
    nilradical R L ≤ J ↔ ∀ I : LieIdeal R L, LieRing.IsNilpotent I → I ≤ J :=
  ⟨fun h I hI ↦ (LieIdeal.le_nilradical R L I hI).trans h, fun h ↦ sSup_le h⟩

/-- Over a Noetherian Lie algebra the nilradical is exactly the ideals nilpotent as Lie algebras.

The `→` direction holds without the Noetherian assumption; it is `LieIdeal.le_nilradical`. -/
theorem _root_.LieIdeal.isNilpotent_iff_le_nilradical [IsNoetherian R L]
    (I : LieIdeal R L) : LieRing.IsNilpotent I ↔ I ≤ nilradical R L :=
  ⟨LieIdeal.le_nilradical R L I, fun h ↦ LieIdeal.isNilpotent_of_le h inferInstance⟩

/-- The centre is contained in the nilradical. -/
theorem center_le_nilradical : LieAlgebra.center R L ≤ nilradical R L :=
  LieIdeal.le_nilradical R L (LieAlgebra.center R L) inferInstance

/-- A Lie algebra equivalence carries the nilradical onto the nilradical. In particular, every
Lie algebra automorphism preserves the nilradical. -/
theorem nilradical_map_equiv {L' : Type*} [LieRing L'] [LieAlgebra R L']
    (e : L ≃ₗ⁅R⁆ L') : (nilradical R L).map e.toLieHom = nilradical R L' := by
  apply le_antisymm
  · rw [LieIdeal.map_le_iff_le_comap]
    refine sSup_le fun I hI ↦ ?_
    rw [← LieIdeal.map_le_iff_le_comap]
    exact le_sSup (LieIdeal.isNilpotent_map_equiv I e hI)
  · refine sSup_le fun I hI y hy ↦ ?_
    have hpre : I.map e.symm ≤ nilradical R L :=
      le_sSup (LieIdeal.isNilpotent_map_equiv I e.symm hI)
    have hx : e.symm y ∈ nilradical R L := hpre (LieIdeal.mem_map hy)
    simpa using (LieIdeal.mem_map (f := e.toLieHom) hx)

/-- Mathlib's `LieAlgebra.maxNilpotentIdeal` is contained in the nilradical: an ideal on which the
ambient algebra acts nilpotently is in particular nilpotent as a Lie algebra.  The containment is
strict in general: see `TauCeti.LieAlgebra.AffineLine.maxNilpotentIdeal_lt_nilradical`. -/
theorem maxNilpotentIdeal_le_nilradical :
    LieAlgebra.maxNilpotentIdeal R L ≤ nilradical R L :=
  sSup_le_sSup fun I hI ↦ by
    have : LieModule.IsNilpotent L I := hI
    exact (inferInstance : LieRing.IsNilpotent I)

/-- The nilradical is contained in the solvable radical. -/
theorem nilradical_le_radical : nilradical R L ≤ LieAlgebra.radical R L :=
  sSup_le_sSup fun I (_ : LieRing.IsNilpotent I) ↦ LieAlgebra.isSolvable_of_isNilpotent I

/-- The nilradical of a nilpotent Lie algebra is the whole Lie algebra. -/
@[simp]
theorem nilradical_eq_top_of_isNilpotent [LieRing.IsNilpotent L] : nilradical R L = ⊤ := by
  rw [eq_top_iff]
  refine le_sSup ?_
  obtain ⟨k, hk⟩ := LieModule.IsNilpotent.nilpotent R L L
  exact (LieIdeal.isNilpotent_iff_exists_lcs_eq_bot _).2 ⟨k, by rwa [LieIdeal.lcs_top]⟩

/-- Over a Noetherian Lie algebra, the nilradical is the whole algebra exactly when the algebra is
nilpotent. -/
theorem nilradical_eq_top_iff [IsNoetherian R L] :
    nilradical R L = ⊤ ↔ LieRing.IsNilpotent L := by
  refine ⟨fun h ↦ ?_, fun _ ↦ nilradical_eq_top_of_isNilpotent R L⟩
  obtain ⟨k, hk⟩ :=
    (LieIdeal.isNilpotent_iff_exists_lcs_eq_bot (nilradical R L)).1 inferInstance
  rw [h, LieIdeal.lcs_top] at hk
  exact (LieModule.isNilpotent_iff R L L).2 ⟨k, hk⟩

variable {R L}

/-- **Every element of the nilradical is `ad`-nilpotent.** -/
theorem isNilpotent_ad_of_mem_nilradical [IsNoetherian R L] {x : L}
    (hx : x ∈ nilradical R L) : IsNilpotent (LieAlgebra.ad R L x) :=
  LieIdeal.isNilpotent_ad_of_mem (nilradical R L) hx

end LieAlgebra

end TauCeti
