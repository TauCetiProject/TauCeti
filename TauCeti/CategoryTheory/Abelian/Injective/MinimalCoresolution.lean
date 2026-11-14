/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Abelian.Coresolution
public import TauCeti.CategoryTheory.Abelian.Injective.Envelope

/-!
# Minimal injective coresolutions

A coresolution with `n` terms (`CategoryTheory.ComposableArrows.IsCoresolution`) is **injective**
when its terms are injective, and **minimal injective** when moreover each cosyzygy embeds into
the next term by an injective envelope, that is, an essential monomorphism
(`TauCeti.IsEssentialMono`).

The main results compare coresolutions. A minimal injective coresolution of a retract of `X` is a
termwise retract of every injective coresolution of `X`
(`CategoryTheory.ComposableArrows.IsMinimalInjectiveCoresolution.nonempty_retract_obj'`), by
induction on the cosyzygies through
`TauCeti.IsEssentialMono.nonempty_retract_and_nonempty_retract_cokernel`. Two minimal injective
coresolutions of the same object have isomorphic terms
(`CategoryTheory.ComposableArrows.IsMinimalInjectiveCoresolution.nonempty_iso_obj'`). Minimal
injective coresolutions are spliced from injective envelopes
(`CategoryTheory.ComposableArrows.IsMinimalInjectiveCoresolution.coresolutionCons`), so they exist
for objects in a property `Q` closed under injective envelopes and their cokernels, and hence for
every object when every object has an injective envelope
(`CategoryTheory.ComposableArrows.exists_isMinimalInjectiveCoresolution`).

## Main definitions

* `CategoryTheory.ComposableArrows.IsInjectiveCoresolution` and
  `CategoryTheory.ComposableArrows.IsMinimalInjectiveCoresolution`: injective and minimal injective
  coresolutions with `n` terms.

## Main results

* `CategoryTheory.ComposableArrows.IsMinimalInjectiveCoresolution.nonempty_retract_obj'`: a minimal
  injective coresolution is a termwise retract of any injective coresolution.
* `CategoryTheory.ComposableArrows.IsMinimalInjectiveCoresolution.nonempty_iso_obj'`: minimal
  injective coresolutions are unique up to isomorphism of their terms.
* `CategoryTheory.ComposableArrows.exists_isMinimalInjectiveCoresolution`: existence, given
  injective envelopes.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, LMS Student Texts 65, CUP (2006), I.5.
* F. W. Anderson, K. R. Fuller, *Rings and Categories of Modules*, 2nd ed., Springer GTM 13
  (1992), §18.
-/

public section

universe v u

namespace CategoryTheory

open Limits TauCeti ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ComposableArrows

variable {n : ℕ}

/-- An **injective coresolution with `n` terms**: a coresolution whose terms `S.obj' (i + 2)`,
`i < n`, are injective. -/
structure IsInjectiveCoresolution (S : ComposableArrows C (n + 1)) : Prop
    extends S.IsCoresolution where
  /-- The terms are injective. -/
  injective (i : ℕ) (hi : i < n) : Injective (S.obj' (i + 2))

/-- A **minimal injective coresolution with `n` terms**: an injective coresolution in which every
cosyzygy embeds into the next term by an injective envelope, that is, an essential
monomorphism. -/
structure IsMinimalInjectiveCoresolution (S : ComposableArrows C (n + 1)) : Prop
    extends S.IsInjectiveCoresolution where
  /-- Each cosyzygy embeds into the next term by an essential monomorphism. -/
  isEssentialMono (i : ℕ) (hi : i < n) :
    IsEssentialMono (cokernel.desc (S.map' i (i + 1)) (S.map' (i + 1) (i + 2))
      (exact.toIsComplex.zero i))

theorem IsMinimalInjectiveCoresolution.isEssentialMono_cosyzygyι
    {S : ComposableArrows C (n + 1)} (hS : S.IsMinimalInjectiveCoresolution) (i : ℕ)
    (hi : i < n) : IsEssentialMono (hS.toIsCoresolution.cosyzygyι i) := by
  rw [IsCoresolution.cosyzygyι_eq_cokernelDesc]
  exact hS.isEssentialMono i hi

/-- An injective coresolution is minimal exactly when each cosyzygy embeds into the next term by
an essential monomorphism. -/
theorem isMinimalInjectiveCoresolution_iff {S : ComposableArrows C (n + 1)} :
    S.IsMinimalInjectiveCoresolution ↔ ∃ hS : S.IsInjectiveCoresolution,
      ∀ (i : ℕ) (hi : i < n), IsEssentialMono (hS.toIsCoresolution.cosyzygyι i) :=
  ⟨fun hS ↦ ⟨hS.toIsInjectiveCoresolution, hS.isEssentialMono_cosyzygyι⟩,
    fun ⟨hS, h⟩ ↦ ⟨hS, fun i hi ↦ by
      simpa only [IsCoresolution.cosyzygyι_eq_cokernelDesc] using h i hi⟩⟩

section Cons

variable {X I : C} {ι : X ⟶ I} {T : ComposableArrows C (n + 1)}

/-- An embedding into an injective object followed by an injective coresolution of its cokernel
is an injective coresolution. -/
theorem IsInjectiveCoresolution.coresolutionCons [Mono ι] [Injective I]
    {e : cokernel ι ≅ T.obj' 1} (hT : T.IsInjectiveCoresolution) :
    (coresolutionCons ι T e).IsInjectiveCoresolution where
  toIsCoresolution := hT.toIsCoresolution.coresolutionCons
  injective i hi := by
    match i, hi with
    | 0, _ => exact ‹Injective I›
    | k + 1, _ => exact hT.injective k (by omega)

/-- An injective envelope followed by a minimal injective coresolution of its cokernel is a
minimal injective coresolution. -/
theorem IsMinimalInjectiveCoresolution.coresolutionCons [Injective I] {e : cokernel ι ≅ T.obj' 1}
    (hι : IsEssentialMono ι) (hT : T.IsMinimalInjectiveCoresolution) :
    (coresolutionCons ι T e).IsMinimalInjectiveCoresolution where
  toIsInjectiveCoresolution := by
    have := hι.mono
    exact hT.toIsInjectiveCoresolution.coresolutionCons
  isEssentialMono i hi := by
    match i, hi with
    | 0, _ =>
      refine (isEssentialMono_cokernelDesc_of_eq_zero (coresolutionCons_map'_zero_one ι T e)
        _).2 ?_
      rw [coresolutionCons_map'_one_two ι T e]
      exact hι
    | 1, _ =>
      have h₀ : IsEssentialMono (cokernel.desc (T.map' 0 1) (T.map' 1 2)
          (hT.exact.toIsComplex.zero' 0 1 2)) := hT.isEssentialMono 0 (by omega)
      rw [isEssentialMono_cokernelDesc_of_eq_zero (hT.isZero_left.eq_of_src _ _)] at h₀
      have w : ι ≫ cokernel.π ι ≫ e.hom ≫ T.map' 1 2 = 0 := by simp
      refine (isEssentialMono_cokernelDesc_congr (coresolutionCons_map'_one_two ι T e)
        (coresolutionCons_map'_two_three ι T e (by omega)) _ w).2 ?_
      have : cokernel.desc ι (cokernel.π ι ≫ e.hom ≫ T.map' 1 2) w = e.hom ≫ T.map' 1 2 := by
        ext
        simp
      refine (TauCeti.isEssentialMono_congr this).2 ?_
      rw [isEssentialMono_isIso_comp_iff]
      exact h₀
    | 2, _ =>
      have h₁₂₃ := hT.exact.toIsComplex.zero' 1 2 3
      have w : (cokernel.π ι ≫ e.hom ≫ T.map' 1 2) ≫ T.map' 2 3 = 0 := by
        simp only [Category.assoc, h₁₂₃, comp_zero]
      have w' : ((cokernel.π ι ≫ e.hom) ≫ T.map' 1 2) ≫ T.map' 2 3 = 0 := by
        simp only [Category.assoc, h₁₂₃, comp_zero]
      refine (isEssentialMono_cokernelDesc_congr (coresolutionCons_map'_two_three ι T e (by omega))
        (coresolutionCons_map'_add_three ι T e 0 (by omega)) _ w).2 ?_
      refine (isEssentialMono_cokernelDesc_congr (Category.assoc _ _ _).symm rfl w w').2 ?_
      exact (isEssentialMono_cokernelDesc_epi_comp _ _ w' h₁₂₃).2 (hT.isEssentialMono 1 (by omega))
    | k + 3, _ =>
      exact (isEssentialMono_cokernelDesc_congr (coresolutionCons_map'_add_three ι T e k (by omega))
        (coresolutionCons_map'_add_three ι T e (k + 1) (by omega)) _
        (hT.exact.toIsComplex.zero' (k + 2) (k + 3) (k + 4))).2
        (hT.isEssentialMono (k + 2) (by omega))

end Cons

section Tail

variable {S : ComposableArrows C (n + 2)}

/-- The tail of an injective coresolution is an injective coresolution. -/
theorem IsInjectiveCoresolution.tail (hS : S.IsInjectiveCoresolution) :
    hS.toIsCoresolution.tail.IsInjectiveCoresolution where
  toIsCoresolution := hS.toIsCoresolution.isCoresolution_tail
  injective i hi := hS.injective (i + 1) (by omega)

/-- The tail of a minimal injective coresolution is a minimal injective coresolution. -/
theorem IsMinimalInjectiveCoresolution.tail (hS : S.IsMinimalInjectiveCoresolution) :
    hS.toIsCoresolution.tail.IsMinimalInjectiveCoresolution where
  toIsInjectiveCoresolution := hS.toIsInjectiveCoresolution.tail
  isEssentialMono i hi := by
    have hS' := hS.toIsCoresolution
    match i, hi with
    | 0, _ =>
      refine (isEssentialMono_cokernelDesc_of_eq_zero hS'.tail_map'_zero_one _).2 ?_
      rw [hS'.tail_map'_one_two (by omega)]
      exact hS.isEssentialMono_cosyzygyι 1 (by omega)
    | 1, _ =>
      have h₂₃₄ := hS.exact.toIsComplex.zero' 2 3 4
      have w : (cokernel.π (S.map' 1 2) ≫ hS'.cosyzygyι 1) ≫ S.map' 3 4 = 0 := by
        rw [hS'.π_cosyzygyι 1]
        exact h₂₃₄
      have w' : hS'.cosyzygyι 1 ≫ S.map' 3 4 = 0 := by
        rw [← cancel_epi (cokernel.π (S.map' 1 2)), comp_zero, ← Category.assoc]
        exact w
      refine (isEssentialMono_cokernelDesc_congr (hS'.tail_map'_one_two (by omega))
        (hS'.tail_map'_add_two 0 (by omega)) _ w').2 ?_
      refine (isEssentialMono_cokernelDesc_epi_comp (cokernel.π (S.map' 1 2)) _ w w').1 ?_
      exact (isEssentialMono_cokernelDesc_congr (hS'.π_cosyzygyι 1) rfl w h₂₃₄).2
        (hS.isEssentialMono 2 (by omega))
    | k + 2, _ =>
      exact (isEssentialMono_cokernelDesc_congr (hS'.tail_map'_add_two k (by omega))
        (hS'.tail_map'_add_two (k + 1) (by omega)) _
        (hS.exact.toIsComplex.zero' (k + 3) (k + 4) (k + 5))).2
        (hS.isEssentialMono (k + 3) (by omega))

end Tail

namespace IsMinimalInjectiveCoresolution

variable {E S : ComposableArrows C (n + 1)}

/-- The cosyzygies of a minimal injective coresolution of a retract of `X` are retracts of the
cosyzygies of any injective coresolution of `X`. -/
theorem nonempty_retract_cosyzygy (hE : E.IsMinimalInjectiveCoresolution)
    (hS : S.IsInjectiveCoresolution) (r : Retract (E.obj' 1) (S.obj' 1)) :
    ∀ (i : ℕ) (hi : i ≤ n), Nonempty (Retract (E.cosyzygy i) (S.cosyzygy i))
  | 0, _ => ⟨(Retract.ofIso hE.cosyzygyZeroIso).trans
      (r.trans (Retract.ofIso hS.cosyzygyZeroIso.symm))⟩
  | i + 1, hi => by
    obtain ⟨r'⟩ := nonempty_retract_cosyzygy hE hS r i (by omega)
    have := hE.injective i (by omega)
    have := hS.injective i (by omega)
    have := hS.mono_cosyzygyι i (by omega)
    obtain ⟨-, ⟨r''⟩⟩ :=
      (hE.isEssentialMono_cosyzygyι i (by omega)).nonempty_retract_and_nonempty_retract_cokernel
      (j := hS.cosyzygyι i _) r'
    exact ⟨(Retract.ofIso (hE.cosyzygySuccIso i)).trans
      (r''.trans (Retract.ofIso (hS.cosyzygySuccIso i).symm))⟩

/-- **A minimal injective coresolution is a termwise retract of any injective coresolution.** If
`E` is a minimal injective coresolution of a retract of `S.obj' 1` and `S` is an injective
coresolution, both with `n` terms, then every term of `E` is a retract of the corresponding term
of `S`. -/
theorem nonempty_retract_obj' (hE : E.IsMinimalInjectiveCoresolution)
    (hS : S.IsInjectiveCoresolution) (r : Retract (E.obj' 1) (S.obj' 1)) (i : ℕ) (hi : i < n) :
    Nonempty (Retract (E.obj' (i + 2)) (S.obj' (i + 2))) := by
  obtain ⟨r'⟩ := hE.nonempty_retract_cosyzygy hS r i (by omega)
  have := hE.injective i hi
  have := hS.injective i hi
  have := hS.mono_cosyzygyι i hi
  exact ((hE.isEssentialMono_cosyzygyι i hi).nonempty_retract_and_nonempty_retract_cokernel
    (j := hS.cosyzygyι i hi) r').1

/-- The inductive step of the uniqueness of minimal injective coresolutions: an isomorphism of
`i`-th cosyzygies extends to an isomorphism of `i`-th terms. -/
theorem exists_iso_obj'_comm (hE : E.IsMinimalInjectiveCoresolution)
    (hS : S.IsMinimalInjectiveCoresolution) (i : ℕ) (hi : i < n)
    (a : E.cosyzygy i ≅ S.cosyzygy i) :
    ∃ b : E.obj' (i + 2) ≅ S.obj' (i + 2), hE.cosyzygyι i ≫ b.hom = a.hom ≫ hS.cosyzygyι i := by
  have := hE.injective i hi
  have := hS.injective i hi
  exact (hE.isEssentialMono_cosyzygyι i hi).exists_iso
    ((isEssentialMono_isIso_comp_iff a.hom _).2 (hS.isEssentialMono_cosyzygyι i hi))

/-- The cosyzygies of two minimal injective coresolutions of the same object are isomorphic. -/
theorem nonempty_iso_cosyzygy (hE : E.IsMinimalInjectiveCoresolution)
    (hS : S.IsMinimalInjectiveCoresolution) (e : E.obj' 1 ≅ S.obj' 1) :
    ∀ (i : ℕ) (hi : i ≤ n), Nonempty (E.cosyzygy i ≅ S.cosyzygy i)
  | 0, _ => ⟨hE.cosyzygyZeroIso ≪≫ e ≪≫ hS.cosyzygyZeroIso.symm⟩
  | i + 1, hi => by
    obtain ⟨a⟩ := nonempty_iso_cosyzygy hE hS e i (by omega)
    obtain ⟨b, hb⟩ := exists_iso_obj'_comm hE hS i (by omega) a
    exact ⟨hE.cosyzygySuccIso i ≪≫ cokernel.mapIso _ _ a b hb ≪≫ (hS.cosyzygySuccIso i).symm⟩

/-- **Minimal injective coresolutions have isomorphic terms.** Two minimal injective coresolutions
with `n` terms of the same object have isomorphic terms. -/
theorem nonempty_iso_obj' (hE : E.IsMinimalInjectiveCoresolution)
    (hS : S.IsMinimalInjectiveCoresolution) (e : E.obj' 1 ≅ S.obj' 1) (i : ℕ) (hi : i < n) :
    Nonempty (E.obj' (i + 2) ≅ S.obj' (i + 2)) := by
  obtain ⟨a⟩ := hE.nonempty_iso_cosyzygy hS e i (by omega)
  obtain ⟨b, -⟩ := exists_iso_obj'_comm hE hS i hi a
  exact ⟨b⟩

end IsMinimalInjectiveCoresolution

/-- **Existence of minimal injective coresolutions.** Let `Q` be a property of objects such that
every object satisfying `Q` has an injective envelope whose target and cokernel satisfy `Q`. Then
every object satisfying `Q` has a minimal injective coresolution with `n` terms, all of which
satisfy `Q`. Taking `Q` to hold everywhere, this says that if every object has an injective
envelope, then every object has minimal injective coresolutions of every length. -/
theorem exists_isMinimalInjectiveCoresolution {Q : ObjectProperty C}
    (hQ : ∀ X, Q X → ∃ (I : C) (ι : X ⟶ I), Injective I ∧ IsEssentialMono ι ∧ Q I ∧
      Q (cokernel ι))
    (n : ℕ) {X : C} (hX : Q X) :
    ∃ S : ComposableArrows C (n + 1), S.IsMinimalInjectiveCoresolution ∧
      Nonempty (S.obj' 1 ≅ X) ∧ ∀ (i : ℕ) (hi : i < n), Q (S.obj' (i + 2)) := by
  induction n generalizing X with
  | zero =>
    exact ⟨mk₁ (0 : 0 ⟶ X),
      { exact := (mk₁ _).exact₁
        isZero_left := isZero_zero C
        injective := fun _ hi ↦ absurd hi (Nat.not_lt_zero _)
        isEssentialMono := fun _ hi ↦ absurd hi (Nat.not_lt_zero _) },
      ⟨Iso.refl _⟩, fun _ hi ↦ absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨I, ι, hI, hι, hQI, hQc⟩ := hQ X hX
    obtain ⟨T, hT, ⟨e⟩, hQT⟩ := ih hQc
    exact ⟨coresolutionCons ι T e.symm, hT.coresolutionCons hι, ⟨Iso.refl _⟩,
      fun i hi ↦ match i, hi with
        | 0, _ => hQI
        | k + 1, _ => hQT k (by omega)⟩

end ComposableArrows

end CategoryTheory
