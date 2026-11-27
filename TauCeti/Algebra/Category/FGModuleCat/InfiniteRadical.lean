/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.RepresentationFinite
import TauCeti.Algebra.Category.FGModuleCat.AlmostSplit.SourceSink
import TauCeti.Algebra.Category.FGModuleCat.Generator.Basic
import TauCeti.Algebra.Category.FGModuleCat.KrullSchmidt
import TauCeti.Algebra.Category.FGModuleCat.MatlisDuality.Basic
import TauCeti.Algebra.Category.ModuleCat.Algebra
import TauCeti.Algebra.Subalgebra.Center
import TauCeti.CategoryTheory.AlmostSplit.Finiteness
import TauCeti.CategoryTheory.Generator.Biproduct
import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Nilpotence
import TauCeti.CategoryTheory.Preadditive.Radical.Chain
import TauCeti.RingTheory.Artinian.Subalgebra

/-!
# The infinite radical of an Artin algebra

An Artin algebra has finite representation type exactly when the intersection of the powers of
the radical of its category of finitely generated modules is zero. For the converse, it suffices
to stabilize the powers on the hom space from the regular module to its Matlis dual. This
gives a uniform bound on nonzero composites of non-isomorphisms between indecomposables.
The finiteness argument then uses left almost split maps out of the summands of the regular
module.

## References

* M. Auslander, *Representation theory of Artin algebras II*, Comm. Algebra 1 (1974),
  269–310, Theorem 3.1.
* O. Kerner and A. Skowroński, *On module categories with nilpotent infinite radical*,
  Compositio Math. 77 (1991), 313–333, Note added in proof (p. 332), for Bongartz's criterion.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), proof of Theorem VI.1.4, for the finiteness argument.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ModuleCat.Algebra

namespace TauCeti

universe u v w

variable (R : Type u) [CommRing R] [IsArtinianRing R] {A : Type v} [Ring A] [Algebra R A]
  [Module.Finite R A] [Small.{w} A]

include R

/-- An Artin algebra is representation-finite if the radical of its category of finitely
generated modules has a vanishing power. -/
theorem isRepresentationFinite_of_jacobsonRadicalIdeal_pow_eq_bot {n : ℕ}
    (hn : jacobsonRadicalIdeal (FGModuleCat.{w} A) ^ n = ⊥) : IsRepresentationFinite.{w} A := by
  classical
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  have hvanish (X : ℕ → FGModuleCat.{w} A) (f : ∀ j, X j ⟶ X (j + 1))
      (hX : ∀ j, Indecomposable (X j)) (hf : ∀ j, ¬ IsIso (f j)) :
      (Functor.ofSequence f).map (homOfLE (Nat.zero_le n)) = 0 := by
    have hval : Monotone (Fin.val : Fin (n + 1) → ℕ) := fun _ _ h ↦ h
    let F : ComposableArrows (FGModuleCat.{w} A) n := hval.functor ⋙ Functor.ofSequence f
    -- The restriction sends the first and last vertices to `0` and `n` and their arrow
    -- to the unique arrow from `0` to `n` in `ℕ`.
    have hF : F.hom = (Functor.ofSequence f).map (homOfLE (Nat.zero_le n)) := rfl
    have hmem := F.hom_mem_jacobsonRadicalIdeal_pow
      (fun i ↦ (IsKrullSchmidt.indecomposable_iff_isLocalRing_end (X i)).1 (hX i))
      (fun j hj ↦ by
        -- The link of the restricted finite chain is the same link of the original sequence.
        change ¬ IsIso ((Functor.ofSequence f).map (homOfLE (Nat.le_add_right j 1)))
        simpa only [Functor.ofSequence_map_homOfLE_succ] using hf j)
    rw [hn] at hmem
    rw [← hF]
    exact MorphismIdeal.mem_bot.mp hmem
  let G := FGModuleCat.of A (Shrink.{w} A)
  have : Module.IsGenerator A (Shrink.{w} A) := .of_linearEquiv (Shrink.linearEquiv A A)
  have hG : IsSeparator G := FGModuleCat.isSeparator_of_isGenerator _
  obtain ⟨m, P, hP, ⟨e⟩⟩ := IsKrullSchmidt.exists_iso_biproduct G
  obtain ⟨S, hS, -, hreach⟩ := exists_finite_forall_iso_of_hom_ne_zero
    (fun X : FGModuleCat.{w} A ↦ Indecomposable X)
    (fun X hX ↦ (IsKrullSchmidt.indecomposable_iff_isLocalRing_end X).1 hX)
    (fun X hX ↦ by
      obtain ⟨k, F, i, hF, hi, -, -⟩ :=
        FGModuleCat.exists_isLeftAlmostSplit_biproduct_of_finite R hX
      exact ⟨k, F, i, hF, hi⟩)
    n hvanish (Set.finite_range P)
    (by rintro _ ⟨j, rfl⟩; have := hP j; exact indecomposable_of_isLocalRing_end)
  let := hS.fintype
  let enum := Fintype.equivFin S
  refine isRepresentationFinite_iff_exists_isAdditiveGenerator.2
    (exists_isAdditiveGenerator_iff.2 ⟨Fintype.card S, fun j ↦ enum.symm j, fun Y hY ↦ ?_⟩)
  obtain ⟨j, f, hf⟩ := hG.exists_hom_ne_zero_of_iso_biproduct e hY.1
  obtain ⟨Q, hQ, hiso⟩ := hreach Y hY (P j) (Set.mem_range_self j) f hf
  exact ⟨enum ⟨Q, hQ⟩, by simpa using hiso⟩

/-- An Artin algebra is representation-finite exactly when the radical of its category of
finitely generated modules is nilpotent. -/
theorem isRepresentationFinite_iff_exists_jacobsonRadicalIdeal_pow_eq_bot :
    IsRepresentationFinite.{w} A ↔ ∃ n : ℕ, jacobsonRadicalIdeal (FGModuleCat.{w} A) ^ n = ⊥ :=
  ⟨fun h ↦ h.exists_jacobsonRadicalIdeal_pow_eq_bot R,
    fun ⟨_, hn⟩ ↦ isRepresentationFinite_of_jacobsonRadicalIdeal_pow_eq_bot R hn⟩

/-- An Artin algebra is representation-finite exactly when the intersection of the powers
of the radical of its category of finitely generated modules is zero. -/
theorem isRepresentationFinite_iff_forall_mem_jacobsonRadicalIdeal_pow :
    IsRepresentationFinite.{w} A ↔
      ∀ (X Y : FGModuleCat.{w} A) (f : X ⟶ Y),
        (∀ n : ℕ, f ∈ (jacobsonRadicalIdeal (FGModuleCat.{w} A) ^ n).hom X Y) → f = 0 := by
  rw [isRepresentationFinite_iff_exists_jacobsonRadicalIdeal_pow_eq_bot R]
  refine ⟨fun ⟨n, hn⟩ X Y f hf ↦ MorphismIdeal.mem_bot.mp (hn ▸ hf n), fun h ↦ ?_⟩
  · -- Use the centre so that the coefficient module for Matlis duality fits the module universe.
    let Z := Subalgebra.center R A
    have : Module.Finite Z A := Subalgebra.finite_centerAlgebra_of_finite
    have : Small.{w} Z := inferInstanceAs (Small.{w} {a : A // a ∈ Z})
    obtain ⟨E, _, _, q, hq, -⟩ := exists_isInjectiveEnvelope_quotient_jacobson.{v, w} Z
    let e := hq.fgModuleCatMatlisDuality (A := A)
    let G := FGModuleCat.of A (Shrink.{w} A)
    have : Module.IsGenerator A (Shrink.{w} A) := .of_linearEquiv (Shrink.linearEquiv A A)
    have : Small.{w} Aᵐᵒᵖ := small_of_injective MulOpposite.unop_injective
    let G' := FGModuleCat.of Aᵐᵒᵖ (Shrink.{w} Aᵐᵒᵖ)
    have : Module.IsGenerator Aᵐᵒᵖ (Shrink.{w} Aᵐᵒᵖ) :=
      .of_linearEquiv (Shrink.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ)
    have hG : IsSeparator G := FGModuleCat.isSeparator_of_isGenerator _
    have hG' : IsSeparator G' := FGModuleCat.isSeparator_of_isGenerator _
    let D := (e.inverse.obj G').unop
    have hD : IsCoseparator D := (isCoseparator_unop_iff _).2 (hG'.of_equivalence e.symm)
    exact (jacobsonRadicalIdeal (FGModuleCat.{w} A))
      |>.exists_pow_eq_bot_of_forall_mem_pow R hG hD (h G D)

end TauCeti
