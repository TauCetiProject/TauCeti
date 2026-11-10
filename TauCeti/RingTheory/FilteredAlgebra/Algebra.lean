/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Map
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Algebra structures on filtered ring completions

The compatible-family completion of a filtered algebra is itself an algebra over the
base semiring, with scalars acting at each finite order. Its projections and the canonical
map from the algebra are algebra homomorphisms, and an algebra homomorphism with a
monotone cutoff modulus induces an algebra homomorphism of completions. The carrier
and the ring structure are those of `TauCeti.AlgFiltration.completion`, so all
ring-level statements apply unchanged. The algebras may be noncommutative.

Adapted from `yuma-mizuno-lean/Mei`, commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`,
`Mei/RingTheory/FilteredAlgebra/Algebra.lean` and `AlgHom.lean` (Apache 2.0).
-/

public section

namespace TauCeti.AlgFiltration

variable {R A B C : Type*} [CommSemiring R]
  [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Ring C] [Algebra R C]
  (F : TauCeti.AlgFiltration A) (G : TauCeti.AlgFiltration B)

/-- Compatible quotient families form a subalgebra of the product of the quotient algebras. -/
def completionSubalgebra : Subalgebra R (∀ k : ℕᵒᵖ, A ⧸ F.ideal (k.unop + 1)) where
  __ := F.completion
  algebraMap_mem' r := (F.mem_completion_iff _).mpr fun {_ _} h =>
    (Ideal.Quotient.factorₐ R (F.antitone (Nat.add_le_add_right h 1))).commutes r

/-- Forgetting scalars recovers the completion's underlying subsemiring. -/
@[simp]
theorem completionSubalgebra_toSubsemiring :
    (F.completionSubalgebra (R := R)).toSubsemiring = F.completion.toSubsemiring := (rfl)

/-- The algebra structure on the ring completion is inherited from componentwise scalars. -/
instance completionAlgebra : Algebra R F.completion :=
  inferInstanceAs (Algebra R (F.completionSubalgebra (R := R)))

/-- Scalars in the completion have their usual classes in each quotient algebra. -/
@[simp]
theorem projection_algebraMap (k : ℕ) (r : R) :
    F.projection k (algebraMap R F.completion r) = algebraMap R (A ⧸ F.ideal (k + 1)) r := by
  rw [projection_apply]
  rfl

/-- The finite-order projection as an algebra homomorphism. -/
def projectionₐ (k : ℕ) : F.completion →ₐ[R] A ⧸ F.ideal (k + 1) where
  __ := F.projection k
  commutes' := F.projection_algebraMap k

/-- Algebra projections evaluate by the existing ring projections. -/
@[simp]
theorem projectionₐ_apply (k : ℕ) (x : F.completion) :
    F.projectionₐ (R := R) k x = F.projection k x := (rfl)

/-- The canonical map into the completion as an algebra homomorphism. -/
def toCompletionₐ : A →ₐ[R] F.completion where
  __ := F.toCompletion
  commutes' r := F.completion_ext fun k => by simp

/-- The canonical algebra map has the same values as the canonical ring map. -/
@[simp]
theorem toCompletionₐ_apply (x : A) :
    F.toCompletionₐ (R := R) x = F.toCompletion x := (rfl)

variable (f : A →ₐ[R] B) (l : ℕ → ℕ) (hl : Monotone l)
  (hf : ∀ k, F.ideal (l k + 1) ≤ (G.ideal (k + 1)).comap f)

/-- Extend an algebra homomorphism to completions along a monotone cutoff modulus. -/
def mapCompletionₐ : F.completion →ₐ[R] G.completion where
  __ := F.mapCompletion G (f : A →+* B) l hl hf
  commutes' r := by
    have h := F.mapCompletion_toCompletion G (f : A →+* B) l hl hf (algebraMap R A r)
    simpa [← toCompletionₐ_apply (R := R)] using h

/-- Forgetting scalars gives the existing filtered ring completion map. -/
@[simp]
theorem coe_mapCompletionₐ :
    (F.mapCompletionₐ G f l hl hf : F.completion →+* G.completion) =
      F.mapCompletion G (f : A →+* B) l hl hf := (rfl)

/-- The order-`k` projection is the induced quotient algebra map at source order `l k`. -/
@[simp]
theorem projection_mapCompletionₐ (k : ℕ) (x : F.completion) :
    G.projection k (F.mapCompletionₐ G f l hl hf x) =
      Ideal.quotientMapₐ (G.ideal (k + 1)) f (hf k) (F.projection (l k) x) :=
  F.projection_mapCompletion G (f : A →+* B) l hl hf k x

/-- The induced algebra map extends the original map on canonical elements. -/
@[simp]
theorem mapCompletionₐ_toCompletion (a : A) :
    F.mapCompletionₐ G f l hl hf (F.toCompletion a) = G.toCompletion (f a) :=
  F.mapCompletion_toCompletion G (f : A →+* B) l hl hf a

/-- Any two valid cutoff moduli induce the same algebra homomorphism on completions. -/
theorem mapCompletionₐ_eq (m : ℕ → ℕ) (hm : Monotone m)
    (hfm : ∀ k, F.ideal (m k + 1) ≤ (G.ideal (k + 1)).comap f) :
    F.mapCompletionₐ G f l hl hf = F.mapCompletionₐ G f m hm hfm := by
  apply AlgHom.toRingHom_injective
  exact F.mapCompletion_eq G (f : A →+* B) hl hf m hm hfm

/-- Completing the identity algebra map gives the identity algebra map. -/
@[simp]
theorem mapCompletionₐ_id :
    F.mapCompletionₐ F (AlgHom.id R A) id monotone_id (fun _ => by simp) =
      AlgHom.id R F.completion := by
  apply AlgHom.toRingHom_injective
  exact F.mapCompletion_id

variable (H : TauCeti.AlgFiltration C) (g : B →ₐ[R] C) (m : ℕ → ℕ) (hm : Monotone m)
  (hg : ∀ k, G.ideal (m k + 1) ≤ (H.ideal (k + 1)).comap g)

/-- Successive algebra completion maps compose with cutoff modulus `l ∘ m`. -/
theorem mapCompletionₐ_comp :
    F.mapCompletionₐ H (g.comp f) (l ∘ m) (hl.comp hm)
      (fun k => by
        rw [← Ideal.comap_comapₐ]
        exact (hf (m k)).trans (Ideal.comap_mono (hg k))) =
      (G.mapCompletionₐ H g m hm hg).comp (F.mapCompletionₐ G f l hl hf) := by
  apply AlgHom.toRingHom_injective
  simpa only [AlgHom.comp_toRingHom, coe_mapCompletionₐ] using
    F.mapCompletion_comp G (f : A →+* B) hl hf H (g : B →+* C) m hm hg

end TauCeti.AlgFiltration
