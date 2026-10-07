/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the types occurring in the exported statements. The isotypic components of the regular
-- module and their isomorphism classes come from `RegularIsotypicComponent`, `IsSimpleRing` is a
-- hypothesis on the factors and a conclusion about endomorphism rings, and the matrix ring is the
-- shape of a Wedderburn presentation.
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.SimpleRing.Defs
public import TauCeti.RingTheory.Semisimple.RegularIsotypicComponent
-- Non-public: used only inside proofs. Factor counts and simplicity of isotypic endomorphism
-- rings match the presentation with simple modules; matrix simplicity gives the specialization.
import Mathlib.RingTheory.SimpleRing.Matrix
import TauCeti.RingTheory.SimpleRing.Pi
import TauCeti.RingTheory.Semisimple.IsotypicEnd

/-!
# Wedderburn blocks enumerate the simple modules

Artin--Wedderburn presents a semisimple ring `R` as a finite product of matrix algebras over
division rings,

`R ≃+* ∏ᵢ Matₙᵢ(Dᵢ)`,

and `RingEquiv.card_blocks_eq` shows that the number of factors does not depend on the presentation.
That count is anonymous: it is read off the central idempotents and says nothing about what a block
*is*.  This file identifies the index: **the blocks of any such presentation correspond to the
isomorphism classes of simple `R`-modules**, so a presentation with `n` blocks exhibits exactly `n`
simple modules up to isomorphism, and every simple module is one of them.

The bridge between the two descriptions is the endomorphism ring of the regular module.  Mathlib's
`IsSemisimpleModule.endRingEquiv` splits `End_R R` along the isotypic components of `R`,

`Rᵐᵒᵖ ≃+* End_R R ≃+* ∏_{c} End_R c`,

and each factor is a *simple* ring, because an isotypic component is a finite power of one simple
module and so has a matrix endomorphism ring
(`TauCeti.isSimpleRing_moduleEnd_of_isIsotypic`).  A presentation `R ≃+* ∏ᵢ Aᵢ` by simple rings
gives a second such product decomposition of `Rᵐᵒᵖ`, so
`RingEquiv.exists_equiv_factors` matches the two index types. Composing with
`TauCeti.simpleSubmoduleClassesEquiv`, which identifies the isotypic components of `R` with the
isomorphism classes of simple left ideals, and with `TauCeti.simpleModuleClass`, which realizes an
abstract simple module by a left ideal, turns the block count into a count of simple modules.

## Main results

* `RingEquiv.card_isotypicComponents_eq_of_pi`: a presentation of `R` as a product of simple
  rings indexed by any type has as many factors as `R` has isotypic components.
* `RingEquiv.card_simpleSubmoduleClasses_eq_of_pi`: such a presentation has as many factors as
  there are isomorphism classes of simple `R`-modules.
* `RingEquiv.nonempty_equiv_simpleSubmoduleClasses_of_pi`: the factors of a presentation
  indexed by any type are in bijection with the isomorphism classes of simple `R`-modules.
* `RingEquiv.exists_simpleSubmodule_of_pi`: **the blocks enumerate the simple modules.**
  A presentation of `R` by simple rings indexed by `ι` yields a family of simple left ideals indexed
  by `ι`, pairwise non-isomorphic, with every simple left ideal isomorphic to one of them.
* `RingEquiv.exists_simpleSubmodule_of_pi_matrix`: the same statement for a Wedderburn presentation
  `R ≃+* ∏ᵢ Matₙᵢ(Dᵢ)` indexed by `Fin n`.
* `TauCeti.exists_nonempty_linearEquiv_of_forall_submodule`: such a family exhausts not only the
  simple left ideals but every simple `R`-module, because over a semisimple ring a simple module is
  realized by a left ideal.

## Implementation notes

The presentation equivalence, family and cardinality results accept arbitrary index types
without an explicit finiteness hypothesis. Semisimplicity of `R` nevertheless forces the index of
an actual presentation by nontrivial simple rings to be finite. The general factor theorem in
`TauCeti/RingTheory/SimpleRing/Pi.lean` also applies to genuinely infinite products.

The results are stated for a presentation `R ≃+* ∏ᵢ Aᵢ` by arbitrary simple rings rather than by
matrix algebras: simplicity of the factors is all the argument uses, and Artin--Wedderburn is what
supplies such a presentation, not part of the statement.  The positivity hypotheses `NeZero (d i)`
of the matrix form enter only to make `Matₙᵢ(Dᵢ)` simple, exactly as in
`RingEquiv.card_blocks_eq`; a block of size `0` is the trivial ring, and any presentation could be
padded with such blocks.

The isomorphism classes are handled through `TauCeti.SimpleSubmoduleClasses R R`, the classes of
simple *left ideals*, which unlike the classes of abstract simple modules form a type.  The
exhaustion clause of `RingEquiv.exists_simpleSubmodule_of_pi` is likewise stated for left
ideals, and `TauCeti.exists_nonempty_linearEquiv_of_forall_submodule` upgrades it to arbitrary
simple modules in any universe; keeping the two apart is what lets the main statement stay
universe-monomorphic in the modules it quantifies over.

## References

See T. Y. Lam, *A First Course in Noncommutative Rings*, GTM 131, §3, or C. W. Curtis and
I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*, §25.
-/

public section

namespace TauCeti

universe u v

variable {R : Type u} [Ring R] [IsSemisimpleRing R]

section Presentation

variable {ι : Type*} {A : ι → Type v} [∀ i, Ring (A i)] [∀ i, IsSimpleRing (A i)]

/-- The factors of a presentation of a semisimple ring by simple rings indexed by any type are
in bijection with the isomorphism classes of simple modules.

Match the given decomposition of `Rᵐᵒᵖ` with its decomposition along the isotypic components of the
regular module, then identify those components with the isomorphism classes of simple modules. -/
theorem _root_.RingEquiv.nonempty_equiv_simpleSubmoduleClasses_of_pi (e : R ≃+* ∀ i, A i) :
    Nonempty (ι ≃ SimpleSubmoduleClasses R R) := by
  classical
  have : ∀ c : isotypicComponents R R, IsSimpleRing (Module.End R (c : Submodule R R)) := by
    rintro ⟨c, hc⟩
    have : Nontrivial c := Submodule.nontrivial_iff_ne_bot.mpr (bot_lt_isotypicComponents hc).ne'
    have : IsSemisimpleModule R c := by obtain ⟨S, _, rfl⟩ := hc; infer_instance
    exact isSimpleRing_moduleEnd_of_isIsotypic (IsIsotypic.isotypicComponents hc)
  let f := ((RingEquiv.op e).trans (RingEquiv.piMulOpposite A)).symm.trans
    ((RingEquiv.moduleEndSelf R).trans (IsSemisimpleModule.endRingEquiv R R))
  obtain ⟨σ, -⟩ := f.exists_equiv_factors
  exact ⟨σ.trans (simpleSubmoduleClassesEquiv R R).symm⟩

/-- **A presentation of a semisimple ring as a product of simple rings indexed by any type has
one factor for each isotypic component of the regular module.**

This is the cardinality consequence of matching the given decomposition of `Rᵐᵒᵖ` with the
splitting of `End_R R ≃+* Rᵐᵒᵖ` along its isotypic components. -/
theorem _root_.RingEquiv.card_isotypicComponents_eq_of_pi (e : R ≃+* ∀ i, A i) :
    Nat.card (isotypicComponents R R) = Nat.card ι := by
  obtain ⟨φ⟩ := e.nonempty_equiv_simpleSubmoduleClasses_of_pi
  exact Nat.card_congr ((simpleSubmoduleClassesEquiv R R).symm.trans φ.symm)

/-- **A presentation of a semisimple ring as a product of simple rings indexed by any type has
one factor for each isomorphism class of simple modules.** -/
theorem _root_.RingEquiv.card_simpleSubmoduleClasses_eq_of_pi (e : R ≃+* ∀ i, A i) :
    Nat.card (SimpleSubmoduleClasses R R) = Nat.card ι := by
  obtain ⟨φ⟩ := e.nonempty_equiv_simpleSubmoduleClasses_of_pi
  exact Nat.card_congr φ.symm

/-- **The blocks enumerate the simple modules.** A presentation of a semisimple ring `R` as a
product of simple rings indexed by `ι` produces a family of simple left ideals indexed by `ι` which
are pairwise non-isomorphic and exhaust the simple left ideals up to isomorphism.

Since every simple `R`-module is isomorphic to a simple left ideal, the family is a complete
irredundant list of the simple `R`-modules; that consequence is
`TauCeti.exists_nonempty_linearEquiv_of_forall_submodule`. -/
theorem _root_.RingEquiv.exists_simpleSubmodule_of_pi (e : R ≃+* ∀ i, A i) :
    ∃ S : ι → Submodule R R,
      (∀ i, IsSimpleModule R (S i)) ∧
      (∀ i j, Nonempty (S i ≃ₗ[R] S j) → i = j) ∧
      ∀ I : Submodule R R, IsSimpleModule R I → ∃ i, Nonempty (I ≃ₗ[R] S i) := by
  obtain ⟨φ⟩ := e.nonempty_equiv_simpleSubmoduleClasses_of_pi
  -- Choose a simple left ideal in each isomorphism class.
  have hrep : ∀ c : SimpleSubmoduleClasses R R, ∃ (N : Submodule R R) (h : IsSimpleModule R N),
      @SimpleSubmoduleClasses.mk R _ R _ _ N h = c :=
    SimpleSubmoduleClasses.ind fun N hN ↦ ⟨N, hN, rfl⟩
  choose N hN hmk using hrep
  refine ⟨fun i ↦ N (φ i), fun i ↦ hN (φ i), fun i j h ↦ ?_, fun I hI ↦ ?_⟩
  · have := hN (φ i)
    have := hN (φ j)
    have hij : SimpleSubmoduleClasses.mk (N (φ i)) = SimpleSubmoduleClasses.mk (N (φ j)) :=
      SimpleSubmoduleClasses.mk_eq_mk_iff.mpr h
    rw [hmk, hmk] at hij
    exact φ.injective hij
  · have := hN (φ (φ.symm (SimpleSubmoduleClasses.mk I)))
    refine ⟨φ.symm (SimpleSubmoduleClasses.mk I), SimpleSubmoduleClasses.mk_eq_mk_iff.mp ?_⟩
    rw [hmk, Equiv.apply_symm_apply]

/-- **Blocks enumerate the simple modules**, for a Wedderburn presentation
`R ≃+* ∏ᵢ Matₙᵢ(Dᵢ)`: the `n` blocks yield `n` pairwise non-isomorphic simple left ideals which
exhaust the simple left ideals up to isomorphism.

The positivity hypotheses `NeZero (d i)` are what make the matrix blocks simple rings; they are the
same hypotheses that `IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing` produces and that
`RingEquiv.card_blocks_eq` needs.

The general statement it specializes is `RingEquiv.exists_simpleSubmodule_of_pi`. -/
theorem _root_.RingEquiv.exists_simpleSubmodule_of_pi_matrix {n : ℕ} {D : Fin n → Type v}
    [∀ i, DivisionRing (D i)]
    {d : Fin n → ℕ} [∀ i, NeZero (d i)]
    (e : R ≃+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :
    ∃ S : Fin n → Submodule R R,
      (∀ i, IsSimpleModule R (S i)) ∧
      (∀ i j, Nonempty (S i ≃ₗ[R] S j) → i = j) ∧
      ∀ I : Submodule R R, IsSimpleModule R I → ∃ i, Nonempty (I ≃ₗ[R] S i) := by
  have : ∀ i, Nonempty (Fin (d i)) := fun i ↦ ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (d i))⟩⟩
  exact e.exists_simpleSubmodule_of_pi

end Presentation

/-- **A family of simple left ideals exhausting the simple left ideals exhausts every simple
module.** Over a semisimple ring every simple module is isomorphic to a left ideal, so no
information is lost by listing only the left ideals; this is what turns the family produced by
`RingEquiv.exists_simpleSubmodule_of_pi` into a list of *all* the simple `R`-modules, in
any universe. -/
theorem exists_nonempty_linearEquiv_of_forall_submodule {κ : Type*} {S : κ → Submodule R R}
    (hS : ∀ I : Submodule R R, IsSimpleModule R I → ∃ k, Nonempty (I ≃ₗ[R] S k))
    (M : Type*) [AddCommGroup M] [Module R M] [IsSimpleModule R M] :
    ∃ k, Nonempty (M ≃ₗ[R] S k) := by
  obtain ⟨I, ⟨f⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R M
  have : IsSimpleModule R I := .congr f.symm
  obtain ⟨k, ⟨g⟩⟩ := hS I inferInstance
  exact ⟨k, ⟨f.trans g⟩⟩

end TauCeti
