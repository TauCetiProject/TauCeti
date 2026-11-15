/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Equivalence
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Morita
public import TauCeti.Algebra.Module.Generator
public import TauCeti.RingTheory.Idempotents.Corner.Retract
public import TauCeti.RingTheory.Morita.Corner

/-!
# Morita equivalence through progenerators

A **progenerator** of a ring `A` is a finitely generated projective `A`-module `P` that is a
generator (`TauCeti.Module.IsGenerator`). This file proves the classical description of Morita
equivalence over a commutative base `R`:

* `A` is Morita equivalent to `(End_A P)ᵐᵒᵖ` for every progenerator `P`, and every algebra Morita
  equivalent to `A` is of this form;
* two algebras are Morita equivalent as soon as their categories of **finitely generated** modules
  are `R`-linearly equivalent, and conversely. No finiteness of the algebras is assumed: every
  module category is recovered from its finitely generated objects.

The first statement does not pass through a tensor product over `End_A P`, nor through matrices.
Both `A` and `(End_A P)ᵐᵒᵖ` are corners of the single ring `S = End_A(A × P)ᵐᵒᵖ`: the endomorphism
ring of a retract of a module `M` is the corner of `End_A M` cut out by the idempotent of the
retract (`TauCeti.cornerEndRetractAlgEquiv`). The corner of `A` is full because `P` is finitely
generated and projective, a dual basis writing `id_P` as a sum of maps factoring through `A`; the
corner of `P` is full because `P` is a generator, which writes `id_A` as a sum of maps factoring
through `P`. Fullness makes `S` Morita equivalent to both corners
(`IsIdempotentElem.isMoritaEquivalent_corner`).

For the second statement, an equivalence `F` from `mod A` to `mod B` carries the regular module `A`
to a progenerator `P = F(A)` of `B` whose endomorphism ring is that of `A`, namely `Aᵐᵒᵖ`; these
facts about `F` are in `TauCeti/Algebra/Category/FGModuleCat/Equivalence.lean`.

## Main results

* `TauCeti.isMoritaEquivalent_moduleEnd_mulOpposite_of_sum_comp_eq_id`: if each of two modules is a
  retract of a finite power of the other, their opposite endomorphism rings are Morita equivalent.
* `TauCeti.isMoritaEquivalent_moduleEnd_mulOpposite`: **a ring is Morita equivalent to the opposite
  endomorphism ring of any progenerator.**
* `CategoryTheory.Equivalence.isMoritaEquivalent`: the algebras of two `R`-linearly equivalent
  categories of finitely generated modules are Morita equivalent.
* `TauCeti.exists_finiteModules_equivalence_iff_isMoritaEquivalent`: **`mod A` and `mod B` are
  `R`-linearly equivalent exactly when `A` and `B` are Morita equivalent.**
* `TauCeti.isMoritaEquivalent_iff_exists_progenerator`: `B` is Morita equivalent to `A` exactly when
  `B ≃ₐ[R] (End_A P)ᵐᵒᵖ` for a progenerator `P` of `A`.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, Graduate Texts in Mathematics 189, §18 (progenerators,
  Morita I and the corner-ring description).
* F. W. Anderson, K. R. Fuller, *Rings and Categories of Modules*, 2nd ed., GTM 13, Springer (1992),
  §22.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge Studies
  in Advanced Mathematics 36 (1995), §II.2.
-/

public section

open CategoryTheory MulOpposite
open scoped ModuleCat.Algebra

universe u

namespace TauCeti

section Linking

variable (R : Type*) [CommSemiring R] {A : Type*} [Ring A] [Algebra R A]
  {X Y : Type u} [AddCommGroup X] [Module A X] [Module R X] [IsScalarTower R A X]
  [AddCommGroup Y] [Module A Y] [Module R Y] [IsScalarTower R A Y]

/-- If each of two modules `X` and `Y` is a retract of a finite power of the other, their opposite
endomorphism rings are Morita equivalent. The hypotheses write each identity map as a finite sum of
maps factoring through the other module. -/
theorem isMoritaEquivalent_moduleEnd_mulOpposite_of_sum_comp_eq_id
    {ι κ : Type*} (s : Finset ι) (u : ι → X →ₗ[A] Y) (v : ι → Y →ₗ[A] X)
    (huv : ∑ j ∈ s, u j ∘ₗ v j = .id)
    (t : Finset κ) (u' : κ → Y →ₗ[A] X) (v' : κ → X →ₗ[A] Y)
    (huv' : ∑ j ∈ t, u' j ∘ₗ v' j = .id) :
    IsMoritaEquivalent R (Module.End A X)ᵐᵒᵖ (Module.End A Y)ᵐᵒᵖ := by
  have hX : LinearMap.fst A X Y ∘ₗ LinearMap.inl A X Y = .id := LinearMap.fst_comp_inl ..
  have hY : LinearMap.snd A X Y ∘ₗ LinearMap.inr A X Y = .id := LinearMap.snd_comp_inr ..
  have hsum : LinearMap.inl A X Y ∘ₗ LinearMap.fst A X Y +
      LinearMap.inr A X Y ∘ₗ LinearMap.snd A X Y = .id := by
    ext <;> simp
  have hsum' : LinearMap.inr A X Y ∘ₗ LinearMap.snd A X Y +
      LinearMap.inl A X Y ∘ₗ LinearMap.fst A X Y = .id := by
    rw [add_comm, hsum]
  have h₁ := (isIdempotentElem_op_comp hX).isMoritaEquivalent_corner R
    (span_op_comp_eq_top hX hsum s u v huv)
  have h₂ := (isIdempotentElem_op_comp hY).isMoritaEquivalent_corner R
    (span_op_comp_eq_top hY hsum' t u' v' huv')
  exact (IsMoritaEquivalent.of_algEquiv R (cornerEndRetractAlgEquiv R hX).symm).trans R
    ((h₁.symm R).trans R (h₂.trans R (.of_algEquiv R (cornerEndRetractAlgEquiv R hY))))

end Linking

section Progenerator

variable (R : Type*) [CommSemiring R] {A : Type u} [Ring A] [Algebra R A]
  (P : Type u) [AddCommGroup P] [Module A P] [Module R P] [IsScalarTower R A P]

/-- **A ring is Morita equivalent to the opposite endomorphism ring of a progenerator**: a finitely
generated projective generator `P` of `A`. For `P = A` the ring `(End_A A)ᵐᵒᵖ` is `A` itself, and
for `P = Aⁿ` it is the matrix ring `Matₙ(A)`. -/
theorem isMoritaEquivalent_moduleEnd_mulOpposite [Module.Finite A P] [Module.Projective A P]
    [Module.IsGenerator A P] : IsMoritaEquivalent R A (Module.End A P)ᵐᵒᵖ := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  obtain ⟨m, φ, x, hφ⟩ := Module.IsGenerator.exists_sum_eq_one (R := A) (M := P)
  have huv : ∑ j, (f ∘ₗ LinearMap.single A (fun _ : Fin n ↦ A) j) ∘ₗ
      (LinearMap.proj j ∘ₗ g) = .id := by
    ext y
    simpa [LinearMap.sum_apply, ← map_sum, ← LinearMap.comp_apply] using
      (congrArg f (LinearMap.sum_single_apply (fun _ ↦ A) (g y))).trans
        (LinearMap.congr_fun hfg y)
  have huv' : ∑ j, φ j ∘ₗ LinearMap.toSpanSingleton A P (x j) = .id := by
    ext
    simpa [LinearMap.sum_apply] using hφ
  have h := isMoritaEquivalent_moduleEnd_mulOpposite_of_sum_comp_eq_id R
    Finset.univ _ _ huv Finset.univ _ _ huv'
  exact (IsMoritaEquivalent.of_algEquiv R
    ((AlgEquiv.opOp R A).trans (AlgEquiv.op (AlgEquiv.moduleEndSelf R)))).trans R h

end Progenerator

end TauCeti

namespace CategoryTheory.Equivalence

open TauCeti

variable {A B : Type u} [Ring A] [Ring B] (e : FGModuleCat.{u} A ≌ FGModuleCat.{u} B)

variable (R : Type*) [CommSemiring R] [Algebra R A] [Algebra R B] [e.functor.Linear R]

include e in
/-- **If the categories of finitely generated modules are `R`-linearly equivalent, then `A` and `B`
are Morita equivalent.** The image `P` of the regular `A`-module is a progenerator of `B` with
`(End_B P)ᵐᵒᵖ ≃ₐ[R] A`. -/
theorem isMoritaEquivalent : IsMoritaEquivalent R A B :=
  have := e.moduleProjective_functor_obj_regular
  have := e.isGenerator_functor_obj_regular
  ((isMoritaEquivalent_moduleEnd_mulOpposite R (e.functor.obj (FGModuleCat.of A A))).trans R
    (.of_algEquiv R (e.algEquivMulOppositeModuleEndRegular R).symm)).symm R

end CategoryTheory.Equivalence

namespace TauCeti

variable (R : Type*) [CommSemiring R] (A B : Type u) [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/-- **Morita equivalence through finitely generated modules.** `A` and `B` are Morita equivalent
exactly when the categories of finitely generated `A`-modules and `B`-modules are `R`-linearly
equivalent. -/
theorem exists_finiteModules_equivalence_iff_isMoritaEquivalent :
    (∃ e : FGModuleCat.{u} A ≌ FGModuleCat.{u} B, e.functor.Linear R) ↔
      IsMoritaEquivalent R A B := by
  refine ⟨fun ⟨e, _⟩ ↦ e.isMoritaEquivalent R, fun ⟨⟨m⟩⟩ ↦ ?_⟩
  exact ⟨m.eqv.finiteModulesEquivalence, inferInstance⟩

/-- **Morita equivalence through progenerators.** `A` and `B` are Morita equivalent exactly when `B`
is the opposite endomorphism algebra of a progenerator of `A`. -/
theorem isMoritaEquivalent_iff_exists_progenerator :
    IsMoritaEquivalent R A B ↔
      ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module A P) (_ : Module R P)
        (_ : IsScalarTower R A P) (_ : Module.Finite A P) (_ : Module.Projective A P)
        (_ : Module.IsGenerator A P), Nonempty (B ≃ₐ[R] (Module.End A P)ᵐᵒᵖ) := by
  constructor
  · intro h
    obtain ⟨⟨m⟩⟩ := h.symm R
    let e := m.eqv.finiteModulesEquivalence
    exact ⟨e.functor.obj (FGModuleCat.of B B), inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, e.moduleProjective_functor_obj_regular,
      e.isGenerator_functor_obj_regular, ⟨e.algEquivMulOppositeModuleEndRegular R⟩⟩
  · rintro ⟨P, _, _, _, _, _, _, _, ⟨f⟩⟩
    exact (isMoritaEquivalent_moduleEnd_mulOpposite R P).trans R (.of_algEquiv R f.symm)

end TauCeti
