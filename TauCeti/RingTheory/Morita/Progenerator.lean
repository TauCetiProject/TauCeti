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
public import TauCeti.RingTheory.Morita.Corner.Basic

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
retract (`TauCeti.cornerOpEndRetractAlgEquiv`). The corner of `A` is full because `P` is finitely
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
* `TauCeti.nonempty_ofAlgEquiv_functor_obj_iso`: the image of a module under the Morita equivalence
  of an algebra isomorphism.
* `TauCeti.exists_moritaEquivalence_moduleEnd_of_comp_eq_id`: if each of two modules is a retract of
  a finite power of the other, a Morita equivalence between their endomorphism rings carries one to
  the other.
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
open scoped ModuleCat.Algebra Pointwise

universe u v

namespace TauCeti

section Linking

/-- The restriction of scalars along an isomorphism of `R`-algebras `f : A ≃ B` carries an
`A`-module `Z` to a `B`-module `W` as soon as an additive isomorphism `Z ≃ W` turns the action of
`f.symm b` into the action of `b`. -/
theorem nonempty_ofAlgEquiv_functor_obj_iso (R : Type*) [CommSemiring R] {A : Type u} {B : Type v}
    [Ring A] [Algebra R A] [Ring B] [Algebra R B] (f : A ≃ₐ[R] B) {Z : ModuleCat.{max u v} A}
    {W : ModuleCat.{max u v} B} (g : Z ≃+ W)
    (hg : ∀ (b : B) (z : Z), g (f.symm b • z) = b • g z) :
    Nonempty ((MoritaEquivalence.ofAlgEquiv f).eqv.functor.obj Z ≅ W) :=
  -- The restricted module has carrier `Z` and action `b • z = f.symm b • z`, by definition.
  let g' : (MoritaEquivalence.ofAlgEquiv f).eqv.functor.obj Z ≃ₗ[B] W :=
    { g with map_smul' := hg }
  ⟨g'.toModuleIso⟩

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
  exact (IsMoritaEquivalent.of_algEquiv R (cornerOpEndRetractAlgEquiv R hX).symm).trans R
    ((h₁.symm R).trans R (h₂.trans R (.of_algEquiv R (cornerOpEndRetractAlgEquiv R hY))))

/-- **Morita equivalence between the endomorphism rings of two modules in each other's additive
closure.** If each of two `A`-modules `X` and `Y` is a retract of a finite power of the other, a
Morita equivalence between `Module.End A X` and `Module.End A Y` carries `X` to `Y`. Both rings are
corners of `Module.End A (X × Y)` at full idempotents. -/
theorem exists_moritaEquivalence_moduleEnd_of_comp_eq_id {m n : ℕ}
    {s : Y →ₗ[A] (Fin m → X)} {r : (Fin m → X) →ₗ[A] Y} (hrs : r ∘ₗ s = .id)
    {s' : X →ₗ[A] (Fin n → Y)} {r' : (Fin n → Y) →ₗ[A] X} (hrs' : r' ∘ₗ s' = .id) :
    ∃ F : MoritaEquivalence R (Module.End A X) (Module.End A Y),
      Nonempty (F.eqv.functor.obj (ModuleCat.of _ X) ≅ ModuleCat.of _ Y) := by
  have hX : LinearMap.fst A X Y ∘ₗ LinearMap.inl A X Y = .id := LinearMap.fst_comp_inl ..
  have hY : LinearMap.snd A X Y ∘ₗ LinearMap.inr A X Y = .id := LinearMap.snd_comp_inr ..
  have hsum : LinearMap.inl A X Y ∘ₗ LinearMap.fst A X Y +
      LinearMap.inr A X Y ∘ₗ LinearMap.snd A X Y = .id := by
    ext <;> simp
  have hp := span_comp_eq_top hX hsum _ _ _ (sum_comp_eq_id_of_comp_eq_id hrs)
  have hq := span_comp_eq_top hY ((add_comm _ _).trans hsum) _ _ _
    (sum_comp_eq_id_of_comp_eq_id hrs')
  -- The `C`-module `N = X × Y`, for `C = Module.End A (X × Y)`, and its two pieces.
  let N := ModuleCat.of (Module.End A (X × Y)) (X × Y)
  let eX := isIdempotentElem_comp hX
  let eY := isIdempotentElem_comp hY
  obtain ⟨I₁⟩ := nonempty_ofAlgEquiv_functor_obj_iso R (cornerEndRetractAlgEquiv R hX).symm
    (Z := ModuleCat.of _ X) (W := eX.cornerFunctor.obj N) (smulTopRetractAddEquiv hX)
    fun c x ↦ by rw [AlgEquiv.symm_symm]; exact smulTopRetractAddEquiv_smul R hX c x
  obtain ⟨I₂⟩ := nonempty_ofAlgEquiv_functor_obj_iso R (cornerEndRetractAlgEquiv R hY)
    (Z := eY.cornerFunctor.obj N) (W := ModuleCat.of _ Y) (smulTopRetractAddEquiv hY).symm
    -- `by exact` elaborates the term against the expected type, where `eY.cornerFunctor.obj N`
    -- is already unfolded to the `smulTop` subtype; passed as a plain term, unifying the two
    -- carriers times out at `whnf`.
    fun g z ↦ by exact smulTopRetractAddEquiv_symm_smul R hY g z
  -- The corner equivalences, built directly so that their functors stay `V ↦ eV`.
  let Cp : MoritaEquivalence R (Module.End A (X × Y)) eX.Corner :=
    ⟨eX.cornerEquivalence.{u, u} hp, inferInstanceAs (eX.cornerFunctor.{u}.Linear R)⟩
  let Cq : MoritaEquivalence R (Module.End A (X × Y)) eY.Corner :=
    ⟨eY.cornerEquivalence.{u, u} hq, inferInstanceAs (eY.cornerFunctor.{u}.Linear R)⟩
  refine ⟨(MoritaEquivalence.ofAlgEquiv (cornerEndRetractAlgEquiv R hX).symm).trans R
    ((Cp.symm R).trans R (Cq.trans R
      (MoritaEquivalence.ofAlgEquiv (cornerEndRetractAlgEquiv R hY)))), ⟨?_⟩⟩
  -- `X ↦ eX ↦ N ↦ eY ↦ Y`, through the unit of the first corner equivalence.
  -- The steps are kept opaque: unfolding them against the goal is slow.
  have J₁ := (Cp.symm R).eqv.functor.mapIso I₁
  have J₂ := (Cp.eqv.unitIso.app N).symm
  have J₃ := (MoritaEquivalence.ofAlgEquiv (cornerEndRetractAlgEquiv R hY)).eqv.functor.mapIso
    (Cq.eqv.functor.mapIso (J₁ ≪≫ J₂))
  exact J₃ ≪≫ I₂

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
  have huv' : ∑ j, φ j ∘ₗ LinearMap.toSpanSingleton A P (x j) = .id := by
    ext
    simpa [LinearMap.sum_apply] using hφ
  have h := isMoritaEquivalent_moduleEnd_mulOpposite_of_sum_comp_eq_id R
    Finset.univ _ _ (sum_comp_eq_id_of_comp_eq_id hfg) Finset.univ _ _ huv'
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
