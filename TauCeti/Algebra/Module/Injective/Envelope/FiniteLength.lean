/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.Envelope.Basic
import TauCeti.Algebra.Module.Injective.SelfInjective
public import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Projection

/-!
# Injective envelopes inside finite-length injectives

Every embedding into a finite-length injective module can be restricted to an injective envelope.
Thus, to obtain finite-length injective envelopes, it suffices to construct finite-length
injective modules containing the modules in question. This is useful for finite-dimensional
algebras, where finite powers of the dual regular module provide such embeddings.

The ambient ring and module may have different universes; `Small` is needed for the
universe-polymorphic extension property of an injective module.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, Section 3.
-/

public section

namespace TauCeti

universe u v w

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
  {Q : Type w} [AddCommGroup Q] [Module R Q] [Small.{w} R]

variable (R) in
/-- Every embedding into a finite-length injective module restricts to an injective envelope
inside that ambient module. In particular the envelope is itself of finite length. -/
theorem exists_isInjectiveEnvelope_submodule [IsArtinian R Q] [IsNoetherian R Q]
    [Module.Injective R Q]
    (i : M →ₗ[R] Q) (hi : Function.Injective i) :
    ∃ (P : Submodule R Q) (hP : LinearMap.range i ≤ P),
      IsInjectiveEnvelope (i.codRestrict P (fun x => hP ⟨x, rfl⟩)) := by
  classical
  -- Choose a minimal injective submodule containing the given image.
  obtain ⟨P, hP⟩ := exists_minimal_of_wellFoundedLT
    (fun P : Submodule R Q => LinearMap.range i ≤ P ∧ Module.Injective R P)
    ⟨⊤, le_top, Module.Baer.injective
      ((Module.Baer.of_injective (inferInstance : Module.Injective R Q)).of_equiv
        Submodule.topEquiv.symm)⟩
  let j := i.codRestrict P (fun x => hP.prop.1 ⟨x, rfl⟩)
  have hj : Function.Injective j := fun x y h => hi (congrArg Subtype.val h)
  let : Module.Injective R P := hP.prop.2
  refine ⟨P, hP.prop.1, ⟨inferInstance, hj, ?_⟩⟩
  apply (isEssential_range_iff_forall_injective hj).2
  intro X _ _ h hh
  let := Module.addCommMonoidToAddCommGroup R (M := X)
  -- Extend the original embedding across `h ∘ j`. The resulting endomorphism fixes `j`.
  obtain ⟨g, hg⟩ := Module.Injective.extension_property R P M X (h ∘ₗ j) hh j
  let f : Module.End R P := g ∘ₗ h
  have hf (x : M) : f (j x) = j x := LinearMap.congr_fun hg x
  have hpow (n : ℕ) (x : M) : (f ^ n) (j x) = j x := by
    induction n with
    | zero => simp
    | succ n hn => simp [pow_succ', Module.End.mul_apply, hn, hf]
  -- Fitting's decomposition makes the stable image another injective summand containing `j`.
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp f.eventually_isCompl_ker_pow_range_pow
  let n := n₀ + 1
  have hn := hn₀ n (Nat.le_succ n₀)
  let V := LinearMap.range (f ^ n)
  have hV : Module.Injective R V := Module.Baer.injective
    ((Module.Baer.of_injective (inferInstance : Module.Injective R P)).of_leftInverse
      V.subtype (V.projectionOnto (LinearMap.ker (f ^ n)) hn.symm)
      (fun x => Submodule.projectionOnto_apply_left hn.symm x))
  let W := V.map P.subtype
  have hW : Module.Injective R W := Module.Baer.injective
    ((Module.Baer.of_injective hV).of_equiv
      (Submodule.equivMapOfInjective P.subtype P.injective_subtype V))
  have hiW : LinearMap.range i ≤ W := by
    rintro _ ⟨x, rfl⟩
    exact ⟨j x, ⟨j x, hpow n x⟩, rfl⟩
  have hWP : W ≤ P := Submodule.map_le_iff_le_comap.mpr (by simp)
  have hPW : P ≤ W := hP.le_of_le ⟨hiW, hW⟩ hWP
  have hVtop : V = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, hy, he⟩ := hPW x.property
    exact (Subtype.ext he : y = x) ▸ hy
  have hker : LinearMap.ker (f ^ n) = ⊥ := by
    have hn' : IsCompl (LinearMap.ker (f ^ n)) V := hn
    simpa only [hVtop, inf_top_eq] using hn'.inf_eq_bot
  have hfn : Function.Injective (f ^ n) := LinearMap.ker_eq_bot.mp hker
  have hfinj : Function.Injective f :=
    Module.End.injective_of_iterate_injective (Nat.succ_ne_zero n₀) hfn
  exact fun x y hxy => hfinj (by simp [f, hxy])

end TauCeti
