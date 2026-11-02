/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import TauCeti.RingTheory.LocalRing.RingHom
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Units and residue fields of inverse limits of rings

For a tower of commutative rings whose transition maps reflect units, the projection from its
limit to stage zero also reflects units. Consequently its kernel is contained in the Jacobson
radical. If the transitions are also surjective, every residue field of the limit factors
uniquely through stage zero.

Surjective transitions with elementwise nilpotent kernels satisfy these hypotheses. No uniform
nilpotence exponent, Noetherian hypothesis, or local-ring hypothesis is needed. This is the
ring-theoretic input that allows a uniform bound on residue fibres at stage zero to control all
residue fibres of an inverse limit.

The limit is an arbitrary limiting cone in `CommRingCat`, rather than a new construction of the
inverse-limit ring. Unit detection uses Mathlib's
`CommRingCat.Limits.π_isLocalHom`, and residue-field descent uses
`RingHom.liftOfSurjective`.

## References

* Stacks Project, More on Algebra, proof of Lemma 15.99.3, Tag 0CQG.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Limits

variable {F : ℕᵒᵖ ⥤ CommRingCat.{u}} {c : Cone F}

/-- If every successive transition of a ring tower reflects units, so does the projection from
its limit to stage zero. The rings need not be local and the transitions need not be surjective.
-/
theorem IsLimit.isLocalHom_π_app_zero_of_isLocalHom_map (hc : IsLimit c)
    (hF : ∀ n, IsLocalHom (F.map (homOfLE (Nat.le_succ n)).op).hom) :
    IsLocalHom (c.π.app (Opposite.op 0)).hom := by
  have h : ∀ n, IsLocalHom (F.map (homOfLE (Nat.zero_le n)).op).hom := by
    intro n
    induction n with
    | zero => simpa using isLocalHom_id (F.obj (Opposite.op 0))
    | succ n ih =>
      have := ih
      have := hF n
      simpa only [← CommRingCat.hom_comp, ← F.map_comp, ← op_comp, homOfLE_comp] using
        (inferInstance : IsLocalHom
          ((F.map (homOfLE (Nat.zero_le n)).op).hom.comp
            (F.map (homOfLE (Nat.le_succ n)).op).hom))
  refine CommRingCat.Limits.π_isLocalHom F hc (Opposite.op 0) fun x _ ⟨n⟩ ↦
    ⟨Opposite.op 0, (homOfLE (Nat.zero_le n)).op, 𝟙 _, h n, ?_⟩
  simpa using c.w_apply (homOfLE (Nat.zero_le n)).op x

/-- The kernel of stage-zero projection is in the Jacobson radical when all successive
transitions reflect units. -/
theorem IsLimit.ker_π_app_zero_le_jacobson_bot_of_isLocalHom_map (hc : IsLimit c)
    (hF : ∀ n, IsLocalHom (F.map (homOfLE (Nat.le_succ n)).op).hom) :
    RingHom.ker (c.π.app (Opposite.op 0)).hom ≤ Ideal.jacobson (⊥ : Ideal c.pt) := by
  have := hc.isLocalHom_π_app_zero_of_isLocalHom_map hF
  exact (c.π.app (Opposite.op 0)).hom.ker_le_jacobson_bot

/-- For surjective transitions with elementwise nilpotent kernels, the projection from the
limit to stage zero reflects units. Each kernel may have unbounded nilpotence exponents. -/
theorem IsLimit.isLocalHom_π_app_zero_of_isNilpotent_ker (hc : IsLimit c)
    (hsurj : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op))
    (hnil : ∀ n x, (F.map (homOfLE (Nat.le_succ n)).op) x = 0 → IsNilpotent x) :
    IsLocalHom (c.π.app (Opposite.op 0)).hom :=
  hc.isLocalHom_π_app_zero_of_isLocalHom_map fun n ↦
    (F.map (homOfLE (Nat.le_succ n)).op).hom.isLocalHom_of_surjective_of_isNilpotent_ker
      (hsurj n) (hnil n)

/-- The stage-zero projection of a tower with surjective transitions and locally nilpotent
kernels has kernel contained in the Jacobson radical of the limit ring. -/
theorem IsLimit.ker_π_app_zero_le_jacobson_bot_of_isNilpotent_ker (hc : IsLimit c)
    (hsurj : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op))
    (hnil : ∀ n x, (F.map (homOfLE (Nat.le_succ n)).op) x = 0 → IsNilpotent x) :
    RingHom.ker (c.π.app (Opposite.op 0)).hom ≤ Ideal.jacobson (⊥ : Ideal c.pt) := by
  have := hc.isLocalHom_π_app_zero_of_isNilpotent_ker hsurj hnil
  exact (c.π.app (Opposite.op 0)).hom.ker_le_jacobson_bot

/-- Every residue field of the limit of a surjective ring tower whose transitions reflect
units is uniquely a quotient of stage zero, compatibly with the original residue map. -/
theorem IsLimit.existsUnique_comp_π_app_zero_eq_quotientMk_of_isLocalHom_map (hc : IsLimit c)
    (hsurj : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op))
    (hF : ∀ n, IsLocalHom (F.map (homOfLE (Nat.le_succ n)).op).hom)
    (m : Ideal c.pt) [m.IsMaximal] :
    ∃! f : F.obj (Opposite.op 0) →+* c.pt ⧸ m,
      f.comp (c.π.app (Opposite.op 0)).hom = Ideal.Quotient.mk m := by
  have hπ := Concrete.surjective_π_app_zero_of_surjective_map hc hsurj
  have hker : RingHom.ker (c.π.app (Opposite.op 0)).hom ≤ RingHom.ker (Ideal.Quotient.mk m) := by
    rw [Ideal.mk_ker]
    exact (hc.ker_π_app_zero_le_jacobson_bot_of_isLocalHom_map hF).trans
      ((Ideal.jacobson_mono bot_le).trans (le_of_eq (Ideal.jacobson_eq_self_of_isMaximal (I := m))))
  refine ⟨(c.π.app (Opposite.op 0)).hom.liftOfSurjective hπ ⟨Ideal.Quotient.mk m, hker⟩,
    RingHom.liftOfSurjective_comp _ _ _, ?_⟩
  exact fun f hf ↦ (c.π.app (Opposite.op 0)).hom.eq_liftOfSurjective hπ _ hker f hf

/-- Every residue field of the limit of a surjective ring tower with locally nilpotent kernels
factors uniquely through stage zero. The factorization retains the given residue map. -/
theorem IsLimit.existsUnique_comp_π_app_zero_eq_quotientMk_of_isNilpotent_ker (hc : IsLimit c)
    (hsurj : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op))
    (hnil : ∀ n x, (F.map (homOfLE (Nat.le_succ n)).op) x = 0 → IsNilpotent x)
    (m : Ideal c.pt) [m.IsMaximal] :
    ∃! f : F.obj (Opposite.op 0) →+* c.pt ⧸ m,
      f.comp (c.π.app (Opposite.op 0)).hom = Ideal.Quotient.mk m :=
  hc.existsUnique_comp_π_app_zero_eq_quotientMk_of_isLocalHom_map hsurj
    (fun n ↦ (F.map (homOfLE (Nat.le_succ n)).op).hom.isLocalHom_of_surjective_of_isNilpotent_ker
      (hsurj n) (hnil n)) m

end CategoryTheory.Limits
