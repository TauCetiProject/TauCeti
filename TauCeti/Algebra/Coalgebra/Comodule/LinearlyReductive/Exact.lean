/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.LinearHom
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Fixed
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic
import TauCeti.Algebra.Coalgebra.Subcomodule.Quotient
import TauCeti.Algebra.Coalgebra.Comodule.Preadditive

/-!
# Linear reductivity from exactness of invariants

A commutative Hopf algebra over a field is linearly reductive if and only if taking
invariant vectors preserves surjections between finite-dimensional comodules. It suffices
to test carriers in the base field's universe, just as for linear reductivity itself.

The converse lifts the identity in the invariant part of a linear Hom comodule to obtain
an equivariant section of any surjective morphism. Applied to a quotient by a subcomodule,
this gives an invariant complement. This characterization allows linear reductivity of
an extension of affine groups to be established by taking kernel and quotient invariants
successively.

No finite-type, smoothness, connectedness or characteristic hypothesis is required.
The forward implication reuses the invariant-lifting theorem in
`Comodule.LinearlyReductive.Fixed`; the converse uses `Comodule.fixedLinearHomEquiv`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
-/

public section

namespace TauCeti

universe u v

noncomputable section

attribute [local instance] Comodule.linearHom

namespace Coalgebra

variable {k : Type u} [Field k] {H : Type v} [CommSemiring H] [HopfAlgebra k H]

/-- A commutative Hopf algebra is linearly reductive exactly when invariant vectors
preserve surjections of finite-dimensional comodules. Testing carriers in the field's
universe suffices, even when the Hopf algebra lies in a different universe. -/
theorem isLinearlyReductive_iff_forall_fixedMap_surjective_of_surjective :
    IsLinearlyReductive.{u, v, u} k H ↔
      ∀ (M N : FGComoduleCat.{u, v, u} k H) (f : M ⟶ N),
        Function.Surjective f.hom → Function.Surjective f.hom.fixedMap := by
  let _ : AddCommGroup H := Module.addCommMonoidToAddCommGroup k
  constructor
  · intro h M N f hf
    exact f.hom.fixedMap_surjective_of_isLinearlyReductive h hf
  · intro h
    apply IsLinearlyReductive.of_forall_isCompletelyReducible
    intro V _ _ _ _
    let _ : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
    apply Comodule.isCompletelyReducible_iff_forall_exists_hom.mpr
    intro W
    let Q := V ⧸ W.toSubmodule
    let q : Comodule.Hom k H V Q := W.mkQ
    let p := q.linearHomPostcomp (M := Q)
    have hp : Function.Surjective p := q.linearHomPostcomp_surjective W.mkQ_surjective
    obtain ⟨s, hs⟩ := q.exists_rightInverse_of_linearHomPostcomp_fixedMap_surjective
      (h (FGComoduleCat.of (R := k) (C := H) (Q →ₗ[k] V))
        (FGComoduleCat.of (R := k) (C := H) (Q →ₗ[k] Q)) (FGComoduleCat.ofHom p) hp)
    let P := Comodule.Hom.id k H V - s.comp q
    have hqs (z : Q) : q (s z) = z := by
      simpa only [Comodule.Hom.comp_apply, Comodule.Hom.id_apply] using
        congrArg (fun f : Comodule.Hom k H Q Q ↦ f z) hs
    refine ⟨P, fun z ↦ ?_, fun z hz ↦ ?_⟩
    · apply (W.mkQ_eq_zero_iff (P z)).mp
      have hqP : q (P z) = 0 := by
        simp only [P, Comodule.Hom.sub_apply, Comodule.Hom.id_apply,
          Comodule.Hom.comp_apply]
        rw [← Comodule.Hom.coe_toLinearMap q, map_sub]
        simp only [Comodule.Hom.coe_toLinearMap, hqs, sub_self]
      exact hqP
    · simp only [P, Comodule.Hom.sub_apply, Comodule.Hom.id_apply,
        Comodule.Hom.comp_apply]
      dsimp only [q]
      rw [(W.mkQ_eq_zero_iff z).mpr hz, ← Comodule.Hom.coe_toLinearMap s,
        map_zero, sub_zero]

end Coalgebra

end

end TauCeti
