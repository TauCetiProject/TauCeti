/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Decomposition
import TauCeti.GroupTheory.Index
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.OfModule
import TauCeti.RepresentationTheory.Simple.Basic

/-!
# The representation decomposition in Clifford's theorem

Let `N` be a normal subgroup of a finite group `G`, and let `W` be an irreducible
finite-dimensional representation of `G` over a splitting field. The isotypic components of the
restriction of `W` to `N` are indexed by the inertia cosets of any one constituent `V`, and every
component is a power of its constituent with one common positive exponent `e`. Combining these
two statements gives the classical decomposition

`Res_N W ≅ ⨁ (g : G / inertia V), e · {}^g V`.

The quotient index is preferable to a chosen transversal: `Quotient.out g` supplies the conjugate
representative, while changing that representative changes the summand only up to isomorphism.

## Main definitions

* `TauCeti.cliffordSum`: the finite sum of `e` copies of the conjugate of `V` attached to every
  inertia coset.

## Main result

* `TauCeti.clifford_restrict_iso`: **Clifford's theorem, representation form**. It supplies a
  simple constituent, a positive common multiplicity, and an isomorphism from the restriction to
  `cliffordSum`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 6.
* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §49.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra

universe u v

namespace TauCeti

/-- The finite sum of `e` copies of every conjugate of `V` indexed by the left cosets of its
inertia group. A finite product of modules is their direct sum; `FDRep.ofShrink` only returns its
possibly larger carrier to the universe in which `FDRep k N` lives. -/
noncomputable def cliffordSum {k : Type u} {G : Type v} [Field k] [Group G]
    {N : Subgroup G} [N.Normal] [Finite G] (V : FDRep k N) (e : ℕ) : FDRep k N :=
  FDRep.ofShrink <| Representation.ofModule' (k := k) (G := N)
    ((q : G ⧸ inertia V) → Fin e →
      _root_.Representation.asModule (conjNormalFDRep (Quotient.out q) V).ρ)

/-- The module carried by an isotypic component is `e` copies of the translated constituent that
defines it, where `e` is the common Clifford multiplicity. -/
private noncomputable def componentLinearEquiv
    {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [Group G]
    {X : Type u} [AddCommGroup X] [Module k X] {N : Subgroup G} [N.Normal]
    (ρ : Representation k G X) [FiniteDimensional k X] [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) (e : ℕ)
    (hcommon : ∀ τ : Subrepresentation (ρ.comp N.subtype), IsAtom τ →
      Module.finrank k
        (τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) = e)
    (q : G ⧸ inertia (FDRep.of σ.toRepresentation)) :
    ((ρ.isotypicComponentsEquivQuotientInertia σ hσ).symm q).1 ≃ₗ[k[N]]
      Fin e → _root_.Representation.asModule
        (conjNormalFDRep (Quotient.out q) (FDRep.of σ.toRepresentation)).ρ := by
  let g : G := Quotient.out q
  have hq : QuotientGroup.mk g = q := Quotient.out_eq' q
  have hc : (ρ.isotypicComponentsEquivQuotientInertia σ hσ).symm q =
      ρ.conjSubrepIsotypicComponent σ hσ g := by
    rw [← hq]
    exact ρ.isotypicComponentsEquivQuotientInertia_symm_mk σ hσ g
  let τ := Representation.conjSubrep ρ g σ
  have hτ : IsAtom τ := Representation.isAtom_conjSubrep_iff.mpr hσ
  let _ : IsSimpleModule k[N] τ.asSubmodule :=
    Subrepresentation.isSimpleModule_asSubmodule_iff.mpr hτ
  let _ : FiniteDimensional k τ.asSubmodule :=
    Module.Finite.of_injective (τ.asSubmodule.subtype.restrictScalars k) Subtype.val_injective
  let eComponent := (nonempty_linearEquiv_isotypicComponent
    (k := k) (A := k[N])
    (M := _root_.Representation.asModule (ρ.comp N.subtype)) (S := τ.asSubmodule)).some
  have hmultiplicity : Module.finrank k
      (τ.asSubmodule →ₗ[k[N]] _root_.Representation.asModule (ρ.comp N.subtype)) = e :=
    hcommon τ hτ
  rw [hmultiplicity] at eComponent
  let i := Representation.fdRepIsoConjSubrep ρ g σ
  let iRep := (nonempty_fdRepIso_iff.mp ⟨i⟩).some
  let eConj : τ.asSubmodule ≃ₗ[k[N]] _root_.Representation.asModule
      (conjNormalFDRep g (FDRep.of σ.toRepresentation)).ρ :=
    (_root_.Subrepresentation.asModuleEquivAsSubmodule τ).symm.trans
      (Representation.asModuleLinearEquivOfEquiv iRep)
  rw [hc, Representation.coe_conjSubrepIsotypicComponent]
  simpa only [τ, g] using
    eComponent.trans (LinearEquiv.piCongrRight fun _ ↦ eConj)

/-- **Clifford's theorem, representation form.** The restriction of an irreducible
representation to a normal subgroup is isomorphic to `e` copies of every conjugate of one simple
constituent, with the distinct conjugates indexed by the left cosets of its inertia group.

The hypothesis on `Nat.card G` is Maschke's condition. Algebraic closure makes `k` a splitting
field, so the Hom-space dimension in the multiplicity theorem is the actual number of copies. -/
theorem clifford_restrict_iso {k : Type u} {G : Type v} [Field k] [Group G]
    {N : Subgroup G} [N.Normal] [Finite G] [IsAlgClosed k]
    (hG : IsUnit (Nat.card G : k)) (W : FDRep k G) [Simple W] :
    ∃ (V : FDRep k N) (_ : Simple V) (e : ℕ),
      e ≠ 0 ∧ Nonempty (resFDRep N W ≅ cliffordSum V e) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Invertible (Nat.card G : k) := hG.invertible
  let _ : Fintype N := Fintype.ofFinite N
  let _ : Invertible (Nat.card N : k) := (isUnit_natCard_subgroup N hG).invertible
  let _ : Representation.IsIrreducible W.ρ := FDRep.isIrreducible_of_simple W
  let _ : Representation.IsSemisimpleRepresentation (W.ρ.comp N.subtype) :=
    Representation.isSemisimpleRepresentation_comp_subtype W.ρ
  obtain ⟨σ, hσ, -⟩ :=
    Representation.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep (N := N) W.ρ
  let V : FDRep k N := FDRep.of σ.toRepresentation
  let _ : Representation.IsIrreducible V.ρ :=
    Representation.isIrreducible_toRepresentation_of_isAtom hσ
  let _ : Simple V := FDRep.simple_of_isIrreducible V
  obtain ⟨e, he, hcommon⟩ :=
    Representation.exists_forall_finrank_linearMap_eq (N := N) W.ρ
  let C := isotypicComponents k[N]
    (_root_.Representation.asModule (W.ρ.comp N.subtype))
  let orbitEquiv : C ≃ G ⧸ inertia V :=
    Representation.isotypicComponentsEquivQuotientInertia W.ρ σ hσ
  let _ : Finite C := Finite.of_injective orbitEquiv orbitEquiv.injective
  let _ : Fintype C := Fintype.ofFinite C
  have hind : iSupIndep (fun c : C ↦ c.1) :=
    (sSupIndep_iff _).mp (sSupIndep_isotypicComponents k[N]
      (_root_.Representation.asModule (W.ρ.comp N.subtype)))
  have htop : ⨆ c : C, c.1 = ⊤ :=
    (sSup_eq_iSup' C).symm.trans
      (sSup_isotypicComponents k[N]
        (_root_.Representation.asModule (W.ρ.comp N.subtype)))
  let splitComponents :
      _root_.Representation.asModule (W.ρ.comp N.subtype) ≃ₗ[k[N]] (c : C) → c.1 :=
    (hind.linearEquiv htop).symm.trans DFinsupp.linearEquivFunOnFintype
  let indexComponents : ((c : C) → c.1) ≃ₗ[k[N]]
      (q : G ⧸ inertia V) → (orbitEquiv.symm q).1 :=
    LinearEquiv.piCongrLeft' k[N] (fun c : C ↦ c.1) orbitEquiv
  let splitMultiplicity : ((q : G ⧸ inertia V) → (orbitEquiv.symm q).1) ≃ₗ[k[N]]
      (q : G ⧸ inertia V) → Fin e → _root_.Representation.asModule
        (conjNormalFDRep (Quotient.out q) V).ρ :=
    LinearEquiv.piCongrRight fun q ↦ by
      simpa only [orbitEquiv, V] using componentLinearEquiv W.ρ σ hσ e hcommon q
  let target := Representation.ofModule' (k := k) (G := N)
    ((q : G ⧸ inertia V) → Fin e → _root_.Representation.asModule
      (conjNormalFDRep (Quotient.out q) V).ρ)
  let moduleEquiv : _root_.Representation.asModule (resFDRep N W).ρ ≃ₗ[k[N]]
      _root_.Representation.asModule target :=
    splitComponents.trans indexComponents |>.trans splitMultiplicity |>.trans
      (Representation.ofModule'AsModuleEquiv _).symm
  let representationEquiv : _root_.Representation.Equiv (resFDRep N W).ρ target :=
    Representation.equivOfAsModuleLinearEquiv moduleEquiv
  have hfinal : Nonempty (_root_.Representation.Equiv
      (resFDRep N W).ρ (cliffordSum V e).ρ) :=
    ⟨representationEquiv.trans (FDRep.ofShrinkEquiv target).symm⟩
  exact ⟨V, inferInstance, e, Nat.ne_of_gt he, nonempty_fdRepIso_iff.mpr hfinal⟩

end TauCeti
