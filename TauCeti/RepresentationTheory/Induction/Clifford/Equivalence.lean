/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Decomposition
import TauCeti.LinearAlgebra.Trace.Pi
import TauCeti.RepresentationTheory.OfModule
import TauCeti.RepresentationTheory.Simple.Basic

/-
Roadmap source: `TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`, Layer 5.
-/

/-!
# The representation decomposition in Clifford's theorem

Let `N` be a normal subgroup of a group `G`, and let `W` be an irreducible
finite-dimensional representation of `G` over a splitting field. The isotypic components of the
restriction of `W` to `N` are indexed by the inertia cosets of any one constituent `V`, and every
component is a power of its constituent with one common positive exponent `e`. Combining these
two statements gives the classical decomposition

`Res_N W ≅ ⨁ (g : G / inertia V), e · {}^g V`.

The quotient index is preferable to a chosen transversal: `Quotient.out g` supplies the conjugate
representative, while changing that representative changes the summand only up to isomorphism.

## Main definitions

* `FDRep.cliffordSum`: the finite sum of `e` copies of the conjugate of `V` attached to every
  inertia coset.
## Main properties

* `FDRep.finrank_cliffordSum` and `FDRep.character_cliffordSum`: its dimension and character.

## Main result

* `FDRep.clifford_restrict_iso_of_isAtom`: **Clifford's theorem for a specified constituent**.
* `FDRep.clifford_restrict_iso`: **Clifford's theorem, representation form**. It supplies a
  simple constituent, finiteness of its inertia quotient, a positive common multiplicity, and an
  isomorphism from the restriction to `cliffordSum`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 6.
* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §49.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra

universe u v

namespace FDRep

open TauCeti

/-- The finite sum of `e` copies of every conjugate of `V` indexed by the left cosets of its
inertia group. A finite product of modules is their direct sum; `FDRep.ofShrink` only returns its
possibly larger carrier to the universe in which `FDRep k N` lives. -/
noncomputable def cliffordSum {k : Type u} {G : Type v} [Field k] [Group G]
    {N : Subgroup G} [N.Normal] (V : FDRep k N) [Finite (G ⧸ inertia V)]
    (e : ℕ) : FDRep k N :=
  FDRep.ofShrink <| Representation.ofModule' (k := k) (G := N)
    ((q : G ⧸ inertia V) → Fin e →
      _root_.Representation.asModule (conjNormalFDRep (Quotient.out q) V).ρ)

/-- The dimension of `V.cliffordSum e` is the number of inertia cosets times `e` times the
dimension of `V`. -/
@[simp]
theorem finrank_cliffordSum {k : Type u} {G : Type v} [Field k] [Group G]
    {N : Subgroup G} [N.Normal] (V : FDRep k N) [Finite (G ⧸ inertia V)] (e : ℕ) :
    Module.finrank k (V.cliffordSum e) =
      Nat.card (G ⧸ inertia V) * e * Module.finrank k V := by
  classical
  let _ : Fintype (G ⧸ inertia V) := Fintype.ofFinite _
  rw [cliffordSum, finrank_ofShrink, Module.finrank_pi_fintype]
  simp_rw [Module.finrank_pi_fintype,
    (_root_.Representation.asModuleEquiv _).finrank_eq]
  simp [Nat.card_eq_fintype_card, mul_assoc]

/-- The character of `V.cliffordSum e` is `e` times the sum of the characters of its conjugate
summands. -/
@[simp]
theorem character_cliffordSum {k : Type u} {G : Type v} [Field k] [Group G]
    {N : Subgroup G} [N.Normal] (V : FDRep k N) [Finite (G ⧸ inertia V)]
    (e : ℕ) (x : N) :
    (V.cliffordSum e).character x =
      (e : k) * ∑ᶠ q : G ⧸ inertia V,
        (conjNormalFDRep (Quotient.out q) V).character x := by
  classical
  let _ : Fintype (G ⧸ inertia V) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ) _ (by simp)]
  rw [cliffordSum, character_ofShrink, _root_.Representation.character]
  let f (q : G ⧸ inertia V) :
      (Fin e → _root_.Representation.asModule
        (conjNormalFDRep (Quotient.out q) V).ρ) →ₗ[k]
      (Fin e → _root_.Representation.asModule
        (conjNormalFDRep (Quotient.out q) V).ρ) := {
    toFun z i := (conjNormalFDRep (Quotient.out q) V).ρ x (z i)
    map_add' a b := funext fun i ↦ map_add _ _ _
    map_smul' a b := funext fun i ↦ map_smul _ _ _
  }
  have htarget : ∀ z q,
      (_root_.Representation.ofModule' (k := k) (G := N)
        ((q : G ⧸ inertia V) → Fin e →
          _root_.Representation.asModule (conjNormalFDRep (Quotient.out q) V).ρ)) x z q =
        f q (z q) := by
    intro z q
    ext i
    simp only [f]
    rw [TauCeti.Representation.ofModule'_apply]
    rw [Pi.smul_apply, Pi.smul_apply, _root_.Representation.single_smul, one_smul,
      _root_.Representation.asModuleEquiv_apply]
    rfl
  rw [LinearMap.trace_pi_of_apply_eq_dependent _ f htarget]
  let g (q : G ⧸ inertia V) :
      _root_.Representation.asModule (conjNormalFDRep (Quotient.out q) V).ρ →ₗ[k]
      _root_.Representation.asModule (conjNormalFDRep (Quotient.out q) V).ρ :=
    (_root_.Representation.asModuleEquiv
      (conjNormalFDRep (Quotient.out q) V).ρ).symm.conj
        ((conjNormalFDRep (Quotient.out q) V).ρ x)
  have hg (q : G ⧸ inertia V) : LinearMap.trace k _ (g q) =
      (conjNormalFDRep (Quotient.out q) V).character x := by
    simp only [g]
    rw [LinearMap.trace_conj', FDRep.character]
  have hf (q : G ⧸ inertia V) : LinearMap.trace k _ (f q) =
      (e : k) * (conjNormalFDRep (Quotient.out q) V).character x := by
    have hfg : ∀ z i, f q z i = g q (z i) := by
      intro z i
      simp only [f, g, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_symm]
      apply (_root_.Representation.asModuleEquiv
        (conjNormalFDRep (Quotient.out q) V).ρ).injective
      rw [LinearEquiv.apply_symm_apply, _root_.Representation.asModuleEquiv_apply]
      rfl
    rw [LinearMap.trace_pi_of_apply_eq (f q) id (fun _ ↦ g q) hfg]
    simp [hg]
  simp_rw [hf]
  rw [Finset.mul_sum]

end FDRep

namespace TauCeti

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

end TauCeti

namespace FDRep

open TauCeti

/-- **Clifford's theorem for a specified constituent.** Given a simple constituent `σ` of the
restriction of an irreducible representation to a normal subgroup, the restriction is isomorphic
to `e` copies of every conjugate of `σ`, with the distinct conjugates indexed by the left cosets
of its inertia group.

Algebraic closure makes `k` a splitting field, so the Hom-space dimension in the multiplicity
theorem is the actual number of copies. Finite dimensionality makes the set of isotypic components,
and hence the inertia quotient indexing the sum, finite. -/
theorem clifford_restrict_iso_of_isAtom {k : Type u} {G : Type v} [Field k] [Group G]
    {N : Subgroup G} [N.Normal] [IsAlgClosed k]
    (W : FDRep k G) [Simple W] (σ : Subrepresentation (W.ρ.comp N.subtype))
    (hσ : IsAtom σ) :
    ∃ hfinite : Finite (G ⧸ inertia (FDRep.of σ.toRepresentation)),
      let _ := hfinite
      ∃ e : ℕ, e ≠ 0 ∧
        Nonempty (resFDRep N W ≅ (FDRep.of σ.toRepresentation).cliffordSum e) := by
  classical
  let _ : Representation.IsIrreducible W.ρ := FDRep.isIrreducible_of_simple W
  let _ : IsSemisimpleModule k[N]
      (_root_.Representation.asModule (W.ρ.comp N.subtype)) :=
    (_root_.Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
      (W.ρ.comp N.subtype)).mp
      (Representation.isSemisimpleRepresentation_comp_subtype W.ρ)
  let _ : Module.Finite k[N]
      (_root_.Representation.asModule (W.ρ.comp N.subtype)) :=
    Module.Finite.of_restrictScalars_finite k k[N] _
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
  let hfinite : Finite (G ⧸ inertia V) :=
    Finite.of_surjective orbitEquiv orbitEquiv.surjective
  refine ⟨hfinite, ?_⟩
  let _ := hfinite
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
      (resFDRep N W).ρ (V.cliffordSum e).ρ) :=
    ⟨representationEquiv.trans (FDRep.ofShrinkEquiv target).symm⟩
  exact ⟨e, Nat.ne_of_gt he, nonempty_fdRepIso_iff.mpr hfinal⟩

/-- **Clifford's theorem, representation form.** The restriction of an irreducible
representation to a normal subgroup is isomorphic to `e` copies of every conjugate of one simple
constituent, with the distinct conjugates indexed by the left cosets of its inertia group.

Algebraic closure makes `k` a splitting field, so the Hom-space dimension in the multiplicity
theorem is the actual number of copies. The conclusion includes the finite inertia quotient that
indexes the sum. -/
theorem clifford_restrict_iso {k : Type u} {G : Type v} [Field k] [Group G]
    {N : Subgroup G} [N.Normal] [IsAlgClosed k]
    (W : FDRep k G) [Simple W] :
    ∃ (V : FDRep k N) (_ : Simple V) (hfinite : Finite (G ⧸ inertia V)),
      let _ := hfinite
      ∃ e : ℕ, e ≠ 0 ∧ Nonempty (resFDRep N W ≅ V.cliffordSum e) := by
  classical
  let _ : Representation.IsIrreducible W.ρ := FDRep.isIrreducible_of_simple W
  obtain ⟨σ, hσ, -⟩ :=
    Representation.exists_isAtom_forall_nonempty_linearEquiv_conjSubrep (N := N) W.ρ
  let V : FDRep k N := FDRep.of σ.toRepresentation
  let _ : Representation.IsIrreducible V.ρ :=
    Representation.isIrreducible_toRepresentation_of_isAtom hσ
  let _ : Simple V := FDRep.simple_of_isIrreducible V
  obtain ⟨hfinite, e, he, h⟩ := W.clifford_restrict_iso_of_isAtom σ hσ
  exact ⟨V, inferInstance, hfinite, e, he, h⟩

end FDRep
