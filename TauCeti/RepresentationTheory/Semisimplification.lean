/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.Charpoly
public import TauCeti.RepresentationTheory.OfModule
public import TauCeti.RingTheory.CompositionSeries.Semisimplification.Charpoly
import TauCeti.RepresentationTheory.Subrepresentation.Semisimple

/-!
# The semisimplification of a representation

For a finite-dimensional representation `ρ` of a monoid `G` on `V` over a field `k`, the
semisimplification `V^ss` is the direct sum of the Jordan-Hölder factors of `V`, the
semisimplification `TauCeti.semisimplification k[G] ρ.asModule` of the `k[G]`-module attached to
`ρ`. This file equips it with its representation `ρ.semisimplification` of `G`, through
`Representation.ofModule'`, and records its basic properties: it is semisimple, it is equivalent to
`ρ` exactly when `ρ` is semisimple, and every `g ∈ G` has the same characteristic polynomial, trace
and determinant on `V^ss` as on `V`.

## Main declarations

* `Representation.semisimplification ρ`: the representation of `G` on `V^ss`.
* `Representation.isSemisimpleRepresentation_semisimplification`: `V^ss` is semisimple.
* `Representation.nonempty_equiv_semisimplification_iff`: `V^ss ≅ V` exactly when `ρ` is
  semisimple.
* `Representation.charpoly_semisimplification_apply`,
  `Representation.trace_semisimplification_apply`, `Representation.char_semisimplification`,
  `Representation.det_semisimplification_apply`: `V^ss` and `V` have the same characteristic
  polynomials, traces, characters and determinants.
* `Representation.nonempty_equiv_semisimplification_semisimplification`: `(V^ss)^ss ≅ V^ss`.
* `Representation.nonempty_equiv_semisimplification_of_equiv`: equivalent representations have
  equivalent semisimplifications.
* `Representation.nonempty_equiv_semisimplification_prod_of_exact`: for a short exact sequence
  `0 → U → V → X → 0` of representations, `V^ss ≅ U^ss ⊕ X^ss`.
* `Subrepresentation.nonempty_equiv_semisimplification_prod_quotient`: for a subrepresentation
  `W` of `V`, `V^ss ≅ W^ss ⊕ (V/W)^ss`.
-/

public section

open scoped MonoidAlgebra

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  (ρ : Representation k G V)

/-- The **semisimplification** of a finite-dimensional representation: the representation of `G`
on the direct sum `V^ss` of the Jordan-Hölder factors of `V`, read off the `k[G]`-module
semisimplification of `ρ.asModule`. -/
noncomputable def semisimplification :
    Representation k G (TauCeti.semisimplification k[G] ρ.asModule) :=
  ofModule' (TauCeti.semisimplification k[G] ρ.asModule)

theorem semisimplification_def :
    ρ.semisimplification = ofModule' (TauCeti.semisimplification k[G] ρ.asModule) :=
  (rfl)

/-- A group element acts on `V^ss` through the corresponding basis element of `k[G]`. -/
@[simp]
theorem semisimplification_apply (g : G) (x : TauCeti.semisimplification k[G] ρ.asModule) :
    ρ.semisimplification g x = MonoidAlgebra.single g (1 : k) • x :=
  TauCeti.Representation.ofModule'_apply _ g x

/-- The action of `g` on `V^ss` is the action of the basis element `MonoidAlgebra.of k G g` of
`k[G]` on the module semisimplification, as a `k`-linear map. This links `ρ.semisimplification` to
the module-level API of `TauCeti.semisimplification`. -/
theorem semisimplification_apply_eq_lsmul (g : G) :
    ρ.semisimplification g =
      Algebra.lsmul k k (TauCeti.semisimplification k[G] ρ.asModule) (MonoidAlgebra.of k G g) := by
  ext x
  rw [semisimplification_apply, Algebra.lsmul_coe, MonoidAlgebra.of_apply]

/-- The `k[G]`-module attached to `ρ.semisimplification` is the semisimplification of the module
attached to `ρ`. -/
noncomputable def semisimplificationAsModuleEquiv :
    ρ.semisimplification.asModule ≃ₗ[k[G]] TauCeti.semisimplification k[G] ρ.asModule :=
  TauCeti.Representation.ofModule'AsModuleEquiv _

/-- `Representation.semisimplificationAsModuleEquiv` is the identity map of the underlying type. -/
@[simp]
theorem semisimplificationAsModuleEquiv_apply (x : ρ.semisimplification.asModule) :
    ρ.semisimplificationAsModuleEquiv x = x :=
  TauCeti.Representation.ofModule'AsModuleEquiv_apply _ x

/-- The inverse of `Representation.semisimplificationAsModuleEquiv` is the identity map of the
underlying type. -/
@[simp]
theorem semisimplificationAsModuleEquiv_symm_apply
    (x : TauCeti.semisimplification k[G] ρ.asModule) :
    ρ.semisimplificationAsModuleEquiv.symm x = x :=
  (LinearEquiv.symm_apply_eq _).mpr (semisimplificationAsModuleEquiv_apply ..).symm

/-- **The semisimplification is semisimple.** -/
instance isSemisimpleRepresentation_semisimplification :
    ρ.semisimplification.IsSemisimpleRepresentation :=
  (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
    (IsSemisimpleModule.congr ρ.semisimplificationAsModuleEquiv)

/-- **`V^ss ≅ V` exactly when `ρ` is semisimple.** -/
theorem nonempty_equiv_semisimplification_iff :
    Nonempty (ρ.semisimplification.Equiv ρ) ↔ ρ.IsSemisimpleRepresentation := by
  refine ⟨fun ⟨e⟩ ↦ e.toIntertwiningMap.isSemisimpleRepresentation_of_surjective
    e.toLinearEquiv.surjective, fun h ↦ ?_⟩
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp h
  obtain ⟨e⟩ := TauCeti.nonempty_linearEquiv_semisimplification_of_isSemisimpleModule
    (R := k[G]) (M := ρ.asModule)
  exact ⟨TauCeti.Representation.equivOfAsModuleLinearEquiv
    (ρ.semisimplificationAsModuleEquiv ≪≫ₗ e)⟩

/-- **The semisimplification has the characteristic polynomials of `ρ`**: every `g ∈ G` has the
same characteristic polynomial on `V^ss` as on `V`. -/
@[simp]
theorem charpoly_semisimplification_apply (g : G) :
    (ρ.semisimplification g).charpoly = (ρ g).charpoly := by
  rw [semisimplification_apply_eq_lsmul, ← charpoly_lsmul_asModule_of ρ g,
    TauCeti.charpoly_lsmul_semisimplification]

/-- The semisimplification has the traces of `ρ`. -/
@[simp]
theorem trace_semisimplification_apply (g : G) :
    LinearMap.trace k _ (ρ.semisimplification g) = LinearMap.trace k _ (ρ g) :=
  LinearMap.trace_eq_of_charpoly_eq (ρ.charpoly_semisimplification_apply g)

/-- The semisimplification has the character of `ρ`. -/
@[simp]
theorem char_semisimplification : ρ.semisimplification.character = ρ.character :=
  funext ρ.trace_semisimplification_apply

/-- The semisimplification has the determinants of `ρ`. -/
@[simp]
theorem det_semisimplification_apply (g : G) :
    LinearMap.det (ρ.semisimplification g) = LinearMap.det (ρ g) :=
  LinearMap.det_eq_of_charpoly_eq (ρ.charpoly_semisimplification_apply g)

/-- **The semisimplification is idempotent**: `(V^ss)^ss ≅ V^ss`. -/
theorem nonempty_equiv_semisimplification_semisimplification :
    Nonempty (ρ.semisimplification.semisimplification.Equiv ρ.semisimplification) :=
  ρ.semisimplification.nonempty_equiv_semisimplification_iff.mpr inferInstance

variable {ρ}

/-- An irreducible representation is equivalent to its semisimplification. -/
theorem nonempty_equiv_semisimplification_of_isIrreducible [ρ.IsIrreducible] :
    Nonempty (ρ.semisimplification.Equiv ρ) :=
  ρ.nonempty_equiv_semisimplification_iff.mpr inferInstance

section Exact

variable {U X : Type*} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
  [AddCommGroup X] [Module k X] [FiniteDimensional k X]
  {σ : Representation k G U} {τ : Representation k G X}

/-- **Equivalent representations have equivalent semisimplifications.** -/
theorem nonempty_equiv_semisimplification_of_equiv (e : ρ.Equiv σ) :
    Nonempty (ρ.semisimplification.Equiv σ.semisimplification) :=
  let ⟨f⟩ := TauCeti.nonempty_linearEquiv_semisimplification_of_linearEquiv
    (TauCeti.Representation.asModuleLinearEquivOfEquiv e)
  ⟨TauCeti.Representation.equivOfAsModuleLinearEquiv
    (ρ.semisimplificationAsModuleEquiv ≪≫ₗ f ≪≫ₗ σ.semisimplificationAsModuleEquiv.symm)⟩

/-- **Semisimplification is additive in short exact sequences of representations**: for
intertwining maps `f : U → V` injective and `g : V → X` surjective with `range f = ker g`,
`V^ss ≅ U^ss ⊕ X^ss`. -/
theorem nonempty_equiv_semisimplification_prod_of_exact (f : IntertwiningMap σ ρ)
    (g : IntertwiningMap ρ τ) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    Nonempty (ρ.semisimplification.Equiv (σ.semisimplification.prod τ.semisimplification)) :=
  let ⟨e⟩ := TauCeti.nonempty_linearEquiv_semisimplification_prod_of_exact
    (IntertwiningMap.equivLinearMapAsModule σ ρ f) (IntertwiningMap.equivLinearMapAsModule ρ τ g)
    hf hg hfg
  ⟨TauCeti.Representation.equivOfAsModuleLinearEquiv
    (ρ.semisimplificationAsModuleEquiv ≪≫ₗ e ≪≫ₗ
      (LinearEquiv.prodCongr σ.semisimplificationAsModuleEquiv.symm
        τ.semisimplificationAsModuleEquiv.symm ≪≫ₗ
        (σ.semisimplification.prodAsModuleEquiv τ.semisimplification).symm))⟩

end Exact

end Representation

namespace Subrepresentation

open Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {ρ : Representation k G V}

/-- **`V^ss ≅ W^ss ⊕ (V/W)^ss`** for a subrepresentation `W` of `V`. -/
theorem nonempty_equiv_semisimplification_prod_quotient (W : Subrepresentation ρ) :
    Nonempty (ρ.semisimplification.Equiv
      (W.toRepresentation.semisimplification.prod W.quotient.semisimplification)) :=
  nonempty_equiv_semisimplification_prod_of_exact W.subtype
    ⟨W.toSubmodule.mkQ, fun g ↦ by ext; rfl⟩ W.subtype_injective W.toSubmodule.mkQ_surjective
    (by rw [coe_subtype]; exact LinearMap.exact_subtype_mkQ W.toSubmodule)

end Subrepresentation
