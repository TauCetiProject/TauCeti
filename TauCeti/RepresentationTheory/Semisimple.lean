/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.Subrepresentation
public import TauCeti.RingTheory.Semisimple.Multiplicity
public import TauCeti.RingTheory.Semisimple.Trace.Basic
-- Non-public: used only inside the proofs about the image of `k[G]`.
import TauCeti.RingTheory.SimpleModule.Basic
import TauCeti.RingTheory.SimpleModule.Subalgebra

/-!
# Semisimple representations are determined by their characters

Over a field of characteristic zero, two finite-dimensional semisimple representations of a monoid
with the same character are equivalent
(`Representation.nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation`). The monoid need
not be finite: for a finite group in characteristic zero every representation is semisimple by
Maschke's theorem, but the statement here is what applies to an infinite group such as `GL n ℂ`,
once complete reducibility is known by other means.

The character determines the trace of every element `a = ∑ a_g g` of the monoid algebra `k[G]`
acting on the representation, namely `∑ a_g χ(g)`. So the `k[G]`-modules of the two
representations are semisimple with equal trace functions, and
`IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq` identifies them.

In any characteristic, semisimple representations are also determined by the dimensions of the
spaces of intertwining maps out of their irreducible subrepresentations
(`Representation.nonempty_equiv_of_finrank_intertwiningMap_eq`). This is the form in which
multiplicities are known for the kernel and cokernel of an equivariant Fredholm operator.

A representation is semisimple exactly when `V` is a semisimple module over the image of `k[G]`
in `End_k(V)`; it is semisimple when that image is a semisimple ring, and conversely in finite
dimension.

## Main results

* `Representation.trace_asAlgebraHom_eq_of_character_eq`: representations with the same character
  have the same trace function on `k[G]`.
* `Representation.nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation`: **semisimple
  representations with the same character are equivalent.**
* `Representation.isSemisimpleRepresentation_prod`: a product of semisimple representations is
  semisimple.
* `Representation.isSemisimpleModule_asModule_iff_isSemisimpleModule_range_asAlgebraHom`:
  over any commutative ring `k`, `ρ.asModule` is semisimple over `k[G]` exactly when `V` is
  semisimple over the image of `k[G]`.
* `Representation.isSemisimpleRepresentation_of_isSemisimpleRing_range_asAlgebraHom` and
  `Representation.isSemisimpleRing_range_asAlgebraHom`: a representation is semisimple when the
  image of `k[G]` is a semisimple ring, and conversely in finite dimension.
* `Representation.nonempty_equiv_of_finrank_intertwiningMap_eq`: over any field, two
  finite-dimensional semisimple representations are equivalent when every irreducible
  subrepresentation of either has intertwiner spaces of the same dimension into both.

## References

* S. Lang, *Algebra*, revised third edition, Chapter XVII, Corollary 3.8.
-/

public section

open scoped MonoidAlgebra

namespace Representation

section CommRing

variable {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]

/-- `ρ.asModule` is semisimple over `k[G]` exactly when `V` is semisimple over the image of
`k[G]` in `End_k(V)`. -/
theorem isSemisimpleModule_asModule_iff_isSemisimpleModule_range_asAlgebraHom
    (ρ : Representation k G V) :
    IsSemisimpleModule k[G] ρ.asModule ↔ IsSemisimpleModule ρ.asAlgebraHom.range V := by
  -- `ρ.asModule` is a type synonym for `V`; its `range`-module structure is that of `V`, through
  -- which the action of `k[G]` on `ρ.asModule` factors.
  let : Module ρ.asAlgebraHom.range ρ.asModule := (inferInstance : Module ρ.asAlgebraHom.range V)
  exact RingHom.isSemisimpleModule_iff_of_surjective (M := ρ.asModule)
    ρ.asAlgebraHom.rangeRestrict.toRingHom (AlgHom.rangeRestrict_surjective _) fun _ _ ↦ rfl

end CommRing

variable {k G V W : Type*} [Field k] [Monoid G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- **The character determines the trace on the monoid algebra.** If two representations have the
same character, then every element of `k[G]` acts on them with the same trace. -/
theorem trace_asAlgebraHom_eq_of_character_eq {ρ : Representation k G V}
    {σ : Representation k G W} (h : ρ.character = σ.character) (a : k[G]) :
    LinearMap.trace k V (ρ.asAlgebraHom a) = LinearMap.trace k W (σ.asAlgebraHom a) := by
  have hlin : (LinearMap.trace k V).comp ρ.asAlgebraHom.toLinearMap =
      (LinearMap.trace k W).comp σ.asAlgebraHom.toLinearMap :=
    MonoidAlgebra.lhom_ext' fun g => LinearMap.ext_ring <| by
      simpa [character] using congrFun h g
  exact LinearMap.congr_fun hlin a

/-- **Semisimple representations are determined by their characters.** Over a field of
characteristic zero, two finite-dimensional semisimple representations of a monoid with the same
character are equivalent. The monoid need not be finite. -/
theorem nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation [CharZero k]
    [FiniteDimensional k V] [FiniteDimensional k W] (ρ : Representation k G V)
    (σ : Representation k G W) [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation]
    (h : ρ.character = σ.character) : Nonempty (ρ.Equiv σ) := by
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp ‹_›
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).mp ‹_›
  refine TauCeti.Representation.nonempty_equiv_iff.mpr <|
    IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq (k := k) _ _ fun a => ?_
  rw [← LinearMap.trace_conj' _ ρ.asModuleEquiv, ← LinearMap.trace_conj' _ σ.asModuleEquiv]
  exact trace_asAlgebraHom_eq_of_character_eq h a

/-- **A product of semisimple representations is semisimple.** -/
instance isSemisimpleRepresentation_prod (ρ : Representation k G V) (σ : Representation k G W)
    [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation] :
    (ρ.prod σ).IsSemisimpleRepresentation := by
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp ‹_›
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).mp ‹_›
  have := IsSemisimpleModule.prod (R := k[G]) (M := ρ.asModule) (N := σ.asModule)
  exact (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
    (IsSemisimpleModule.congr (ρ.prodAsModuleEquiv σ))

/-- **A representation whose image algebra is a semisimple ring is semisimple.** No finiteness is
needed: `V` is a module over the image `A` of `k[G]` in `End_k(V)`, semisimple because `A` is, and
its subrepresentations are its `A`-submodules. -/
theorem isSemisimpleRepresentation_of_isSemisimpleRing_range_asAlgebraHom
    (ρ : Representation k G V) [IsSemisimpleRing ρ.asAlgebraHom.range] :
    ρ.IsSemisimpleRepresentation := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
    isSemisimpleModule_asModule_iff_isSemisimpleModule_range_asAlgebraHom]
  infer_instance

/-- **The image algebra of a finite-dimensional semisimple representation is a semisimple
ring.** -/
theorem isSemisimpleRing_range_asAlgebraHom (ρ : Representation k G V) [FiniteDimensional k V]
    [ρ.IsSemisimpleRepresentation] : IsSemisimpleRing ρ.asAlgebraHom.range := by
  have := (isSemisimpleModule_asModule_iff_isSemisimpleModule_range_asAlgebraHom ρ).mp <|
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp ‹_›
  exact Subalgebra.isSemisimpleRing_of_isSemisimpleModule _

/-- A finite-dimensional representation is semisimple exactly when the image of `k[G]` in
`End_k(V)` is a semisimple ring. -/
theorem isSemisimpleRing_range_asAlgebraHom_iff (ρ : Representation k G V)
    [FiniteDimensional k V] :
    IsSemisimpleRing ρ.asAlgebraHom.range ↔ ρ.IsSemisimpleRepresentation :=
  ⟨fun _ ↦ isSemisimpleRepresentation_of_isSemisimpleRing_range_asAlgebraHom ρ,
    fun _ ↦ isSemisimpleRing_range_asAlgebraHom ρ⟩

/-- **Semisimple representations are determined by intertwiner dimensions.** Two
finite-dimensional semisimple representations `ρ` and `σ` of a monoid over a field are equivalent
when every irreducible subrepresentation `τ` of either has spaces of intertwining maps `τ → ρ` and
`τ → σ` of the same dimension. Unlike the character criterion, this holds in every
characteristic. -/
theorem nonempty_equiv_of_finrank_intertwiningMap_eq [FiniteDimensional k V]
    [FiniteDimensional k W] (ρ : Representation k G V) (σ : Representation k G W)
    [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation]
    (hρ : ∀ τ : Subrepresentation ρ, IsAtom τ →
      Module.finrank k (IntertwiningMap τ.toRepresentation ρ) =
        Module.finrank k (IntertwiningMap τ.toRepresentation σ))
    (hσ : ∀ τ : Subrepresentation σ, IsAtom τ →
      Module.finrank k (IntertwiningMap τ.toRepresentation ρ) =
        Module.finrank k (IntertwiningMap τ.toRepresentation σ)) :
    Nonempty (ρ.Equiv σ) := by
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp ‹_›
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).mp ‹_›
  refine TauCeti.Representation.nonempty_equiv_iff.mpr <|
    IsSemisimpleModule.nonempty_linearEquiv_of_finrank_linearMap_eq (k := k)
      (fun S _ ↦ ?_) (fun S _ ↦ ?_) <;>
  -- A simple submodule of the associated module is carried by an irreducible subrepresentation `τ`,
  -- whose intertwiners are the module maps out of that submodule; `τ` lives in `ρ` or in `σ`, and
  -- the matching hypothesis `hρ` or `hσ` is found by its type.
  · obtain ⟨τ, rfl⟩ : ∃ τ : Subrepresentation _, τ.asSubmodule = S :=
      Subrepresentation.subrepresentationSubmoduleOrderIso.surjective S
    simpa only [(τ.intertwiningMapEquivLinearMapAsSubmodule _).finrank_eq] using
      ‹∀ τ' : Subrepresentation _, IsAtom τ' →
        Module.finrank k (IntertwiningMap τ'.toRepresentation ρ) =
          Module.finrank k (IntertwiningMap τ'.toRepresentation σ)› τ
        (Subrepresentation.isSimpleModule_asSubmodule_iff.mp ‹_›)

end Representation
