/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.Invariants
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Fixed

/-!
# Invariants of a normal subgroup with linearly reductive quotient

Let `I` be a normal Hopf ideal of a reduced finite-type commutative Hopf algebra `H` over an
algebraically closed field. If the quotient Hopf algebra is linearly reductive, taking the
scheme-theoretic invariants `HopfIdeal.IsNormal.weightSpaceOneSubcomodule` preserves surjections of
`H`-comodules.

## Main declaration

* `TauCeti.HopfIdeal.IsNormal.exists_surjective_hom_weightSpaceOneSubcomodule`: a surjection of
  comodules restricts to a surjection of the invariants of a normal subgroup with linearly
  reductive quotient.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {H : CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H] [IsReduced H] {I : HopfIdeal k H}
variable {M : Type u} [AddCommGroup M] [Module k M] [Comodule k H M]
  {N : Type u} [AddCommGroup N] [Module k N] [Comodule k H N]

/-- Taking invariants of a normal Hopf ideal with linearly reductive quotient preserves
surjections of comodules. -/
theorem IsNormal.exists_surjective_hom_weightSpaceOneSubcomodule (hI : I.IsNormal)
    (hC : Coalgebra.IsLinearlyReductive.{u, u, u} k (CommHopfAlgCat.quotient H I))
    (f : Comodule.Hom k H M N) (hf : Function.Surjective f) :
    ∃ a : Comodule.Hom k H (hI.weightSpaceOneSubcomodule M) (hI.weightSpaceOneSubcomodule N),
      Function.Surjective a ∧ ∀ m, (a m : N) = f m := by
  let q := (CommHopfAlgCat.mkQuotient H I).hom
  let fC := Comodule.corestrictHom q.toCoalgHom f
  have hmap (m : hI.weightSpaceOneSubcomodule M) :
      (f.comp (hI.weightSpaceOneSubcomodule M).subtype) m ∈ hI.weightSpaceOneSubcomodule N := by
    let _ : Comodule k (CommHopfAlgCat.quotient H I) M := Comodule.Corestrict q.toCoalgHom
    let _ : Comodule k (CommHopfAlgCat.quotient H I) N := Comodule.Corestrict q.toCoalgHom
    rw [Comodule.Hom.comp_apply, Subcomodule.subtype_apply]
    exact (hI.mem_weightSpaceOneSubcomodule_iff_coact_corestrict N _).mpr <|
      Comodule.mem_fixedSubcomodule.mp <| fC.mem_fixedSubcomodule
        (Comodule.mem_fixedSubcomodule.mpr
          ((hI.mem_weightSpaceOneSubcomodule_iff_coact_corestrict M _).mp m.property))
  refine ⟨(f.comp (hI.weightSpaceOneSubcomodule M).subtype).codRestrict _ hmap, ?_, fun m ↦ by
    simp only [Comodule.Hom.codRestrict_apply, Comodule.Hom.comp_apply,
      Subcomodule.subtype_apply]⟩
  intro y
  let _ : Comodule k (CommHopfAlgCat.quotient H I) M := Comodule.Corestrict q.toCoalgHom
  let _ : Comodule k (CommHopfAlgCat.quotient H I) N := Comodule.Corestrict q.toCoalgHom
  obtain ⟨m, hm, hmy⟩ := fC.exists_fixed_preimage_of_isLinearlyReductive hC
    (Comodule.mem_fixedSubcomodule.mpr
      ((hI.mem_weightSpaceOneSubcomodule_iff_coact_corestrict N _).mp y.property)) (hf y)
  exact ⟨⟨m, (hI.mem_weightSpaceOneSubcomodule_iff_coact_corestrict M _).mpr
      (Comodule.mem_fixedSubcomodule.mp hm)⟩,
    Subtype.ext (by simpa only [Comodule.Hom.codRestrict_apply,
      Comodule.Hom.comp_apply, Subcomodule.subtype_apply, fC,
      Comodule.corestrictHom_apply] using hmy)⟩

end TauCeti.HopfIdeal
