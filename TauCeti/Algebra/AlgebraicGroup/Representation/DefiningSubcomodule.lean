/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.SubspaceStabilizer
public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
public import TauCeti.Algebra.Coalgebra.Subcomodule.Comap

/-!
# The defining subspace as a subgroup representation

Let `I` define a closed subgroup of an affine group with coordinate Hopf algebra `H`, and
let `V` be a regular `H`-subcomodule. The subspace of functions in `V` vanishing on the
subgroup is a subcomodule after corestriction to `H/I`. It is the kernel of restriction
`V → H/I`, viewed as a morphism to the subgroup's regular comodule.

This equips the defining subspace in Chevalley's stabilizer construction with its subgroup
representation. It is intended as input to an exterior-power construction of an invariant
line under additional hypotheses, such as finite-dimensionality over a field. The
subcomodule construction itself requires no reducedness or smoothness.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 4.27 and Lemma 4.28.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
-/

public section

namespace TauCeti.HopfIdeal

universe u v

variable {k : Type u} [CommRing k] {H : _root_.CommHopfAlgCat.{v} k}
variable [Module.Flat k H]

/-- Restrict a regular subcomodule's functions to a closed subgroup, as a morphism to the
subgroup's regular comodule. -/
noncomputable def restrictionHom (I : HopfIdeal k H) (V : Subcomodule k H H) :
    letI : Comodule k (H ⧸ I.toIdeal) V :=
      Comodule.Corestrict (CommHopfAlgCat.mkQuotient H I).hom.toCoalgHom
    Comodule.Hom k (H ⧸ I.toIdeal) V (H ⧸ I.toIdeal) := by
  let f := (CommHopfAlgCat.mkQuotient H I).hom.toCoalgHom
  let g := Comodule.corestrictHom f (Subcomodule.subtype V)
  letI : Comodule k (H ⧸ I.toIdeal) V := Comodule.Corestrict f
  letI : Comodule k (H ⧸ I.toIdeal) H := Comodule.Corestrict f
  exact f.toComoduleHom.comp g

/-- The linear map underlying restriction is the quotient map after inclusion in `H`. -/
@[simp]
theorem restrictionHom_toLinearMap (I : HopfIdeal k H) (V : Subcomodule k H H) :
    letI : Comodule k (H ⧸ I.toIdeal) V :=
      Comodule.Corestrict (CommHopfAlgCat.mkQuotient H I).hom.toCoalgHom
    (I.restrictionHom V).toLinearMap =
      (Ideal.Quotient.mkₐ k I.toIdeal).toLinearMap.comp (SMulMemClass.subtype V) := by
  simp only [restrictionHom, Comodule.Hom.comp_toLinearMap,
    CoalgHom.toComoduleHom_toLinearMap, Comodule.corestrictHom_toLinearMap,
    Subcomodule.subtype_toLinearMap]
  exact congrArg (fun f : H →ₗ[k] (H ⧸ I.toIdeal) ↦ f.comp (SMulMemClass.subtype V))
    (CommHopfAlgCat.mkQuotient_toLinearMap H I)

/-- Restriction sends a function to its residue class modulo the defining ideal. -/
@[simp]
theorem restrictionHom_apply (I : HopfIdeal k H) (V : Subcomodule k H H) (x : V) :
    letI : Comodule k (H ⧸ I.toIdeal) V :=
      Comodule.Corestrict (CommHopfAlgCat.mkQuotient H I).hom.toCoalgHom
    I.restrictionHom V x = Ideal.Quotient.mk I.toIdeal (x : H) := by
  let : Comodule k (H ⧸ I.toIdeal) V :=
    Comodule.Corestrict (CommHopfAlgCat.mkQuotient H I).hom.toCoalgHom
  exact LinearMap.congr_fun (I.restrictionHom_toLinearMap V) x

/-- The functions in a regular subcomodule vanishing on a closed subgroup, as a subcomodule
of the representation restricted to that subgroup. -/
noncomputable def definingSubcomodule (I : HopfIdeal k H)
    [Module.Flat k (H ⧸ I.toIdeal)] (V : Subcomodule k H H) :
    letI : Comodule k (H ⧸ I.toIdeal) V :=
      Comodule.Corestrict (CommHopfAlgCat.mkQuotient H I).hom.toCoalgHom
    Subcomodule k (H ⧸ I.toIdeal) V := by
  let : Comodule k (H ⧸ I.toIdeal) V :=
    Comodule.Corestrict (CommHopfAlgCat.mkQuotient H I).hom.toCoalgHom
  exact (I.restrictionHom V).ker

/-- The defining subcomodule has exactly the previously defined vanishing subspace. -/
@[simp]
theorem definingSubcomodule_toSubmodule (I : HopfIdeal k H)
    [Module.Flat k (H ⧸ I.toIdeal)] (V : Subcomodule k H H) :
    letI : Comodule k (H ⧸ I.toIdeal) V :=
      Comodule.Corestrict (CommHopfAlgCat.mkQuotient H I).hom.toCoalgHom
    (I.definingSubcomodule V).toSubmodule = I.definingSubspace V := by
  let : Comodule k (H ⧸ I.toIdeal) V :=
    Comodule.Corestrict (CommHopfAlgCat.mkQuotient H I).hom.toCoalgHom
  rw [definingSubcomodule, Comodule.Hom.ker_toSubmodule, restrictionHom_toLinearMap]
  ext x
  simp [LinearMap.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- A vector is in the defining subcomodule precisely when it vanishes on the subgroup. -/
@[simp]
theorem mem_definingSubcomodule (I : HopfIdeal k H)
    [Module.Flat k (H ⧸ I.toIdeal)] (V : Subcomodule k H H) (x : V) :
    letI : Comodule k (H ⧸ I.toIdeal) V :=
      Comodule.Corestrict (CommHopfAlgCat.mkQuotient H I).hom.toCoalgHom
    x ∈ I.definingSubcomodule V ↔ (x : H) ∈ I := by
  let : Comodule k (H ⧸ I.toIdeal) V :=
    Comodule.Corestrict (CommHopfAlgCat.mkQuotient H I).hom.toCoalgHom
  rw [← Subcomodule.mem_toSubmodule, definingSubcomodule_toSubmodule, mem_definingSubspace]

end TauCeti.HopfIdeal
