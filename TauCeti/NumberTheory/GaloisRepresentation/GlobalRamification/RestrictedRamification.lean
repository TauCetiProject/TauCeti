/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GaloisRepresentation.GlobalRamification
public import TauCeti.NumberTheory.NumberField.RestrictedRamification.Restriction
import TauCeti.NumberTheory.NumberField.RestrictedRamification.Inertia

/-!
# Representations unramified outside `S` factor through `G_{F,S}`

Let `F` be a number field, `G_F` its absolute Galois group (on `F^alg = AlgebraicClosure F`), `S` a
set of finite places of `F`, `K_S ⊆ F^alg` the maximal extension of `F` unramified outside `S` and
`G_{F,S} = Gal(K_S / F)`. This file proves the unramified factorisation criterion: a continuous
representation `ρ` of `G_F` on a Hausdorff module is unramified outside `S`
(`TauCeti.ContinuousRep.IsUnramifiedOutside`) exactly when it factors, necessarily continuously,
through the restriction `G_F → G_{F,S}` (`TauCeti.RestrictedRamification.restrictionS`).

The arithmetic content is that the kernel `H_S = Gal(F^alg / K_S)` of the restriction is generated,
as a closed normal subgroup, by the inertia groups at the finite places outside `S`
(`TauCeti.RestrictedRamification.inertiaGroup_le_fixingSubgroup_maxUnramifiedOutside` and
`TauCeti.RestrictedRamification.fixingSubgroup_maxUnramifiedOutside_le`). The kernel of a
continuous representation on a Hausdorff module is closed (`TauCeti.ContinuousRep.isClosed_ker`),
which gives the criterion. The descended representation of `G_{F,S}` is
`TauCeti.ContinuousRep.descendS`, the descent `TauCeti.ContinuousRep.descend` along the open
surjection `G_F → G_{F,S}`.

## Main results

* `TauCeti.ContinuousRep.isUnramifiedOutside_iff_fixingSubgroup_le_ker`: `ρ` is unramified outside
  `S` iff `Gal(F^alg / K_S)` acts trivially.
* `TauCeti.ContinuousRep.descendS`: a representation unramified outside `S`, as a representation
  of `G_{F,S}`, with `res_descendS`.
* `TauCeti.ContinuousRep.isUnramifiedOutside_iff_exists_res_eq`: `ρ` is unramified outside `S` iff
  it is the restriction of a continuous representation of `G_{F,S}`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, §4.
-/

public section

noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti.ContinuousRep

open RestrictedRamification

variable {F : Type*} [Field F] [NumberField F] {S : Set (HeightOneSpectrum (𝓞 F))}
  {A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  {ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M}

/-- A representation on which `Gal(F^alg / K_S)` acts trivially is unramified outside `S`. -/
theorem IsUnramifiedOutside.of_fixingSubgroup_le_ker
    (h : (maxUnramifiedOutside F (AlgebraicClosure F) S).fixingSubgroup ≤
      ρ.toRepresentation.ker) :
    ρ.IsUnramifiedOutside S :=
  isUnramifiedOutside_iff.2 fun _ hv ↦ isUnramifiedAt_iff.2 fun Q hQ hQv σ hσ ↦ by
    have := hQ.isPrime
    exact MonoidHom.mem_ker.1 (h (inertiaGroup_le_fixingSubgroup_maxUnramifiedOutside hv Q hQv hσ))

/-- **Unramified outside `S` means trivial on `Gal(F^alg / K_S)`.** A continuous representation
of `G_F` on a Hausdorff module is unramified outside `S` exactly when the absolute Galois group of
the maximal extension `K_S` unramified outside `S` acts trivially. -/
theorem isUnramifiedOutside_iff_fixingSubgroup_le_ker [T2Space M] :
    ρ.IsUnramifiedOutside S ↔
      (maxUnramifiedOutside F (AlgebraicClosure F) S).fixingSubgroup ≤
        ρ.toRepresentation.ker :=
  ⟨fun h ↦ fixingSubgroup_maxUnramifiedOutside_le ρ.isClosed_ker
    fun v hv Q hQ hQv σ hσ ↦ by
      simpa using isUnramifiedAt_iff.1 (isUnramifiedOutside_iff.1 h v hv) Q hQ hQv σ hσ,
    IsUnramifiedOutside.of_fixingSubgroup_le_ker⟩

/-- **Descent to `G_{F,S}`.** A continuous representation of `G_F` unramified outside `S`, on a
Hausdorff module, as a continuous representation of `G_{F,S} = Gal(K_S / F)`: `σ|_{K_S}` acts by
`ρ σ`. It is the descent `TauCeti.ContinuousRep.descend` along the open surjection
`G_F → G_{F,S}`. -/
def descendS [T2Space M] (ρ : ContinuousRep (Field.absoluteGaloisGroup F) A M)
    (h : ρ.IsUnramifiedOutside S) :
    ContinuousRep (galoisGroupS F (AlgebraicClosure F) S) A M :=
  ρ.descend (restrictionS F (AlgebraicClosure F) S) (isOpenMap_restrictionS F _ S)
    (restrictionS_surjective F _ S)
    ((ker_restrictionS F _ S).le.trans (isUnramifiedOutside_iff_fixingSubgroup_le_ker.1 h))

variable [T2Space M]

/-- In the descended representation, `σ|_{K_S}` acts by `ρ σ`. -/
@[simp]
theorem descendS_restrictionS_apply (h : ρ.IsUnramifiedOutside S)
    (σ : Gal(AlgebraicClosure F/F)) :
    ρ.descendS h (restrictionS F (AlgebraicClosure F) S σ) = ρ σ :=
  descend_apply σ

/-- The descended representation restricts back to `ρ` along `G_F → G_{F,S}`. -/
@[simp]
theorem res_descendS (h : ρ.IsUnramifiedOutside S) :
    (ρ.descendS h).res (restrictionS F (AlgebraicClosure F) S) = ρ :=
  res_descend

/-- **The unramified factorisation criterion.** A continuous representation of `G_F` on a
Hausdorff module is unramified outside `S` exactly when it is the restriction of a continuous
representation of `G_{F,S}` along `G_F → G_{F,S}`. -/
theorem isUnramifiedOutside_iff_exists_res_eq :
    ρ.IsUnramifiedOutside S ↔ ∃ ρ' : ContinuousRep (galoisGroupS F (AlgebraicClosure F) S) A M,
      ρ'.res (restrictionS F (AlgebraicClosure F) S) = ρ := by
  rw [isUnramifiedOutside_iff_fixingSubgroup_le_ker, ← ker_restrictionS]
  exact (exists_res_eq_iff _ (isOpenMap_restrictionS F _ S) (restrictionS_surjective F _ S)).symm

/-- The descent to `G_{F,S}` does not depend on the proof of unramifiedness, and it is unique:
a representation of `G_{F,S}` restricting to `ρ` is `ρ.descendS h`. -/
theorem eq_descendS_of_res_eq (h : ρ.IsUnramifiedOutside S)
    {ρ' : ContinuousRep (galoisGroupS F (AlgebraicClosure F) S) A M}
    (h' : ρ'.res (restrictionS F (AlgebraicClosure F) S) = ρ) :
    ρ' = ρ.descendS h :=
  eq_descend_of_res_eq h'

end TauCeti.ContinuousRep
