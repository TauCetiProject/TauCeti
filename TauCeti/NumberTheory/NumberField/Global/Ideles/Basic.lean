/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing

import Mathlib.Topology.Algebra.Group.Units
import TauCeti.NumberTheory.NumberField.Global.Adeles.Basic
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Units

/-!
# Basic API for ideles

This file records the relation between Mathlib's diagonal embeddings into the idele group and the
adele ring. In particular, principal-idele membership can be tested on the underlying adele.

It also defines the finite component `NumberField.IdeleGroup.toFiniteIdele` of an idele, a unit of
the finite adele ring, and the idele `NumberField.IdeleGroup.ofFiniteIdele` with a given finite
component and trivial infinite components.  This is how ideles are handed to and from the
finite-idele theory of fractional ideals: on a principal idele the finite component is the
principal finite idele of the same element.

The coordinate maps `IsDedekindDomain.HeightOneSpectrum.ideleFiniteCoord` and
`NumberField.InfinitePlace.ideleInfiniteCoord` read the local units of an idele.
`NumberField.IdeleGroup.ext` determines an idele by equality of all these coordinates. The
constructor `TauCeti.GlobalNumberFields.ideleOfUnits` assembles local units that are integral units
at almost every finite place; `TauCeti.GlobalNumberFields.ideleFiniteCoord_ideleOfUnits` and
`TauCeti.GlobalNumberFields.ideleInfiniteCoord_ideleOfUnits` recover those units.

The embeddings of the units of the completions, at the infinite and at the finite places, into
the idele group and the idele class group are continuous.

Finally, `NumberField.IdeleGroup.localUnitsEquiv` identifies the idele group, with its units
topology, with the product of the unit groups `K_wˣ` at the infinite places and the restricted
product of the unit groups `K_vˣ` at the finite places with respect to the local integral units
`𝒪_vˣ`, as topological groups. Its coordinates are the coordinate maps above, and its inverse is
`TauCeti.GlobalNumberFields.ideleOfUnits`. This is the classical description of the idele group as
a restricted product over all places, and it shows that the units topology of the adele ring is
the restricted-product topology of the local unit groups.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §16.
* A. Weil, *Basic Number Theory*, Chapter IV, §3.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace

namespace NumberField.IdeleGroup

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- An idele is principal exactly when its underlying adele lies in the diagonal copy of the
fraction field. -/
-- This is intentionally not a simp lemma: Mathlib's `MonoidHom.mem_range` is already `simp`, so it
-- rewrites this left-hand side to an existential over `unitEmbedding` and the simp-normal-form
-- linter rejects the membership form.
theorem mem_principalSubgroup_iff (x : IdeleGroup R K) :
    x ∈ principalSubgroup R K ↔
      (x : AdeleRing R K) ∈ AdeleRing.principalSubgroup R K := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (val_unitEmbedding_apply R K y).symm⟩
  · rintro ⟨y, hy⟩
    by_cases hA : Nontrivial (AdeleRing R K)
    · let _ := hA
      have hy0 : y ≠ 0 := by
        intro hyzero
        subst y
        exact x.ne_zero (by simpa using hy.symm)
      refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
      simpa only [val_unitEmbedding_apply, Units.val_mk0] using hy
    · have _ : Subsingleton (AdeleRing R K) := not_nontrivial_iff_subsingleton.mp hA
      exact ⟨1, Units.ext (Subsingleton.elim _ _)⟩

/-- The finite component of an idele, a unit of the finite adele ring (a *finite idele*). -/
def toFiniteIdele : IdeleGroup R K →* (FiniteAdeleRing R K)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing R K))

@[simp]
theorem coe_toFiniteIdele (x : IdeleGroup R K) :
    (toFiniteIdele R K x : FiniteAdeleRing R K) = (x : AdeleRing R K).2 :=
  (rfl)

/-- The finite component of a principal idele is the principal finite idele of the same
element. -/
@[simp]
theorem toFiniteIdele_unitEmbedding (x : Kˣ) :
    toFiniteIdele R K (unitEmbedding R K x) = FiniteAdeleRing.unitEmbedding R K x :=
  Units.ext (rfl)

/-- The idele with the given finite component and all infinite components equal to `1`. -/
def ofFiniteIdele : (FiniteAdeleRing R K)ˣ →* IdeleGroup R K :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing R K))

@[simp]
theorem coe_ofFiniteIdele (a : (FiniteAdeleRing R K)ˣ) :
    (ofFiniteIdele R K a : AdeleRing R K) =
      ((1 : InfiniteAdeleRing K), (a : FiniteAdeleRing R K)) :=
  (rfl)

/-- The finite component of `ofFiniteIdele R K a` is `a`. -/
@[simp]
theorem toFiniteIdele_ofFiniteIdele (a : (FiniteAdeleRing R K)ˣ) :
    toFiniteIdele R K (ofFiniteIdele R K a) = a :=
  Units.ext (rfl)

/-- The finite component of an idele concentrated at an infinite place is trivial. -/
@[simp]
theorem toFiniteIdele_ofCompletion (w : NumberField.InfinitePlace K) (u : w.Completionˣ) :
    toFiniteIdele R K (ofCompletion R K w u) = 1 :=
  Units.ext (rfl)

/-- The embedding of the units of the completion at an infinite place into the idele group is
continuous. -/
@[continuity, fun_prop]
theorem continuous_ofCompletion (w : NumberField.InfinitePlace K) :
    Continuous (ofCompletion R K w) :=
  (AdeleRing.continuous_ofCompletion R K w).units_map _

/-- The embedding of the units of the completion at a finite place into the idele group is
continuous. -/
@[continuity, fun_prop]
theorem continuous_ofAdicCompletion (v : HeightOneSpectrum R) :
    Continuous (ofAdicCompletion R K v) :=
  (AdeleRing.continuous_ofAdicCompletion R K v).units_map _

end NumberField.IdeleGroup

namespace NumberField.IdeleClassGroup

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The embedding of the units of the completion at an infinite place into the idele class group
is continuous. -/
@[continuity, fun_prop]
theorem continuous_ofCompletion (w : NumberField.InfinitePlace K) :
    Continuous (ofCompletion R K w) :=
  continuous_quot_mk.comp (IdeleGroup.continuous_ofCompletion R K w)

/-- The embedding of the units of the completion at a finite place into the idele class group is
continuous. -/
@[continuity, fun_prop]
theorem continuous_ofAdicCompletion (v : HeightOneSpectrum R) :
    Continuous (ofAdicCompletion R K v) :=
  continuous_quot_mk.comp (IdeleGroup.continuous_ofAdicCompletion R K v)

end NumberField.IdeleClassGroup

/-! ### Coordinates and assembly of an idele -/

section Coordinates

variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]

/-- The coordinate of an idele at a finite place `v`, a unit of the `v`-adic completion. -/
def IsDedekindDomain.HeightOneSpectrum.ideleFiniteCoord (v : HeightOneSpectrum R) :
    IdeleGroup R K →* (v.adicCompletion K)ˣ :=
  Units.map <| (RestrictedProduct.evalMonoidHom _ v).comp
    (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing R K))

/-- The coordinate of an idele at an infinite place `w`, a unit of the completion at `w`. -/
def NumberField.InfinitePlace.ideleInfiniteCoord
    (w : InfinitePlace K) : IdeleGroup R K →* w.Completionˣ :=
  Units.map <| (Pi.evalMonoidHom _ w).comp
    (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing R K))

@[simp]
theorem IsDedekindDomain.HeightOneSpectrum.coe_ideleFiniteCoord
    (v : HeightOneSpectrum R) (x : IdeleGroup R K) :
    (v.ideleFiniteCoord x : v.adicCompletion K) = (x : AdeleRing R K).2 v :=
  (rfl)

@[simp]
theorem NumberField.InfinitePlace.coe_ideleInfiniteCoord
    (w : InfinitePlace K) (x : IdeleGroup R K) :
    (w.ideleInfiniteCoord x : w.Completion) = (x : AdeleRing R K).1 w :=
  (rfl)

/-- **Ideles are determined by their coordinates**: two ideles with the same coordinate at every
infinite and finite place are equal. -/
@[ext]
theorem NumberField.IdeleGroup.ext {x y : IdeleGroup R K}
    (hinf : ∀ w : InfinitePlace K, w.ideleInfiniteCoord x = w.ideleInfiniteCoord y)
    (hfin : ∀ v : HeightOneSpectrum R, v.ideleFiniteCoord x = v.ideleFiniteCoord y) : x = y := by
  refine Units.ext (Prod.ext (funext fun w ↦ ?_) (FiniteAdeleRing.ext K fun v ↦ ?_))
  · have h := congrArg Units.val (hinf w)
    rwa [InfinitePlace.coe_ideleInfiniteCoord, InfinitePlace.coe_ideleInfiniteCoord] at h
  · have h := congrArg Units.val (hfin v)
    rwa [HeightOneSpectrum.coe_ideleFiniteCoord, HeightOneSpectrum.coe_ideleFiniteCoord] at h

namespace TauCeti.GlobalNumberFields

/-- Assemble an idele from local units that are integral units at almost every finite place. -/
def ideleOfUnits (zi : ∀ w : InfinitePlace K, w.Completionˣ)
    (z : ∀ v : HeightOneSpectrum R, (v.adicCompletion K)ˣ)
    (hz : ∀ᶠ v in Filter.cofinite, z v ∈ (v.adicCompletionIntegers K).units) :
    IdeleGroup R K :=
  MulEquiv.prodUnits.symm (MulEquiv.piUnits.symm zi, RestrictedProduct.mkUnit z hz)

/-- The finite coordinates of the idele assembled from local units are the prescribed units. -/
@[simp]
theorem ideleFiniteCoord_ideleOfUnits (zi : ∀ w : InfinitePlace K, w.Completionˣ)
    (z : ∀ v : HeightOneSpectrum R, (v.adicCompletion K)ˣ)
    (hz : ∀ᶠ v in Filter.cofinite, z v ∈ (v.adicCompletionIntegers K).units)
    (v : HeightOneSpectrum R) : v.ideleFiniteCoord (ideleOfUnits zi z hz) = z v := by
  apply Units.ext
  rw [HeightOneSpectrum.coe_ideleFiniteCoord]
  rfl

/-- The infinite coordinates of the idele assembled from local units are the prescribed units. -/
@[simp]
theorem ideleInfiniteCoord_ideleOfUnits (zi : ∀ w : InfinitePlace K, w.Completionˣ)
    (z : ∀ v : HeightOneSpectrum R, (v.adicCompletion K)ˣ)
    (hz : ∀ᶠ v in Filter.cofinite, z v ∈ (v.adicCompletionIntegers K).units)
    (w : InfinitePlace K) : w.ideleInfiniteCoord (ideleOfUnits zi z hz) = zi w := by
  apply Units.ext
  rw [InfinitePlace.coe_ideleInfiniteCoord]
  rfl

end TauCeti.GlobalNumberFields

end Coordinates

/-! ### The idele group as a restricted product of local unit groups -/

namespace NumberField.IdeleGroup

open scoped RestrictedProduct

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The idele group is the restricted product of the local unit groups**: the idele group, with
its units topology, is isomorphic as a topological group to the product of the unit groups `K_wˣ`
of the completions at the infinite places with the restricted product of the unit groups `K_vˣ`
at the finite places with respect to the local integral units `𝒪_vˣ`. -/
noncomputable def localUnitsEquiv :
    IdeleGroup R K ≃ₜ* (∀ w : InfinitePlace K, w.Completionˣ) ×
      Πʳ v : HeightOneSpectrum R,
        [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units] where
  toMulEquiv := MulEquiv.prodUnits.trans
    (MulEquiv.prodCongr MulEquiv.piUnits (FiniteAdeleRing.unitsContinuousMulEquiv R K))
  continuous_toFun := (ContinuousMulEquiv.piUnits.continuous.prodMap
    (FiniteAdeleRing.unitsContinuousMulEquiv R K).continuous).comp Homeomorph.prodUnits.continuous
  continuous_invFun := Homeomorph.prodUnits.symm.continuous.comp
    (ContinuousMulEquiv.piUnits.symm.continuous.prodMap
      (FiniteAdeleRing.unitsContinuousMulEquiv R K).symm.continuous)

variable {R K}

/-- The infinite part of `NumberField.IdeleGroup.localUnitsEquiv` consists of the coordinates of
an idele at the infinite places. -/
@[simp]
theorem localUnitsEquiv_apply_fst (x : IdeleGroup R K) (w : InfinitePlace K) :
    (localUnitsEquiv R K x).1 w = w.ideleInfiniteCoord x :=
  Units.ext (rfl)

/-- The finite part of `NumberField.IdeleGroup.localUnitsEquiv` consists of the coordinates of an
idele at the finite places. -/
@[simp]
theorem localUnitsEquiv_apply_snd (x : IdeleGroup R K) (v : HeightOneSpectrum R) :
    (localUnitsEquiv R K x).2 v = v.ideleFiniteCoord x :=
  Units.ext (FiniteAdeleRing.coe_unitsContinuousMulEquiv_apply _ v)

/-- The inverse of `NumberField.IdeleGroup.localUnitsEquiv` assembles an idele from its local
units, as `TauCeti.GlobalNumberFields.ideleOfUnits` does. -/
theorem localUnitsEquiv_symm_apply (zi : ∀ w : InfinitePlace K, w.Completionˣ)
    (z : ∀ v : HeightOneSpectrum R, (v.adicCompletion K)ˣ)
    (hz : ∀ᶠ v in Filter.cofinite, z v ∈ (v.adicCompletionIntegers K).units) :
    (localUnitsEquiv R K).symm (zi, .mk z hz) = TauCeti.GlobalNumberFields.ideleOfUnits zi z hz :=
  NumberField.IdeleGroup.ext
    (fun w ↦ by
      rw [← localUnitsEquiv_apply_fst, ContinuousMulEquiv.apply_symm_apply,
        TauCeti.GlobalNumberFields.ideleInfiniteCoord_ideleOfUnits])
    (fun v ↦ by
      rw [← localUnitsEquiv_apply_snd, ContinuousMulEquiv.apply_symm_apply,
        TauCeti.GlobalNumberFields.ideleFiniteCoord_ideleOfUnits]
      exact RestrictedProduct.mk_apply _ _ z hz v)

end NumberField.IdeleGroup
