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
import TauCeti.Topology.Algebra.ContinuousMulEquiv

/-!
# Basic API for ideles

This file records the relation between Mathlib's diagonal embeddings into the idele group and the
adele ring. In particular, principal-idele membership can be tested on the underlying adele.

It also defines the finite component `NumberField.IdeleGroup.toFiniteIdele` of an idele, a unit of
the finite adele ring, and the idele `NumberField.IdeleGroup.ofFiniteIdele` with a given finite
component and trivial infinite components, and its counterpart
`NumberField.IdeleGroup.ofInfiniteIdele` with a given infinite component and trivial finite
components.  The finite component is how ideles are handed to and from the
finite-idele theory of fractional ideals: on a principal idele the finite component is the
principal finite idele of the same element.

The coordinate maps `IsDedekindDomain.HeightOneSpectrum.ideleFiniteCoord` and
`NumberField.InfinitePlace.ideleInfiniteCoord` read the local units of an idele.
`NumberField.IdeleGroup.ext` determines an idele by equality of all these coordinates. The
constructor `TauCeti.GlobalNumberFields.ideleOfUnits` assembles local units that are integral units
at almost every finite place; `TauCeti.GlobalNumberFields.ideleFiniteCoord_ideleOfUnits` and
`TauCeti.GlobalNumberFields.ideleInfiniteCoord_ideleOfUnits` recover those units.

The embeddings of the units of the completions, at the infinite and at the finite places, into
the idele group and the idele class group are continuous, and so are `toFiniteIdele` and
`ofFiniteIdele`.

Finally, `NumberField.IdeleGroup.localUnitsEquiv` identifies the idele group, with its units
topology, with the product of the unit groups `K_wˣ` at the infinite places and the restricted
product of the unit groups `K_vˣ` at the finite places with respect to the local integral units
`𝒪_vˣ`, as topological groups. Its coordinates are the coordinate maps above, and its inverse is
`TauCeti.GlobalNumberFields.ideleOfUnits`. This is the classical description of the idele group as
a restricted product over all places, and it shows that the units topology of the adele ring is
the restricted-product topology of the local unit groups.

The idele `TauCeti.GlobalNumberFields.twoInf` is `2` at the infinite places and `1` at the finite
places. Its projection and norm lemmas describe dyadic scaling of arbitrary adeles.

This topology need not be the subspace topology of the adele ring: when `R` has infinitely many
height-one primes, `NumberField.IdeleGroup.not_isEmbedding_val` shows that the inclusion of the
ideles into the adeles is not an embedding.

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

/-- The idele with the given infinite component and all finite components equal to `1`. -/
def ofInfiniteIdele : (InfiniteAdeleRing K)ˣ →* IdeleGroup R K :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing R K))

@[simp]
theorem coe_ofInfiniteIdele (a : (InfiniteAdeleRing K)ˣ) :
    (ofInfiniteIdele R K a : AdeleRing R K) =
      ((a : InfiniteAdeleRing K), (1 : FiniteAdeleRing R K)) :=
  (rfl)

/-- The finite component of `ofInfiniteIdele R K a` is trivial. -/
@[simp]
theorem toFiniteIdele_ofInfiniteIdele (a : (InfiniteAdeleRing K)ˣ) :
    toFiniteIdele R K (ofInfiniteIdele R K a) = 1 :=
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

/-- The finite component of an idele depends continuously on the idele. -/
@[continuity, fun_prop]
theorem continuous_toFiniteIdele : Continuous (toFiniteIdele R K) :=
  continuous_snd.units_map _

/-- The idele with a given finite component and trivial infinite components depends continuously
on the finite component. -/
@[continuity, fun_prop]
theorem continuous_ofFiniteIdele : Continuous (ofFiniteIdele R K) :=
  (continuous_const.prodMk continuous_id).units_map _

end NumberField.IdeleGroup

namespace NumberField.IdeleClassGroup

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The idele class group is commutative. This instance makes commutativity available to
instance search without unfolding the quotient abbreviation. -/
instance instIsMulCommutative : IsMulCommutative (IdeleClassGroup R K) :=
  ⟨⟨fun a b ↦ mul_comm a b⟩⟩

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
        [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units] :=
  (ContinuousMulEquiv.prodUnits _ _).trans
    (ContinuousMulEquiv.piUnits.prodCongr (FiniteAdeleRing.unitsContinuousMulEquiv R K))

variable {R K}

/-- The infinite part of `NumberField.IdeleGroup.localUnitsEquiv` consists of the coordinates of
an idele at the infinite places. -/
@[simp]
theorem localUnitsEquiv_apply_fst (x : IdeleGroup R K) (w : InfinitePlace K) :
    (localUnitsEquiv R K x).1 w = w.ideleInfiniteCoord x := by
  rw [localUnitsEquiv, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.prodCongr_apply]
  exact Units.ext (rfl)

/-- The finite part of `NumberField.IdeleGroup.localUnitsEquiv` consists of the coordinates of an
idele at the finite places. -/
@[simp]
theorem localUnitsEquiv_apply_snd (x : IdeleGroup R K) (v : HeightOneSpectrum R) :
    (localUnitsEquiv R K x).2 v = v.ideleFiniteCoord x := by
  rw [localUnitsEquiv, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.prodCongr_apply]
  exact Units.ext (FiniteAdeleRing.coe_unitsContinuousMulEquiv_apply _ v)

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

namespace NumberField.IdeleGroup

open Filter Topology

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The ideles do not carry the subspace topology of the adeles** when `R` has infinitely many
height-one primes, for instance for the ring of integers of a number field: the inclusion of the
idele group, with the units topology, into the adele ring is not an embedding. -/
theorem not_isEmbedding_val [Infinite (HeightOneSpectrum R)] :
    ¬IsEmbedding (Units.val : IdeleGroup R K → AdeleRing R K) := by
  intro h
  -- `ofFiniteIdele` is an embedding, since `toFiniteIdele` is a continuous left inverse
  have hof : IsEmbedding (ofFiniteIdele R K) :=
    Function.LeftInverse.isEmbedding (toFiniteIdele_ofFiniteIdele R K)
      (continuous_toFiniteIdele R K) (continuous_ofFiniteIdele R K)
  have hval : Units.val ∘ ofFiniteIdele R K =
      (fun a ↦ ((1 : InfiniteAdeleRing K), a)) ∘ Units.val :=
    funext fun a ↦ coe_ofFiniteIdele R K a
  exact FiniteAdeleRing.not_isEmbedding_val R K <|
    .of_comp Units.continuous_val (continuous_const.prodMk continuous_id) (hval ▸ h.comp hof)

end NumberField.IdeleGroup

namespace TauCeti.GlobalNumberFields

open scoped NumberField.AdeleRing

variable (K : Type*) [Field K] [NumberField K]

/-- The idele `2_∞` of a number field `K`: it is `2` at every infinite place and `1` at every
finite place. -/
noncomputable def twoInf : 𝔸[K]ˣ :=
  IdeleGroup.ofInfiniteIdele (𝓞 K) K
    (Units.map (algebraMap K (InfiniteAdeleRing K)).toMonoidHom
      (Units.mk0 (2 : K) two_ne_zero))

variable {K}

/-- The integral powers of `2_∞` are `2 ^ k` at the infinite places and `1` at the finite
places. -/
@[simp]
theorem coe_twoInf_zpow (k : ℤ) :
    ((twoInf K ^ k : 𝔸[K]ˣ) : 𝔸[K]) = (algebraMap K (InfiniteAdeleRing K) (2 ^ k), 1) := by
  rw [twoInf, ← map_zpow, IdeleGroup.coe_ofInfiniteIdele, ← map_zpow, Units.coe_map,
    Units.val_zpow_eq_zpow_val, Units.val_mk0]
  rfl

/-- The idele `2_∞` is `2` at the infinite places and `1` at the finite places. -/
@[simp]
theorem coe_twoInf : ((twoInf K : 𝔸[K]ˣ) : 𝔸[K]) = (2, 1) := by
  rw [← zpow_one (twoInf K), coe_twoInf_zpow, zpow_one, map_ofNat]

/-- The inverses of the integral powers of `2_∞`, in the form `simp` reaches through
`zpow_neg`. -/
@[simp]
theorem coe_inv_twoInf_zpow (k : ℤ) :
    (((twoInf K ^ k)⁻¹ : 𝔸[K]ˣ) : 𝔸[K]) = (algebraMap K (InfiniteAdeleRing K) (2 ^ k)⁻¹, 1) := by
  rw [← zpow_neg, coe_twoInf_zpow, zpow_neg]

/-- Multiplying an adele by a power of `2_∞` does not change its finite part. -/
theorem snd_twoInf_zpow_mul (k : ℤ) (a : 𝔸[K]) :
    (((twoInf K ^ k : 𝔸[K]ˣ) : 𝔸[K]) * a).2 = a.2 := by
  rw [coe_twoInf_zpow, Prod.snd_mul, one_mul]

/-- Multiplying an adele by `2_∞ ^ k` multiplies its norm at every infinite place by `2 ^ k`. -/
theorem norm_fst_twoInf_zpow_mul_apply (k : ℤ) (a : 𝔸[K]) (w : InfinitePlace K) :
    ‖(((twoInf K ^ k : 𝔸[K]ˣ) : 𝔸[K]) * a).1 w‖ = 2 ^ k * ‖a.1 w‖ := by
  have hnorm (z : K) : ‖algebraMap K (InfiniteAdeleRing K) z w‖ = w z := by
    simp [InfiniteAdeleRing.algebraMap_apply, AbsoluteValue.Completion.norm_coe,
      InfinitePlace.coe_apply]
  have h2 : w 2 = 2 := by exact_mod_cast w.map_natCast 2
  rw [coe_twoInf_zpow]
  -- Normalize the product projection before rewriting at the dependent coordinate `w`.
  change ‖algebraMap K (InfiniteAdeleRing K) (2 ^ k) w * a.1 w‖ = _
  rw [norm_mul, hnorm, map_zpow₀, h2]

/-- Multiplying a diagonal adele by `2_∞ ^ k` multiplies its absolute value at every infinite
place by `2 ^ k`. -/
theorem norm_fst_twoInf_zpow_mul_algebraMap_apply (k : ℤ) (x : K) (w : InfinitePlace K) :
    ‖(((twoInf K ^ k : 𝔸[K]ˣ) : 𝔸[K]) * algebraMap K 𝔸[K] x).1 w‖ = 2 ^ k * w x := by
  rw [norm_fst_twoInf_zpow_mul_apply, AdeleRing.algebraMap_fst_def]
  simp only [InfiniteAdeleRing.algebraMap_apply, AbsoluteValue.Completion.norm_coe,
    InfinitePlace.coe_apply]

/-- The finite component of `2_∞` is trivial. Powers simplify using `map_zpow`. -/
@[simp]
theorem toFiniteIdele_twoInf : IdeleGroup.toFiniteIdele (𝓞 K) K (twoInf K) = 1 := by
  simp [twoInf]

/-- The coordinate of `2_∞` at every finite place is `1`. Powers simplify using `map_zpow`. -/
@[simp]
theorem _root_.IsDedekindDomain.HeightOneSpectrum.ideleFiniteCoord_twoInf
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : v.ideleFiniteCoord (twoInf K) = 1 := by
  apply Units.ext
  rw [IsDedekindDomain.HeightOneSpectrum.coe_ideleFiniteCoord, coe_twoInf, Units.val_one]
  rfl

/-- The coordinate of `2_∞` at an infinite place is the unit `2`. Powers simplify using
`map_zpow`. -/
@[simp]
theorem _root_.NumberField.InfinitePlace.ideleInfiniteCoord_twoInf (w : InfinitePlace K) :
    w.ideleInfiniteCoord (twoInf K) =
      Units.map (algebraMap K w.Completion).toMonoidHom (Units.mk0 (2 : K) two_ne_zero) := by
  apply Units.ext
  rw [InfinitePlace.coe_ideleInfiniteCoord, coe_twoInf, Units.coe_map, Units.val_mk0]
  -- The infinite-adele numeral is pointwise; normalize its projection before `map_ofNat`.
  change (2 : InfiniteAdeleRing K) w = algebraMap K w.Completion 2
  rw [map_ofNat]
  rfl

end TauCeti.GlobalNumberFields
