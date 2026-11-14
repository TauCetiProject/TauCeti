/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
public import TauCeti.NumberTheory.ClassFieldTheory.Global.PrincipalIdeal
import TauCeti.FieldTheory.Galois.Abelian.Equiv
import TauCeti.FieldTheory.Galois.Restriction
import TauCeti.FieldTheory.IntermediateField.ScalarTower
import TauCeti.FieldTheory.IsSepClosed
import TauCeti.NumberTheory.NumberField.AlgEquiv
import TauCeti.NumberTheory.NumberField.InfinitePlace.Transport

/-!
# The Hilbert class field tower in the separable closure

Let `L/K` be a finite Galois extension of number fields that is unramified at every finite
and infinite place and contains the Hilbert class field `H` of `K`. Its maximal abelian
subextension is exactly `H`: every abelian subextension is unramified and so lies in `H`,
while `H` itself is abelian.

`fixedField_commutator_eq_hilbertClassField` gives this identification in the finite-layer
presentation used by transfer. Consequently every idele class of `K`, extended to `H`, is a
norm from `L` (`ideleClassExtension_mem_range_ideleClassNormMap_of_unramified`,
`ideleClassExtension_mem_range_ideleClassNormMap_of_isGalois_of_unramified`).

To instantiate this at the second step of the Hilbert class field tower, we also realize the ray
class fields — and hence the ordinary and narrow Hilbert class fields — of any number field `L`
in a tower `K → L → Kˢ` inside `Kˢ` itself (`rayClassFieldOver`, `hilbertClassFieldOver`,
`narrowHilbertClassFieldOver`):

* `rayClassFieldOver K 𝔪` specializes to `rayClassField 𝔪` over the base (`rayClassFieldOver_self`)
  and is `L`-isomorphic to `rayClassField 𝔪` (`rayClassFieldOverEquivOfAlgHom`), so its idele-class
  norm group over `L` is `raySubgroup 𝔪` (`range_ideleClassNormMap_rayClassFieldOver`), `𝔪` is
  admissible for it (`isAdmissibleModulus_rayClassFieldOver`), and it inherits the admissibility,
  norm-group, monotonicity, and degree characterizations of `rayClassField 𝔪`
  (`isAdmissibleModulus_iff_le_rayClassFieldOver`, `fieldRange_eq_rayClassFieldOver_iff`,
  `rayClassFieldOver_le_rayClassFieldOver_iff`, `rayClassFieldOver_mono`,
  `finrank_rayClassFieldOver`, `finrank_hilbertClassFieldOver`,
  `finrank_narrowHilbertClassFieldOver`, `fieldRange_le_hilbertClassFieldOver_iff`,
  `fieldRange_le_narrowHilbertClassFieldOver_iff`).
* `rayClassFieldOver K 𝔪` is unramified over `𝓞 L` outside `𝔪.support`
  (`isUnramifiedAt_rayClassFieldOver_tower_top_of_notMem_support`) and over `𝓞 K` at primes whose
  restriction to `𝓞 L` avoids `𝔪.support` and is unramified over `𝓞 K`
  (`isUnramifiedAt_rayClassFieldOver_of_notMem_support_of_isUnramifiedAt`), specializing to
  `hilbertClassFieldOver K L` and `narrowHilbertClassFieldOver K L`
  (`isUnramifiedAt_hilbertClassFieldOver_tower_top`,
  `isUnramifiedAt_hilbertClassFieldOver_of_isUnramifiedAt`,
  `isUnramifiedAt_narrowHilbertClassFieldOver_tower_top`,
  `isUnramifiedAt_narrowHilbertClassFieldOver_of_isUnramifiedAt`), while infinite-place
  unramifiedness lifts in the Hilbert tower
  (`isUnramifiedAtInfinitePlaces_hilbertClassFieldOver_tower_top`,
  `isUnramifiedAtInfinitePlaces_hilbertClassFieldOver`).
* When `L/K` is Galois, both `hilbertClassFieldOver K L` and `narrowHilbertClassFieldOver K L` are
  Galois over `K` (`isGalois_hilbertClassFieldOver`, `isGalois_narrowHilbertClassFieldOver`), by
  transporting their admissibility characterizations along automorphisms of `Kˢ/K`.

## Main definitions

* `rayClassFieldOver`: the ray class field of a modulus `𝔪` of `L` realized inside
  `SeparableClosure K`.
* `hilbertClassFieldOver`, `narrowHilbertClassFieldOver`: the ordinary and narrow Hilbert class
  fields of `L` inside `SeparableClosure K`.
* `rayClassFieldOverEquivOfAlgHom`: the `L`-algebra isomorphism
  `rayClassField 𝔪 ≃ₐ[L] rayClassFieldOver K 𝔪` induced by any `L`-embedding into `Kˢ`.

## Main results

* `ideleClassExtension_mem_range_ideleClassNormMap_of_isGalois_of_unramified`: extended idele
  classes in `hilbertClassField K` are norms from any everywhere-unramified finite Galois
  intermediate field containing `hilbertClassField K`.
* `range_ideleClassNormMap_rayClassFieldOver`, `isAdmissibleModulus_iff_le_rayClassFieldOver`,
  `fieldRange_eq_rayClassFieldOver_iff`, `rayClassFieldOver_le_rayClassFieldOver_iff`,
  `finrank_rayClassFieldOver`: norm-group, universal-property, inclusion, and degree
  characterizations of `rayClassFieldOver K 𝔪`.
* `isUnramifiedAt_rayClassFieldOver_of_notMem_support_of_isUnramifiedAt`,
  `isUnramifiedAt_hilbertClassFieldOver_of_isUnramifiedAt`,
  `isUnramifiedAtInfinitePlaces_hilbertClassFieldOver`: preservation of unramifiedness in the
  relative class-field tower.
* `isGalois_hilbertClassFieldOver`, `isGalois_narrowHilbertClassFieldOver`: Galoisness over `K` when
  `L/K` is Galois.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter XIII.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §§6–7.
-/

public noncomputable section

open IntermediateField NumberField IsDedekindDomain

namespace TauCeti.ClassFieldTheory

open GlobalNumberFields

section Transfer

variable {K : Type} [Field K] [NumberField K]

/-! ### Maximal abelian subextension and transfer in unramified extensions -/

/-- The maximal abelian subextension of an everywhere-unramified finite Galois extension
containing the Hilbert class field is the Hilbert class field itself. -/
theorem classField_maximalAbelianLayer_eq_hilbertClassField
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    (hH : hilbertClassField K ≤ classField K V)
    (hur : ∀ w : HeightOneSpectrum (𝓞 (classField K V)),
      Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    [IsUnramifiedAtInfinitePlaces K (classField K V)] :
    classField K V.maximalAbelianLayer = hilbertClassField K := by
  let M := classField K V.maximalAbelianLayer
  have hML : M ≤ classField K V :=
    (classField_le_classField_iff K V V.maximalAbelianLayer).2 V.le_maximalAbelianLayer
  let : Algebra M (classField K V) := (IntermediateField.inclusion hML).toAlgebra
  have : IsScalarTower K M (classField K V) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsAbelianGalois K M :=
    isAbelianGalois_classField_iff.2 V.isAbelianClassFieldLayer_maximalAbelianLayer
  apply le_antisymm
  · have hMinf : IsUnramifiedAtInfinitePlaces K M :=
      IsUnramifiedAtInfinitePlaces.bot K M (classField K V)
    have hMfin (w : HeightOneSpectrum (𝓞 M)) :
        Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
      obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (w.asIdeal.primesOver (𝓞 (classField K V))))
      have : Algebra.IsUnramifiedAt (𝓞 K) Q :=
        hur ⟨Q, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot Q⟩
      exact Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) w.asIdeal Q
    simpa only [fieldRange_val] using
      (fieldRange_le_hilbertClassField_iff M.val).2 ⟨hMfin, hMinf⟩
  · rw [hilbertClassField, rayClassField_def] at hH ⊢
    exact (classField_le_classField_iff K V.maximalAbelianLayer _).2
      (OpenNormalSubgroup.maximalAbelianLayer_le
        ((classField_le_classField_iff K V _).1 hH)
        (globalClassField (rayNormSubgroup (Modulus.one K))).2)

/-- In an everywhere-unramified finite Galois extension containing the Hilbert class field,
the preimage of the finite Galois group's commutator fixes exactly the Hilbert class field.
This is the field identification required by the idelic transfer theorem. -/
theorem fixedField_commutator_eq_hilbertClassField
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    (hH : hilbertClassField K ≤ classField K V)
    (hur : ∀ w : HeightOneSpectrum (𝓞 (classField K V)),
      Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    [IsUnramifiedAtInfinitePlaces K (classField K V)] :
    fixedField ((NormalLayer.ofOpenNormal V).subgroupLayer
      (commutator (NormalLayer.ofOpenNormal V).Gal)).ground.toSubgroup = hilbertClassField K := by
  rw [NormalLayer.ground_subgroupLayer, V.subgroupGround_commutator]
  have hfield : fixedField V.maximalAbelianLayer.toSubgroup =
      classField K V.maximalAbelianLayer := by
    simpa only [NormalLayer.top_ofOpenNormal] using
      fixedField_top_ofOpenNormal_eq_classField V.maximalAbelianLayer
  rw [hfield]
  exact classField_maximalAbelianLayer_eq_hilbertClassField V hH hur

/-- Every idele class of `K`, extended to its Hilbert class field, is a norm from any
everywhere-unramified finite Galois extension containing that field. The relative algebra
and scalar tower are the caller's compatible choices. -/
theorem ideleClassExtension_mem_range_ideleClassNormMap_of_unramified
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    [Algebra (hilbertClassField K) (classField K V)]
    [IsScalarTower (hilbertClassField K) (classField K V) (SeparableClosure K)]
    (hur : ∀ w : HeightOneSpectrum (𝓞 (classField K V)),
      Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    [IsUnramifiedAtInfinitePlaces K (classField K V)]
    (c : IdeleClassGroup (𝓞 K) K) :
    ideleClassExtension K (hilbertClassField K) c ∈
      (ideleClassNormMap (hilbertClassField K) (classField K V) :
        IdeleClassGroup (𝓞 (classField K V)) (classField K V) →*
          IdeleClassGroup (𝓞 (hilbertClassField K)) (hilbertClassField K)).range :=
  ideleClassExtension_mem_range_ideleClassNormMap_commutator_ofOpenNormal V
    (fixedField_commutator_eq_hilbertClassField V
      IntermediateField.le_of_isScalarTower hur)
    (fixedField_top_ofOpenNormal_eq_classField V) c

/-- Intermediate-field form of `ideleClassExtension_mem_range_ideleClassNormMap_of_unramified`:
every idele class of `K`, extended to `hilbertClassField K`, is a norm from any
everywhere-unramified finite Galois intermediate field `E` of `Kˢ / K` containing
`hilbertClassField K`. -/
theorem ideleClassExtension_mem_range_ideleClassNormMap_of_isGalois_of_unramified
    (E : IntermediateField K (SeparableClosure K)) [NumberField E]
    [IsGalois K E] [Algebra (hilbertClassField K) E]
    [IsScalarTower (hilbertClassField K) E (SeparableClosure K)]
    (hur : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal)
    [IsUnramifiedAtInfinitePlaces K E]
    (c : IdeleClassGroup (𝓞 K) K) :
    ideleClassExtension K (hilbertClassField K) c ∈
      (ideleClassNormMap (hilbertClassField K) E :
        IdeleClassGroup (𝓞 E) E →*
          IdeleClassGroup (𝓞 (hilbertClassField K)) (hilbertClassField K)).range := by
  obtain ⟨V, rfl⟩ := (exists_classField_eq_iff E).2 ⟨inferInstance, inferInstance⟩
  exact ideleClassExtension_mem_range_ideleClassNormMap_of_unramified V hur c

end Transfer

/-! ### Relative class fields in the separable closure of the base -/

section RelativeClassFields

variable (K : Type) [Field K]
  {L : Type} [Field L] [NumberField L] [Algebra K L]
  [Algebra L (SeparableClosure K)] [IsScalarTower K L (SeparableClosure K)]
  (𝔪 : Modulus L)

/-- **The ray class field of a modulus `𝔪` of `L`, realized in `SeparableClosure K`**: the normal
closure over `L` of `rayClassField 𝔪` inside `SeparableClosure K`, viewed as an intermediate field
over `K`. Because `rayClassField 𝔪` is normal over `L`, every `L`-embedding of `rayClassField 𝔪`
into `SeparableClosure K` has this field as its image (`rayClassFieldOver_eq_fieldRange`). -/
def rayClassFieldOver : IntermediateField K (SeparableClosure K) :=
  (IntermediateField.normalClosure L (rayClassField 𝔪) (SeparableClosure K)).restrictScalars K

/-- Unfolding lemma for `rayClassFieldOver`. -/
theorem rayClassFieldOver_def :
    rayClassFieldOver K 𝔪 =
      (IntermediateField.normalClosure L (rayClassField 𝔪) (SeparableClosure K)).restrictScalars
        K :=
  (rfl)

/-- Every `L`-embedding of `rayClassField 𝔪` into `SeparableClosure K` has image
`rayClassFieldOver K 𝔪`. -/
theorem rayClassFieldOver_eq_fieldRange (ι : rayClassField 𝔪 →ₐ[L] SeparableClosure K) :
    rayClassFieldOver K 𝔪 = ι.fieldRange.restrictScalars K :=
  congrArg (IntermediateField.restrictScalars K) (IntermediateField.normalClosure_eq_fieldRange ι)

/-- Over the base field `K` itself, `rayClassFieldOver K 𝔪` is `rayClassField 𝔪`. -/
@[simp]
theorem rayClassFieldOver_self {K : Type} [Field K] [NumberField K] (𝔪 : Modulus K) :
    rayClassFieldOver K 𝔪 = rayClassField 𝔪 := by
  rw [rayClassFieldOver_eq_fieldRange K 𝔪 (rayClassField 𝔪).val, IntermediateField.fieldRange_val]
  rfl

/-- The image of `L` in `SeparableClosure K` lies inside `rayClassFieldOver K 𝔪`. -/
theorem algebraMap_mem_rayClassFieldOver (a : L) :
    algebraMap L (SeparableClosure K) a ∈ rayClassFieldOver K 𝔪 :=
  (IntermediateField.normalClosure L (rayClassField 𝔪) (SeparableClosure K)).algebraMap_mem a

/-- When `E` is an intermediate field of `SeparableClosure K / K`, `E` lies inside
`rayClassFieldOver K 𝔪` for every modulus `𝔪` of `E`. -/
theorem le_rayClassFieldOver {K : Type} [Field K]
    (E : IntermediateField K (SeparableClosure K)) [NumberField E] (𝔪 : Modulus E) :
    E ≤ rayClassFieldOver K 𝔪 :=
  fun x hx ↦ algebraMap_mem_rayClassFieldOver K 𝔪 ⟨x, hx⟩

/-- Canonical `K`-algebra homomorphism `L →ₐ[K] rayClassFieldOver K 𝔪`. -/
def toRayClassFieldOver : L →ₐ[K] rayClassFieldOver K 𝔪 :=
  (IsScalarTower.toAlgHom K L (SeparableClosure K)).codRestrict
    (rayClassFieldOver K 𝔪).toSubalgebra (algebraMap_mem_rayClassFieldOver K 𝔪)

/-- In `SeparableClosure K`, `toRayClassFieldOver K 𝔪` is `algebraMap L (SeparableClosure K)`. -/
@[simp]
theorem coe_toRayClassFieldOver_apply (a : L) :
    (toRayClassFieldOver K 𝔪 a : SeparableClosure K) = algebraMap L (SeparableClosure K) a :=
  (rfl)

/-- Any `L`-embedding `ι : rayClassField 𝔪 →ₐ[L] SeparableClosure K` restricts to an `L`-algebra
isomorphism `rayClassField 𝔪 ≃ₐ[L] rayClassFieldOver K 𝔪`, for any compatible `L`-algebra
structure on `rayClassFieldOver K 𝔪`. -/
def rayClassFieldOverEquivOfAlgHom (ι : rayClassField 𝔪 →ₐ[L] SeparableClosure K)
    [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)] :
    rayClassField 𝔪 ≃ₐ[L] rayClassFieldOver K 𝔪 :=
  AlgEquiv.ofRingEquiv
    (f := ι.equivFieldRange.toRingEquiv.trans <|
      (IntermediateField.restrictScalarsAlgEquiv K ι.fieldRange).symm.toRingEquiv.trans
        (IntermediateField.equivOfEq (rayClassFieldOver_eq_fieldRange K 𝔪 ι).symm).toRingEquiv)
    fun a ↦ Subtype.ext <| by
      simp [← IntermediateField.algebraMap_apply (rayClassFieldOver K 𝔪),
        ← IsScalarTower.algebraMap_apply L (rayClassFieldOver K 𝔪) (SeparableClosure K)]

/-- In `SeparableClosure K`, `rayClassFieldOverEquivOfAlgHom K 𝔪 ι` acts as `ι`. -/
@[simp]
theorem coe_rayClassFieldOverEquivOfAlgHom_apply (ι : rayClassField 𝔪 →ₐ[L] SeparableClosure K)
    [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)] (x : rayClassField 𝔪) :
    (rayClassFieldOverEquivOfAlgHom K 𝔪 ι x : SeparableClosure K) = ι x := by
  simp [rayClassFieldOverEquivOfAlgHom]

/-- `rayClassFieldOver K 𝔪` is `L`-isomorphic to `rayClassField 𝔪`. -/
theorem nonempty_algEquiv_rayClassFieldOver [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)] :
    Nonempty (rayClassField 𝔪 ≃ₐ[L] rayClassFieldOver K 𝔪) :=
  ⟨rayClassFieldOverEquivOfAlgHom K 𝔪 IsSepClosed.lift⟩

/-- `rayClassFieldOver K 𝔪` is an abelian Galois extension of `L`. -/
instance isAbelianGalois_rayClassFieldOver [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)] :
    IsAbelianGalois L (rayClassFieldOver K 𝔪) :=
  IsAbelianGalois.of_algHom (rayClassFieldOverEquivOfAlgHom K 𝔪 IsSepClosed.lift).symm.toAlgHom

/-- `rayClassFieldOver K 𝔪` is a number field. -/
instance numberField_rayClassFieldOver : NumberField (rayClassFieldOver K 𝔪) :=
  have : NumberField (IntermediateField.normalClosure L (rayClassField 𝔪) (SeparableClosure K)) :=
    .of_module_finite L _
  .of_ringEquiv _ _ (IntermediateField.restrictScalarsAlgEquiv K _).symm.toRingEquiv

/-- `rayClassFieldOver K 𝔪` is finite-dimensional over `K`. -/
instance finiteDimensional_rayClassFieldOver :
    FiniteDimensional K (rayClassFieldOver K 𝔪) := by
  have := (algebraMap K L).charZero
  exact Module.Finite.of_restrictScalars_finite ℚ K (rayClassFieldOver K 𝔪)

/-- **The norm group of `rayClassFieldOver K 𝔪` over `L` is `raySubgroup 𝔪`.** -/
@[simp]
theorem range_ideleClassNormMap_rayClassFieldOver
    [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)] :
    (ideleClassNormMap L (rayClassFieldOver K 𝔪) :
        IdeleClassGroup (𝓞 (rayClassFieldOver K 𝔪)) (rayClassFieldOver K 𝔪) →*
          IdeleClassGroup (𝓞 L) L).range = raySubgroup 𝔪 :=
  (range_ideleClassNormMap_eq_of_algEquiv
    (rayClassFieldOverEquivOfAlgHom K 𝔪 IsSepClosed.lift).symm).trans
    (range_ideleClassNormMap_rayClassField 𝔪)

/-- A modulus `𝔪` of `L` is admissible for `rayClassFieldOver K 𝔪 / L`. -/
@[simp]
theorem isAdmissibleModulus_rayClassFieldOver
    [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)] :
    IsAdmissibleModulus L (rayClassFieldOver K 𝔪) 𝔪 :=
  isAdmissibleModulus_iff.2 (range_ideleClassNormMap_rayClassFieldOver K 𝔪).ge

/-- **The degree of `rayClassFieldOver K 𝔪` over `L` is the order of `RayClassGroup 𝔪`.** -/
@[simp]
theorem finrank_rayClassFieldOver
    [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)] :
    Module.finrank L (rayClassFieldOver K 𝔪) = Nat.card (RayClassGroup 𝔪) :=
  (rayClassFieldOverEquivOfAlgHom K 𝔪 IsSepClosed.lift).symm.toLinearEquiv.finrank_eq.trans
    (finrank_rayClassField 𝔪)

/-- An `L`-algebra isomorphism `e : SeparableClosure K ≃ₐ[L] SeparableClosure L` identifies
`rayClassFieldOver K 𝔪` with `(rayClassField 𝔪).map e.symm.toAlgHom`. -/
private theorem rayClassFieldOver_eq_map
    (e : SeparableClosure K ≃ₐ[L] SeparableClosure L) :
    rayClassFieldOver K 𝔪 = ((rayClassField 𝔪).map e.symm.toAlgHom).restrictScalars K := by
  rw [rayClassFieldOver_eq_fieldRange K 𝔪 (e.symm.toAlgHom.comp (rayClassField 𝔪).val),
    IntermediateField.fieldRange_comp_val]

variable {K 𝔪} in
omit [NumberField L] [Algebra K L] [IsScalarTower K L (SeparableClosure K)] in
private theorem map_symm_map (E : IntermediateField L (SeparableClosure L))
    (e : SeparableClosure K ≃ₐ[L] SeparableClosure L) :
    (E.map e.symm.toAlgHom).map e.toAlgHom = E := by
  rw [IntermediateField.map_map, show e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id _ _ by ext; simp,
    IntermediateField.map_id]

variable {K 𝔪} in
omit [NumberField L] [Algebra K L] [IsScalarTower K L (SeparableClosure K)] in
private theorem map_map_symm (F : IntermediateField L (SeparableClosure K))
    (e : SeparableClosure K ≃ₐ[L] SeparableClosure L) :
    (F.map e.toAlgHom).map e.symm.toAlgHom = F := by
  rw [IntermediateField.map_map, show e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id _ _ by ext; simp,
    IntermediateField.map_id]

private theorem restrictScalars_le_rayClassFieldOver_iff
    (F : IntermediateField L (SeparableClosure K))
    (e : SeparableClosure K ≃ₐ[L] SeparableClosure L) :
    F.restrictScalars K ≤ rayClassFieldOver K 𝔪 ↔ F.map e.toAlgHom ≤ rayClassField 𝔪 := by
  rw [rayClassFieldOver_eq_map K 𝔪 e, IntermediateField.restrictScalars_le_iff K]
  exact ⟨fun h ↦ (IntermediateField.map_mono e.toAlgHom h).trans_eq
      (map_symm_map (rayClassField 𝔪) e),
    fun h ↦ (map_map_symm F e).symm.trans_le (IntermediateField.map_mono e.symm.toAlgHom h)⟩

private theorem rayClassFieldOver_le_restrictScalars_iff
    (F : IntermediateField L (SeparableClosure K))
    (e : SeparableClosure K ≃ₐ[L] SeparableClosure L) :
    rayClassFieldOver K 𝔪 ≤ F.restrictScalars K ↔ rayClassField 𝔪 ≤ F.map e.toAlgHom := by
  rw [rayClassFieldOver_eq_map K 𝔪 e, IntermediateField.restrictScalars_le_iff K]
  exact ⟨fun h ↦ (map_symm_map (rayClassField 𝔪) e).symm.trans_le
      (IntermediateField.map_mono e.toAlgHom h),
    fun h ↦ (IntermediateField.map_mono e.symm.toAlgHom h).trans_eq (map_map_symm F e)⟩

/-- **Universal property of `rayClassFieldOver K 𝔪`**: for a finite abelian extension `M/L` and any
`L`-embedding `ι : M →ₐ[L] SeparableClosure K`, `𝔪` is admissible for `M/L` if and only if the
image of `ι` lies in `rayClassFieldOver K 𝔪`. -/
theorem isAdmissibleModulus_iff_le_rayClassFieldOver
    {M : Type} [Field M] [NumberField M] [Algebra L M] [IsAbelianGalois L M]
    (ι : M →ₐ[L] SeparableClosure K) :
    IsAdmissibleModulus L M 𝔪 ↔ ι.fieldRange.restrictScalars K ≤ rayClassFieldOver K 𝔪 := by
  have := TauCeti.isSepClosure_tower_top K L (SeparableClosure K)
  let e := IsSepClosure.equiv L (SeparableClosure K) (SeparableClosure L)
  have hrange : (e.toAlgHom.comp ι).fieldRange = ι.fieldRange.map e.toAlgHom := by ext; simp
  rw [isAdmissibleModulus_iff_le_rayClassField 𝔪 (e.toAlgHom.comp ι), hrange,
    restrictScalars_le_rayClassFieldOver_iff K 𝔪 _ e]

/-- **Norm-group characterization of `rayClassFieldOver K 𝔪`**: a finite abelian extension `M/L`
embedded in `SeparableClosure K` by `ι` has image `rayClassFieldOver K 𝔪` if and only if its
idele-class norm group over `L` is `raySubgroup 𝔪`. -/
theorem fieldRange_eq_rayClassFieldOver_iff
    {M : Type} [Field M] [NumberField M] [Algebra L M] [IsAbelianGalois L M]
    (ι : M →ₐ[L] SeparableClosure K) :
    ι.fieldRange.restrictScalars K = rayClassFieldOver K 𝔪 ↔
      (ideleClassNormMap L M : IdeleClassGroup (𝓞 M) M →* IdeleClassGroup (𝓞 L) L).range =
        raySubgroup 𝔪 := by
  have := TauCeti.isSepClosure_tower_top K L (SeparableClosure K)
  let e := IsSepClosure.equiv L (SeparableClosure K) (SeparableClosure L)
  have hrange : (e.toAlgHom.comp ι).fieldRange = ι.fieldRange.map e.toAlgHom := by ext; simp
  rw [← fieldRange_eq_rayClassField_iff 𝔪 (e.toAlgHom.comp ι), hrange, le_antisymm_iff,
    le_antisymm_iff, restrictScalars_le_rayClassFieldOver_iff K 𝔪 _ e,
    rayClassFieldOver_le_restrictScalars_iff K 𝔪 _ e]

variable {K 𝔪} in
/-- **Inclusions of relative ray class fields are inclusions of ray subgroups, reversed.** -/
theorem rayClassFieldOver_le_rayClassFieldOver_iff {𝔫 : Modulus L} :
    rayClassFieldOver K 𝔪 ≤ rayClassFieldOver K 𝔫 ↔ raySubgroup 𝔫 ≤ raySubgroup 𝔪 := by
  have := TauCeti.isSepClosure_tower_top K L (SeparableClosure K)
  let e := IsSepClosure.equiv L (SeparableClosure K) (SeparableClosure L)
  rw [rayClassFieldOver_eq_map K 𝔪 e, restrictScalars_le_rayClassFieldOver_iff K 𝔫 _ e,
    map_symm_map (rayClassField 𝔪) e, rayClassField_le_rayClassField_iff]

variable {K 𝔪} in
/-- **Relative ray class fields grow with the modulus**: if `𝔪 ∣ 𝔫`, then
`rayClassFieldOver K 𝔪 ≤ rayClassFieldOver K 𝔫`. -/
theorem rayClassFieldOver_mono {𝔫 : Modulus L} (h : 𝔪 ∣ 𝔫) :
    rayClassFieldOver K 𝔪 ≤ rayClassFieldOver K 𝔫 :=
  rayClassFieldOver_le_rayClassFieldOver_iff.2 (raySubgroup_antitone h)

variable (L) in
/-- **The Hilbert class field of `L`, realized inside `SeparableClosure K`.** -/
abbrev hilbertClassFieldOver : IntermediateField K (SeparableClosure K) :=
  rayClassFieldOver K (Modulus.one L)

variable (L) in
/-- **The narrow Hilbert class field of `L`, realized inside `SeparableClosure K`.** -/
abbrev narrowHilbertClassFieldOver : IntermediateField K (SeparableClosure K) :=
  rayClassFieldOver K (narrowModulus L)

variable (L) in
/-- **The degree of `hilbertClassFieldOver K L` over `L` is the class number of `L`.** -/
@[simp high]
theorem finrank_hilbertClassFieldOver
    [Algebra L (hilbertClassFieldOver K L)]
    [IsScalarTower L (hilbertClassFieldOver K L) (SeparableClosure K)] :
    Module.finrank L (hilbertClassFieldOver K L) = classNumber L :=
  (rayClassFieldOverEquivOfAlgHom K (Modulus.one L)
    IsSepClosed.lift).symm.toLinearEquiv.finrank_eq.trans (finrank_hilbertClassField L)

variable (L) in
/-- **The degree of `narrowHilbertClassFieldOver K L` over `L` is `#(NarrowClassGroup L)`.** -/
@[simp high]
theorem finrank_narrowHilbertClassFieldOver
    [Algebra L (narrowHilbertClassFieldOver K L)]
    [IsScalarTower L (narrowHilbertClassFieldOver K L) (SeparableClosure K)] :
    Module.finrank L (narrowHilbertClassFieldOver K L) = Nat.card (NarrowClassGroup L) :=
  (rayClassFieldOverEquivOfAlgHom K (narrowModulus L)
    IsSepClosed.lift).symm.toLinearEquiv.finrank_eq.trans (finrank_narrowHilbertClassField L)

variable {K} in
/-- **Universal property of `hilbertClassFieldOver K L`**: a finite abelian extension `M/L`
embedded in `SeparableClosure K` by `ι` lies in `hilbertClassFieldOver K L` if and only if `M/L`
is unramified at all finite and infinite places. -/
theorem fieldRange_le_hilbertClassFieldOver_iff
    {M : Type} [Field M] [NumberField M] [Algebra L M] [IsAbelianGalois L M]
    (ι : M →ₐ[L] SeparableClosure K) :
    ι.fieldRange.restrictScalars K ≤ hilbertClassFieldOver K L ↔
      (∀ w : HeightOneSpectrum (𝓞 M), Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal) ∧
        IsUnramifiedAtInfinitePlaces L M := by
  rw [← isAdmissibleModulus_iff_le_rayClassFieldOver, isAdmissibleModulus_one_iff]

variable {K} in
/-- **Universal property of `narrowHilbertClassFieldOver K L`**: a finite abelian extension `M/L`
embedded in `SeparableClosure K` by `ι` lies in `narrowHilbertClassFieldOver K L` if and only if
`M/L` is unramified at every finite prime. -/
theorem fieldRange_le_narrowHilbertClassFieldOver_iff
    {M : Type} [Field M] [NumberField M] [Algebra L M] [IsAbelianGalois L M]
    (ι : M →ₐ[L] SeparableClosure K) :
    ι.fieldRange.restrictScalars K ≤ narrowHilbertClassFieldOver K L ↔
      ∀ w : HeightOneSpectrum (𝓞 M), Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal := by
  rw [← isAdmissibleModulus_iff_le_rayClassFieldOver, isAdmissibleModulus_narrowModulus_iff]

/-- Every prime `w` of `rayClassFieldOver K 𝔪` lying over a prime of `𝓞 L` outside `𝔪.support` is
unramified over `𝓞 L`. -/
theorem isUnramifiedAt_rayClassFieldOver_tower_top_of_notMem_support
    [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)]
    {w : HeightOneSpectrum (𝓞 (rayClassFieldOver K 𝔪))}
    (hw : w.under (𝓞 L) ∉ 𝔪.support) :
    Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal :=
  (isAdmissibleModulus_rayClassFieldOver K 𝔪).isUnramifiedAt_of_notMem_support hw w

/-- If `w` is a prime of `rayClassFieldOver K 𝔪` whose restriction `w.under (𝓞 L)` avoids
`𝔪.support` and is unramified over `𝓞 K`, then `w` is unramified over `𝓞 K`. -/
theorem isUnramifiedAt_rayClassFieldOver_of_notMem_support_of_isUnramifiedAt
    [Algebra L (rayClassFieldOver K 𝔪)]
    [IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K)]
    {w : HeightOneSpectrum (𝓞 (rayClassFieldOver K 𝔪))}
    (hw : w.under (𝓞 L) ∉ 𝔪.support)
    (hL : Algebra.IsUnramifiedAt (𝓞 K) (w.under (𝓞 L)).asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  have : IsScalarTower K L (rayClassFieldOver K 𝔪) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext <|
      (IntermediateField.coe_algebraMap_apply _ x).trans <|
        (IsScalarTower.algebraMap_apply K L (SeparableClosure K) x).trans <|
          (IsScalarTower.algebraMap_apply L (rayClassFieldOver K 𝔪) (SeparableClosure K) _).trans
            (IntermediateField.algebraMap_apply _ _)
  have : Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal :=
    isUnramifiedAt_rayClassFieldOver_tower_top_of_notMem_support K 𝔪 hw
  exact Algebra.IsUnramifiedAt.comp (w.under (𝓞 L)).asIdeal w.asIdeal

variable (L) in
/-- Every prime of `hilbertClassFieldOver K L` is unramified over `𝓞 L`. -/
theorem isUnramifiedAt_hilbertClassFieldOver_tower_top
    [Algebra L (hilbertClassFieldOver K L)]
    [IsScalarTower L (hilbertClassFieldOver K L) (SeparableClosure K)]
    (w : HeightOneSpectrum (𝓞 (hilbertClassFieldOver K L))) :
    Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal :=
  isUnramifiedAt_rayClassFieldOver_tower_top_of_notMem_support K (Modulus.one L) (by simp)

variable (L) in
/-- Every prime of `narrowHilbertClassFieldOver K L` is unramified over `𝓞 L`. -/
theorem isUnramifiedAt_narrowHilbertClassFieldOver_tower_top
    [Algebra L (narrowHilbertClassFieldOver K L)]
    [IsScalarTower L (narrowHilbertClassFieldOver K L) (SeparableClosure K)]
    (w : HeightOneSpectrum (𝓞 (narrowHilbertClassFieldOver K L))) :
    Algebra.IsUnramifiedAt (𝓞 L) w.asIdeal :=
  isUnramifiedAt_rayClassFieldOver_tower_top_of_notMem_support K (narrowModulus L) (by simp)

variable (L) in
/-- `hilbertClassFieldOver K L` is unramified over `L` at all infinite places. -/
instance isUnramifiedAtInfinitePlaces_hilbertClassFieldOver_tower_top
    [Algebra L (hilbertClassFieldOver K L)]
    [IsScalarTower L (hilbertClassFieldOver K L) (SeparableClosure K)] :
    IsUnramifiedAtInfinitePlaces L (hilbertClassFieldOver K L) :=
  (isAdmissibleModulus_one_iff.1 (isAdmissibleModulus_rayClassFieldOver K (Modulus.one L))).2

variable (L) in
/-- Any prime `w` of `hilbertClassFieldOver K L` lying over a prime of `𝓞 L` unramified over `𝓞 K`
is itself unramified over `𝓞 K`. -/
theorem isUnramifiedAt_hilbertClassFieldOver_of_isUnramifiedAt
    [Algebra L (hilbertClassFieldOver K L)]
    [IsScalarTower L (hilbertClassFieldOver K L) (SeparableClosure K)]
    {w : HeightOneSpectrum (𝓞 (hilbertClassFieldOver K L))}
    (hL : Algebra.IsUnramifiedAt (𝓞 K) (w.under (𝓞 L)).asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
  isUnramifiedAt_rayClassFieldOver_of_notMem_support_of_isUnramifiedAt K (Modulus.one L)
    (by simp) hL

variable (L) in
/-- Any prime `w` of `narrowHilbertClassFieldOver K L` lying over a prime of `𝓞 L` unramified over
`𝓞 K` is itself unramified over `𝓞 K`. -/
theorem isUnramifiedAt_narrowHilbertClassFieldOver_of_isUnramifiedAt
    [Algebra L (narrowHilbertClassFieldOver K L)]
    [IsScalarTower L (narrowHilbertClassFieldOver K L) (SeparableClosure K)]
    {w : HeightOneSpectrum (𝓞 (narrowHilbertClassFieldOver K L))}
    (hL : Algebra.IsUnramifiedAt (𝓞 K) (w.under (𝓞 L)).asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
  isUnramifiedAt_rayClassFieldOver_of_notMem_support_of_isUnramifiedAt K (narrowModulus L)
    (by simp) hL

section CanonicalAlgebra

@[instance_reducible]
private def algebraRayClassFieldOver : Algebra L (rayClassFieldOver K 𝔪) :=
  (toRayClassFieldOver K 𝔪).toRingHom.toAlgebra

private theorem isScalarTower_left_rayClassFieldOver :
    letI := algebraRayClassFieldOver K 𝔪
    IsScalarTower K L (rayClassFieldOver K 𝔪) := by
  let _ := algebraRayClassFieldOver K 𝔪
  exact IsScalarTower.of_algebraMap_eq fun x ↦ Subtype.ext <|
    (IntermediateField.coe_algebraMap_apply _ x).trans
      (IsScalarTower.algebraMap_apply K L (SeparableClosure K) x)

private theorem isScalarTower_right_rayClassFieldOver :
    letI := algebraRayClassFieldOver K 𝔪
    IsScalarTower L (rayClassFieldOver K 𝔪) (SeparableClosure K) := by
  let _ := algebraRayClassFieldOver K 𝔪
  exact IsScalarTower.of_algebraMap_eq fun x ↦
    (IntermediateField.algebraMap_apply _ (toRayClassFieldOver K 𝔪 x)).symm

attribute [local instance] algebraRayClassFieldOver
  isScalarTower_left_rayClassFieldOver isScalarTower_right_rayClassFieldOver

variable (L) in
/-- If `L/K` is unramified at all infinite places, then so is `hilbertClassFieldOver K L / K`. -/
instance isUnramifiedAtInfinitePlaces_hilbertClassFieldOver [IsUnramifiedAtInfinitePlaces K L] :
    IsUnramifiedAtInfinitePlaces K (hilbertClassFieldOver K L) :=
  IsUnramifiedAtInfinitePlaces.trans K L (hilbertClassFieldOver K L)

/-- For `L/K` Galois and `σ ∈ Gal(Kˢ/K)`, the image of `rayClassFieldOver K 𝔪` under `σ` carries a
compatible `L`-algebra structure and is isomorphic to `rayClassField 𝔪` compatibly with `σ`'s
restriction to `L`. -/
private theorem exists_ringEquiv_map_rayClassFieldOver [IsGalois K L]
    (σ : Gal(SeparableClosure K/K)) :
    ∃ (_ : Algebra L ((rayClassFieldOver K 𝔪).map
        (σ : SeparableClosure K →ₐ[K] SeparableClosure K))),
      ∃ (_ : IsScalarTower L
          ((rayClassFieldOver K 𝔪).map (σ : SeparableClosure K →ₐ[K] SeparableClosure K))
          (SeparableClosure K)),
        ∃ g : rayClassField 𝔪 ≃+*
            (rayClassFieldOver K 𝔪).map (σ : SeparableClosure K →ₐ[K] SeparableClosure K),
          (algebraMap L
              ((rayClassFieldOver K 𝔪).map
                (σ : SeparableClosure K →ₐ[K] SeparableClosure K))).comp
            ((σ.restrictNormal L).toRingEquiv : L →+* L) =
            (g : rayClassField 𝔪 →+* _).comp (algebraMap L (rayClassField 𝔪)) := by
  let H := rayClassFieldOver K 𝔪
  let Hσ := H.map (σ : SeparableClosure K →ₐ[K] SeparableClosure K)
  have hmem (a : L) : algebraMap L (SeparableClosure K) a ∈ Hσ := by
    let b := (σ.restrictNormal L).symm a
    have hσb : (σ : SeparableClosure K →ₐ[K] SeparableClosure K)
        (algebraMap L (SeparableClosure K) b) ∈ Hσ :=
      (H.map_mem_map _).mpr (algebraMap_mem_rayClassFieldOver K 𝔪 b)
    rwa [AlgEquiv.coe_toAlgHom, ← AlgEquiv.restrictNormal_commutes σ L b,
      AlgEquiv.apply_symm_apply] at hσb
  let φL : L →+* Hσ := (algebraMap L (SeparableClosure K)).codRestrict Hσ hmem
  let instAlg : Algebra L Hσ := φL.toAlgebra
  have instTower : IsScalarTower L Hσ (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      ((IntermediateField.algebraMap_apply Hσ (φL x)).trans
        (RingHom.codRestrict_apply _ Hσ hmem x)).symm
  let ι : rayClassField 𝔪 →ₐ[L] SeparableClosure K := IsSepClosed.lift
  let g : rayClassField 𝔪 ≃+* Hσ :=
    (rayClassFieldOverEquivOfAlgHom K 𝔪 ι).toRingEquiv.trans
      (H.equivMap (σ : SeparableClosure K →ₐ[K] SeparableClosure K)).toRingEquiv
  refine ⟨instAlg, instTower, g, RingHom.ext fun a ↦ Subtype.ext ?_⟩
  have hEq : ((algebraMap L Hσ (σ.restrictNormal L a) : Hσ) : SeparableClosure K) =
      σ ((algebraMap L H a : H) : SeparableClosure K) :=
    ((IntermediateField.algebraMap_apply Hσ _).symm.trans <|
      (IsScalarTower.algebraMap_apply L Hσ (SeparableClosure K) _).symm.trans
        (AlgEquiv.restrictNormal_commutes σ L a)).trans <|
      congrArg σ <|
        (IsScalarTower.algebraMap_apply L H (SeparableClosure K) a).trans
          (IntermediateField.algebraMap_apply H _)
  simpa [g] using hEq

/-- If `L/K` is Galois and `𝔪` remains admissible for every extension `M/L` linked to
`rayClassField 𝔪 / L` by a ring automorphism of `L`, then `rayClassFieldOver K 𝔪` is Galois over
`K`. -/
private theorem isGalois_rayClassFieldOver_of_forall_isAdmissibleModulus [IsGalois K L]
    (hadm : ∀ {M : Type} [Field M] [NumberField M] [Algebra L M] [IsAbelianGalois L M]
      (f : L ≃+* L) (g : rayClassField 𝔪 ≃+* M),
      (algebraMap L M).comp (f : L →+* L) =
        (g : rayClassField 𝔪 →+* M).comp (algebraMap L (rayClassField 𝔪)) →
      IsAdmissibleModulus L M 𝔪) :
    IsGalois K (rayClassFieldOver K 𝔪) := by
  have : Normal K (rayClassFieldOver K 𝔪) := by
    refine IntermediateField.normal_iff_forall_map_le'.mpr fun σ ↦ ?_
    obtain ⟨instAlg, instTower, g, hcomp⟩ := exists_ringEquiv_map_rayClassFieldOver K 𝔪 σ
    let Hσ := (rayClassFieldOver K 𝔪).map (σ : SeparableClosure K →ₐ[K] SeparableClosure K)
    have : NumberField Hσ := .of_ringEquiv _ _ g
    have : IsAbelianGalois L Hσ :=
      IsAbelianGalois.of_equiv_equiv (σ.restrictNormal L).toRingEquiv g hcomp
    have hle := (isAdmissibleModulus_iff_le_rayClassFieldOver K 𝔪
      (IsScalarTower.toAlgHom L Hσ (SeparableClosure K))).mp
        (hadm (σ.restrictNormal L).toRingEquiv g hcomp)
    intro x hx
    exact hle ⟨⟨x, hx⟩, IntermediateField.algebraMap_apply Hσ ⟨x, hx⟩⟩
  exact {}

variable (L) in
/-- **The Hilbert class field of a Galois subextension `L/K` is Galois over `K`.** Every conjugate
of `hilbertClassFieldOver K L` over `K` is an everywhere-unramified abelian extension of `L`, hence
lies in `hilbertClassFieldOver K L` by maximality of the Hilbert class field. -/
instance isGalois_hilbertClassFieldOver [IsGalois K L] :
    IsGalois K (hilbertClassFieldOver K L) :=
  isGalois_rayClassFieldOver_of_forall_isAdmissibleModulus K (Modulus.one L)
    fun f g hcomp ↦ isAdmissibleModulus_one_iff.mpr
      ⟨(RingEquiv.forall_heightOneSpectrum_ringOfIntegers_isUnramifiedAt_iff f g hcomp).mp
          (isUnramifiedAt_hilbertClassField L),
        IsUnramifiedAtInfinitePlaces.of_equiv_equiv f g hcomp⟩

variable (L) in
/-- **The narrow Hilbert class field of a Galois subextension `L/K` is Galois over `K`.** Every
conjugate of `narrowHilbertClassFieldOver K L` over `K` is an abelian extension of `L` unramified
at all finite primes, hence lies in `narrowHilbertClassFieldOver K L` by maximality of the narrow
Hilbert class field. -/
instance isGalois_narrowHilbertClassFieldOver [IsGalois K L] :
    IsGalois K (narrowHilbertClassFieldOver K L) :=
  isGalois_rayClassFieldOver_of_forall_isAdmissibleModulus K (narrowModulus L)
    fun f g hcomp ↦ isAdmissibleModulus_narrowModulus_iff.mpr <|
      (RingEquiv.forall_heightOneSpectrum_ringOfIntegers_isUnramifiedAt_iff f g hcomp).mp
        (isUnramifiedAt_narrowHilbertClassField L)

end CanonicalAlgebra

end RelativeClassFields

end TauCeti.ClassFieldTheory
